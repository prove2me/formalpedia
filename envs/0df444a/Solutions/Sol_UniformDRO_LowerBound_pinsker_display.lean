-- Prove2me | solution 1 for UniformDRO.LowerBound.pinsker_display
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T16:06:44.675081+00:00
-- url     : https://prove2.me/submissions/dae22e7e-3a34-47f3-8433-ab5d95e4445c

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_UniformDRO_LowerBound_Setting

open Real Set

/-- the binary divergence as a function of the second argument -/
noncomputable def binKL (a b : ℝ) : ℝ := a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b))

lemma binKL_deriv (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    HasDerivAt (fun x => binKL a x - 2 * (a - x) ^ 2)
      ((b - a) * (1 / (b * (1 - b)) - 4)) b := by
  set g : ℝ → ℝ := fun x => a * Real.log a - a * Real.log x + (1 - a) * Real.log (1 - a)
    - (1 - a) * Real.log (1 - x) - 2 * (a - x) ^ 2 with hg
  have hlog1 : HasDerivAt (fun x => Real.log (1 - x)) (-1 / (1 - b)) b := by
    have hd : HasDerivAt (fun x => 1 - x) (-1) b := by simpa using (hasDerivAt_id b).const_sub 1
    have := hd.log (by linarith)
    simpa using this
  have hsq : HasDerivAt (fun x => 2 * (a - x) ^ 2) (2 * (2 * (a - b) * (-1))) b := by
    have hd : HasDerivAt (fun x => a - x) (-1) b := by simpa using (hasDerivAt_id b).const_sub a
    have := (hd.pow 2).const_mul 2
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have hgd : HasDerivAt g (-(a * b⁻¹) - (1 - a) * (-1 / (1 - b)) - 2 * (2 * (a - b) * (-1))) b := by
    have := ((((hasDerivAt_const b (a * Real.log a)).sub ((Real.hasDerivAt_log hb0.ne').const_mul a)).add
      (hasDerivAt_const b ((1 - a) * Real.log (1 - a)))).sub (hlog1.const_mul (1 - a))).sub hsq
    refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv (by ring)
    simp [hg]
  have hev : (fun x => binKL a x - 2 * (a - x) ^ 2) =ᶠ[nhds b] g := by
    filter_upwards [Ioo_mem_nhds hb0 hb1] with x hx
    simp only [binKL, hg]
    rw [Real.log_div ha0.ne' hx.1.ne', Real.log_div (by linarith) (by linarith [hx.2])]; ring
  refine (hgd.congr_of_eventuallyEq hev).congr_deriv ?_
  have : (1 - b) ≠ 0 := by linarith
  have : b ≠ 0 := hb0.ne'
  field_simp; ring

/-- binary Pinsker: `kl(a,b) ≥ 2 (a-b)²` on the open square -/
theorem binary_pinsker (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ binKL a b := by
  set f := fun x => binKL a x - 2 * (a - x) ^ 2 with hf
  have hfa : f a = 0 := by simp [hf, binKL, div_self ha0.ne', div_self (by linarith : (1:ℝ) - a ≠ 0)]
  have hfac : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ 1 / (x * (1 - x)) - 4 := by
    intro x hx
    have hp : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
    rw [sub_nonneg, le_div_iff₀ hp]; nlinarith [sq_nonneg (x - 1 / 2)]
  have hcont : ∀ c d, 0 < c → d < 1 → ContinuousOn f (Icc c d) := by
    intro c d hc hd x hx
    exact (binKL_deriv a x ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
  rcases le_total a b with hab | hba
  · -- f increases on [a, b]
    have hmono : MonotoneOn f (Icc a b) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (hcont a b ha0 hb1)
      · intro x hx; rw [interior_Icc] at hx
        exact (binKL_deriv a x ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
      · intro x hx; rw [interior_Icc] at hx
        rw [(binKL_deriv a x ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])).deriv]
        exact mul_nonneg (by linarith [hx.1]) (hfac x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    simp only [hf] at this hfa; linarith
  · -- f decreases on [b, a]
    have hanti : AntitoneOn f (Icc b a) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc b a) (hcont b a hb0 ha1)
      · intro x hx; rw [interior_Icc] at hx
        exact (binKL_deriv a x ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
      · intro x hx; rw [interior_Icc] at hx
        rw [(binKL_deriv a x ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])).deriv]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) (hfac x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have := hanti ⟨le_rfl, hba⟩ ⟨hba, le_rfl⟩ hba
    simp only [hf] at this hfa; linarith

/-- binary Pinsker on the closed range of the first argument -/
theorem binary_pinsker' (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ binKL a b := by
  -- `a ↦ binKL a b - 2 (a - b)^2` is continuous on ℝ
  have hc : Continuous (fun x : ℝ => binKL x b - 2 * (x - b) ^ 2) := by
    have e : (fun x : ℝ => binKL x b) = fun x => (x * Real.log x - x * Real.log b)
        + ((1 - x) * Real.log (1 - x) - (1 - x) * Real.log (1 - b)) := by
      funext x
      simp only [binKL]
      rcases eq_or_ne x 0 with h0 | h0
      · subst h0; simp
      rcases eq_or_ne (1 - x) 0 with h1 | h1
      · rw [h1]; simp [Real.log_div h0 hb0.ne']; ring
      rw [Real.log_div h0 hb0.ne', Real.log_div h1 (by linarith)]; ring
    rw [show (fun x : ℝ => binKL x b - 2 * (x - b) ^ 2)
        = fun x => ((x * Real.log x - x * Real.log b)
          + ((1 - x) * Real.log (1 - x) - (1 - x) * Real.log (1 - b))) - 2 * (x - b) ^ 2 from by
        funext x; rw [show binKL x b = _ from congrFun e x]]
    have h1 := Real.continuous_mul_log
    have h2 : Continuous (fun x : ℝ => (1 - x) * Real.log (1 - x)) :=
      h1.comp (continuous_const.sub continuous_id)
    fun_prop
  -- the interior points are dense near the endpoints
  have hclosed : IsClosed {x : ℝ | 0 ≤ binKL x b - 2 * (x - b) ^ 2} :=
    isClosed_le continuous_const hc
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {x : ℝ | 0 ≤ binKL x b - 2 * (x - b) ^ 2} := by
    intro x hx
    have := binary_pinsker x b hx.1 hx.2 hb0 hb1
    simp only [Set.mem_setOf_eq]; nlinarith [sq_nonneg (x - b), sq_nonneg (b - x)]
  have hcl := hclosed.closure_subset_iff.mpr hsub
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hcl
  have := hcl ⟨ha0, ha1⟩
  simp only [Set.mem_setOf_eq] at this
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - a)]


open Finset Real

/-- Cover–Thomas Theorem 2.7.1 (log-sum inequality), for `a ≥ 0`, `b > 0`. -/
theorem log_sum_ineq {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 < b i) (hs : s.Nonempty) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤ ∑ i ∈ s, a i * Real.log (a i / b i) := by
  set B := ∑ i ∈ s, b i with hB
  have hB0 : 0 < B := Finset.sum_pos hb hs
  -- Jensen for φ(x) = x log x with weights b_i / B at points a_i / b_i
  have hJ := convexOn_mul_log.map_sum_le (t := s) (w := fun i => b i / B) (p := fun i => a i / b i)
    (fun i hi => (div_pos (hb i hi) hB0).le) (by rw [← Finset.sum_div, div_self hB0.ne'])
    (fun i hi => Set.mem_Ici.mpr (div_nonneg (ha i hi) (hb i hi).le))
  have e1 : ∑ i ∈ s, (b i / B) • (a i / b i) = (∑ i ∈ s, a i) / B := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun i hi => ?_)
    have := (hb i hi).ne'; rw [smul_eq_mul]; field_simp
  have e2 : ∑ i ∈ s, (b i / B) • ((a i / b i) * Real.log (a i / b i))
      = (∑ i ∈ s, a i * Real.log (a i / b i)) / B := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun i hi => ?_)
    have := (hb i hi).ne'; rw [smul_eq_mul]; field_simp
  rw [e1, e2] at hJ
  have := mul_le_mul_of_nonneg_left hJ hB0.le
  rw [mul_div_cancel₀ _ hB0.ne'] at this
  calc (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / B)
      = B * ((∑ i ∈ s, a i) / B * Real.log ((∑ i ∈ s, a i) / B)) := by field_simp
    _ ≤ _ := this


/-- finite Pinsker: `½ (Σ |P - Q|)² ≤ Σ P log (P / Q)` for distributions with `Q > 0` -/
theorem finite_pinsker {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i)
    (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    (1 / 2) * (∑ i, |P i - Q i|) ^ 2 ≤ ∑ i, P i * Real.log (P i / Q i) := by
  classical
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hQ1; norm_num at hQ1
  set A := Finset.univ.filter (fun i => Q i < P i) with hA
  set Ac := Finset.univ.filter (fun i => ¬ Q i < P i) with hAc
  set a := ∑ i ∈ A, P i
  set b := ∑ i ∈ A, Q i
  have hsplitP : ∑ i ∈ A, P i + ∑ i ∈ Ac, P i = 1 := by rw [← hP1, Finset.sum_filter_add_sum_filter_not]
  have hsplitQ : ∑ i ∈ A, Q i + ∑ i ∈ Ac, Q i = 1 := by rw [← hQ1, Finset.sum_filter_add_sum_filter_not]
  have hsplitK : ∑ i ∈ A, P i * Real.log (P i / Q i) + ∑ i ∈ Ac, P i * Real.log (P i / Q i)
      = ∑ i, P i * Real.log (P i / Q i) := Finset.sum_filter_add_sum_filter_not _ _ _
  -- L1 distance = 2 (a - b)
  have hL1 : ∑ i, |P i - Q i| = 2 * (a - b) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => Q i < P i)]
    have h1 : ∑ i ∈ A, |P i - Q i| = a - b := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i hi => abs_of_pos (by have := (Finset.mem_filter.mp hi).2; linarith))
    have h2 : ∑ i ∈ Ac, |P i - Q i| = (∑ i ∈ Ac, Q i) - ∑ i ∈ Ac, P i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i hi => by
        have := (Finset.mem_filter.mp hi).2; rw [abs_of_nonpos (by linarith)]; ring)
    rw [← hA, ← hAc, h1, h2]; linarith
  -- RHS ≥ 0 (Gibbs) for the degenerate cases
  have hgibbs : 0 ≤ ∑ i, P i * Real.log (P i / Q i) := by
    have := log_sum_ineq Finset.univ P Q (fun i _ => hP i) (fun i _ => hQ i) hne
    rw [hP1, hQ1, div_one, Real.log_one, mul_zero] at this; exact this
  by_cases hAe : A.Nonempty
  · by_cases hAce : Ac.Nonempty
    · have hb0 : 0 < b := Finset.sum_pos (fun i _ => hQ i) hAe
      have hb1 : b < 1 := by
        have : 0 < ∑ i ∈ Ac, Q i := Finset.sum_pos (fun i _ => hQ i) hAce
        linarith
      have ha0 : 0 ≤ a := Finset.sum_nonneg (fun i _ => hP i)
      have ha1 : a ≤ 1 := by
        have : 0 ≤ ∑ i ∈ Ac, P i := Finset.sum_nonneg (fun i _ => hP i)
        linarith
      have hls1 := log_sum_ineq A P Q (fun i _ => hP i) (fun i _ => hQ i) hAe
      have hls2 := log_sum_ineq Ac P Q (fun i _ => hP i) (fun i _ => hQ i) hAce
      have hPc : ∑ i ∈ Ac, P i = 1 - a := by linarith
      have hQc : ∑ i ∈ Ac, Q i = 1 - b := by linarith
      rw [hPc, hQc] at hls2
      have hbin := binary_pinsker' a b ha0 ha1 hb0 hb1
      unfold binKL at hbin
      rw [hL1]
      nlinarith
    · -- Ac empty: P > Q everywhere, impossible with equal sums
      exfalso
      rw [Finset.not_nonempty_iff_eq_empty] at hAce
      have hlt : ∑ i, Q i < ∑ i, P i := by
        apply Finset.sum_lt_sum_of_nonempty hne
        intro i _
        by_contra h
        have : i ∈ Ac := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        rw [hAce] at this; simp at this
      linarith
  · -- A empty: P ≤ Q, equal sums force a = b = 0
    rw [Finset.not_nonempty_iff_eq_empty] at hAe
    have : a = 0 ∧ b = 0 := by simp [a, b, hAe]
    rw [hL1, this.1, this.2]; simpa using hgibbs


open UniformDRO.LowerBound

theorem solution (n : ℕ) (p₁ p₂ : ℝ) (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Icc (0 : ℝ) 1) :
    tvDist n p₁ p₂ ^ 2 ≤ n / 2 * BanditAlgorithm.bernoulliRelativeEntropy p₂ p₁ := by
  classical
  obtain ⟨h10, h11⟩ := hp₁
  obtain ⟨h20, h21⟩ := hp₂
  set w : ℝ → Bool → ℝ := fun p x => if x then p else 1 - p with hw
  have hSP : ∀ p (b : Fin n → Bool), sampleProb p b = ∏ i, w p (b i) := fun p b => rfl
  have hsum : ∀ p, ∑ b : Fin n → Bool, sampleProb p b = 1 := by
    intro p; simp only [hSP]
    rw [← Fintype.prod_sum (fun (_ : Fin n) (x : Bool) => w p x)]; simp [hw]
  have hw1 : ∀ x, 0 < w p₁ x := fun x => by cases x <;> simp [hw] <;> linarith
  have hw2 : ∀ x, 0 ≤ w p₂ x := fun x => by cases x <;> simp [hw] <;> linarith
  set h : Bool → ℝ := fun x => Real.log (w p₂ x / w p₁ x) with hh
  -- tensorization of the divergence
  have hpt : ∀ b : Fin n → Bool, sampleProb p₂ b * Real.log (sampleProb p₂ b / sampleProb p₁ b)
      = sampleProb p₂ b * ∑ i, h (b i) := by
    intro b
    by_cases h0 : sampleProb p₂ b = 0
    · rw [h0, zero_mul, zero_mul]
    · congr 1
      have hpos : ∀ i, w p₂ (b i) ≠ 0 := by
        intro i hi; apply h0; rw [hSP]; exact Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [hSP, hSP, ← Finset.prod_div_distrib, Real.log_prod]
      intro i _; exact div_ne_zero (hpos i) (hw1 _).ne'
  have hmarg : ∀ i : Fin n, ∑ b : Fin n → Bool, sampleProb p₂ b * h (b i)
      = BanditAlgorithm.bernoulliRelativeEntropy p₂ p₁ := by
    intro i
    have e : ∀ b : Fin n → Bool, sampleProb p₂ b * h (b i)
        = ∏ j, (fun (j : Fin n) (x : Bool) => w p₂ x * (if j = i then h x else 1)) j (b j) := by
      intro b
      rw [hSP, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i]; simp
    simp_rw [e]
    rw [← Fintype.prod_sum (fun (j : Fin n) (x : Bool) => w p₂ x * (if j = i then h x else 1))]
    rw [Finset.prod_eq_single i]
    · simp [hw, hh, BanditAlgorithm.bernoulliRelativeEntropy]
    · intro j _ hj; simp [hj, hw]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hKL : ∑ b : Fin n → Bool, sampleProb p₂ b * Real.log (sampleProb p₂ b / sampleProb p₁ b)
      = n * BanditAlgorithm.bernoulliRelativeEntropy p₂ p₁ := by
    simp_rw [hpt, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hmarg]; simp
  -- finite Pinsker
  have hP := finite_pinsker (fun b => sampleProb p₂ b) (fun b => sampleProb p₁ b)
    (fun b => by rw [hSP]; exact Finset.prod_nonneg (fun i _ => hw2 _))
    (fun b => by rw [hSP]; exact Finset.prod_pos (fun i _ => hw1 _)) (hsum p₂) (hsum p₁)
  rw [hKL] at hP
  have hTV : tvDist n p₁ p₂ = (1 / 2) * ∑ b : Fin n → Bool, |sampleProb p₂ b - sampleProb p₁ b| := by
    unfold tvDist; congr 1; refine Finset.sum_congr rfl (fun b _ => abs_sub_comm _ _)
  rw [hTV]
  nlinarith [hP]
