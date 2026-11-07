-- Prove2me | solution 1 for WaitJudge.Convex.inf_poly_eq_gammaStar
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T23:48:33.844938+00:00
-- url     : https://prove2.me/submissions/33175aaa-bf06-4faf-9438-c6964b964d80

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_WaitJudge_Convex_Setting
import Theorems.Thm_WaitJudge_Convex_iteratedDeriv_pow_div_factorial

open MeasureTheory ScenarioApproach.Generalization WaitJudge.Convex

theorem solution (N d : ℕ) (ε : ℕ → ℝ) (hε : ∀ k ≤ d, 0 ≤ ε k ∧ ε k ≤ 1) :
    sInf {y | ∃ q : Polynomial ℝ, IsFeasible10 N d ε (fun t => q.eval t) ∧ y = q.eval 1} =
      gammaStar N d ε := by
  classical
  set s : Set ℝ := Set.Icc 0 1 with hsdef
  have hs : UniqueDiffOn ℝ s := uniqueDiffOn_Icc zero_lt_one
  -- (1/k!) D^k of an explicit polynomial function, via (23)
  have key : ∀ (cf : ℕ → ℝ) (M k : ℕ) (t : ℝ),
      (1 / (k.factorial : ℝ)) * iteratedDeriv k (fun t => ∑ m ∈ Finset.range (M + 1), cf m * t ^ m) t =
        ∑ m ∈ Finset.Icc k M, cf m * (m.choose k : ℝ) * t ^ (m - k) := by
    intro cf M k t
    rw [iteratedDeriv_fun_sum (fun i _ => by fun_prop), Finset.mul_sum]
    have h1 : ∀ m ∈ Finset.range (M + 1), (1 / (k.factorial : ℝ)) *
        iteratedDeriv k (fun t => cf m * t ^ m) t =
          if m < k then 0 else cf m * (m.choose k : ℝ) * t ^ (m - k) := by
      intro m _
      rw [iteratedDeriv_const_mul_field, mul_left_comm, iteratedDeriv_pow_div_factorial]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl h1, Finset.sum_ite, Finset.sum_const_zero, zero_add]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
  have hfd : ∀ (cf : ℕ → ℝ) (M : ℕ),
      ContDiff ℝ ⊤ (fun t : ℝ => ∑ m ∈ Finset.range (M + 1), cf m * t ^ m) := by
    intro cf M; fun_prop
  have hwithin : ∀ (cf : ℕ → ℝ) (M k : ℕ) (t : ℝ), t ∈ s →
      iteratedDerivWithin k (fun t => ∑ m ∈ Finset.range (M + 1), cf m * t ^ m) s t =
        iteratedDeriv k (fun t => ∑ m ∈ Finset.range (M + 1), cf m * t ^ m) t := by
    intro cf M k t ht
    exact iteratedDerivWithin_eq_iteratedDeriv hs ((hfd cf M).of_le le_top).contDiffAt ht
  have hevalpoly : ∀ (cf : ℕ → ℝ) (M : ℕ),
      (fun t => (∑ m ∈ Finset.range (M + 1), Polynomial.C (cf m) * Polynomial.X ^ m).eval t) =
        fun t => ∑ m ∈ Finset.range (M + 1), cf m * t ^ m := by
    intro cf M; funext t; simp [Polynomial.eval_finset_sum]
  -- feasible values are nonnegative
  have hnonneg : ∀ ξ : ℝ → ℝ, IsFeasible10 N d ε ξ → 0 ≤ ξ 1 := by
    intro ξ hξ
    have h := hξ.2 0 (Nat.zero_le _) 1 ⟨zero_le_one, le_rfl⟩
    simp only [iteratedDerivWithin_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      one_mul] at h
    have : 0 ≤ (N.choose 0 : ℝ) * (1 : ℝ) ^ (N - 0) * Set.indicator (Set.Ico 0 (1 - ε 0)) 1 1 :=
      mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    linarith
  -- t ^ N is a feasible polynomial
  have hfeasN : IsFeasible10 N d ε (fun t => (Polynomial.X ^ N : Polynomial ℝ).eval t) := by
    have hfun : (fun t => (Polynomial.X ^ N : Polynomial ℝ).eval t) = fun t : ℝ => t ^ N := by
      funext t; simp
    rw [hfun]
    refine ⟨by fun_prop, fun k hk t ht => ?_⟩
    rw [iteratedDerivWithin_eq_iteratedDeriv hs (by fun_prop) ht, iteratedDeriv_pow_div_factorial]
    by_cases hkN : N < k
    · rw [if_pos hkN, Nat.choose_eq_zero_of_lt hkN]; simp
    · rw [if_neg hkN]
      have h0 : 0 ≤ (N.choose k : ℝ) * t ^ (N - k) := by have := ht.1; positivity
      have hind : Set.indicator (Set.Ico 0 (1 - ε k)) (1 : ℝ → ℝ) t ≤ 1 := by
        unfold Set.indicator; split_ifs <;> simp
      calc (N.choose k : ℝ) * t ^ (N - k) * Set.indicator (Set.Ico 0 (1 - ε k)) 1 t
          ≤ (N.choose k : ℝ) * t ^ (N - k) * 1 := mul_le_mul_of_nonneg_left hind h0
        _ = _ := mul_one _
  set PS := {y | ∃ q : Polynomial ℝ, IsFeasible10 N d ε (fun t => q.eval t) ∧ y = q.eval 1}
    with hPS
  set BS := {y | ∃ ξ, IsFeasible10 N d ε ξ ∧ y = ξ 1} with hBS
  have hPSne : PS.Nonempty := ⟨_, _, hfeasN, rfl⟩
  have hBSne : BS.Nonempty := ⟨_, _, hfeasN, rfl⟩
  have hPSbdd : BddBelow PS := ⟨0, by rintro y ⟨q, hq, rfl⟩; exact hnonneg _ hq⟩
  have hBSbdd : BddBelow BS := ⟨0, by rintro y ⟨ξ, hξ, rfl⟩; exact hnonneg _ hξ⟩
  -- density: every feasible ξ is approached from above by feasible polynomials
  have hdense : ∀ ξ : ℝ → ℝ, IsFeasible10 N d ε ξ → ∀ η > 0,
      ∃ q : Polynomial ℝ, IsFeasible10 N d ε (fun t => q.eval t) ∧ q.eval 1 ≤ ξ 1 + η := by
    intro ξ hξ η hη
    set δ : ℝ := η / (d + 2) with hδ
    have hδpos : 0 < δ := by positivity
    have hgc : ContinuousOn (iteratedDerivWithin d ξ s) s :=
      hξ.1.continuousOn_iteratedDerivWithin le_rfl hs
    obtain ⟨r, hr⟩ := exists_polynomial_near_of_continuousOn 0 1 _ hgc δ hδpos
    set M := d + r.natDegree with hM
    set a : ℕ → ℝ := fun k => iteratedDerivWithin k ξ s 0 with ha
    set cf : ℕ → ℝ := fun m => if m < d then a m / (m.factorial : ℝ)
      else r.coeff (m - d) / ((d.factorial : ℝ) * (m.choose d : ℝ)) with hcf
    set f : ℝ → ℝ := fun t => ∑ m ∈ Finset.range (M + 1), cf m * t ^ m with hf
    -- lower derivatives at 0 match
    have hF1 : ∀ k < d, iteratedDeriv k f 0 = a k := by
      intro k hk
      have h := key cf M k 0
      rw [Finset.sum_eq_single k] at h
      · simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, pow_zero, hcf,
          if_pos hk] at h
        have hkf : (k.factorial : ℝ) ≠ 0 := by positivity
        field_simp at h
        linarith
      · intro m hm hmk
        have : 0 < m - k := by simp at hm; omega
        simp [zero_pow this.ne']
      · intro hk'; simp at hk'; omega
    -- top derivative is r
    have hF2 : ∀ t, iteratedDeriv d f t = r.eval t := by
      intro t
      have h := key cf M d t
      have hsum : ∑ m ∈ Finset.Icc d M, cf m * (m.choose d : ℝ) * t ^ (m - d) =
          (1 / (d.factorial : ℝ)) * r.eval t := by
        have h1 : ∀ m ∈ Finset.Icc d M, cf m * (m.choose d : ℝ) * t ^ (m - d) =
            (1 / (d.factorial : ℝ)) * (r.coeff (m - d) * t ^ (m - d)) := by
          intro m hm
          simp only [Finset.mem_Icc] at hm
          have hc : (m.choose d : ℝ) ≠ 0 := by
            have := Nat.choose_pos hm.1; positivity
          have hdf : (d.factorial : ℝ) ≠ 0 := by positivity
          simp only [hcf, if_neg (show ¬ m < d by omega)]
          field_simp
        rw [Finset.sum_congr rfl h1, ← Finset.mul_sum,
          Polynomial.eval_eq_sum_range' (show r.natDegree < r.natDegree + 1 by omega)]
        congr 1
        rw [show Finset.Icc d M = Finset.Ico d (M + 1) by rfl, Finset.sum_Ico_eq_sum_range,
          show M + 1 - d = r.natDegree + 1 by omega]
        apply Finset.sum_congr rfl; intro j _; simp
      rw [hsum] at h
      have hdf : (1 / (d.factorial : ℝ)) ≠ 0 := by positivity
      exact mul_left_cancel₀ hdf h
    -- error estimates by downward induction
    set D : ℕ → ℝ → ℝ := fun k t => iteratedDerivWithin k ξ s t - iteratedDeriv k f t with hD
    have herr : ∀ j ≤ d, ∀ t ∈ s, |D (d - j) t| ≤ δ := by
      intro j
      induction j with
      | zero =>
        intro _ t ht
        simp only [hD, Nat.sub_zero, hF2]
        rw [abs_sub_comm]; exact (hr t ht).le
      | succ j ih =>
        intro hj t ht
        set k := d - (j + 1) with hk
        have hk1 : k + 1 = d - j := by omega
        have hkd : k < d := by omega
        have hdiff1 : DifferentiableOn ℝ (iteratedDerivWithin k ξ s) s :=
          hξ.1.differentiableOn_iteratedDerivWithin (by exact_mod_cast hkd) hs
        have hdiff2 : Differentiable ℝ (iteratedDeriv k f) :=
          (hfd cf M).differentiable_iteratedDeriv k (by exact_mod_cast WithTop.coe_lt_top _)
        have hDdiff : DifferentiableOn ℝ (D k) s := fun x hx =>
          (hdiff1 x hx).sub (hdiff2 x).differentiableWithinAt
        have hder : ∀ x ∈ s, derivWithin (D k) s x = D (k + 1) x := by
          intro x hx
          simp only [hD]
          rw [derivWithin_fun_sub (hdiff1 x hx) (hdiff2 x).differentiableWithinAt,
            (hdiff2 x).derivWithin (hs x hx), ← iteratedDerivWithin_succ, ← iteratedDeriv_succ]
        have hbound : ∀ x ∈ s, ‖derivWithin (D k) s x‖ ≤ δ := by
          intro x hx
          rw [hder x hx, hk1, Real.norm_eq_abs]
          exact ih (by omega) x hx
        have h0 : (0 : ℝ) ∈ s := ⟨le_rfl, zero_le_one⟩
        have hmv := Convex.norm_image_sub_le_of_norm_derivWithin_le hDdiff hbound (convex_Icc 0 1) h0 ht
        have hD0 : D k 0 = 0 := by simp only [hD, hF1 k hkd, ha, sub_self]
        rw [hD0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at hmv
        have : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
        calc |D k t| ≤ δ * |t| := hmv
          _ ≤ δ * 1 := mul_le_mul_of_nonneg_left this hδpos.le
          _ = δ := mul_one δ
    have herr' : ∀ k ≤ d, ∀ t ∈ s, |D k t| ≤ δ := by
      intro k hk t ht
      have := herr (d - k) (by omega) t ht
      rwa [show d - (d - k) = k by omega] at this
    -- the shifted polynomial
    set cf' : ℕ → ℝ := fun m => cf m + δ * (if m ≤ d then 1 else 0) with hcf'
    refine ⟨∑ m ∈ Finset.range (M + 1), Polynomial.C (cf' m) * Polynomial.X ^ m, ?_, ?_⟩
    · rw [hevalpoly]
      refine ⟨(hfd cf' M).contDiffOn.of_le le_top, fun k hk t ht => ?_⟩
      rw [hwithin cf' M k t ht, key]
      have hsplit : ∑ m ∈ Finset.Icc k M, cf' m * (m.choose k : ℝ) * t ^ (m - k) =
          (1 / (k.factorial : ℝ)) * iteratedDeriv k f t +
            δ * ∑ m ∈ Finset.Icc k M, (if m ≤ d then 1 else 0) * (m.choose k : ℝ) * t ^ (m - k) := by
        rw [hf, key cf M k t, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro m _; simp only [hcf']; ring
      have hone : 1 ≤ ∑ m ∈ Finset.Icc k M, (if m ≤ d then (1 : ℝ) else 0) *
          (m.choose k : ℝ) * t ^ (m - k) := by
        have hmem : k ∈ Finset.Icc k M := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
        have := Finset.single_le_sum (f := fun m => (if m ≤ d then (1 : ℝ) else 0) *
          (m.choose k : ℝ) * t ^ (m - k)) (fun m _ => by
            have := ht.1; split_ifs <;> positivity) hmem
        simpa [if_pos hk] using this
      rw [hsplit]
      have hfeas := hξ.2 k hk t ht
      have hek := herr' k hk t ht
      simp only [hD] at hek
      have hkf : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero k)
      have hinv : 0 < 1 / (k.factorial : ℝ) := by positivity
      have hinvle : 1 / (k.factorial : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hkf
      have h1 : (1 / (k.factorial : ℝ)) * iteratedDerivWithin k ξ s t - δ ≤
          (1 / (k.factorial : ℝ)) * iteratedDeriv k f t := by
        have h2 : iteratedDerivWithin k ξ s t - δ ≤ iteratedDeriv k f t := by
          linarith [(abs_le.1 hek).2]
        have h3 : (1 / (k.factorial : ℝ)) * (iteratedDerivWithin k ξ s t - δ) ≤
            (1 / (k.factorial : ℝ)) * iteratedDeriv k f t :=
          mul_le_mul_of_nonneg_left h2 hinv.le
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hone hδpos.le]
    · have hev := congrFun (hevalpoly cf' M) 1
      rw [hev]
      have h0 := herr' 0 (Nat.zero_le _) 1 ⟨zero_le_one, le_rfl⟩
      simp only [hD, iteratedDerivWithin_zero, iteratedDeriv_zero, hf] at h0
      have hsum : ∑ m ∈ Finset.range (M + 1), cf' m * (1 : ℝ) ^ m =
          (∑ m ∈ Finset.range (M + 1), cf m * (1 : ℝ) ^ m) + δ * (d + 1) := by
        simp only [hcf', one_pow, mul_one, Finset.sum_add_distrib, ← Finset.mul_sum]
        congr 2
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          mul_one]
        have : (Finset.range (M + 1)).filter (fun m => m ≤ d) = Finset.range (d + 1) := by
          ext m; simp; omega
        rw [this, Finset.card_range]; push_cast; ring
      rw [hsum]
      have hle := (abs_le.1 h0).1
      have : δ * (d + 2) = η := by rw [hδ]; field_simp
      nlinarith
  apply le_antisymm
  · -- polynomial infimum ≤ γ*
    apply le_csInf hBSne
    rintro y ⟨ξ, hξ, rfl⟩
    apply le_of_forall_pos_le_add
    intro η hη
    obtain ⟨q, hq, hq1⟩ := hdense ξ hξ η hη
    exact (csInf_le hPSbdd ⟨q, hq, rfl⟩).trans hq1
  · apply le_csInf hPSne
    rintro y ⟨q, hq, rfl⟩
    exact csInf_le hBSbdd ⟨_, hq, rfl⟩
