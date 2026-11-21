-- Prove2me | solution 1 for TranspositionIID.Main.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:28:45.449434+00:00
-- url     : https://prove2.me/submissions/2dc1d33d-8ae5-44f5-8a36-da1fd6a3c3b7

import Mathlib
import Definitions.Def_TranspositionIID_Main_Stationary
import Definitions.Def_TranspositionIID_Main_Entropy

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.Rev
open TranspositionIID.Main

variable {n : ℕ}

lemma pow_markov {S : Type*} [Fintype S] [DecidableEq S] (P : Matrix S S ℝ)
    (hP : ActuarialValuation.isFiniteMarkovKernel P) (t : ℕ) :
    (∀ a b, 0 ≤ (P ^ t) a b) ∧ ∀ a, ∑ b, (P ^ t) a b = 1 := by
  induction t with
  | zero =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · simp [Matrix.one_apply]; split_ifs <;> simp
    · simp [Matrix.one_apply]
  | succ t ih =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun c _ => mul_nonneg (ih.1 a c) (hP.1 c b)
    · rw [pow_succ]
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      calc ∑ c, ∑ b, (P ^ t) a c * P c b = ∑ c, (P ^ t) a c := by
            apply Finset.sum_congr rfl; intro c _
            rw [← Finset.mul_sum, hP.2 c, mul_one]
        _ = 1 := ih.2 a

end TranspositionIID.Main.Dev.Rev
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.Kl

open Real Set

noncomputable def G (x : ℝ) : ℝ := x * Real.log x - 5 / 2 * x + 7 - 27 / 2 * (x + 2)⁻¹
noncomputable def L (x : ℝ) : ℝ := Real.log x - 3 / 2 + 27 / 2 * ((x + 2) ^ 2)⁻¹

lemma hasDerivAt_G {x : ℝ} (hx : 0 < x) : HasDerivAt G (L x) x := by
  have h1 := Real.hasDerivAt_mul_log hx.ne'
  have h2 : HasDerivAt (fun x : ℝ => x + 2) 1 x := (hasDerivAt_id x).add_const 2
  have h3 := h2.inv (show x + 2 ≠ 0 by positivity)
  have h4 := ((h1.sub ((hasDerivAt_id x).const_mul (5 / 2))).add_const 7).sub (h3.const_mul (27 / 2))
  have h5 : HasDerivAt G _ x := h4
  convert h5 using 1
  unfold L; field_simp; ring

lemma hasDerivAt_L {x : ℝ} (hx : 0 < x) : HasDerivAt L (1 / x - 27 / (x + 2) ^ 3) x := by
  have h1 := Real.hasDerivAt_log hx.ne'
  have h2 : HasDerivAt (fun x : ℝ => (x + 2) ^ 2) (2 * (x + 2)) x := by
    have := (((hasDerivAt_id x).add_const (2 : ℝ)).pow 2)
    exact this.congr_deriv (by simp)
  have h3 := h2.inv (show (x + 2) ^ 2 ≠ 0 by positivity)
  have h4 := (h1.sub_const (3 / 2)).add (h3.const_mul (27 / 2))
  have h5 : HasDerivAt L _ x := h4
  convert h5 using 1
  field_simp; ring

lemma L_mono : MonotoneOn L (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro x hx; exact (hasDerivAt_L hx).continuousAt.continuousWithinAt
  · intro x hx; rw [interior_Ioi] at hx; exact (hasDerivAt_L hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hasDerivAt_L hx).deriv]
    have hx' : (0 : ℝ) < x := hx
    have : 27 / (x + 2) ^ 3 ≤ 1 / x := by
      rw [div_le_div_iff₀ (by positivity) hx']
      nlinarith [sq_nonneg (x - 1), mul_nonneg hx'.le (sq_nonneg (x - 1))]
    linarith

lemma L_one : L 1 = 0 := by unfold L; norm_num

lemma G_one : G 1 = 0 := by unfold G; norm_num

lemma G_contOn : ContinuousOn G (Ici 0) := by
  have e1 : ContinuousOn (fun x : ℝ => x * Real.log x) (Ici 0) :=
    Real.continuous_mul_log.continuousOn
  have e2 : ContinuousOn (fun x : ℝ => (x + 2)⁻¹) (Ici 0) :=
    ContinuousOn.inv₀ (by fun_prop) (fun y hy => by have : (0 : ℝ) ≤ y := hy; positivity)
  unfold G
  exact ((e1.sub (continuousOn_const.mul continuousOn_id)).add continuousOn_const).sub
    (continuousOn_const.mul e2)

lemma G_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ G x := by
  rcases le_total 1 x with h | h
  · have hm : MonotoneOn G (Ici 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
      · exact G_contOn.mono (fun y hy => by have : (1 : ℝ) ≤ y := hy; exact le_trans zero_le_one this)
      · intro y hy; rw [interior_Ici] at hy
        have : (0 : ℝ) < y := lt_trans zero_lt_one hy
        exact (hasDerivAt_G this).differentiableAt.differentiableWithinAt
      · intro y hy; rw [interior_Ici] at hy
        have h0 : (0 : ℝ) < y := lt_trans zero_lt_one hy
        rw [(hasDerivAt_G h0).deriv]
        have := L_mono (Set.mem_Ioi.2 (zero_lt_one' ℝ)) h0 (le_of_lt hy)
        rw [L_one] at this; exact this
    have := hm (Set.mem_Ici.2 le_rfl) h h
    rw [G_one] at this; exact this
  · have hm : AntitoneOn G (Icc 0 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      · exact G_contOn.mono (fun y hy => hy.1)
      · intro y hy; rw [interior_Icc] at hy
        exact (hasDerivAt_G hy.1).differentiableAt.differentiableWithinAt
      · intro y hy; rw [interior_Icc] at hy
        rw [(hasDerivAt_G hy.1).deriv]
        have := L_mono hy.1 (Set.mem_Ioi.2 (zero_lt_one' ℝ)) (le_of_lt hy.2)
        rw [L_one] at this; exact this
    have := hm ⟨hx, h⟩ ⟨zero_le_one, le_refl _⟩ h
    rw [G_one] at this; exact this

lemma scalar_x {x : ℝ} (hx : 0 ≤ x) :
    3 * (x - 1) ^ 2 / (2 * (x + 2)) ≤ x * Real.log x - x + 1 := by
  have h := G_nonneg hx
  have hx2 : 0 < x + 2 := by linarith
  have key : x * Real.log x - x + 1 - 3 * (x - 1) ^ 2 / (2 * (x + 2)) = G x := by
    unfold G; field_simp; ring
  linarith

/-- The scalar inequality behind Pinsker. -/
lemma scalar_ineq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    3 * (a - b) ^ 2 / (2 * (a + 2 * b)) ≤ a * Real.log (a / b) - a + b := by
  have hx : 0 ≤ a / b := div_nonneg ha hb.le
  have h := scalar_x hx
  have hab : 0 < a + 2 * b := by linarith
  have e1 : a * Real.log (a / b) - a + b = b * ((a / b) * Real.log (a / b) - a / b + 1) := by
    field_simp
  have e2 : 3 * (a - b) ^ 2 / (2 * (a + 2 * b)) = b * (3 * (a / b - 1) ^ 2 / (2 * (a / b + 2))) := by
    field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left h hb.le

lemma term_ineq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < a → 0 < b) :
    3 * (a - b) ^ 2 / (2 * (a + 2 * b)) ≤ a * Real.log (a / b) - a + b := by
  rcases hb.eq_or_lt with h | h
  · have : a = 0 := by
      by_contra hne
      have := hs (lt_of_le_of_ne ha (Ne.symm hne)); linarith
    subst this; rw [← h]; simp
  · exact scalar_ineq a b ha h

variable {X : Type*} [Fintype X]

lemma kl_ge (a b : X → ℝ) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hsa : ∑ x, a x = 1) (hsb : ∑ x, b x = 1) (hsupp : ∀ x, 0 < a x → 0 < b x) :
    ∑ x, 3 * (a x - b x) ^ 2 / (2 * (a x + 2 * b x)) ≤ ∑ x, a x * Real.log (a x / b x) := by
  have h : ∑ x, 3 * (a x - b x) ^ 2 / (2 * (a x + 2 * b x)) ≤
      ∑ x, (a x * Real.log (a x / b x) - a x + b x) :=
    Finset.sum_le_sum fun x _ => term_ineq _ _ (ha x) (hb x) (hsupp x)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsa, hsb] at h
  linarith

lemma kl_nonneg (a b : X → ℝ) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hsa : ∑ x, a x = 1) (hsb : ∑ x, b x = 1) (hsupp : ∀ x, 0 < a x → 0 < b x) :
    0 ≤ ∑ x, a x * Real.log (a x / b x) := by
  refine le_trans (Finset.sum_nonneg fun x _ => ?_) (kl_ge a b ha hb hsa hsb hsupp)
  have := ha x; have := hb x
  positivity

lemma pinsker (a b : X → ℝ) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hsa : ∑ x, a x = 1) (hsb : ∑ x, b x = 1) (hsupp : ∀ x, 0 < a x → 0 < b x) :
    (∑ x, |a x - b x|) ^ 2 ≤ 2 * ∑ x, a x * Real.log (a x / b x) := by
  classical
  have hkl := kl_ge a b ha hb hsa hsb hsupp
  set s : Finset X := Finset.univ.filter (fun x => 0 < a x + 2 * b x) with hs
  have hzero : ∀ x, ¬ (0 < a x + 2 * b x) → a x = 0 ∧ b x = 0 := by
    intro x hx
    have := ha x; have := hb x
    constructor <;> linarith
  have h1 : ∑ x, |a x - b x| = ∑ x ∈ s, |a x - b x| := by
    rw [hs, Finset.sum_filter_of_ne]
    intro x _ hne
    by_contra hx
    obtain ⟨h1, h2⟩ := hzero x hx
    apply hne; rw [h1, h2]; simp
  have h2 : ∑ x, 3 * (a x - b x) ^ 2 / (2 * (a x + 2 * b x)) =
      ∑ x ∈ s, 3 * (a x - b x) ^ 2 / (2 * (a x + 2 * b x)) := by
    rw [hs, Finset.sum_filter_of_ne]
    intro x _ hne
    by_contra hx
    obtain ⟨h1, h2⟩ := hzero x hx
    apply hne; rw [h1, h2]; simp
  have hT : ∑ x ∈ s, (a x + 2 * b x) = 3 := by
    have : ∑ x ∈ s, (a x + 2 * b x) = ∑ x, (a x + 2 * b x) := by
      rw [hs, Finset.sum_filter_of_ne]
      intro x _ hne
      by_contra hx
      obtain ⟨h1, h2⟩ := hzero x hx
      apply hne; rw [h1, h2]; simp
    rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, hsa, hsb]; norm_num
  have hpos : ∀ x ∈ s, 0 < a x + 2 * b x := fun x hx => (Finset.mem_filter.1 hx).2
  have htitu := Finset.sq_sum_div_le_sum_sq_div s (fun x => |a x - b x|) hpos
  rw [hT] at htitu
  have hR : ∑ x ∈ s, |a x - b x| ^ 2 / (a x + 2 * b x) =
      (2 / 3) * ∑ x ∈ s, 3 * (a x - b x) ^ 2 / (2 * (a x + 2 * b x)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x hx
    have := hpos x hx
    rw [sq_abs]; field_simp
  rw [hR] at htitu
  rw [h1]
  rw [h2] at hkl
  have : (∑ x ∈ s, |a x - b x|) ^ 2 / 3 ≤ (2 / 3) * ∑ x ∈ s, 3 * (a x - b x) ^ 2 / (2 * (a x + 2 * b x)) := htitu
  linarith

end TranspositionIID.Main.Dev.Kl
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L42
open TranspositionIID.Main
open TranspositionIID.Main.Dev

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma lw_nonneg (P : Matrix S S ℝ) (hP : ActuarialValuation.isFiniteMarkovKernel P) (ν : S → ℝ)
    (hν : ActuarialValuation.isFiniteStateDistribution ν) (s : ℕ) (z : S) :
    0 ≤ lawAfter P ν s z :=
  Finset.sum_nonneg fun a _ => mul_nonneg (hν.1 a) ((Rev.pow_markov P hP s).1 a z)

lemma lw_sum (P : Matrix S S ℝ) (hP : ActuarialValuation.isFiniteMarkovKernel P) (ν : S → ℝ)
    (hν : ActuarialValuation.isFiniteStateDistribution ν) (s : ℕ) :
    ∑ z, lawAfter P ν s z = 1 := by
  unfold lawAfter
  rw [Finset.sum_comm]
  calc ∑ a, ∑ z, ν a * (P ^ s) a z = ∑ a, ν a := by
        apply Finset.sum_congr rfl; intro a _
        rw [← Finset.mul_sum, (Rev.pow_markov P hP s).2 a, mul_one]
    _ = 1 := hν.2

lemma lw_zero (P : Matrix S S ℝ) (ν : S → ℝ) (z : S) : lawAfter P ν 0 z = ν z := by
  unfold lawAfter; simp [Matrix.one_apply]

lemma lw_succ (P : Matrix S S ℝ) (ν : S → ℝ) (s : ℕ) (z : S) :
    lawAfter P ν (s + 1) z = ∑ a, lawAfter P ν s a * P a z := by
  unfold lawAfter
  rw [pow_succ]
  simp_rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro c _
  ring

lemma f_succ (P : Matrix S S ℝ) (μ : S → ℝ) (hμ : ReversibleProbability P μ) (ν : S → ℝ) (s : ℕ)
    (z : S) :
    densityAfter P μ ν (s + 1) z = ∑ a, P z a * densityAfter P μ ν s a := by
  have hz := hμ.2.1 z
  unfold densityAfter
  rw [lw_succ, Finset.sum_div]
  have : ∀ a, lawAfter P ν s a * P a z / μ z = P z a * (lawAfter P ν s a / μ a) := by
    intro a
    have ha := hμ.2.1 a
    have hdb := hμ.2.2.2 a z
    field_simp
    calc lawAfter P ν s a * P a z * μ a = lawAfter P ν s a * (μ a * P a z) := by ring
      _ = lawAfter P ν s a * (μ z * P z a) := by rw [hdb]
      _ = _ := by ring
  exact Finset.sum_congr rfl fun a _ => this a

lemma dirichlet_eq (P : Matrix S S ℝ) (hP : ActuarialValuation.isFiniteMarkovKernel P)
    (μ : S → ℝ) (hμ : ReversibleProbability P μ) (u v : S → ℝ) :
    GibbsCongestion.dirichletForm P μ u v =
      ∑ x, μ x * (u x - ∑ y, P x y * u y) * v x := by
  unfold GibbsCongestion.dirichletForm
  have hexp : ∀ x y, μ x * P x y * (u x - u y) * (v x - v y) =
      μ x * P x y * (u x * v x) + μ x * P x y * (u y * v y)
        - μ x * P x y * (u x * v y) - μ x * P x y * (u y * v x) := fun x y => by ring
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hexp x y]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have t1 : ∑ x, ∑ y, μ x * P x y * (u x * v x) = ∑ x, μ x * (u x * v x) := by
    apply Finset.sum_congr rfl; intro x _
    rw [← Finset.sum_mul, ← Finset.mul_sum, hP.2 x]; ring
  have t2 : ∑ x, ∑ y, μ x * P x y * (u y * v y) = ∑ y, μ y * (u y * v y) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    rw [← Finset.sum_mul, hμ.2.2.1 y]
  have t3 : ∑ x, ∑ y, μ x * P x y * (u x * v y) = ∑ x, ∑ y, μ x * P x y * (u y * v x) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    apply Finset.sum_congr rfl; intro x _
    rw [hμ.2.2.2 y x]
  have t4 : ∑ x, ∑ y, μ x * P x y * (u y * v x) = ∑ x, μ x * (∑ y, P x y * u y) * v x := by
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro y _; ring
  rw [t1, t2, t3, t4]
  have : ∑ x, μ x * (u x - ∑ y, P x y * u y) * v x =
      ∑ x, μ x * (u x * v x) - ∑ x, μ x * (∑ y, P x y * u y) * v x := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro x _; ring
  rw [this]; ring

end TranspositionIID.Main.Dev.L42
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L42
open TranspositionIID.Main
open TranspositionIID.Main.Dev

variable {S : Type*} [Fintype S] [DecidableEq S]

noncomputable def Hs (P : Matrix S S ℝ) (μ ν : S → ℝ) (s : ℕ) : ℝ :=
  ∑ z, lawAfter P ν s z * Real.log (densityAfter P μ ν s z)

noncomputable def Ts (P : Matrix S S ℝ) (ν : S → ℝ) (s : ℕ) : ℝ :=
  ∑ z, |lawAfter P ν s z - lawAfter P ν (s + 2) z|

lemma Ts_nonneg (P : Matrix S S ℝ) (ν : S → ℝ) (s : ℕ) : 0 ≤ Ts P ν s :=
  Finset.sum_nonneg fun z _ => abs_nonneg _

lemma Ts_succ_le (P : Matrix S S ℝ) (hP : ActuarialValuation.isFiniteMarkovKernel P) (ν : S → ℝ)
    (s : ℕ) : Ts P ν (s + 1) ≤ Ts P ν s := by
  have e : s + 1 + 2 = (s + 2) + 1 := by omega
  unfold Ts
  rw [e]
  have hd : ∀ z, lawAfter P ν (s + 1) z - lawAfter P ν (s + 2 + 1) z =
      ∑ a, (lawAfter P ν s a - lawAfter P ν (s + 2) a) * P a z := by
    intro z
    rw [lw_succ P ν s z, lw_succ P ν (s + 2) z]
    simp only [sub_mul, Finset.sum_sub_distrib]
  calc ∑ z, |lawAfter P ν (s + 1) z - lawAfter P ν (s + 2 + 1) z|
      = ∑ z, |∑ a, (lawAfter P ν s a - lawAfter P ν (s + 2) a) * P a z| := by
        apply Finset.sum_congr rfl; intro z _; rw [hd z]
    _ ≤ ∑ z, ∑ a, |lawAfter P ν s a - lawAfter P ν (s + 2) a| * P a z := by
        apply Finset.sum_le_sum; intro z _
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        apply Finset.sum_congr rfl; intro a _
        rw [abs_mul, abs_of_nonneg (hP.1 a z)]
    _ = ∑ a, |lawAfter P ν s a - lawAfter P ν (s + 2) a| := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro a _
        rw [← Finset.mul_sum, hP.2 a, mul_one]

lemma Hs_nonneg (P : Matrix S S ℝ) (hP : ActuarialValuation.isFiniteMarkovKernel P)
    (μ : S → ℝ) (hμ : ReversibleProbability P μ) (ν : S → ℝ)
    (hν : ActuarialValuation.isFiniteStateDistribution ν) (s : ℕ) : 0 ≤ Hs P μ ν s := by
  have := Kl.kl_nonneg (lawAfter P ν s) μ (lw_nonneg P hP ν hν s) (fun z => (hμ.2.1 z).le)
    (lw_sum P hP ν hν s) hμ.1.2 (fun z _ => hμ.2.1 z)
  unfold Hs densityAfter
  exact this

lemma Ts_sq_le (P : Matrix S S ℝ) (hP : ActuarialValuation.isFiniteMarkovKernel P)
    (μ : S → ℝ) (hμ : ReversibleProbability P μ) (ν : S → ℝ)
    (hν : ActuarialValuation.isFiniteStateDistribution ν) (s : ℕ) :
    Ts P ν s ^ 2 ≤ 2 * (Hs P μ ν s - Hs P μ ν (s + 1)) := by
  set a : S × S → ℝ := fun xy => lawAfter P ν s xy.1 * P xy.1 xy.2 with ha
  set b : S × S → ℝ := fun xy => lawAfter P ν (s + 1) xy.2 * P xy.2 xy.1 with hb
  have hlw := lw_nonneg P hP ν hν
  have ha0 : ∀ xy, 0 ≤ a xy := fun xy => mul_nonneg (hlw s _) (hP.1 _ _)
  have hb0 : ∀ xy, 0 ≤ b xy := fun xy => mul_nonneg (hlw (s + 1) _) (hP.1 _ _)
  have hsa : ∑ xy, a xy = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [ha]
    calc ∑ x, ∑ y, lawAfter P ν s x * P x y = ∑ x, lawAfter P ν s x := by
          apply Finset.sum_congr rfl; intro x _
          rw [← Finset.mul_sum, hP.2 x, mul_one]
      _ = 1 := lw_sum P hP ν hν s
  have hsb : ∑ xy, b xy = 1 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [hb]
    calc ∑ y, ∑ x, lawAfter P ν (s + 1) y * P y x = ∑ y, lawAfter P ν (s + 1) y := by
          apply Finset.sum_congr rfl; intro y _
          rw [← Finset.mul_sum, hP.2 y, mul_one]
      _ = 1 := lw_sum P hP ν hν (s + 1)
  have hPpos : ∀ x y, 0 < P x y → 0 < P y x := by
    intro x y h
    have hdb := hμ.2.2.2 x y
    have h1 := hμ.2.1 x; have h2 := hμ.2.1 y
    have h3 : 0 < μ x * P x y := mul_pos h1 h
    rw [hdb] at h3
    exact lt_of_le_of_ne (hP.1 y x) (fun h0 => by rw [← h0] at h3; simp at h3)
  have hpos_of : ∀ r q : ℝ, 0 ≤ r → 0 ≤ q → 0 < r * q → 0 < r ∧ 0 < q := by
    intro r q hr hq h
    exact ⟨lt_of_le_of_ne hr (fun h0 => by rw [← h0] at h; simp at h),
      lt_of_le_of_ne hq (fun h0 => by rw [← h0] at h; simp at h)⟩
  have hsupp : ∀ xy, 0 < a xy → 0 < b xy := by
    rintro ⟨x, y⟩ h
    simp only [ha] at h
    obtain ⟨hl, hp⟩ := hpos_of _ _ (hlw s x) (hP.1 x y) h
    have h1 : 0 < lawAfter P ν (s + 1) y := by
      rw [lw_succ]
      exact lt_of_lt_of_le h (Finset.single_le_sum (f := fun a => lawAfter P ν s a * P a y)
        (fun a _ => mul_nonneg (hlw s a) (hP.1 a y)) (Finset.mem_univ x))
    exact mul_pos h1 (hPpos x y hp)
  have hpin := Kl.pinsker a b ha0 hb0 hsa hsb hsupp
  have hmarg : Ts P ν s ≤ ∑ xy, |a xy - b xy| := by
    rw [Fintype.sum_prod_type]
    unfold Ts
    apply Finset.sum_le_sum; intro x _
    have e1 : lawAfter P ν s x = ∑ y, a (x, y) := by
      simp only [ha]; rw [← Finset.mul_sum, hP.2 x, mul_one]
    have e2 : lawAfter P ν (s + 2) x = ∑ y, b (x, y) := by
      simp only [hb]; exact lw_succ P ν (s + 1) x
    rw [e1, e2, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hdens_pos : ∀ r x, 0 < lawAfter P ν r x → 0 < densityAfter P μ ν r x :=
    fun r x h => div_pos h (hμ.2.1 x)
  have hpt : ∀ xy, a xy * Real.log (a xy / b xy) =
      a xy * (Real.log (densityAfter P μ ν s xy.1) - Real.log (densityAfter P μ ν (s + 1) xy.2)) := by
    rintro ⟨x, y⟩
    by_cases h : a (x, y) = 0
    · simp [h]
    · have hpos : 0 < a (x, y) := lt_of_le_of_ne (ha0 _) (Ne.symm h)
      have hb' := hsupp _ hpos
      have hax := hpos
      simp only [ha] at hax
      obtain ⟨hl, hp⟩ := hpos_of _ _ (hlw s x) (hP.1 x y) hax
      have hb2 := hb'
      simp only [hb] at hb2
      obtain ⟨hl2, hp2⟩ := hpos_of _ _ (hlw (s + 1) y) (hP.1 y x) hb2
      have hdx := hdens_pos s x hl
      have hdy := hdens_pos (s + 1) y hl2
      have hμx := hμ.2.1 x; have hμy := hμ.2.1 y
      have hc : 0 < μ x * P x y := mul_pos hμx hp
      have ea : a (x, y) = densityAfter P μ ν s x * (μ x * P x y) := by
        simp only [ha]; unfold densityAfter; field_simp
      have eb : b (x, y) = densityAfter P μ ν (s + 1) y * (μ x * P x y) := by
        simp only [hb]; unfold densityAfter
        rw [hμ.2.2.2 x y]; field_simp
      have : a (x, y) / b (x, y) = densityAfter P μ ν s x / densityAfter P μ ν (s + 1) y := by
        rw [ea, eb, mul_div_mul_right _ _ hc.ne']
      rw [this, Real.log_div hdx.ne' hdy.ne']
  have hKL : ∑ xy, a xy * Real.log (a xy / b xy) = Hs P μ ν s - Hs P μ ν (s + 1) := by
    simp_rw [hpt]
    rw [Fintype.sum_prod_type]
    simp only [mul_sub, Finset.sum_sub_distrib]
    unfold Hs
    congr 1
    · apply Finset.sum_congr rfl; intro x _
      simp only [ha]
      rw [← Finset.sum_mul, ← Finset.mul_sum, hP.2 x, mul_one]
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro y _
      rw [lw_succ, Finset.sum_mul]
  have hT0 := Ts_nonneg P ν s
  calc Ts P ν s ^ 2 ≤ (∑ xy, |a xy - b xy|) ^ 2 := pow_le_pow_left₀ hT0 hmarg 2
    _ ≤ _ := by rw [← hKL]; exact hpin

end TranspositionIID.Main.Dev.L42
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L42
open TranspositionIID.Main
open TranspositionIID.Main.Dev

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma Ts_bound (P : Matrix S S ℝ) (hP : ActuarialValuation.isFiniteMarkovKernel P)
    (μ : S → ℝ) (hμ : ReversibleProbability P μ) (ν : S → ℝ)
    (hν : ActuarialValuation.isFiniteStateDistribution ν) (H : ℝ)
    (hH : Hs P μ ν 0 ≤ H) (t : ℕ) :
    ((t : ℝ) + 1) * Ts P ν t ^ 2 ≤ 2 * H := by
  have hanti : Antitone (fun s => Ts P ν s) := antitone_nat_of_succ_le (Ts_succ_le P hP ν)
  have h1 : ∀ s ∈ Finset.range (t + 1), Ts P ν t ^ 2 ≤ 2 * (Hs P μ ν s - Hs P μ ν (s + 1)) := by
    intro s hs
    have hst : s ≤ t := by have := Finset.mem_range.1 hs; omega
    have := hanti hst
    exact (pow_le_pow_left₀ (Ts_nonneg P ν t) this 2).trans (Ts_sq_le P hP μ hμ ν hν s)
  have h2 := Finset.sum_le_sum h1
  rw [Finset.sum_const, Finset.card_range, ← Finset.mul_sum, Finset.sum_range_sub'] at h2
  simp only [nsmul_eq_mul] at h2
  push_cast at h2
  have := Hs_nonneg P hP μ hμ ν hν (t + 1)
  linarith

lemma Hs_zero_le (P : Matrix S S ℝ) (μ ν : S → ℝ) (hμ : ∀ z, 0 < μ z)
    (hν : ActuarialValuation.isFiniteStateDistribution ν) (m : ℝ) (hm : 0 < m)
    (hmu : ∀ z, m ≤ μ z) : Hs P μ ν 0 ≤ Real.log (1 / m) := by
  unfold Hs
  calc ∑ z, lawAfter P ν 0 z * Real.log (densityAfter P μ ν 0 z)
      ≤ ∑ z, ν z * Real.log (1 / m) := by
        apply Finset.sum_le_sum; intro z _
        rw [lw_zero]
        rcases (hν.1 z).eq_or_lt with h | h
        · rw [← h]; simp
        · apply mul_le_mul_of_nonneg_left _ h.le
          apply Real.log_le_log
          · unfold densityAfter; rw [lw_zero]; exact div_pos h (hμ z)
          · unfold densityAfter; rw [lw_zero]
            have hν1 : ν z ≤ 1 := by
              rw [← hν.2]
              exact Finset.single_le_sum (f := ν) (fun i _ => hν.1 i) (Finset.mem_univ z)
            rw [div_le_div_iff₀ (hμ z) hm]
            nlinarith [hmu z]
    _ = Real.log (1 / m) := by rw [← Finset.sum_mul, hν.2, one_mul]

end TranspositionIID.Main.Dev.L42
end

section
set_option autoImplicit false

namespace TranspositionIID.Main
open TranspositionIID.Main.Dev
open TranspositionIID.Main.Dev.L42

theorem chk_lemma_4_2 {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : ActuarialValuation.isFiniteMarkovKernel P)
    (μ : S → ℝ) (hμ : ReversibleProbability P μ)
    (ν : S → ℝ) (hν : ActuarialValuation.isFiniteStateDistribution ν) (t : ℕ) :
    GibbsCongestion.dirichletForm P μ (smoothedDensity P μ ν t)
      (fun z => Real.log (smoothedDensity P μ ν t z)) ≤
      ((entropyCeiling μ + Real.log 3) / 3) *
        Real.sqrt (entropyCeiling μ / (2 * ((t : ℝ) + 1))) := by
  classical
  obtain ⟨z0, hz0⟩ := (Set.range_nonempty μ).csInf_mem (Set.finite_range μ)
  have hm : sInf (Set.range μ) = μ z0 := hz0.symm
  have hμmin : ∀ z, μ z0 ≤ μ z := fun z => by
    rw [← hm]; exact csInf_le (Set.finite_range μ).bddBelow ⟨z, rfl⟩
  have hm0 : 0 < μ z0 := hμ.2.1 z0
  have hμ1 : μ z0 ≤ 1 := by
    rw [← hμ.1.2]
    exact Finset.single_le_sum (f := μ) (fun i _ => hμ.1.1 i) (Finset.mem_univ z0)
  obtain ⟨H, hHdef⟩ : ∃ H, H = entropyCeiling μ := ⟨_, rfl⟩
  have hHeq : H = Real.log (1 / μ z0) := by rw [hHdef]; unfold entropyCeiling; rw [hm]
  rw [← hHdef]
  have hH0 : 0 ≤ H := by
    rw [hHeq]; exact Real.log_nonneg (by rw [le_div_iff₀ hm0]; linarith)
  have hexpH : Real.exp H = 1 / μ z0 := by rw [hHeq, Real.exp_log (by positivity)]
  have hlw := lw_nonneg P hP ν hν
  have hdens0 : ∀ s z, 0 ≤ densityAfter P μ ν s z := fun s z =>
    div_nonneg (hlw s z) (hμ.2.1 z).le
  have hlw1 : ∀ s z, lawAfter P ν s z ≤ 1 := fun s z => by
    rw [← lw_sum P hP ν hν s]
    exact Finset.single_le_sum (f := lawAfter P ν s) (fun i _ => hlw s i) (Finset.mem_univ z)
  have hdens_le : ∀ s z, densityAfter P μ ν s z ≤ Real.exp H := fun s z => by
    rw [hexpH]; unfold densityAfter
    rw [div_le_div_iff₀ (hμ.2.1 z) hm0]
    nlinarith [hlw s z, hlw1 s z, hμmin z]
  obtain ⟨g, hgdef⟩ : ∃ g, g = smoothedDensity P μ ν t := ⟨_, rfl⟩
  rw [← hgdef]
  have hg : ∀ z, g z = (1 + densityAfter P μ ν t z + densityAfter P μ ν (t + 1) z) / 3 := fun z => by
    rw [hgdef]; rfl
  have he1 : 1 ≤ Real.exp H := Real.one_le_exp hH0
  have hglow : ∀ z, 1 / 3 ≤ g z := fun z => by
    rw [hg]; linarith [hdens0 t z, hdens0 (t + 1) z]
  have hgup : ∀ z, g z ≤ Real.exp H := fun z => by
    rw [hg]; linarith [hdens_le t z, hdens_le (t + 1) z]
  have hLlow : ∀ z, -Real.log 3 ≤ Real.log (g z) := fun z => by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 3) (hglow z)
    rwa [one_div, Real.log_inv] at this
  have hLup : ∀ z, Real.log (g z) ≤ H := fun z => by
    have := Real.log_le_log (by linarith [hglow z]) (hgup z)
    rwa [Real.log_exp] at this
  have hPg : ∀ z, ∑ y, P z y * g y =
      (1 + densityAfter P μ ν (t + 1) z + densityAfter P μ ν (t + 2) z) / 3 := fun z => by
    have e : ∀ y, P z y * g y = (P z y + P z y * densityAfter P μ ν t y +
        P z y * densityAfter P μ ν (t + 1) y) / 3 := fun y => by rw [hg y]; ring
    simp_rw [e]
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, hP.2 z,
      ← f_succ P μ hμ ν t z, ← f_succ P μ hμ ν (t + 1) z]
  rw [dirichlet_eq P hP μ hμ g (fun z => Real.log (g z))]
  have hμd : ∀ s z, μ z * densityAfter P μ ν s z = lawAfter P ν s z := fun s z => by
    have := (hμ.2.1 z).ne'
    unfold densityAfter; field_simp
  have hterm : ∀ z, μ z * (g z - ∑ y, P z y * g y) * Real.log (g z) =
      (1 / 3) * ((lawAfter P ν t z - lawAfter P ν (t + 2) z) * Real.log (g z)) := fun z => by
    rw [hPg, hg, ← hμd t z, ← hμd (t + 2) z]; ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  set d : S → ℝ := fun z => lawAfter P ν t z - lawAfter P ν (t + 2) z with hd
  have hdsum : ∑ z, d z = 0 := by
    simp only [hd, Finset.sum_sub_distrib, lw_sum P hP ν hν]; ring
  have hdL : ∑ z, d z * Real.log (g z) ≤ Ts P ν t * ((H + Real.log 3) / 2) := by
    have e1 : ∑ z, d z * Real.log (g z) =
        ∑ z, d z * (Real.log (g z) - (H - Real.log 3) / 2) := by
      have : ∑ z, d z * ((H - Real.log 3) / 2) = 0 := by rw [← Finset.sum_mul, hdsum]; ring
      simp only [mul_sub, Finset.sum_sub_distrib] at this ⊢
      linarith
    rw [e1]
    calc ∑ z, d z * (Real.log (g z) - (H - Real.log 3) / 2)
        ≤ ∑ z, |d z| * ((H + Real.log 3) / 2) := by
          apply Finset.sum_le_sum; intro z _
          calc d z * (Real.log (g z) - (H - Real.log 3) / 2)
              ≤ |d z * (Real.log (g z) - (H - Real.log 3) / 2)| := le_abs_self _
            _ = |d z| * |Real.log (g z) - (H - Real.log 3) / 2| := abs_mul _ _
            _ ≤ |d z| * ((H + Real.log 3) / 2) := by
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                rw [abs_le]; constructor <;> linarith [hLlow z, hLup z]
      _ = Ts P ν t * ((H + Real.log 3) / 2) := by
          rw [← Finset.sum_mul]; rfl
  have hH0le : Hs P μ ν 0 ≤ H := by
    rw [hHeq]; exact Hs_zero_le P μ ν (hμ.2.1) hν (μ z0) hm0 hμmin
  have hTb := Ts_bound P hP μ hμ ν hν H hH0le t
  have hTsq : Ts P ν t / 2 ≤ Real.sqrt (H / (2 * ((t : ℝ) + 1))) := by
    have hpos : (0 : ℝ) < 2 * ((t : ℝ) + 1) := by positivity
    have hle : (Ts P ν t / 2) ^ 2 ≤ H / (2 * ((t : ℝ) + 1)) := by
      rw [le_div_iff₀ hpos]; nlinarith [hTb]
    calc Ts P ν t / 2 = Real.sqrt ((Ts P ν t / 2) ^ 2) :=
          (Real.sqrt_sq (by linarith [Ts_nonneg P ν t])).symm
      _ ≤ _ := Real.sqrt_le_sqrt hle
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hc : 0 ≤ (H + Real.log 3) / 3 := by positivity
  calc 1 / 3 * ∑ z, d z * Real.log (g z) ≤ 1 / 3 * (Ts P ν t * ((H + Real.log 3) / 2)) :=
        mul_le_mul_of_nonneg_left hdL (by norm_num)
    _ = ((H + Real.log 3) / 3) * (Ts P ν t / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hTsq hc

end TranspositionIID.Main
end

theorem solution : type_of% @TranspositionIID.Main.chk_lemma_4_2 := @TranspositionIID.Main.chk_lemma_4_2
