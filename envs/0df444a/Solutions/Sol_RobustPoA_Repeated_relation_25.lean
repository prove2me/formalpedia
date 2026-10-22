-- Prove2me | solution 1 for RobustPoA.Repeated.relation_25
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:11:07.366976+00:00
-- url     : https://prove2.me/submissions/2c71061b-99fa-4852-a424-9297f7bbcdaf

import Mathlib
import Definitions.Def_RobustPoA_Static_Smoothness
import Definitions.Def_RobustPoA_Repeated_Regret

set_option autoImplicit false

theorem rel23 {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ)
    (hsm : RobustPoA.Static.IsSmooth C lam mu) (hmu : mu < 1) (s s' : ∀ i, S i) :
    RobustPoA.Static.cost C s ≤ lam / (1 - mu) * RobustPoA.Static.cost C s' +
      (∑ i, RobustPoA.Repeated.delta C s' s i) / (1 - mu) := by
  have h := hsm s s'
  have hd : ∑ i, RobustPoA.Repeated.delta C s' s i =
      RobustPoA.Static.cost C s - ∑ i, C i (Function.update s i (s' i)) := by
    unfold RobustPoA.Repeated.delta RobustPoA.Static.cost
    rw [Finset.sum_sub_distrib]
  have hpos : 0 < 1 - mu := by linarith
  rw [hd, div_mul_eq_mul_div, ← add_div, le_div_iff₀ hpos]
  nlinarith [h]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ)
    (hsm : RobustPoA.Static.IsSmooth C lam mu) (hmu : mu < 1)
    (seq : ℕ → ∀ i, S i) (s' : ∀ i, S i) (T : ℕ) (hT : 1 ≤ T) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, RobustPoA.Static.cost C (seq t) ≤
      lam / (1 - mu) * RobustPoA.Static.cost C s' +
        (1 / (1 - mu)) *
          ∑ i, ((1 / (T : ℝ)) *
            ∑ t ∈ Finset.Icc 1 T, RobustPoA.Repeated.delta C s' (seq t) i) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hsum : ∑ t ∈ Finset.Icc 1 T, RobustPoA.Static.cost C (seq t) ≤
      ∑ t ∈ Finset.Icc 1 T, (lam / (1 - mu) * RobustPoA.Static.cost C s' +
        (∑ i, RobustPoA.Repeated.delta C s' (seq t) i) / (1 - mu)) :=
    Finset.sum_le_sum (fun t _ => rel23 C lam mu hsm hmu (seq t) s')
  have hcard : (Finset.Icc 1 T).card = T := by simp
  have e1 : ∑ t ∈ Finset.Icc 1 T, (lam / (1 - mu) * RobustPoA.Static.cost C s' +
        (∑ i, RobustPoA.Repeated.delta C s' (seq t) i) / (1 - mu)) =
      (T : ℝ) * (lam / (1 - mu) * RobustPoA.Static.cost C s') +
        (1 / (1 - mu)) * ∑ i, ∑ t ∈ Finset.Icc 1 T, RobustPoA.Repeated.delta C s' (seq t) i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul, Finset.sum_comm]
    rw [← Finset.sum_div, Finset.sum_comm]
    simp [div_eq_mul_inv, mul_comm, Finset.mul_sum]
  have e2 : ∑ i, ((1 / (T : ℝ)) *
            ∑ t ∈ Finset.Icc 1 T, RobustPoA.Repeated.delta C s' (seq t) i) =
      (1 / (T : ℝ)) * ∑ i, ∑ t ∈ Finset.Icc 1 T, RobustPoA.Repeated.delta C s' (seq t) i := by
    rw [Finset.mul_sum]
  rw [e2]
  have := mul_le_mul_of_nonneg_left hsum (le_of_lt (one_div_pos.mpr hT0))
  rw [e1] at this
  calc _ ≤ _ := this
    _ = _ := by field_simp
