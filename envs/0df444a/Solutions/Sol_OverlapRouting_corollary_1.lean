-- Prove2me | solution 1 for OverlapRouting.corollary_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T01:20:25.473543+00:00
-- url     : https://prove2.me/submissions/f5989c52-130b-4a7b-8a76-0c3b3aa83b27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OverlapRouting_vrpOpt
import Definitions.Def_OverlapRouting_DemandLaw
import Definitions.Def_OverlapRouting_costAO
import Definitions.Def_OverlapRouting_ZAO
import Theorems.Thm_OverlapRouting_lemma_4

set_option autoImplicit false

open OverlapRouting

theorem solution (N' Q : ℕ) (hN' : 1 ≤ N') (hQ : 1 ≤ Q) (D : DemandLaw) :
    (0 < D.p 0 → ∃ Γ₃ : ℝ, ∀ M : ℕ, 1 ≤ M →
      ∑ j ∈ Finset.Icc 1 M, |expTrips N' Q D M j - rAvg N' Q D M| ≤ Γ₃) ∧
    ∃ Γ₃ : ℝ, ∀ M j : ℕ, 1 ≤ M → j ≤ M →
      |∑ k ∈ Finset.Icc 1 j, (expTrips N' Q D M k - rAvg N' Q D M)| ≤ Γ₃ := by
  have L4 := OverlapRouting.lemma_4 N' Q hN' hQ D
  constructor
  · intro hp0
    obtain ⟨Γ₁, Γ₂, γ, hγ0, hγ1, hb⟩ := L4.1 hp0
    refine ⟨|Γ₁| / (1 - γ) + |Γ₂|, fun M hM => ?_⟩
    have h1γ : 0 < 1 - γ := by linarith
    have hgeom : ∑ j ∈ Finset.Icc 1 M, γ ^ j ≤ 1 / (1 - γ) := by
      have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := M + 1) hγ0.le hγ1
      rw [Finset.Ico_add_one_right_eq_Icc] at h
      refine h.trans ?_
      rw [pow_one]
      exact div_le_div_of_nonneg_right (by linarith) h1γ.le
    have hgeom0 : 0 ≤ ∑ j ∈ Finset.Icc 1 M, γ ^ j :=
      Finset.sum_nonneg (fun j _ => pow_nonneg hγ0.le j)
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    calc ∑ j ∈ Finset.Icc 1 M, |expTrips N' Q D M j - rAvg N' Q D M|
        ≤ ∑ j ∈ Finset.Icc 1 M, (Γ₁ * γ ^ j + Γ₂ / M) :=
          Finset.sum_le_sum fun j hj =>
            hb M j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
      _ = Γ₁ * ∑ j ∈ Finset.Icc 1 M, γ ^ j + Γ₂ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
            nsmul_eq_mul]
          simp only [add_tsub_cancel_right]
          field_simp
      _ ≤ |Γ₁| / (1 - γ) + |Γ₂| := by
          have e1 : Γ₁ * ∑ j ∈ Finset.Icc 1 M, γ ^ j ≤ |Γ₁| * ∑ j ∈ Finset.Icc 1 M, γ ^ j :=
            mul_le_mul_of_nonneg_right (le_abs_self Γ₁) hgeom0
          have e2 : |Γ₁| * ∑ j ∈ Finset.Icc 1 M, γ ^ j ≤ |Γ₁| * (1 / (1 - γ)) :=
            mul_le_mul_of_nonneg_left hgeom (abs_nonneg Γ₁)
          have e3 : |Γ₁| * (1 / (1 - γ)) = |Γ₁| / (1 - γ) := by ring
          linarith [le_abs_self Γ₂]
  · obtain ⟨rInf, Γ, hb2⟩ := L4.2
    refine ⟨2 * Γ, fun M j hM hj => ?_⟩
    have hΓ0 : 0 ≤ Γ := le_trans (abs_nonneg _) (hb2 M 0 (Nat.zero_le _))
    have hfull := hb2 M M le_rfl
    have hpart := hb2 M j hj
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have key : ∑ k ∈ Finset.Icc 1 j, (expTrips N' Q D M k - rAvg N' Q D M) =
        (∑ k ∈ Finset.Icc 1 j, expTrips N' Q D M k - j * rInf) -
          (j / M) * (∑ k ∈ Finset.Icc 1 M, expTrips N' Q D M k - M * rInf) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp only [add_tsub_cancel_right]
      unfold rAvg
      field_simp
      ring
    rw [key]
    have hjM : (j : ℝ) / M ≤ 1 := by
      rw [div_le_one hMpos]
      exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j / M := by positivity
    calc |(∑ k ∈ Finset.Icc 1 j, expTrips N' Q D M k - j * rInf) -
          (j / M) * (∑ k ∈ Finset.Icc 1 M, expTrips N' Q D M k - M * rInf)|
        ≤ |∑ k ∈ Finset.Icc 1 j, expTrips N' Q D M k - j * rInf| +
          |(j / M) * (∑ k ∈ Finset.Icc 1 M, expTrips N' Q D M k - M * rInf)| := abs_sub _ _
      _ ≤ Γ + 1 * Γ := by
          rw [abs_mul, abs_of_nonneg hj0]
          exact add_le_add hpart (mul_le_mul hjM hfull (abs_nonneg _) zero_le_one)
      _ = 2 * Γ := by ring
