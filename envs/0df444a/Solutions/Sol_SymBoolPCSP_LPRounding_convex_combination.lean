-- Prove2me | solution 1 for SymBoolPCSP.LPRounding.convex_combination
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:36:06.385986+00:00
-- url     : https://prove2.me/submissions/2f3dddde-d6c4-41be-bee3-8dc137890cde

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_LPRounding_Basic
set_option autoImplicit false
open PCSPBLPAff.Symmetric
open SymBoolPCSP.LPRounding

theorem solution {τ : Type} {ar : τ → ℕ} (𝔸 : RelStruct τ ar Bool)
    (X : Instance τ ar) {m : ℕ} (u : Fin m → Fin X.n → ℚ) (hu : ∀ k, IsHullLPSol 𝔸 X (u k))
    (lam : Fin m → ℚ) (hlam0 : ∀ k, 0 ≤ lam k) (hlam1 : ∑ k, lam k = 1) :
    IsHullLPSol 𝔸 X (∑ k, lam k • u k) := by
  have happ : ∀ i, (∑ k, lam k • u k) i = ∑ k, lam k * u k i := by
    intro i; simp [Finset.sum_apply]
  refine ⟨fun i => ?_, fun j => ?_⟩
  · rw [happ]
    constructor
    · exact Finset.sum_nonneg fun k _ => mul_nonneg (hlam0 k) ((hu k).1 i).1
    · calc ∑ k, lam k * u k i ≤ ∑ k, lam k * 1 :=
            Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ((hu k).1 i).2 (hlam0 k)
        _ = 1 := by simp [hlam1]
  · choose α hα0 hαsupp hαsum hαval using fun k => (hu k).2 j
    refine ⟨fun y => ∑ k, lam k * α k y, ?_, ?_, ?_, ?_⟩
    · intro y; exact Finset.sum_nonneg fun k _ => mul_nonneg (hlam0 k) (hα0 k y)
    · intro y hy; exact Finset.sum_eq_zero fun k _ => by rw [hαsupp k y hy, mul_zero]
    · rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hαsum, mul_one]
      exact hlam1
    · intro c
      rw [happ]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hαval k c, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
