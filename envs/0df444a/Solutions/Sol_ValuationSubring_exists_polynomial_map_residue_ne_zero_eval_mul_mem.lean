-- Prove2me | solution 1 for ValuationSubring.exists_polynomial_map_residue_ne_zero_eval_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/7d9c7479-91d7-5e83-a5bf-d31ed0628423

import Mathlib
import Theorems.Thm_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem
import Theorems.Thm_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_polynomial_map_residue_ne_zero_eval_mul_mem

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    (f : F) [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (z : F) :
    ∃ q : Polynomial A, (q.map (IsLocalRing.residue A)) ≠ 0 ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V →
        (Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f q) * z ∈ V := by
  classical

  obtain ⟨q₀, hq₀0, hq₀T⟩ := Algebra.exists_adjoin_ne_zero_mul_forall_valuationSubring_mem (L := L) f z

  have hmem : (↑q₀ : F) ∈ (Polynomial.aeval (R := L) f).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact q₀.2
  obtain ⟨q₁, hq₁⟩ := hmem
  have hq₁0 : q₁ ≠ 0 := by
    rintro rfl; simp only [map_zero] at hq₁
    exact hq₀0 (Subtype.ext hq₁.symm)

  obtain ⟨q, c, hc0, hqmap, hqbar⟩ := ValuationSubring.exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero A q₁ hq₁0
  refine ⟨q, hqbar, fun V hL hfV => ?_⟩

  have heval : Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f q =
      algebraMap L F c⁻¹ * (q₀ : F) := by
    have h1 : Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f q =
        Polynomial.aeval f (q.map A.subtype) := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [h1, hqmap, map_mul, aeval_C]
    exact congrArg _ hq₁
  rw [heval, mul_assoc]
  exact mul_mem (hL c⁻¹) (hq₀T V hL hfV)

end S_ValuationSubring_exists_polynomial_map_residue_ne_zero_eval_mul_mem
end P2MW
export P2MW.S_ValuationSubring_exists_polynomial_map_residue_ne_zero_eval_mul_mem (solution)
