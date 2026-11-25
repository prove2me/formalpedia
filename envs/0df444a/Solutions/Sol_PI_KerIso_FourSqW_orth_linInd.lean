-- Prove2me | solution 1 for PI.KerIso.FourSqW.orth_linInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:57.246031+00:00
-- url     : https://prove2.me/submissions/c08194a2-14ce-4d38-a095-de72cc31b7c1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_OrthogonalDiagonal
import Theorems.Thm_PI_KerIso_FourSqW_trL_apply
import Theorems.Thm_PI_KerIso_FourSqW_tr_self_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open PI PI.KerIso PI.KerIso.FourSqW
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
namespace PI.KerIso.FourSqW
theorem _root_.solution {n : Type} [Fintype n] (cj : E ≃ₐ[ℚ] E)
    (hpos : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x)) (v : n → E)
    (hv0 : ∀ i, v i ≠ 0) (hvo : ∀ i j, i ≠ j → Algebra.trace K E (v i * cj (v j)) = 0) :
    LinearIndependent K v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (trL (K := K) cj (v j)) hg
  rw [map_sum, map_zero, Finset.sum_eq_single j] at h
  · rw [map_smul, trL_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_right (tr_self_ne cj hpos _ (hv0 j))
  · intro i _ hij
    rw [map_smul, trL_apply, hvo i j hij, smul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h
end PI.KerIso.FourSqW
