-- Prove2me | solution 1 for P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:34.418749+00:00
-- url     : https://prove2.me/submissions/4448c149-c1b7-4f06-af41-9734a9325a4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.exteriorPowerMapOver_ιMulti

set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable (A : Type*) {B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] {D : ℕ}
variable {A} {L : Type*} [AddCommGroup L] [Module A L]
namespace GlobalTheory
theorem _root_.solution (φ : Fin D → L →ₗ[A] B) (v : Fin D → L) :
    wedgeContract φ (exteriorPower.ιMulti A D v) = (Matrix.of fun j k => φ k (v j)).det := by
  simp only [wedgeContract, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl
end GlobalTheory
