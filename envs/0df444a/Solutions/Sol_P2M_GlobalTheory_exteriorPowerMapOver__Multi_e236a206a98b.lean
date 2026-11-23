-- Prove2me | solution 1 for P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:29.920528+00:00
-- url     : https://prove2.me/submissions/220951cb-2a3f-40e2-a3ea-3ff95a63f960

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply

set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable (A : Type*) {B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] {D : ℕ}
variable {A} {L : Type*} [AddCommGroup L] [Module A L]
namespace GlobalTheory
theorem _root_.solution (φ : L →ₗ[A] M) (v : Fin D → L) :
    exteriorPowerMapOver B D φ (exteriorPower.ιMulti A D v)
      = exteriorPower.ιMulti B D (fun k => φ (v k)) := by
  simp [exteriorPowerMapOver]
end GlobalTheory
