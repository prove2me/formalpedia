-- Prove2me | solution 1 for P2M_GlobalTheory__Multi_mem_regForms_c782fe77fe92
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:25.97435+00:00
-- url     : https://prove2.me/submissions/e9ff5037-5b01-419e-87fb-205a5d718970

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_P2M_GlobalTheory_formMap__Multi_014b852379ac
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


attribute [local simp] GlobalTheory.formMap_ιMulti

set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (K V F : Type*) [CommRing K] [CommRing V] [CommRing F] [Algebra K V] [Algebra V F]
  [Algebra K F] [IsScalarTower K V F] (p : ℕ)
variable {V p}
namespace GlobalTheory
theorem _root_.solution (w : Fin p → Ω[F⁄K])
    (hw : ∀ k, w k ∈ LinearMap.range (KaehlerDifferential.map K K V F)) :
    exteriorPower.ιMulti F p w ∈ regForms K V F p := by
  choose v hv using hw
  exact ⟨exteriorPower.ιMulti V p v, by rw [formMap_ιMulti, funext hv]⟩
end GlobalTheory
