-- Prove2me | solution 1 for P2M_GlobalTheory_formMap__Multi_014b852379ac
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:13.779791+00:00
-- url     : https://prove2.me/submissions/2002594e-89ba-4367-a204-897acfae7fbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b



set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (K V F : Type*) [CommRing K] [CommRing V] [CommRing F] [Algebra K V] [Algebra V F]
  [Algebra K F] [IsScalarTower K V F] (p : ℕ)
variable {V p}
namespace GlobalTheory
theorem _root_.solution (v : Fin p → Ω[V⁄K]) :
    formMap K V F p (exteriorPower.ιMulti V p v)
      = exteriorPower.ιMulti F p (fun k => KaehlerDifferential.map K K V F (v k)) :=
  exteriorPowerMapOver_ιMulti _ _
end GlobalTheory
