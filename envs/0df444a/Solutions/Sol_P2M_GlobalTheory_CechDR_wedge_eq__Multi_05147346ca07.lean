-- Prove2me | solution 1 for P2M_GlobalTheory_CechDR_wedge_eq__Multi_05147346ca07
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:06.071201+00:00
-- url     : https://prove2.me/submissions/0a1e6a9c-6ace-4ff7-96ce-147b528473ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
variable {R B}
namespace GlobalTheory.CechDR
theorem _root_.solution (a b : Ω[B⁄R]) : wedge R B a b = exteriorPower.ιMulti B 2 ![a, b] :=
  Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply])
end GlobalTheory.CechDR
