-- Prove2me | solution 1 for P2M_GlobalTheory_LocalFiniteOddFixed_norm_prod__35ea87ad5dd5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:31:36.025417+00:00
-- url     : https://prove2.me/submissions/7ea1517e-a916-4f5a-b080-54b6bb2235d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LocalFiniteOddFixed
open GlobalTheory.UnitLemma
namespace GlobalTheory.LocalFiniteOddFixed
theorem _root_.solution (E A B : Type) [Field E] [CommRing A] [CommRing B] [Algebra E A] [Algebra E B]
    [Module.Finite E A] [Module.Finite E B] (a : A) (b : B) :
    Algebra.norm E ((a, b) : A × B) = Algebra.norm E a * Algebra.norm E b := by
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_prodMap]
  congr 1
end GlobalTheory.LocalFiniteOddFixed
