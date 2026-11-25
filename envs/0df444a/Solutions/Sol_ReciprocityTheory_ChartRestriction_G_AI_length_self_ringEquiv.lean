-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_self_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:50.832559+00:00
-- url     : https://prove2.me/submissions/70103e56-9875-4b95-91de-f1450776e4c9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_HeightOneIffDimOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module
universe u v
variable {R S : Type*} [CommRing R] [CommRing S]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (e : R ≃+* S) : Module.length R R = Module.length S S := by
  haveI : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) := RingHomInvPair.of_ringEquiv e
  haveI : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) := RingHomInvPair.symm _ _
  have iso : Submodule R R ≃o Submodule S S := Submodule.orderIsoMapComap e.toSemilinearEquiv
  have h : Order.krullDim (Submodule R R) = Order.krullDim (Submodule S S) := by
    first
      | exact le_antisymm (Order.krullDim_le_of_strictMono iso iso.strictMono)
          (Order.krullDim_le_of_strictMono iso.symm iso.symm.strictMono)
      | exact Order.krullDim_eq_of_orderIso iso
      | exact iso.krullDim_eq
  unfold Module.length
  first
    | simp only [h]
    | congr 1
end ReciprocityTheory.ChartRestriction.G.AI
