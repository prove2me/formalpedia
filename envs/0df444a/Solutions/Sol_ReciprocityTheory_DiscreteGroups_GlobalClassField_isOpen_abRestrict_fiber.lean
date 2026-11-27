-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.isOpen_abRestrict_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:28:01.102988+00:00
-- url     : https://prove2.me/submissions/b127bacc-2da6-4f3f-a760-9de5208c4bd7

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_AsGabLim
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_AsGabLimB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_isOpen_fiber_of_isOpen_ker
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_isOpen_ker_abRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.GlobalClassField
open _root_.Neutral.B1 Topology Function
variable {F : Type*} [Field F] {L : IntermediateField F (AlgebraicClosure F)}
namespace ReciprocityTheory.DiscreteGroups.GlobalClassField
theorem _root_.solution (h : IsFiniteAbelian F L) (τ : L ≃ₐ[F] L) :
    IsOpen {x : Field.absoluteGaloisGroupAbelianization F | abRestrict F L h x = τ} :=
  isOpen_fiber_of_isOpen_ker _ (isOpen_ker_abRestrict h) τ
end ReciprocityTheory.DiscreteGroups.GlobalClassField
