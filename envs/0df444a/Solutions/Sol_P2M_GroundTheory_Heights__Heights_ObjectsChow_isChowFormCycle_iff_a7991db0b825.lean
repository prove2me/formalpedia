-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_isChowFormCycle_iff_a7991db0b825
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:10.329055+00:00
-- url     : https://prove2.me/submissions/b98227f1-ed05-4acc-92bf-d37ed770d903

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow
theorem _root_.solution {F : Type*} [Field F] {k : ℕ} (Z : ProjCycle F n)
    (f : MvPolynomial (Fin k × Fin n) F) :
    IsChowFormCycle Z k f ↔ ∃ c : F, c ≠ 0 ∧ ∃ g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F,
      (∀ W ∈ Z.support, IsChowForm W k (g W)) ∧ f = C c * IndefiniteRowSideFullHecke.ArithBezout.cycleChowForm Z g :=
  Iff.rfl
end GroundTheory.Heights₂.Heights.ObjectsChow
