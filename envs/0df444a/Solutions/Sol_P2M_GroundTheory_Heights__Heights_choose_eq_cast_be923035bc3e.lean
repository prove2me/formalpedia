-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_choose_eq_cast_be923035bc3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:46.597104+00:00
-- url     : https://prove2.me/submissions/6ffb1143-8027-4c93-b305-a104b9216a17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {α β : Type} (e : α = β) {p : α → Prop} {q : β → Prop}
    (hp : ∃ x, p x) (hq : ∃ y, q y) (hpq : ∀ x, q (cast e x) ↔ p x) :
    Classical.choose hq = cast e (Classical.choose hp) := by
  subst e
  have : q = p := funext fun x => propext (hpq x)
  subst this
  rfl
end GroundTheory.Heights₂.Heights
