-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmple_of_eq_zero_44fe3d743ff6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:20:57.226317+00:00
-- url     : https://prove2.me/submissions/d82680ea-060c-441c-8a01-bf4caea14fc3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hx : x = 0) (F : SubSystem k x Ω) : IsVeryAmple F := by
  have hI : IsEmpty (Chart x) := ⟨fun I => by
    obtain ⟨i, hi⟩ := I.2.1
    exact (mem_support x).mp (I.2.2 hi) (by rw [hx]; rfl)⟩
  exact ⟨0, fun _ => 0, ⟨fun _ => zero_mem _, fun I => (hI.false I).elim,
    fun _ h => (h rfl).elim, fun _ h => (h rfl).elim⟩⟩
end GroundTheory.Heights₂.Heights.Kleiman
