-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_lineO1_chart_nontrivial_8ae5f9d9a6e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:03:13.608618+00:00
-- url     : https://prove2.me/submissions/f840f1ea-c3bd-4f0b-a743-8ff321423a45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects

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
universe u v w
variable (k : Type u) [Field k]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution : Nontrivial ((tautologicalLineBundle k).toSubFamily.toFamily.F (lineChart0 k)) := by
  have h1 : (1 : RatFunc k) ∈ (tautologicalLineBundle k).sub (lineChart0 k) := by
    have := mem_twistMod_one (S := k) (lineChart0 k) 0
    change (1 : RatFunc k) ∈ twistMod k (lineX k) 1 (lineChart0 k)
    simpa [lineX] using this
  exact ⟨⟨⟨1, h1⟩, 0, fun e => one_ne_zero (congrArg Subtype.val e)⟩⟩
end GroundTheory.Heights₂.Heights.Kleiman
