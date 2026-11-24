-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_maximalIdeal_smul_top_lt_top_3d10a1377dbd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:14.557542+00:00
-- url     : https://prove2.me/submissions/238c27f6-d406-4b7f-81f1-962c7b71638a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAuslanderBuchsbaumDepthLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing CategoryTheory Limits Abelian RingTheory.Sequence
universe u
open GroundTheory.Heights₂.Heights.AuslanderBuchsbaumDepthLower
variable {R : Type u} [CommRing R] [IsLocalRing R]
namespace GroundTheory.Heights₂.Heights.AuslanderBuchsbaumDepthLower
theorem _root_.solution (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] : maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by
  refine (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator ?_).symm.lt_top
  have H : Module.annihilator R M ≠ ⊤ := fun h =>
    not_subsingleton M (Module.annihilator_eq_top_iff.mp h)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ H]
end GroundTheory.Heights₂.Heights.AuslanderBuchsbaumDepthLower
