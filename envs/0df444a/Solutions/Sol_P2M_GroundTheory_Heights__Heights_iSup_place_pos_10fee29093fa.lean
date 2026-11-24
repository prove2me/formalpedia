-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_iSup_place_pos_10fee29093fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:07:13.18583+00:00
-- url     : https://prove2.me/submissions/75efe1bd-7485-4be6-8926-87e6be69f319

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange

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
open NumberField Module
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F : Type*} [Field F] [NumberField F] {ι : Type*} [Finite ι] {y : ι → F}
    (hy : y ≠ 0) (w : FinitePlace F) : 0 < ⨆ i, w (y i) := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hy
  exact lt_of_lt_of_le ((FinitePlace.pos_iff (w := w)).mpr hi0)
    (le_ciSup (f := fun i ↦ w (y i)) (Set.finite_range _).bddAbove i0)
end GroundTheory.Heights₂.Heights
