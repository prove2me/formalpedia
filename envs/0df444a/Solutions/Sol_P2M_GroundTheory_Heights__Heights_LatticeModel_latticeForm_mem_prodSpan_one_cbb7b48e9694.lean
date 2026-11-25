-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_mem_prodSpan_one_cbb7b48e9694
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:01:41.73155+00:00
-- url     : https://prove2.me/submissions/d34babab-37c4-4dd4-9d0a-eb1b82069569

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution {u : Fin m → K} (hu : u ∈ latticeDual L) :
    latticeForm u ∈ prodSpan L 1 :=
  Submodule.subset_span ⟨fun _ ↦ u, fun _ ↦ hu, by simp⟩
end GroundTheory.Heights₂.Heights.LatticeModel
