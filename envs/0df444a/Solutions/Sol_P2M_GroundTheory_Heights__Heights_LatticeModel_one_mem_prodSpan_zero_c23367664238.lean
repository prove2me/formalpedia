-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_one_mem_prodSpan_zero_c23367664238
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:58.764147+00:00
-- url     : https://prove2.me/submissions/5416c5e1-f171-4916-a3b7-dbe8db700fec

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
theorem _root_.solution : (1 : MvPolynomial (Fin m) K) ∈ prodSpan L 0 :=
  Submodule.subset_span ⟨Fin.elim0, fun i ↦ i.elim0, by simp⟩
end GroundTheory.Heights₂.Heights.LatticeModel
