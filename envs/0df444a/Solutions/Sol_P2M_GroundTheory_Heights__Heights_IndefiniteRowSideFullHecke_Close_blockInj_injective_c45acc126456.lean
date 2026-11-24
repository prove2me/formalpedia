-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_blockInj_injective_c45acc126456
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:48.588892+00:00
-- url     : https://prove2.me/submissions/a3755a1e-bfe1-4ec7-af50-601e708cd418

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (secM sec IsMultiHomog)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (k₀ : ι) :
    Function.Injective (fun i : Fin (n k₀ + 1) ↦ (⟨k₀, i⟩ : Coord n)) := fun i j h ↦ by
  simpa using h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
