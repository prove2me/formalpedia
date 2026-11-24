-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_hermLine_eq_of_a037cafb6bb9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:49.386642+00:00
-- url     : https://prove2.me/submissions/7ed62b56-c9d0-48af-9666-e49dc7611bcc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_FunFieldEquivMemChartRingIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal

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
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution {A B : HermLine n} (hdeg : A.deg = B.deg) (hmet : A.metric = B.metric) :
    A = B := by
  cases A
  cases B
  cases hdeg
  cases hmet
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
