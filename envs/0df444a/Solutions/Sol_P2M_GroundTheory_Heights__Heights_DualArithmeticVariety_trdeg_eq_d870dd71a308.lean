-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_trdeg_eq_d870dd71a308
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:47.641305+00:00
-- url     : https://prove2.me/submissions/67444df0-e786-42b4-bc3d-fe35fbd4e98a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_algebraicIndependent_gen_854857cd4c30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_mem_of_gen_mem_a23b53b6b97d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_isAlgebraic_of_adjoin_b50a6ba2f986

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualArithmeticVariety
variable {K : Type} [Field K]
namespace GroundTheory.Heights₂.Heights.DualArithmeticVariety
theorem _root_.solution (m : ℕ) : Cardinal.mk (Fin m) = Algebra.trdeg K (ProjField K m) :=
  ((algebraicIndependent_gen m).isTranscendenceBasis_iff_isAlgebraic.mpr
    (isAlgebraic_of_adjoin _ (mem_of_gen_mem _ fun j =>
      IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩))).cardinalMk_eq_trdeg
end GroundTheory.Heights₂.Heights.DualArithmeticVariety
