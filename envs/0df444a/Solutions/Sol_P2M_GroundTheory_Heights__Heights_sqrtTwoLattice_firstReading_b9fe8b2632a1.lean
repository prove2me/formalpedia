-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sqrtTwoLattice_firstReading_b9fe8b2632a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:34.428359+00:00
-- url     : https://prove2.me/submissions/bfd8cb42-d44e-4a1e-bb11-8f1b39f30533

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linearIndependent_one_sqrtTwo_5dd4db1be431
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_one_mem_sqrtTwoLattice_095e75f5c692

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
open ReciprocityTheory.ChartRestriction.G.Geo
open IndefiniteRowSideFullHecke.Antisym
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    Module.Finite zTwo sqrtTwoLattice ∧ Module.Projective zTwo sqrtTwoLattice ∧
      Submodule.span ℝ (sqrtTwoLattice : Set ℝ) = ⊤ := by
  have b := Module.Basis.span linearIndependent_one_sqrtTwo
  have : Module.Free zTwo sqrtTwoLattice := Module.Free.of_basis b
  have : Module.Finite zTwo sqrtTwoLattice := Module.Finite.of_basis b
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [eq_top_iff]
  intro v _
  simpa using Submodule.smul_mem _ v (Submodule.subset_span one_mem_sqrtTwoLattice :
    (1 : ℝ) ∈ Submodule.span ℝ (sqrtTwoLattice : Set ℝ))
end GroundTheory.Heights₂.Heights
