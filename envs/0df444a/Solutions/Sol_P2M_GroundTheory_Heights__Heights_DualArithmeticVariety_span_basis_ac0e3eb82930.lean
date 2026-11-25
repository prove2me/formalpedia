-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_span_basis_ac0e3eb82930
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:39.020968+00:00
-- url     : https://prove2.me/submissions/03f0e64f-eb55-4633-b46a-ceb540c61214

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_span_dualLattice_879b19e8a055

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
variable [NumberField K] {i : ℕ}
variable {F : HermLattice K i} {T : Type}
namespace GroundTheory.Heights₂.Heights.DualArithmeticVariety
theorem _root_.solution [Fintype T] (b : Module.Basis T ℤ (dualLattice F)) :
    Submodule.span K (Set.range fun t => (b t : Fin i → K)) = ⊤ := by
  refine eq_top_iff.mpr ((span_dualLattice F).symm.le.trans (Submodule.span_le.mpr fun φ hφ => ?_))
  have h := congrArg Subtype.val (b.sum_repr ⟨φ, hφ⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  rw [← h]
  exact Submodule.sum_mem _ fun t _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self t)) _
end GroundTheory.Heights₂.Heights.DualArithmeticVariety
