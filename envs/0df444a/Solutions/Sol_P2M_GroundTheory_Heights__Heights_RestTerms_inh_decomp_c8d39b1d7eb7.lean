-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_inh_decomp_c8d39b1d7eb7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:43.893233+00:00
-- url     : https://prove2.me/submissions/b85d0b44-aa6f-4701-a4e6-9995a0a26b39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_F_eq_cb105611b658

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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
noncomputable section
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution : IsPowerSumDecomposition 1 (1+1) (restPolynomial 1 1 1 .last)
    (fun k _ => if k = 1 then C (2⁻¹) * (flagTwoSecondRoot - flagTwoFirstRoot) else if k = 2 then C (2⁻¹) else 0) := by
  have h2 : (C (2⁻¹ : ℚ) : RootRing 1 (1+1)) * 2 = 1 := by
    have : (2 : RootRing 1 (1+1)) = C 2 := (map_ofNat C 2).symm
    rw [this, ← C_mul]; norm_num
  have hI : Finset.Icc 1 (1+1) = ({1, 2} : Finset ℕ) := by decide
  rw [inh_F_eq, IsPowerSumDecomposition, hI]
  simp [blockPowerSum, Fin.sum_univ_two]
  linear_combination (-(flagTwoSecondRoot ^ 2)) * h2
end GroundTheory.Heights₂.Heights.RestTerms
