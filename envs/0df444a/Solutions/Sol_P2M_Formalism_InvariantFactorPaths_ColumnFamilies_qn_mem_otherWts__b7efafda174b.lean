-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_ColumnFamilies_qn_mem_otherWts__b7efafda174b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:22.178459+00:00
-- url     : https://prove2.me/submissions/39475651-d62f-40c9-8516-e89f5cba5a70

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_mem_otherWts
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_swap_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_coeff_transposeVariables
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_weight_rowW
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (ν : Fin n → ℕ) (g : MvPolynomial (Fin n × Fin n) ℚ)
    (hg : weightedHomogeneousComponent (rowW n n) ν (transposeVariables ℚ n g) = 0) :
    g ∈ otherWts (glOps ℚ n (rowLetters n) Set.univ) (fun a => (ν a : ℤ)) := by
  classical
  refine qn_mem_otherWts n _ g fun m hm hwt => ?_
  have h1 := congrArg (coeff (Finsupp.mapDomain Prod.swap m)) hg
  have hw : Finsupp.weight (rowW n n) (Finsupp.mapDomain Prod.swap m) = ν := by
    funext a
    rw [lehw_weight_rowW, rowDeg]
    simp only [qn_swap_apply]
    have := congrFun hwt a
    simp only [qn_wt] at this
    exact_mod_cast this
  rw [coeff_weightedHomogeneousComponent, if_pos hw, coeff_transposeVariables, coeff_zero] at h1
  exact (mem_support_iff.mp hm) h1
end Formalism.InvariantFactorPaths.ColumnFamilies
