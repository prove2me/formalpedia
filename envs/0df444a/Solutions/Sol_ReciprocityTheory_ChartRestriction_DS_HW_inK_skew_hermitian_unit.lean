-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.inK_skew_hermitian_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:18:06.251636+00:00
-- url     : https://prove2.me/submissions/76bba6ed-109b-4f00-805e-ff68e32d9fcc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_inK_iff__24a5ac304dfc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_single_mul_Jm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ε : Fin n → Bool} {a b : Fin n} (h : ε a = ε b) : inK ε (kp2 a b) := by
  rw [inK_iff']
  unfold kp2
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_single,
      Matrix.conjTranspose_single, add_comm, ← neg_smul]
    congr 1 <;> simp [Complex.conj_I] <;> ring
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, single_mul_Jm h,
      single_mul_Jm h.symm]
end ReciprocityTheory.ChartRestriction.DS.HW
