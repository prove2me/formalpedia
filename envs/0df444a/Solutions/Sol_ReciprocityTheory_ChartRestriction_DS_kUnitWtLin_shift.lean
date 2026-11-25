-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kUnitWtLin_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:23:16.764286+00:00
-- url     : https://prove2.me/submissions/55209ec2-4391-4ce0-a6aa-85bd1d43098f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_Lemmata_SimultaneousEigenvectors_BlSimeig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    kUnitWtLin μ < kUnitWtLin (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) := by
  have hlt : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  have h : kUnitWtLin (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) =
      kUnitWtLin μ + ((n : ℝ) - ((a : ℕ) : ℝ)) - ((n : ℝ) - ((b : ℕ) : ℝ)) := by
    simp only [kUnitWtLin, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  linarith
end ReciprocityTheory.ChartRestriction.DS
