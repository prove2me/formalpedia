-- Prove2me | solution 2 for QEC.Semantics.Davies.weightedJump_dissipator_traceNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:03:46.141118+00:00
-- url     : https://prove2.me/submissions/dfe7e8fc-8848-4f53-bc18-9a1ad2fd1263

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Pinching
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
import Theorems.Thm_QEC_Semantics_Davies_weightedJump_squareSum_operatorNorm_le
import Theorems.Thm_QEC_Semantics_Davies_dissipator_traceNorm_le_squareSum
import Theorems.Thm_QEC_Semantics_traceNorm_nonneg


set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators ComplexOrder
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.Davies
theorem _root_.solution [Nontrivial V] {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (A : κ → Operator V)
    (hA : ∀ a, operatorNorm (A a) ≤ 1) (rate : κ → Frequency e → ℝ)
    (hmax : ℝ) (hm : 0 ≤ hmax) (hn : ∀ a w, 0 ≤ rate a w) (hu : ∀ a w, rate a w ≤ hmax)
    (F : Operator V) (hF : F.IsSymmetric) :
    traceNorm (lindbladDissipator (weightedJump b e A rate) F) ≤
      (2 * Fintype.card κ * hmax) * traceNorm F := by
  apply (dissipator_traceNorm_le_squareSum _ F hF).trans
  have h := weightedJump_squareSum_operatorNorm_le b e A hA rate hmax hm hn hu
  have htwo : 2 * operatorNorm (squareSum (weightedJump b e A rate)) ≤
      2 * Fintype.card κ * hmax := by linarith
  exact mul_le_mul_of_nonneg_right htwo (traceNorm_nonneg F)
end QEC.Semantics.Davies
