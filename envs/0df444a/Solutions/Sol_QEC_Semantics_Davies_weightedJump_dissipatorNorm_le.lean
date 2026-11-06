-- Prove2me | solution 1 for QEC.Semantics.Davies.weightedJump_dissipatorNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:32:23.662393+00:00
-- url     : https://prove2.me/submissions/e930fda0-15f0-49c3-889f-0ad60dc3c1aa

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Pinching
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
import Theorems.Thm_QEC_Semantics_Davies_weightedJump_squareSum_operatorNorm_le
import Theorems.Thm_QEC_Semantics_Davies_dissipatorNorm_le_squareSum


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
    (hmax : ℝ) (hm : 0 ≤ hmax) (hn : ∀ a w, 0 ≤ rate a w) (hu : ∀ a w, rate a w ≤ hmax) :
    lindbladDissipatorNorm (weightedJump b e A rate) ≤ 2 * Fintype.card κ * hmax := by
  apply (dissipatorNorm_le_squareSum _).trans
  have h := weightedJump_squareSum_operatorNorm_le b e A hA rate hmax hm hn hu
  linarith
end QEC.Semantics.Davies
