-- Prove2me | solution 1 for PositivityTheory.KReal.Delta.sumR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:43:46.208429+00:00
-- url     : https://prove2.me/submissions/3d79b45c-62a0-4355-bd65-87fb4b645acc

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta
import Theorems.Thm_PI_FockOneDegW_Core_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace TensorProduct
open PositivityTheory PositivityTheory.KReal
open PositivityTheory.KReal.Delta
variable {p q r s : ℕ}
variable (b : Pol p q r 0 →ₗ[ℂ] Pol p q 0 s →ₗ[ℂ] ℂ)
namespace PositivityTheory.KReal.Delta
theorem _root_.solution {ι : Type} [Fintype ι] (F : ι → Module.End ℂ (Pol p q 0 s)) (t : Pol p q r 0 ⊗[ℂ] Pol p q 0 s) :
    (∑ i, F i).lTensor (Pol p q r 0) t = ∑ i, (F i).lTensor (Pol p q r 0) t := by
  classical
  have key : ∀ S : Finset ι, (∑ i ∈ S, F i).lTensor (Pol p q r 0) t = ∑ i ∈ S, (F i).lTensor (Pol p q r 0) t := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, LinearMap.lTensor_add, LinearMap.add_apply, ih]
  exact key Finset.univ
end PositivityTheory.KReal.Delta
