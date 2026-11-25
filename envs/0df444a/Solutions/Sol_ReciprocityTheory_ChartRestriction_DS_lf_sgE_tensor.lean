-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lf_sgE_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:43.867176+00:00
-- url     : https://prove2.me/submissions/7d487657-3b2a-40cf-985b-3e3a7c2c2b83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockE

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
variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (a b : Fin n) :
    sgE ε (cpT (N := N) (n := n)) cmT a b = TensorProduct.map LinearMap.id (sgE ε cpFock cmFock a b) := by
  have hcp : ∀ i c : Fin n, cpT (N := N) i c = LinearMap.lTensor N (cpFock i c) := fun _ _ => rfl
  have hcm : ∀ i c : Fin n, cmT (N := N) i c = LinearMap.lTensor N (cmFock i c) := fun _ _ => rfl
  have hsum : ∀ (s : Finset (Fin n)) (F : Fin n → Module.End ℂ (Fock n)),
      LinearMap.lTensor N (∑ x ∈ s, F x) = ∑ x ∈ s, LinearMap.lTensor N (F x) :=
    fun s F => map_sum (LinearMap.lTensorHom N) F s
  rw [show TensorProduct.map LinearMap.id (sgE ε cpFock cmFock a b) =
    LinearMap.lTensor N (sgE ε cpFock cmFock a b) from rfl]
  unfold sgE
  split_ifs
  · rw [hsum]
    simp only [hcp, hcm, LinearMap.lTensor_mul]
  · rw [LinearMap.lTensor_neg, hsum]
    simp only [hcp, hcm, LinearMap.lTensor_mul]
  · rw [LinearMap.lTensor_zero]
end ReciprocityTheory.ChartRestriction.DS
