-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lfa_mul_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:39.251263+00:00
-- url     : https://prove2.me/submissions/bdb3ff53-d37f-4d4e-af04-154d66a58ff4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eq_sign_smul_of_intUnit

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
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (s t : Finset (Fin (n * n))) (h : Disjoint s t) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ fockBasis n s * fockBasis n t = σ • fockBasis n (s ∪ t) := by
  have hm := ExteriorAlgebra.basis_mul_of_disjoint ((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv)
    (Set.powersetCard.ofCard (rfl : s.card = s.card)) (Set.powersetCard.ofCard (rfl : t.card = t.card)) h
  obtain ⟨σ, hσ, h'⟩ := eq_sign_smul_of_intUnit _ _ _ hm
  refine ⟨σ, hσ, h'.trans ?_⟩
  exact congrArg (fun U => σ • fockBasis n U) (Finset.disjUnion_eq_union s t h)
end ReciprocityTheory.ChartRestriction.DS
