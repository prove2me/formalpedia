-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.isInfUnitary_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:22:32.280805+00:00
-- url     : https://prove2.me/submissions/e4a22fbf-bb7a-4a0a-bbeb-1c66abbd9430

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prFst_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prSnd_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prFst_prodE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prSnd_prodE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.prFst_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.prSnd_apply

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M₁ M₂ : Type*} [NormedAddCommGroup M₁] [InnerProductSpace ℂ M₁] [NormedAddCommGroup M₂]
  [InnerProductSpace ℂ M₂] {ε : Fin n → Bool}
  {E₁ : Fin n → Fin n → Module.End ℂ M₁} {E₂ : Fin n → Fin n → Module.End ℂ M₂}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hU₁ : IsInfUnitary ε E₁) (hU₂ : IsInfUnitary ε E₂) :
    IsInfUnitary ε (prodE E₁ E₂) := by
  intro a b x y
  have h₁ := hU₁ a b (prFst x) (prFst y)
  have h₂ := hU₂ a b (prSnd x) (prSnd y)
  simp only [WithLp.prod_inner_apply]
  change inner ℂ (prFst (prodE E₁ E₂ a b x)) (prFst y) + inner ℂ (prSnd (prodE E₁ E₂ a b x)) (prSnd y) =
    adjSign ε a b * (inner ℂ (prFst x) (prFst (prodE E₁ E₂ b a y)) +
      inner ℂ (prSnd x) (prSnd (prodE E₁ E₂ b a y)))
  rw [prFst_prodE, prSnd_prodE, prFst_prodE, prSnd_prodE, h₁, h₂, mul_add]
end ReciprocityTheory.ChartRestriction.DS
