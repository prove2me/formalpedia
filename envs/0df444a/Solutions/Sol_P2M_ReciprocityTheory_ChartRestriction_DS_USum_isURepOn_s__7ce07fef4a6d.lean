-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_USum_isURepOn_s__7ce07fef4a6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:52.836155+00:00
-- url     : https://prove2.me/submissions/45929ccd-1682-44e5-952c-9f8a38e06bab

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_norm_sop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_sop_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_sop_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix WithLp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.USum
variable {n : ℕ}
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
variable {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
variable {ε : Fin n → Bool}
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
namespace ReciprocityTheory.ChartRestriction.DS.USum
theorem _root_.solution {G : Set (Matrix (Fin n) (Fin n) ℂ)} (h₁ : IsURepOn G σ₁) (h₂ : IsURepOn G σ₂) :
    IsURepOn G (sσ σ₁ σ₂) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show sop (σ₁ 1) (σ₂ 1) = 1
    rw [h₁.1.1, h₂.1.1]; exact sop_one
  · intro a ha b hb
    show sop (σ₁ (a * b)) (σ₂ (a * b)) = (sop (σ₁ a) (σ₂ a)).comp (sop (σ₁ b) (σ₂ b))
    rw [h₁.1.2 a ha b hb, h₂.1.2 a ha b hb, sop_comp]
  · intro g hg v
    exact norm_sop (h₁.2.1 g hg) (h₂.2.1 g hg) v
  · intro v
    have hc := ((h₁.2.2 (ofLp v).1).prodMk (h₂.2.2 (ofLp v).2))
    exact (WithLp.prod_continuous_toLp 2 H₁ H₂).comp_continuousOn hc
end ReciprocityTheory.ChartRestriction.DS.USum
