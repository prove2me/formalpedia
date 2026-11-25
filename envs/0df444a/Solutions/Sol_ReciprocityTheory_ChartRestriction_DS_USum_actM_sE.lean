-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.USum.actM_sE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:56.36786+00:00
-- url     : https://prove2.me/submissions/158ec498-5a2d-4f2f-af80-cc046609ef2b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_liftL_apply

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
namespace ReciprocityTheory.ChartRestriction.DS.USum
theorem _root_.solution (E₁ : Fin n → Fin n → Module.End ℂ D₁) (E₂ : Fin n → Fin n → Module.End ℂ D₂)
    (X : Matrix (Fin n) (Fin n) ℂ) : actM (sE E₁ E₂) X = lift (actM E₁ X) (actM E₂ X) := by
  have h : ∀ a b, X a b • sE E₁ E₂ a b = liftL (X a b • (E₁ a b, E₂ a b)) := by
    intro a b; rw [map_smul]; rfl
  unfold actM
  simp only [h, ← map_sum]
  rw [liftL_apply]
  congr 1
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum]
end ReciprocityTheory.ChartRestriction.DS.USum
