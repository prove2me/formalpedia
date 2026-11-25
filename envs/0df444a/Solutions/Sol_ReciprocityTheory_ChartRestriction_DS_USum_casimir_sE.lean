-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.USum.casimir_sE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:04.355994+00:00
-- url     : https://prove2.me/submissions/d04722d5-4994-42f3-b277-a32cb6003f30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_lift_mul
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
theorem _root_.solution (E₁ : Fin n → Fin n → Module.End ℂ D₁) (E₂ : Fin n → Fin n → Module.End ℂ D₂) :
    casimir (sE E₁ E₂) = lift (casimir E₁) (casimir E₂) := by
  have h : ∀ a b, sE E₁ E₂ a b * sE E₁ E₂ b a = liftL (E₁ a b * E₁ b a, E₂ a b * E₂ b a) := by
    intro a b; rw [liftL_apply]; exact (lift_mul _ _ _ _).symm
  unfold casimir
  simp only [h, ← map_sum]
  rw [liftL_apply]
  congr 1
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum]
end ReciprocityTheory.ChartRestriction.DS.USum
