-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_USum_isDerivedOn_s__20eda4b900b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:24:53.167277+00:00
-- url     : https://prove2.me/submissions/baf12fb0-d61e-4f9a-b2a4-2f70c354ddb6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_lift_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_lift_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_lift_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_actM_sE

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
theorem _root_.solution {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
    {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}
    (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) :
    IsDerivedOn ε (sσ σ₁ σ₂) (sD D₁ D₂) (sE E₁ E₂) where
  glRep := by
    intro a b c d
    have e1 := hD₁.glRep a b c d
    have e2 := hD₂.glRep a b c d
    show lift (E₁ a b) (E₂ a b) * lift (E₁ c d) (E₂ c d) - lift (E₁ c d) (E₂ c d) * lift (E₁ a b) (E₂ a b) =
      (if b = c then lift (E₁ a d) (E₂ a d) else 0) - (if d = a then lift (E₁ c b) (E₂ c b) else 0)
    rw [← lift_mul, ← lift_mul, ← lift_sub, e1, e2]
    split_ifs <;> rw [lift_sub] <;> simp only [lift_zero]
  kStable := by
    intro k hk v hv
    exact ⟨hD₁.kStable k hk _ hv.1, hD₂.kStable k hk _ hv.2⟩
  deriv := by
    intro X hX v
    have h1 := hD₁.deriv X hX (toP v).1
    have h2 := hD₂.deriv X hX (toP v).2
    have h3 := (WithLp.prodContinuousLinearEquiv 2 ℝ H₁ H₂).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) (h1.prodMk h2)
    rw [actM_sE]
    exact h3
end ReciprocityTheory.ChartRestriction.DS.USum
