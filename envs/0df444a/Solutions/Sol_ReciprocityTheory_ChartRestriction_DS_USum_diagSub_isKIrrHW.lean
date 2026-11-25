-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.USum.diagSub_isKIrrHW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:38.474726+00:00
-- url     : https://prove2.me/submissions/1f7124f8-f6e7-4e06-b870-f7d2aa69c3cf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_InKRealSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_DiagSubIsKIrrHW
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_USum_diag__apply_d051f1906fda
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_USum_sE_diag__c40f84c7b864
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_toPrimitive_ofPrimitive


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
variable {n : ℕ} {ε : Fin n → Bool}
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}
  {V₁ : Submodule ℂ D₁} {V₂ : Submodule ℂ D₂}
namespace ReciprocityTheory.ChartRestriction.DS.USum
theorem _root_.solution (φ : V₁ →ₗ[ℂ] V₂) {Λ : Fin n → ℝ} (hV₁ : IsKIrrHW ε E₁ Λ V₁)
    (hcomm : ∀ a b (hab : ε a = ε b) (v : V₁),
      E₂ a b ((φ v : V₂) : D₂) = ((φ ⟨E₁ a b v, hV₁.2.1 a b hab _ v.2⟩ : V₂) : D₂)) :
    IsKIrrHW ε (sE E₁ E₂) Λ (diagSub φ) := by
  unfold IsKIrrHW
  have : FiniteDimensional ℂ V₁ := hV₁.1
  have hstab : IsKStableSub ε (sE E₁ E₂) (diagSub φ) := by
    intro a b hab x hx
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hx
    rw [sE_diagι φ hV₁.2.1 hcomm hab v]
    exact LinearMap.mem_range_self _ _
  refine ⟨inferInstanceAs (FiniteDimensional ℂ (LinearMap.range (diagι φ))), hstab, ?_, ?_⟩
  · intro S' hS' hS'st
    let T : Submodule ℂ D₁ := (S'.comap (diagι φ)).map V₁.subtype
    have hTle : T ≤ V₁ := by
      intro u hu
      obtain ⟨v, -, rfl⟩ := Submodule.mem_map.mp hu
      exact v.2
    have hTst : IsKStableSub ε E₁ T := by
      intro a b hab u hu
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
      refine Submodule.mem_map.mpr ⟨⟨E₁ a b v, hV₁.2.1 a b hab _ v.2⟩, ?_, rfl⟩
      show diagι φ _ ∈ S'
      rw [← sE_diagι φ hV₁.2.1 hcomm hab v]
      exact hS'st a b hab _ hv
    rcases hV₁.2.2.1 T hTle hTst with hT | hT
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp (hS' hx)
      have hvT : (v : D₁) ∈ T := Submodule.mem_map.mpr ⟨v, hx, rfl⟩
      rw [hT, Submodule.mem_bot] at hvT
      have hv0 : v = 0 := (Submodule.coe_eq_zero).mp hvT
      rw [hv0, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      intro x hx
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hx
      have hvT : (v : D₁) ∈ T := by
        rw [hT]
        exact v.2
      obtain ⟨v', hv', hvv'⟩ := Submodule.mem_map.mp hvT
      have hv'v : v' = v := Subtype.ext hvv'
      rw [← hv'v]
      exact hv'
  · obtain ⟨w, hwV, hw0, hK⟩ := hV₁.2.2.2
    obtain ⟨hwa, hwb⟩ := hK
    refine ⟨diagι φ ⟨w, hwV⟩, LinearMap.mem_range_self _ _, ?_, ?_⟩
    · intro h
      apply hw0
      have h1 := congrArg (fun x => (toP x).1) h
      simpa [diagι_apply, toPrimitive_ofPrimitive] using h1
    · refine ⟨fun a => ?_, fun a b hab hε => ?_⟩
      · rw [sE_diagι φ hV₁.2.1 hcomm (a := a) (b := a) rfl, ← map_smul]
        congr 1
        exact Subtype.ext (hwa a)
      · rw [sE_diagι φ hV₁.2.1 hcomm hε]
        have h0 : (⟨E₁ a b w, hV₁.2.1 a b hε _ hwV⟩ : V₁) = 0 := Subtype.ext (hwb a b hab hε)
        rw [h0, map_zero]
end ReciprocityTheory.ChartRestriction.DS.USum
