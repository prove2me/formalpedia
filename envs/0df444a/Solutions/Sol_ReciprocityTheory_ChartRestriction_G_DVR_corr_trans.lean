-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.corr_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:29.427119+00:00
-- url     : https://prove2.me/submissions/94ac310c-f0de-4b6e-b6ba-abad3cae9d2c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_res_eq_of_res_eq
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_units_ext_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' K₂ K₂' : Type} [Fintype K] [Fintype K'] [Fintype K₂] [Fintype K₂']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
  {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {φ₂' : K₂' → (Y ⟶ X)} {ε₂' : K₂' → ℤ}
open scoped Classical
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hL : L.IsLB) {t : LB.Gen (LB.LinComb L φ ε)} {t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)}
    {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ₂ ε₂ t t₂) (h' : LB.Gen.Corr L φ₂ ε₂ φ' ε' t₂ t') :
    LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' hj hj' hm
  let ρ : ((Y ⟶ X) → L.ι) → (Y ⟶ X) → L.ι := fun ρ₀ ψ =>
    if h₁ : ∃ k, φ k = ψ then j h₁.choose else if h₃ : ∃ k', φ' k' = ψ then j' h₃.choose else ρ₀ ψ
  have hρ1 : ∀ ρ₀ k, ρ ρ₀ (φ k) = j k := fun ρ₀ k => by
    simp only [ρ, dif_pos (⟨k, rfl⟩ : ∃ k₀, φ k₀ = φ k)]
    exact hj _ _ (⟨k, rfl⟩ : ∃ k₀, φ k₀ = φ k).choose_spec
  have hρ3 : ∀ ρ₀ k', ρ ρ₀ (φ' k') = j' k' := fun ρ₀ k' => by
    simp only [ρ]
    split_ifs with h₁ h₃
    · exact hm _ _ h₁.choose_spec
    · exact hj' _ _ h₃.choose_spec
    · exact absurd ⟨k', rfl⟩ h₃
  set O := LB.wchart L φ j ⊓ LB.wchart L φ' j'
  apply units_ext_cover O (fun ρ₀ => O ⊓ LB.wchart L φ₂ (ρ ρ₀ ∘ φ₂)) (fun _ => inf_le_left)
  · intro y hy
    have hex : ∀ ψ : Y ⟶ X, ∃ i, ψ.base y ∈ L.U i := fun ψ => by
      have : ψ.base y ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using this
    choose ρ₀ hρ₀ using hex
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨ρ₀, hy, Set.mem_iInter.2 fun k₂ => ?_⟩
    show (φ₂ k₂).base y ∈ L.U (ρ ρ₀ (φ₂ k₂))
    simp only [ρ]
    split_ifs with h₁ h₃
    · have := Set.mem_iInter.1 hy.1 h₁.choose
      rw [h₁.choose_spec] at this
      exact this
    · have := Set.mem_iInter.1 hy.2 h₃.choose
      rw [h₃.choose_spec] at this
      exact this
    · exact hρ₀ _
  · intro ρ₀
    have c2 : LB.Coh L φ₂ (ρ ρ₀ ∘ φ₂) := fun k₁ k₂ e => by simp only [Function.comp, e]
    have e1 := h j (ρ ρ₀ ∘ φ₂) hj c2 (fun k k₂ e => by simp only [Function.comp, ← e, hρ1])
    have e2 := h' (ρ ρ₀ ∘ φ₂) j' c2 hj' (fun k₂ k' e => by simp only [Function.comp, e, hρ3])
    have le1 : O ⊓ LB.wchart L φ₂ (ρ ρ₀ ∘ φ₂) ≤ LB.wchart L φ j := fun _ hy => hy.1.1
    have le2 : O ⊓ LB.wchart L φ₂ (ρ ρ₀ ∘ φ₂) ≤ LB.wchart L φ₂ (ρ ρ₀ ∘ φ₂) := fun _ hy => hy.2
    have le3 : O ⊓ LB.wchart L φ₂ (ρ ρ₀ ∘ φ₂) ≤ LB.wchart L φ' j' := fun _ hy => hy.1.2
    have f1 := res_eq_of_res_eq _ _ le1 le2 e1
    have f2 := res_eq_of_res_eq _ _ le2 le3 e2
    erw [res_res', res_res']
    exact f1.trans f2
end ReciprocityTheory.ChartRestriction.G.DVR
