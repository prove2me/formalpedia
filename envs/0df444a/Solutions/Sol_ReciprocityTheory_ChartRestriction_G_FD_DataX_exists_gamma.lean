-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DataX.exists_gamma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:06.131887+00:00
-- url     : https://prove2.me/submissions/c5fa0fd0-57b7-4101-a4df-d5d3029c1cb2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_Mmat_cong
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_g_smul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Mmat_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_herm_Mmat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.DataX
variable {r : ℕ} (X : DataX E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.DataX
theorem _root_.solution (u : Fin 2 → Fin r → E) (hu : IsIsoPair X.Gm u) (hmem : ∀ i, u i ∈ X.Λ)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : b ∈ X.LZ X.g) :
    ∃ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) ∧
      ∀ τ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.zmat u b τ := by
  obtain ⟨β, hβh, hβi, rfl⟩ := hb
  have hiso := hu.1
  have hγc : ∀ v ∈ X.Λ, ∃ y ∈ X.Λ, X.Mmat u β *ᵥ v - v = (X.g : E) • y :=
    X.Mmat_cong u hmem β hβi
  have hγc' : ∀ v ∈ X.Λ, ∃ y ∈ X.Λ, X.Mmat u (-β) *ᵥ v - v = (X.g : E) • y :=
    X.Mmat_cong u hmem (-β) (fun i k => by
      obtain ⟨γ', h1, h2⟩ := hβi i k
      exact ⟨-γ', h1.neg, by simp [h2]⟩)
  have hstab : IsUStab X.Gm X.Λ (X.gam u hiso β) := by
    refine ⟨fun x y => X.herm_Mmat u hiso β hβh x y, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · obtain ⟨y, hy, hyeq⟩ := hγc x hx
      have e1 : X.Mmat u β *ᵥ x = x + (X.g : E) • y := by rw [← hyeq]; abel
      show X.Mmat u β *ᵥ x ∈ X.Λ
      rw [e1]; exact X.Λ.add_mem hx (X.g_smul_mem hy)
    · change X.Mmat u β *ᵥ x ∈ X.Λ at hx
      have hinv : X.Mmat u (-β) *ᵥ (X.Mmat u β *ᵥ x) = x := by
        rw [Matrix.mulVec_mulVec, X.Mmat_mul u hiso, neg_add_cancel, Data.Mmat_zero, Matrix.one_mulVec]
      obtain ⟨y, hy, hyeq⟩ := hγc' _ hx
      have e1 : X.Mmat u (-β) *ᵥ (X.Mmat u β *ᵥ x) = X.Mmat u β *ᵥ x + (X.g : E) • y := by
        rw [← hyeq]; abel
      rw [← hinv, e1]; exact X.Λ.add_mem hx (X.g_smul_mem hy)
  exact ⟨X.gam u hiso β, X.cong _ hstab hγc, hγc, fun τ => X.Mmat_map u β τ⟩
end ReciprocityTheory.ChartRestriction.G.FD.DataX
