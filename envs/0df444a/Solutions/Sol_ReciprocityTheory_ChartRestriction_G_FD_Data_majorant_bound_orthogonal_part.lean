-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.majorant_bound_orthogonal_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:30.528597+00:00
-- url     : https://prove2.me/submissions/3245b18f-a487-4536-af05-c587a7023b9f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantBoundOrthogonalPart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Jp_adj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_zero_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (ξ : Fin r → E) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ) (κ : ℝ)
    (hδ : ∀ u ∈ X.Uz x ξ, ∀ τ, X.maj x τ (δ τ (u τ) • emb τ.1 ξ) ≤ κ ^ 2 * X.maj x τ (u τ))
    (τ : X.Ψ) (w : Fin r → ℂ) (hw1 : hermC τ.1 X.Gm w (emb τ.1 ξ) = 0)
    (hw2 : hermC τ.1 X.Gm w (X.Jp x τ (emb τ.1 ξ)) = 0) :
    X.maj x τ (δ τ w • emb τ.1 ξ) ≤ κ ^ 2 * X.maj x τ w := by
  classical
  let u : X.Ψ → Fin r → ℂ := fun τ' => if τ' = τ then w else 0
  have hu : u ∈ X.Uz x ξ := by
    refine ⟨fun τ' => ?_, fun τ' => ?_⟩
    · by_cases h : τ' = τ
      · subst h
        simp [u, hw1]
      · simp [u, h, hC_zero_left]
    · by_cases h : τ' = τ
      · subst h
        have hsm : hermC τ'.1 X.Gm (X.Jz x u τ') (emb τ'.1 ξ) =
            I * hermC τ'.1 X.Gm (X.Jp x τ' w) (emb τ'.1 ξ) := by
          simp [Data.Jz, Data.Jp, u, hermC, Finset.mul_sum, mul_assoc]
        rw [hsm, X.Jp_adj hx τ' w (emb τ'.1 ξ), hw2, mul_zero]
      · simp [Data.Jz, u, h, X.ppos_zero, hC_zero_left]
  have hmain := hδ u hu τ
  simpa [u] using hmain
end ReciprocityTheory.ChartRestriction.G.FD.Data
