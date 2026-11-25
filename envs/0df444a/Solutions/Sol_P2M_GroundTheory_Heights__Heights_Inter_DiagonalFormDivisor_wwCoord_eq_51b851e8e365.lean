-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_wwCoord_eq_51b851e8e365
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:18:58.448977+00:00
-- url     : https://prove2.me/submissions/78ea9ce6-7c67-49f2-a369-6afa857ec10d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartFormsRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PMobiusAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagFormDiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_lineVal_comb_27def6546364

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
set_option linter.unusedSectionVars false
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
  [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
theorem _root_.solution (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (F : Subfield Ω)
    (i : ι) (l₀ : ν) (k₀ k₁ : κ) (hx : x i ≠ 0) (hδ : δ l₀ ≠ 0) (xb : ι → F) (ε : ν → F) (c₀ c₁ : κ → F)
    (hxb : ∀ j, (xb j : Ω) = x j / x i) (hε : ∀ l, (ε l : Ω) = δ l / δ l₀)
    (hc : ∀ k, φ k = (c₀ k : Ω) • φ k₀ + (c₁ k : Ω) • φ k₁) (b₀ b₁ : Φ) (w : Fin 2 → Φ)
    (h₀ : T.lineVal e (φ k₀) b₀ ≠ 0) (h₁ : T.lineVal e (φ k₀) b₁ ≠ 0)
    (hw₀ : w 0 = T.lineVal e (φ k₁) b₀ / T.lineVal e (φ k₀) b₀)
    (hw₁ : w 1 = T.lineVal e (φ k₁) b₁ / T.lineVal e (φ k₀) b₁) :
    T.wwCoord x δ e φ b₀ b₁ = fun p => blockScale (algebraMap Ω Φ (x i)) (algebraMap Ω Φ (δ l₀))
      (T.lineVal e (φ k₀) b₀) (T.lineVal e (φ k₀) b₁) p.1 *
        eval₂ ((algebraMap Ω Φ).comp F.subtype) w (ratioPoly xb ε c₀ c₁ p) := by
  have hx' : algebraMap Ω Φ (x i) ≠ 0 := (map_ne_zero _).2 hx
  have hδ' : algebraMap Ω Φ (δ l₀) ≠ 0 := (map_ne_zero _).2 hδ
  funext p
  rcases p with ⟨_ | _ | _ | _, j⟩
  · simp only [T.wwCoord, blockScale, ratioPoly, eval₂_C, RingHom.comp_apply, Subfield.coe_subtype]
    rw [hxb j, map_div₀]
    field_simp
  · simp only [T.wwCoord, blockScale, ratioPoly, eval₂_C, RingHom.comp_apply, Subfield.coe_subtype]
    rw [hε j, map_div₀]
    field_simp
  · simp only [T.wwCoord, blockScale, ratioPoly, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, RingHom.comp_apply,
      Subfield.coe_subtype, hw₀]
    rw [hc j, lineVal_comb]
    field_simp
  · simp only [T.wwCoord, blockScale, ratioPoly, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, RingHom.comp_apply,
      Subfield.coe_subtype, hw₁]
    rw [hc j, lineVal_comb]
    field_simp
end GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
