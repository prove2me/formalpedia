-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IsotropicThreshold.iso_threshold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:30:32.191115+00:00
-- url     : https://prove2.me/submissions/ff7bf675-bc8c-48cc-8742-2d6bf68a04b1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicThreshold
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IsotropicThreshold_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_eq_zero_of_conj_lt_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_norm_hermC_le_maj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.IsotropicThreshold
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.IsotropicThreshold
theorem _root_.solution (X : Data E r) : ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ x ∈ X.dom, ∀ v ∈ X.Λ,
    ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) < δ0 → herm X.Gm v v = 0 := by
  classical
  have hcpos := c_pos X
  obtain ⟨D, hD, hDb⟩ : ∃ D : ℝ, 0 < D ∧ ∀ σ : E →+* ℂ, ‖σ (X.den : E)‖ ≤ D := by
    refine ⟨∑ σ : E →+* ℂ, ‖σ (X.den : E)‖ + 1, by positivity, fun σ => ?_⟩
    have := Finset.single_le_sum (f := fun σ : E →+* ℂ => ‖σ (X.den : E)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)
    linarith
  set S := ∑ τ : X.Ψ, (X.c τ)⁻¹ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun τ _ => (inv_pos.2 (hcpos τ)).le
  have hcl : ∀ τ, (S + 1)⁻¹ ≤ X.c τ := fun τ => by
    have h1 : (X.c τ)⁻¹ ≤ S := Finset.single_le_sum (f := fun τ => (X.c τ)⁻¹)
      (fun τ _ => (inv_pos.2 (hcpos τ)).le) (Finset.mem_univ τ)
    rw [inv_le_comm₀ (by linarith) (hcpos τ)]
    linarith
  refine ⟨(S + 1)⁻¹ / D, div_pos (inv_pos.2 (by linarith)) hD, ?_⟩
  intro x hx v hv hsum
  have hmaj0 : ∀ τ : X.Ψ, 0 ≤ X.maj x τ (Data.emb τ.1 v) := fun τ =>
    (norm_nonneg _).trans (UnipotentCoefficientShift.norm_hermC_le_maj hx τ _)
  have hterm : ∀ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 v) < (S + 1)⁻¹ / D := fun τ =>
    lt_of_le_of_lt (Finset.single_le_sum (f := fun τ => X.c τ * X.maj x τ (Data.emb τ.1 v))
      (fun τ _ => mul_nonneg (hcpos τ).le (hmaj0 τ)) (Finset.mem_univ τ)) hsum
  have hmaj : ∀ τ : X.Ψ, D * X.maj x τ (Data.emb τ.1 v) < 1 := fun τ => by
    have h3 := hcpos τ
    have h5 : X.c τ * X.maj x τ (Data.emb τ.1 v) < X.c τ / D :=
      lt_of_lt_of_le (hterm τ) (div_le_div_of_nonneg_right (hcl τ) hD.le)
    rw [lt_div_iff₀ hD] at h5
    nlinarith
  have hemb : ∀ τ : E →+* ℂ,
      hermC τ X.Gm (Data.emb τ v) (Data.emb τ v) = τ (herm X.Gm v v) := by
    intro τ
    simp only [hermC, herm, Data.emb, map_sum, map_mul, emb_cc]
  have ha : IsIntegral ℤ ((X.den : E) * herm X.Gm v v) := X.Λ_int v hv v hv
  have hzero := UnipotentCoefficientShift.eq_zero_of_conj_lt_one ha (fun σ => by
    obtain ⟨τ, h1, h2⟩ : ∃ τ : X.Ψ, ‖σ (herm X.Gm v v)‖ = ‖τ.1 (herm X.Gm v v)‖ ∧
        ‖σ (X.den : E)‖ = ‖τ.1 (X.den : E)‖ := by
      by_cases hσ : σ ∈ X.Ψ
      · exact ⟨⟨σ, hσ⟩, rfl, rfl⟩
      · have hc : NumberField.ComplexEmbedding.conjugate σ ∈ X.Ψ := by
          by_contra h
          exact hσ ((X.cmType σ).2 h)
        refine ⟨⟨_, hc⟩, ?_, ?_⟩ <;> simp [NumberField.ComplexEmbedding.conjugate_coe_eq]
    rw [map_mul, norm_mul, h1]
    have hb := UnipotentCoefficientShift.norm_hermC_le_maj hx τ (Data.emb τ.1 v)
    rw [hemb] at hb
    calc ‖σ (X.den : E)‖ * ‖τ.1 (herm X.Gm v v)‖ ≤ D * X.maj x τ (Data.emb τ.1 v) :=
          mul_le_mul (hDb σ) hb (norm_nonneg _) hD.le
      _ < 1 := hmaj τ)
  rcases mul_eq_zero.1 hzero with h | h
  · exact absurd h (NumberField.RingOfIntegers.coe_ne_zero_iff.2 X.den_ne)
  · exact h
end ReciprocityTheory.ChartRestriction.G.FD.IsotropicThreshold
