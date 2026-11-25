-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.isotropic_outside_line_of_covering
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:55.298813+00:00
-- url     : https://prove2.me/submissions/adaccec0-a88b-4920-91fa-d1d498e8c982

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLineOfCovering
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_self
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_coef_shift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_eq_zero_of_conj_lt_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_maj_decomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_maj_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_norm_hermC_le_maj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_ucomp_shift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sub_right
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
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution (hD3 : IntegerApproximationCount (E := E)) : IsotropicOutsideLine (E := E) := by
  intro r X ξ hξ z0 hz0 x hxL hxξ _hxne hsmall
  obtain ⟨hξΛ, hξξ, -⟩ := hξ
  obtain ⟨hzdom, hzD⟩ := hz0
  have hmaj_ne : ∀ τ : X.Ψ, X.maj z0 τ (Data.emb τ.1 ξ) ≠ 0 := fun τ h => by
    have h1 := hzD τ
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  have hHne : ∀ τ : X.Ψ, X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := fun τ => by
    rw [X.Hf_self hzdom τ]
    exact_mod_cast hmaj_ne τ
  have hu : ∀ (v : Fin r → E) (τ : X.Ψ), X.ucomp z0 ξ (X.embV v) τ = Data.emb τ.1 v -
      (X.Hf z0 τ (Data.emb τ.1 v) (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
        Data.emb τ.1 ξ := fun v τ => rfl
  have hxx : herm X.Gm x x = 0 := by
    apply UnipotentCoefficientShift.eq_zero_of_conj_lt_one (X.L'_int x hxL x hxL)
    have hΨ : ∀ τ : X.Ψ, ‖τ.1 (herm X.Gm x x)‖ < 1 := by
      intro τ
      have h1 : hermC τ.1 X.Gm (Data.emb τ.1 x) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hxξ, map_zero]
      have h2 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 x) = 0 := by
        rw [← hermC_conj τ.1 X.Gm_herm, h1, map_zero]
      have h3 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hξξ, map_zero]
      have hww : hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV x) τ) (X.ucomp z0 ξ (X.embV x) τ) =
          τ.1 (herm X.Gm x x) := by
        rw [hu x τ]
        simp only [hermC_sub_left, hermC_sub_right, hermC_smul_left, hermC_smul_right]
        rw [h1, h2, h3, hermC_emb]
        ring
      rw [← hww]
      exact lt_of_le_of_lt (UnipotentCoefficientShift.norm_hermC_le_maj hzdom τ _) (hsmall τ)
    intro σ
    by_cases hσ : σ ∈ X.Ψ
    · exact hΨ ⟨σ, hσ⟩
    · have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
        have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
          RingHom.ext fun a => by simp
        rw [X.cmType, hcc]
        exact hσ
      have h := hΨ ⟨_, hc⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using h
  refine ⟨hxx, ?_⟩
  obtain ⟨α, hα⟩ := (hD3 r X.toData).1 (fun τ => -(X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
    X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) / (X.NA : ℂ))
  refine ⟨α, ?_⟩
  intro x'
  have hemb : ∀ τ : X.Ψ, Data.emb τ.1 x' =
      Data.emb τ.1 x + τ.1 ((X.NA : E) * α) • Data.emb τ.1 ξ := by
    intro τ
    funext a
    simp [x', Data.emb]
  have hx'L : x' ∈ X.L' := by
    apply X.L'.add_mem hxL
    have h1 : (X.NA : E) • ξ ∈ X.L' := X.NA_sub ξ hξΛ
    have h2 := X.L'.smul_mem α h1
    have h3 : α • ((X.NA : E) • ξ) = ((X.NA : E) * (α : E)) • ξ := by
      rw [← algebraMap_smul E α ((X.NA : E) • ξ), smul_smul]
      congr 1
      exact mul_comm _ _
    rwa [h3] at h2
  have hx'ξ : herm X.Gm x' ξ = 0 := by
    simp only [x']
    rw [HermitianTraceFormVanishing.herm_add_left, HermitianTraceFormVanishing.herm_smul_left, hxξ, hξξ, mul_zero, add_zero]
  have hucomp : X.ucomp z0 ξ (X.embV x') = X.ucomp z0 ξ (X.embV x) := by
    funext τ
    rw [hu x' τ, hu x τ, hemb τ, UnipotentCoefficientShift.ucomp_shift _ _ _ _ _ (hHne τ)]
  have hcoef : ∀ τ : X.Ψ, ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E * X.NA := by
    intro τ
    rw [hemb τ, UnipotentCoefficientShift.coef_shift _ _ _ _ _ (hHne τ)]
    have hNA : (X.NA : ℂ) ≠ 0 := by exact_mod_cast X.NA_pos.ne'
    set k := X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with hkdef
    have hk : (X.NA : ℂ) * (k / X.NA) = k := by field_simp
    have e : k + τ.1 ((X.NA : E) * α) = (X.NA : ℂ) * (τ.1 (α : E) - -k / X.NA) := by
      rw [map_mul, map_natCast]
      linear_combination (-1 : ℂ) * hk
    rw [e, norm_mul, Complex.norm_natCast]
    have hb : ‖τ.1 (α : E) - -k / X.NA‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := hα τ
    calc (X.NA : ℝ) * ‖τ.1 (α : E) - -k / X.NA‖ ≤ X.NA * (2 * (fdeg E : ℝ) ^ 2 * rdE E) :=
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = 2 * (fdeg E : ℝ) ^ 2 * rdE E * X.NA := by ring
  refine ⟨hx'L, hx'ξ, hucomp, hcoef, ?_⟩
  intro τ
  have hembNC : Data.emb τ.1 ((X.NC : E) • x') = ((X.NC : ℝ) : ℂ) • Data.emb τ.1 x' := by
    funext a
    simp [Data.emb]
  rw [hembNC, UnipotentCoefficientShift.maj_smul hzdom, UnipotentCoefficientShift.maj_decomp hzdom τ _ _ (hHne τ)]
  have hw : Data.emb τ.1 x' - (X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ =
        X.ucomp z0 ξ (X.embV x) τ := by
    rw [← hucomp, hu x' τ]
  rw [hw]
  have hK := hcoef τ
  set K := ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
    X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ with hKdef
  set m := X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) with hmdef
  have hc2 : X.c τ ≤ 2 := by
    unfold Data.c
    rw [X.ξ0_abs τ]
    linarith [X.k0_le]
  have hc0 : 0 ≤ X.c τ := by
    unfold Data.c
    positivity
  have hD := hzD τ
  have hm : m < 1 := hsmall τ
  have hK0 : 0 ≤ K := norm_nonneg _
  have h1 : X.c τ * m ≤ 2 := by nlinarith
  have h2 : K ^ 2 ≤ 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2 := by
    nlinarith [mul_le_mul hK hK hK0 (le_trans hK0 hK)]
  have h3 : X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)) = X.c τ * m + K ^ 2 := by
    linear_combination K ^ 2 * hD
  have h4 : X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)) ≤
      2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2 := by
    rw [h3]
    linarith
  calc X.c τ * ((X.NC : ℝ) ^ 2 * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)))
      = (X.NC : ℝ) ^ 2 * (X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
end ReciprocityTheory.ChartRestriction.G.FD
