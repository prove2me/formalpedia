-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.flowMinimumLowerBound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:33:12.790976+00:00
-- url     : https://prove2.me/submissions/8ed8113c-3ac0-412e-8b53-57be26e6aa11

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ImaginaryMajorants
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMinimumLowerBoundHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_majorant_realFlow_transfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_flow_fix
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_flowMat_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_flow_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_maj_flow_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_ImaginaryMajorants_maj_imag_flow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_maj_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_emb_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_flowDomainCriterion_holds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_emb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MajorantConjugateTransfer FlowMatrixMajorants ImaginaryMajorants
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : FlowMinimumLowerBound (E := E) := by
  unfold FlowMinimumLowerBound
  intro r X B hB
  refine ⟨1 + B, by linarith, ?_⟩
  intro ξ hξ x hx hcm s hs hdom μ hμ0 hμ
  obtain ⟨hξΛ, hξ0, hξne⟩ := hξ
  have hc : ∀ τ : X.Ψ, 0 ≤ X.c τ := fun τ => by
    show 0 ≤ 2 * ‖τ.1 X.ξ0‖
    positivity
  have hiso : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := fun τ => by
    rw [ReciprocityTheory.ChartRestriction.G.FD.hermC_emb, hξ0, map_zero]
  have hne : ∀ τ : X.Ψ, Data.emb τ.1 ξ ≠ 0 := fun τ => ReciprocityTheory.ChartRestriction.G.FD.emb_ne_zero τ.1 hξne

  have hy : X.flow ξ (fun τ => ((s τ).re : ℂ)) x ∈ X.dom := by
    have hm3a := flowDomainCriterion_holds (E := E)
    unfold FlowDomainCriterion at hm3a
    have key := (hm3a r X (fun τ => Data.emb τ.1 ξ) (by intro τ; exact ⟨hiso τ, hne τ⟩) x hx
      (fun τ => ((s τ).re : ℂ))).1
    exact key.2 (fun τ => by simp)
  have hsplit := flow_split (hiso := hiso) (s := s) (x := x)
  have hzdom : X.flow ξ (fun τ => I * ((s τ).im : ℂ)) (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) ∈ X.dom := by
    rw [← hsplit]; exact hdom
  have hreal : ∀ (τ : X.Ψ) (u : Fin r → ℂ), X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ u =
      X.maj x τ (Matrix.mulVec (X.flowMat ξ τ (-((s τ).re : ℂ))) u) :=
    fun τ u => majorant_realFlow_transfer X ξ (fun τ => (s τ).re) hx hy τ (hiso τ) u
  have hmy : ∀ τ : X.Ψ, X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ) =
      X.maj x τ (Data.emb τ.1 ξ) := fun τ => by
    rw [hreal τ, Data.flow_fix (s := -((s τ).re : ℂ)) (hv := hiso τ)]
  rcases eq_or_lt_of_le hμ0 with hμz | hμpos
  · rw [← hμz, Real.sqrt_zero, mul_zero]
    exact Real.sqrt_nonneg _

  have hmain : ∀ (τ : X.Ψ) (w : Fin r → ℂ),
      μ * X.maj x τ w ≤ (1 + B) ^ 2 * X.maj (X.flow ξ s x) τ w := by
    intro τ w
    have hinv : Matrix.mulVec (X.flowMat ξ τ (-((s τ).re : ℂ)))
        (Matrix.mulVec (X.flowMat ξ τ ((s τ).re : ℂ)) w) = w := by
      have h := flowMat_inv (hiso := hiso τ) (a := -((s τ).re : ℂ)) (w := w)
      rwa [neg_neg] at h
    have e1 : X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ
        (Matrix.mulVec (X.flowMat ξ τ ((s τ).re : ℂ)) w) = X.maj x τ w := by
      rw [hreal τ, hinv]
    have hfl : X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ
        (Matrix.mulVec (X.flowMat ξ τ ((s τ).re : ℂ)) w) ≤
        (1 + X.c τ * |(s τ).re| * X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ)) ^ 2 *
          X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ w :=
      maj_flow_le X ξ τ hy (s τ).re w
    rw [e1, hmy τ] at hfl
    have hnn : 0 ≤ X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ) :=
      mul_nonneg (mul_nonneg (hc τ) (abs_nonneg _)) (MajorantConjugateTransfer.maj_nonneg (hx := hx) (τ := τ) (v := _))
    have hle : X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ) ≤ B := by
      have h3 : X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ) =
          |(s τ).re| * (X.c τ * X.maj x τ (Data.emb τ.1 ξ)) := by ring
      rw [h3]
      calc |(s τ).re| * (X.c τ * X.maj x τ (Data.emb τ.1 ξ)) ≤ |(s τ).re| * 1 :=
            mul_le_mul_of_nonneg_left (hcm τ) (abs_nonneg _)
        _ ≤ B := by linarith [hs τ]
    have hsqle : (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 ≤ (1 + B) ^ 2 := by
      nlinarith
    have hRnn : 0 ≤ X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ w :=
      MajorantConjugateTransfer.maj_nonneg (hx := hy) (τ := τ) (v := w)
    have hxR : X.maj x τ w ≤ (1 + B) ^ 2 * X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ w :=
      hfl.trans (mul_le_mul_of_nonneg_right hsqle hRnn)

    have hq_eq : 1 + (s τ).im / X.tt ξ x τ =
        1 + X.c τ * (s τ).im * X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ) := by
      rw [hmy τ, show X.tt ξ x τ = 1 / (X.c τ * X.maj x τ (Data.emb τ.1 ξ)) from rfl,
        div_div_eq_mul_div, div_one]
      ring
    have hμq := hμ τ
    rw [hq_eq] at hμq
    have hq : 0 < 1 + X.c τ * (s τ).im *
        X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ) :=
      lt_of_lt_of_le hμpos (hμq.trans (min_le_left _ _))
    have himag : min (1 + X.c τ * (s τ).im *
          X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ))
        (1 + X.c τ * (s τ).im *
          X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ))⁻¹ *
        X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ w ≤
        X.maj (X.flow ξ (fun τ => I * ((s τ).im : ℂ)) (X.flow ξ (fun τ => ((s τ).re : ℂ)) x)) τ w :=
      maj_imag_flow (hz := hy) (ξ := ξ) (b := fun τ => (s τ).im) (hy := hzdom) (τ := τ)
        (hee := hiso τ) (he0 := hne τ) (hq := hq) (w := w)
    rw [hsplit]
    calc μ * X.maj x τ w ≤ μ * ((1 + B) ^ 2 * X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ w) :=
          mul_le_mul_of_nonneg_left hxR hμ0
      _ = (1 + B) ^ 2 * (μ * X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ w) := by ring
      _ ≤ (1 + B) ^ 2 * (min (1 + X.c τ * (s τ).im *
            X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ))
          (1 + X.c τ * (s τ).im *
            X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ))⁻¹ *
          X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ w) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hμq hRnn) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left himag (by positivity)

  have hB1 : (0 : ℝ) < (1 + B) ^ 2 := by positivity
  have hK : 0 ≤ μ * ((1 + B) ^ 2)⁻¹ := mul_nonneg hμ0 (by positivity)
  have hpt : ∀ (τ : X.Ψ) (w : Fin r → ℂ),
      μ * ((1 + B) ^ 2)⁻¹ * X.maj x τ w ≤ X.maj (X.flow ξ s x) τ w := by
    intro τ w
    calc μ * ((1 + B) ^ 2)⁻¹ * X.maj x τ w = ((1 + B) ^ 2)⁻¹ * (μ * X.maj x τ w) := by ring
      _ ≤ ((1 + B) ^ 2)⁻¹ * ((1 + B) ^ 2 * X.maj (X.flow ξ s x) τ w) :=
          mul_le_mul_of_nonneg_left (hmain τ w) (by positivity)
      _ = X.maj (X.flow ξ s x) τ w := inv_mul_cancel_left₀ hB1.ne' _
  have hsumnn : ∀ t ∈ {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)}, 0 ≤ t := by
    rintro t ⟨u, -, -, rfl⟩
    exact Finset.sum_nonneg (fun τ _ => mul_nonneg (hc τ) (MajorantConjugateTransfer.maj_nonneg (hx := hx) (τ := τ) (v := _)))
  have hL : 0 ≤ X.firstMinimumSq x := Real.sInf_nonneg hsumnn
  have hKL : μ * ((1 + B) ^ 2)⁻¹ * X.firstMinimumSq x ≤ X.firstMinimumSq (X.flow ξ s x) := by
    apply le_csInf
    · exact ⟨_, ξ, hξΛ, hξne, rfl⟩
    · rintro b ⟨v, hv, hv0, rfl⟩
      have h1 : X.firstMinimumSq x ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) :=
        csInf_le ⟨0, hsumnn⟩ ⟨v, hv, hv0, rfl⟩
      calc μ * ((1 + B) ^ 2)⁻¹ * X.firstMinimumSq x
          ≤ μ * ((1 + B) ^ 2)⁻¹ * ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) :=
            mul_le_mul_of_nonneg_left h1 hK
        _ = ∑ τ, X.c τ * (μ * ((1 + B) ^ 2)⁻¹ * X.maj x τ (Data.emb τ.1 v)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun τ _ => by ring)
        _ ≤ ∑ τ, X.c τ * X.maj (X.flow ξ s x) τ (Data.emb τ.1 v) :=
            Finset.sum_le_sum (fun τ _ => mul_le_mul_of_nonneg_left (hpt τ _) (hc τ))
  have hlhs : 0 ≤ (1 + B)⁻¹ * X.la1 x * Real.sqrt μ :=
    mul_nonneg (mul_nonneg (inv_nonneg.2 (by linarith)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hsq : ((1 + B)⁻¹ * X.la1 x * Real.sqrt μ) ^ 2 = μ * ((1 + B) ^ 2)⁻¹ * X.firstMinimumSq x := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hμ0, show X.la1 x = Real.sqrt (X.firstMinimumSq x) from rfl,
      Real.sq_sqrt hL, inv_pow]
    ring
  calc (1 + B)⁻¹ * X.la1 x * Real.sqrt μ
      = Real.sqrt (((1 + B)⁻¹ * X.la1 x * Real.sqrt μ) ^ 2) := (Real.sqrt_sq hlhs).symm
    _ = Real.sqrt (μ * ((1 + B) ^ 2)⁻¹ * X.firstMinimumSq x) := by rw [hsq]
    _ ≤ Real.sqrt (X.firstMinimumSq (X.flow ξ s x)) := Real.sqrt_le_sqrt hKL
    _ = X.la1 (X.flow ξ s x) := rfl
end ReciprocityTheory.ChartRestriction.G.FD
