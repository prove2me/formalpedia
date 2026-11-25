-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.maj_two_sided
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:00:38.699265+00:00
-- url     : https://prove2.me/submissions/10b8da33-b5e4-4eb7-abfc-86251f3c646a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMinimumLowerBoundHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TwoSidedBoostBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TwoSidedBoostBounds_boost_upper
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TwoSidedBoostBounds_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_flow_fix
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_flowMat_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_flow_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_maj_flow_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_ImaginaryMajorants_maj_imag_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_ImaginaryMajorants_maj_imag_flow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_maj_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_flowDomainCriterion_holds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_majorant_realFlow_transfer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries BoostLowerBounds ImaginaryMajorants
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    (s : X.Ψ → ℂ) (hy : X.flow ξ s x ∈ X.dom) (τ : X.Ψ) (w : Fin r → ℂ) :
    0 < 1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ) ∧
    min (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
        (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ /
        (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 * X.maj x τ w ≤
      X.maj (X.flow ξ s x) τ w ∧
    X.maj (X.flow ξ s x) τ w ≤ max (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
        (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ *
        (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 * X.maj x τ w := by
  obtain ⟨_, hξξ, hξ0⟩ := hξ
  have hiso : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := fun τ => by
    rw [hermC_emb, hξξ, map_zero]
  have he0 : ∀ τ : X.Ψ, Data.emb τ.1 ξ ≠ 0 := fun τ h => hξ0 (funext fun a => by
    have := congrFun h a
    simpa [Data.emb] using this)
  have hIsoV : X.IsIsoV (fun τ => Data.emb τ.1 ξ) := fun τ => ⟨hiso τ, he0 τ⟩
  have hm0 : 0 ≤ X.maj x τ (Data.emb τ.1 ξ) := MajorantConjugateTransfer.maj_nonneg X hx τ _
  have hc0 : 0 ≤ X.c τ := (c_pos X τ).le
  have hyd : X.flow ξ (fun τ => ((s τ).re : ℂ)) x ∈ X.dom :=
    ((flowDomainCriterion_holds r X (fun τ => Data.emb τ.1 ξ) hIsoV x hx (fun τ => ((s τ).re : ℂ))).1).2
      (fun τ => by simp)
  have hsplit := flow_split (X := X) (ξ := ξ) hiso s x
  have hyd2 : X.flow ξ (fun τ => I * ((s τ).im : ℂ)) (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) ∈ X.dom :=
    hsplit ▸ hy
  have hmy : X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ) =
      X.maj x τ (Data.emb τ.1 ξ) := by
    rw [majorant_realFlow_transfer X ξ (fun τ => (s τ).re) hx hyd τ (hiso τ) (Data.emb τ.1 ξ),
      Data.flow_fix (X := X) (τ := τ) (ξ := ξ) _ _ (hiso τ)]
  have hq : 0 < 1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ) := by
    have h := ((flowDomainCriterion_holds r X (fun τ => Data.emb τ.1 ξ) hIsoV x hx s).1).1 hy τ
    simp only [Data.ttV, div_div_eq_mul_div, div_one] at h
    have e1 : (s τ).im * (X.c τ * X.maj x τ (Data.emb τ.1 ξ)) =
        X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ) := by ring
    linarith
  have hq' : 0 < 1 + X.c τ * (s τ).im *
      X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ) := by
    rw [hmy]; exact hq
  have hlow := ImaginaryMajorants.maj_imag_flow (X := X) hyd ξ (fun τ => (s τ).im) hyd2 τ (hiso τ) (he0 τ) hq' w
  have heq := ImaginaryMajorants.maj_imag_eq (X := X) hyd ξ (fun τ => (s τ).im) hyd2 τ (hiso τ) (he0 τ) hq' w
  have hsq : 0 < Real.sqrt (1 + X.c τ * (s τ).im *
      X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ)) := Real.sqrt_pos.2 hq'
  have hup := boost_upper X τ hyd (hiso τ) (he0 τ) hsq w
  rw [Real.sq_sqrt hq'.le] at hup
  simp only [hmy] at hlow heq hup
  have hyw := majorant_realFlow_transfer X ξ (fun τ => (s τ).re) hx hyd τ (hiso τ) w
  have hup1 := FlowMatrixMajorants.maj_flow_le (X := X) (τ := τ) (ξ := ξ) hx (-(s τ).re) w
  simp only [Complex.ofReal_neg, abs_neg] at hup1
  have hlo1 := FlowMatrixMajorants.maj_flow_le (X := X) (τ := τ) (ξ := ξ) hx ((s τ).re)
    (Matrix.mulVec (X.flowMat ξ τ (-((s τ).re : ℂ))) w)
  rw [FlowMatrixMajorants.flowMat_inv (X := X) (τ := τ) (ξ := ξ) (hiso τ)] at hlo1
  rw [← hyw] at hup1 hlo1
  have hP : 0 < (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 := by positivity
  have hmin0 : 0 ≤ min (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
      (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ := le_min hq.le (inv_nonneg.2 hq.le)
  have hmax0 : 0 ≤ max (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
      (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ := le_max_of_le_left hq.le
  have hdiv : X.maj x τ w / (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 ≤
      X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ w := by
    rw [div_le_iff₀ hP, mul_comm]
    exact hlo1
  rw [hsplit]
  refine ⟨hq, ?_, ?_⟩
  · calc _ = min (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
          (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ *
          (X.maj x τ w / (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiv hmin0
      _ ≤ _ := hlow
  · rw [heq]
    calc _ ≤ _ := hup
      _ ≤ _ := mul_le_mul_of_nonneg_left hup1 hmax0
      _ = _ := by ring
end ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds
