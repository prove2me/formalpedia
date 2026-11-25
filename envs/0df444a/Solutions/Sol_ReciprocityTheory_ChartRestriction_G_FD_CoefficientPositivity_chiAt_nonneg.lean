-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity.chiAt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:27:50.405597+00:00
-- url     : https://prove2.me/submissions/7d6d3d39-66c1-44fa-9699-89cf4dca3861

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeMinorExistence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExponentialGrowthExclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bNormHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientPositivity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_nfac_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_pnorm_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_flowV_uvec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeMinorExistence_herm_rank1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeMinorExistence_isIsoV_uvec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeMinorExistence_pairR_rank1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_d4l4_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_flowDomainCriterion_holds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_holomorphic_periodicity_extension
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_m3bNorm_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
  ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
theorem _root_.solution (X : Data E r) (u : Fin 2 → Fin r → E) (hu : IsIsoPair X.Gm u) (la : Wt X.Ψ r)
    (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (F : Frame X.Ψ r → ℂ) (hF : DifferentiableOn ℂ F X.dom)
    (hZ : ∀ b, IsHermFam b → ∀ x ∈ X.dom, F (X.Zb u b x) = cexp (4 * Real.pi * I * X.pairR χ b) * F x)
    (C : ℝ) (hC : ∀ y ∈ X.dom, X.pnorm la F y ≤ C) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom)
    (hF0 : F x0 ≠ 0) (a : X.Ψ → Fin 2 → ℂ) (ha : ∀ τ, a τ ≠ 0) (τ0 : X.Ψ) :
    0 ≤ (X.chiAt χ a τ0).re := by
  classical
  by_contra hneg
  push_neg at hneg
  have he : X.IsIsoV (X.uvec u a) := isIsoV_uvec (X := X) hu ha
  have hreal : ∀ s : X.Ψ → ℝ, F (X.flowV (X.uvec u a) (fun τ => (s τ : ℂ)) x0) =
      cexp (4 * Real.pi * I * ∑ τ, ((X.chiAt χ a τ).re : ℂ) * s τ) * F x0 := by
    intro s
    rw [Data.flowV_uvec (X := X), hZ _ (herm_rank1 X s a) x0 hx0, pairR_rank1]
    congr 3
    push_cast
    exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
  have hcont := holomorphic_periodicity_extension r X (X.uvec u a) he F hF (fun τ => ((X.chiAt χ a τ).re : ℂ)) x0 hx0 hreal
  obtain ⟨T, hT_eq⟩ : ∃ T, T = X.ttV (X.uvec u a) x0 τ0 := ⟨_, rfl⟩
  have hT : 0 < T := by
    rw [hT_eq, Data.ttV]
    exact one_div_pos.2 (mul_pos (d4l4_c_pos X τ0) (Data.maj_pos (X := X) hx0 τ0 (he τ0).2))
  obtain ⟨b, hb_eq⟩ : ∃ b : ℝ, b = -(4 * Real.pi * (X.chiAt χ a τ0).re * T) := ⟨_, rfl⟩
  have hb : 0 < b := by
    have h1 := mul_pos (mul_pos (mul_pos four_pos Real.pi_pos) (neg_pos.2 hneg)) hT
    rw [hb_eq]
    linarith
  have hK : 0 < ‖F x0‖ * X.nfac la x0 := mul_pos (norm_pos_iff.2 hF0) (BoundedSectionAlgebra.nfac_pos (X := X) hx0 la)

  obtain ⟨y, hyM, hy1⟩ := (((tendsto_exp_mul_div_rpow_atTop (X.spread la τ0 / 2) b hb).eventually_gt_atTop
    (C / (‖F x0‖ * X.nfac la x0 * Real.exp (-b)))).and (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨t, ht_eq⟩ : ∃ t : ℝ, t = T * (y - 1) := ⟨_, rfl⟩
  let s : X.Ψ → ℂ := Function.update 0 τ0 (I * t)
  have hs0 : s τ0 = I * t := by simp [s]
  have hsne : ∀ τ, τ ≠ τ0 → s τ = 0 := fun τ h => by simp [s, h]
  have hq : ∀ τ, 1 + (s τ).im / X.ttV (X.uvec u a) x0 τ = if τ = τ0 then y else 1 := by
    intro τ
    split_ifs with h
    · rw [h, hs0, ← hT_eq, ht_eq]
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, one_mul, zero_add]
      field_simp
      ring
    · rw [hsne τ h]
      simp
  have hdom : X.flowV (X.uvec u a) s x0 ∈ X.dom := by
    refine ((flowDomainCriterion_holds r X (X.uvec u a) he x0 hx0 s).1).2 fun τ => ?_
    rw [hq τ]
    split_ifs <;> linarith
  have hsum : ∑ τ, ((X.chiAt χ a τ).re : ℂ) * s τ = ((X.chiAt χ a τ0).re : ℂ) * (I * t) := by
    rw [Finset.sum_eq_single τ0 (fun τ _ h => by rw [hsne τ h, mul_zero])
      (fun h => absurd (Finset.mem_univ τ0) h), hs0]
  have hnormF : ‖F (X.flowV (X.uvec u a) s x0)‖ = Real.exp (b * (y - 1)) * ‖F x0‖ := by
    rw [hcont s hdom, hsum, norm_mul]
    congr 1
    have h1 : 4 * (Real.pi : ℂ) * I * (((X.chiAt χ a τ0).re : ℂ) * (I * t)) =
        ((b * (y - 1) : ℝ) : ℂ) := by
      rw [hb_eq, ht_eq]
      push_cast
      linear_combination (4 * (Real.pi : ℂ) * ((X.chiAt χ a τ0).re : ℂ) * T * (y - 1)) * Complex.I_sq
    rw [h1, Complex.norm_exp_ofReal]
  have hN := (m3bNorm_holds r X (X.uvec u a) he la x0 hx0 s hdom).2
  simp only [hq] at hN
  have hprod : ∏ τ, max (if τ = τ0 then y else 1) (if τ = τ0 then y else 1)⁻¹ ^ (X.spread la τ / 2) =
      y ^ (X.spread la τ0 / 2) := by
    rw [Finset.prod_eq_single τ0 (fun τ _ h => by simp [h]) (fun h => absurd (Finset.mem_univ τ0) h)]
    rw [if_pos rfl, max_eq_left ((inv_le_one_of_one_le₀ hy1).trans hy1)]
  rw [hprod] at hN
  have hY := BoundedSectionAlgebra.nfac_pos (X := X) hdom la
  have hypos : 0 < y ^ (X.spread la τ0 / 2) := Real.rpow_pos_of_pos (by linarith) _
  have hnf : X.nfac la x0 / y ^ (X.spread la τ0 / 2) ≤ X.nfac la (X.flowV (X.uvec u a) s x0) := by
    rw [div_le_iff₀ hY] at hN
    rw [div_le_iff₀ hypos]
    linarith [mul_comm (y ^ (X.spread la τ0 / 2)) (X.nfac la (X.flowV (X.uvec u a) s x0))]
  have hC' := hC _ hdom
  rw [BoundedSectionAlgebra.pnorm_eq (X := X), hnormF] at hC'
  have key : ‖F x0‖ * X.nfac la x0 * Real.exp (-b) *
      (Real.exp (b * y) / y ^ (X.spread la τ0 / 2)) ≤ C := by
    calc _ = Real.exp (b * (y - 1)) * ‖F x0‖ * (X.nfac la x0 / y ^ (X.spread la τ0 / 2)) := by
          rw [show b * (y - 1) = b * y + -b by ring, Real.exp_add]
          ring
      _ ≤ Real.exp (b * (y - 1)) * ‖F x0‖ * X.nfac la (X.flowV (X.uvec u a) s x0) :=
          mul_le_mul_of_nonneg_left hnf (by positivity)
      _ ≤ C := hC'
  rw [div_lt_iff₀ (mul_pos hK (Real.exp_pos _))] at hyM
  linarith
end ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
