-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.coefficient_index_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:55:32.296901+00:00
-- url     : https://prove2.me/submissions/d4107ad4-329b-4a55-af82-413960cc3967

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientIndexLowerBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowIsotropicPairs_isIsoPair_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowIsotropicPairs_mem_pair
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticCoefficientForms_card_Psi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticCoefficientForms_card_Psi_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticCoefficientForms_coef_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticCoefficientForms_one_le_prod_norm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticCoefficientForms_quad2
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


section
namespace ReciprocityTheory.ChartRestriction.G.FD
open Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
private lemma card_le_sum_of_one_le_prod {ι : Type} [Fintype ι] [Nonempty ι] (z : ι → ℝ) (hz : ∀ i, 0 < z i)
    (h1 : 1 ≤ ∏ i, z i) : (Fintype.card ι : ℝ) ≤ ∑ i, z i := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hw : ∑ _i : ι, (1 / (Fintype.card ι : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
  have key := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1 / (Fintype.card ι : ℝ)) z
    (fun i _ => by positivity) hw (fun i _ => (hz i).le)
  rw [Real.finset_prod_rpow _ _ (fun i _ => (hz i).le), ← Finset.mul_sum] at key
  have h2 : 1 ≤ (∏ i, z i) ^ (1 / (Fintype.card ι : ℝ)) := Real.one_le_rpow h1 (by positivity)
  have h3 := h2.trans key
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hn] at h3
  linarith
private lemma prod_le_one_of_sum_le_card {ι : Type} [Fintype ι] [Nonempty ι] (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (hs : ∑ i, v i ≤ Fintype.card ι) : ∏ i, v i ≤ 1 := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hw : ∑ _i : ι, (1 / (Fintype.card ι : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
  have key := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1 / (Fintype.card ι : ℝ)) v
    (fun i _ => by positivity) hw (fun i _ => (hv i).le)
  rw [Real.finset_prod_rpow _ _ (fun i _ => (hv i).le), ← Finset.mul_sum] at key
  have h3 : 1 / (Fintype.card ι : ℝ) * ∑ i, v i ≤ 1 := by
    rw [one_div, inv_mul_le_iff₀ hn]; linarith
  by_contra hgt
  push_neg at hgt
  have := Real.one_lt_rpow hgt (by positivity : (0 : ℝ) < 1 / (Fintype.card ι : ℝ))
  linarith
private lemma card_sq_div_le_two_mul_sum_of_bounds {ι : Type} [Fintype ι] [Nonempty ι] (d ν A R : ι → ℝ) (N NC k0 c1 ε : ℝ)
    (hN : 0 < N) (hNC : 0 < NC) (hk0 : 0 < k0) (hk2 : k0 ≤ 2) (hε : 0 < ε) (hc1 : 0 < c1)
    (hd : ∀ i, 0 < d i) (hν : ∀ i, 0 < ν i) (hνs : ∑ i, ν i ≤ c1)
    (hprod : 1 ≤ ∏ i, (N ^ 2 * d i))
    (hA : ∀ i, 1 / (NC ^ 2 * k0 * ε) ≤ A i)
    (hq : ∀ i, d i * A i ≤ ν i * R i) :
    (Fintype.card ι : ℝ) ^ 2 / (N ^ 2 * NC ^ 2 * c1 * ε) ≤ 2 * ∑ i, R i := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  set K : ℝ := 1 / (NC ^ 2 * k0 * ε) with hK
  have hKpos : 0 < K := by positivity
  have hR : ∀ i, d i / ν i * K ≤ R i := by
    intro i
    rw [div_mul_eq_mul_div, div_le_iff₀ (hν i)]
    calc d i * K ≤ d i * A i := mul_le_mul_of_nonneg_left (hA i) (hd i).le
      _ ≤ ν i * R i := hq i
      _ = R i * ν i := mul_comm _ _
  have hv : ∏ i, (n * ν i / c1) ≤ 1 := by
    apply prod_le_one_of_sum_le_card (fun i => n * ν i / c1) (fun i => by have := hν i; positivity)
    rw [← Finset.sum_div, ← Finset.mul_sum, div_le_iff₀ hc1]
    exact mul_le_mul_of_nonneg_left hνs hn.le
  have hvpos : 0 < ∏ i, (n * ν i / c1) :=
    Finset.prod_pos fun i _ => by have := hν i; positivity
  have hz : n ≤ ∑ i, (N ^ 2 * d i) / (n * ν i / c1) := by
    apply card_le_sum_of_one_le_prod _ (fun i => by have := hν i; have := hd i; positivity)
    rw [Finset.prod_div_distrib]
    exact (one_le_div hvpos).mpr (hv.trans hprod)
  have hsum : ∑ i, (N ^ 2 * d i) / (n * ν i / c1) = (N ^ 2 * c1 / n) * ∑ i, d i / ν i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hν i
    field_simp
  rw [hsum] at hz
  have hdν : n ^ 2 / (N ^ 2 * c1) ≤ ∑ i, d i / ν i := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, le_div_iff₀ hn] at hz
    nlinarith
  have h2K : 1 / (NC ^ 2 * ε) ≤ 2 * K := by
    rw [hK, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < NC ^ 2 * ε := by positivity
    nlinarith
  calc n ^ 2 / (N ^ 2 * NC ^ 2 * c1 * ε) = (1 / (NC ^ 2 * ε)) * (n ^ 2 / (N ^ 2 * c1)) := by
        field_simp
    _ ≤ (2 * K) * (n ^ 2 / (N ^ 2 * c1)) := mul_le_mul_of_nonneg_right h2K (by positivity)
    _ ≤ (2 * K) * ∑ i, d i / ν i := mul_le_mul_of_nonneg_left hdν (by positivity)
    _ = 2 * ∑ i, d i / ν i * K := by rw [← Finset.sum_mul]; ring
    _ ≤ 2 * ∑ i, R i := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hR i) (by norm_num)
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution (h2 : UnipotentLatticeLift (E := E)) (h3d : FourierCoefficientSupport (E := E))
    (h5 : NonvanishingCoefficientPositivity (E := E)) : CoefficientIndexLowerBound (E := E) := by
  intro r X la P ξ ν c1 w z0 x a ε hS hε hmaj χ hy
  obtain ⟨hH, hxL, hxξ, hxx, hne, hu0, hu⟩ := hS
  obtain ⟨_, hSS, hIso, hc1, hνc1, _, _, _, hchar, hz0, _⟩ := hH
  have hpair := FlowIsotropicPairs.isIsoPair_of X hIso hxξ hxx hne
  have hmem := FlowIsotropicPairs.mem_pair X hIso hxL
  obtain ⟨y, hyd, hy⟩ := hy
  have hHF : IsHermFam χ ∧ X.IsFreqZ X.g χ := by
    by_contra hn
    apply hy
    unfold Data.fz
    rw [if_neg hn]
  have hSS' : X.IsBddSec la P ∧ _ := hSS
  have h3 := h3d r X ![ξ, (X.NC : E) • x] hpair hmem la P hSS'.1.1 hchar ν χ y hyd
  have hy' : X.fz ![ξ, (X.NC : E) • x] X.g χ
      (X.fj la ((![ξ, (X.NC : E) • x] : Fin 2 → Fin r → E) 0) ν P) y ≠ 0 := hy
  rw [h3] at hy'
  by_cases hcond : ∀ τ, χ τ 0 0 = (ν τ : ℂ)
  swap
  · rw [if_neg hcond] at hy'
    exact absurd rfl hy'
  rw [if_pos hcond] at hy'
  have hPD := h5 r X ![ξ, (X.NC : E) • x] hpair hmem la P hSS hchar χ ⟨y, hyd, hy'⟩
  obtain ⟨β, -, hβ, hβint⟩ := (h2 r X ![ξ, (X.NC : E) • x] hpair hmem).2.2 χ hHF.1 hHF.2
  have hne0 : Nonempty X.Ψ := Fintype.card_pos_iff.mp (QuadraticCoefficientForms.card_Psi_pos (X := X.toData))

  have hz0dom : z0 ∈ X.dom := hz0.1
  have hmpos : ∀ τ, 0 < X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) :=
    fun τ => X.maj_pos hz0dom τ (hu0 τ)
  have hck : ∀ τ, X.c τ = X.k0 := by
    intro τ
    show 2 * ‖τ.1 X.ξ0‖ = X.k0
    rw [X.ξ0_abs τ]
    ring

  have ha1 : ∀ τ, Complex.normSq (a τ 1) *
      ((X.NC : ℝ) ^ 2 * X.k0 * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) = 1 := by
    intro τ
    obtain ⟨T, hT, h⟩ : ∃ T : ℂ,
        T = ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) ∧
        X.uvec ![ξ, (X.NC : E) • x] a τ = T • X.ucomp z0 ξ (X.embV x) τ := ⟨_, rfl, hu τ⟩
    have hV : X.ucomp z0 ξ (X.embV x) τ = Data.emb τ.1 x -
        (X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
          Data.emb τ.1 ξ := rfl
    have hU : X.uvec ![ξ, (X.NC : E) • x] a τ =
        a τ 0 • Data.emb τ.1 ξ + a τ 1 • ((X.NC : ℂ) • Data.emb τ.1 x) := by
      ext i
      simp [Data.uvec, Data.emb, Fin.sum_univ_two, smul_eq_mul, map_mul, map_natCast]
    rw [hU, hV] at h
    set S := X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)
    have h0 : (a τ 0 + T * S) • Data.emb τ.1 ξ + (a τ 1 * X.NC - T) • Data.emb τ.1 x = 0 := by
      ext i
      have hi := congrFun h i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      linear_combination hi
    have hq := QuadraticCoefficientForms.coef_zero hIso.2.2 hne τ.1 _ _ h0
    have hTa : a τ 1 * X.NC = T := sub_eq_zero.mp hq
    have hpos : 0 < X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) := by
      rw [hck τ]; exact mul_pos X.minWeight_pos (hmpos τ)
    have hT2 : Complex.normSq T = (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ))⁻¹ := by
      rw [hT, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hpos.le]
    have h4 : Complex.normSq (a τ 1) * (X.NC : ℝ) ^ 2 =
        (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ))⁻¹ := by
      rw [← hT2, ← hTa, Complex.normSq_mul, Complex.normSq_natCast]
      ring
    rw [hck τ] at h4 hpos
    rw [show Complex.normSq (a τ 1) * ((X.NC : ℝ) ^ 2 * X.k0 * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ))
        = (Complex.normSq (a τ 1) * (X.NC : ℝ) ^ 2) * (X.k0 * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ))
        by ring, h4]
    exact inv_mul_cancel₀ hpos.ne'

  have hχβ : ∀ (τ : X.Ψ) i k, χ τ i k = τ.1 (β i k) := by
    intro τ i k; rw [hβ]; rfl
  have hdpos : ∀ τ, 0 < (Matrix.of (χ τ)).det.re ∧ (Matrix.of (χ τ)).det.im = 0 := by
    intro τ
    have h := (hPD τ).det_pos
    rw [Complex.lt_def] at h
    exact ⟨by simpa using h.1, by simpa using h.2.symm⟩
  have hνpos : ∀ τ, 0 < ν τ := by
    intro τ
    have h := (hPD τ).diag_pos (i := 0)
    rw [Matrix.of_apply, hcond τ] at h
    exact_mod_cast h

  set Nn : ℕ := X.g * dEnat E ^ 2 with hNn
  have hdE : dE E = (dEnat E : ℝ) := by
    unfold dE dEnat
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hNpos : 0 < (X.g : ℝ) * dE E ^ 2 := by
    rw [hdE]
    have h1 : 0 < dEnat E := Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)
    have h2 := X.g_pos
    positivity
  have hNcast : ((Nn : ℕ) : ℝ) = (X.g : ℝ) * dE E ^ 2 := by
    rw [hNn, hdE]; push_cast; ring
  set γ : E := (((X.g * dEnat E ^ 2 : ℕ) : E) * β 0 0) * (((X.g * dEnat E ^ 2 : ℕ) : E) * β 1 1) -
      (((X.g * dEnat E ^ 2 : ℕ) : E) * β 0 1) * (((X.g * dEnat E ^ 2 : ℕ) : E) * β 1 0) with hγ
  have hint : IsIntegral ℤ γ :=
    ((hβint 0 0).mul (hβint 1 1)).sub ((hβint 0 1).mul (hβint 1 0))
  have hγτ : ∀ τ : X.Ψ, τ.1 γ = ((Nn : ℂ)) ^ 2 * (Matrix.of (χ τ)).det := by
    intro τ
    rw [Matrix.det_fin_two, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply,
      hχβ, hχβ, hχβ, hχβ, hγ]
    simp only [map_sub, map_mul, map_natCast, hNn]
    push_cast
    ring
  have hnorm : ∀ τ : X.Ψ, ‖τ.1 γ‖ = ((X.g : ℝ) * dE E ^ 2) ^ 2 * (Matrix.of (χ τ)).det.re := by
    intro τ
    have hdet : (Matrix.of (χ τ)).det = (((Matrix.of (χ τ)).det.re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [(hdpos τ).2])
    rw [hγτ τ, norm_mul, norm_pow, Complex.norm_natCast, hNcast]
    congr 1
    conv_lhs => rw [hdet]
    rw [Complex.norm_real, Real.norm_of_nonneg (hdpos τ).1.le]
  have hγ0 : γ ≠ 0 := by
    intro h0
    obtain ⟨τ⟩ := hne0
    have := hnorm τ
    rw [h0, map_zero, norm_zero] at this
    have := (hdpos τ).1
    have := hNpos
    nlinarith [mul_pos (pow_pos hNpos 2) (hdpos τ).1]
  have hp := QuadraticCoefficientForms.one_le_prod_norm (X := X.toData) γ hint hγ0
  simp_rw [hnorm] at hp
  rw [Finset.prod_pow] at hp
  have hprod : 1 ≤ ∏ τ : X.Ψ, (((X.g : ℝ) * dE E ^ 2) ^ 2 * (Matrix.of (χ τ)).det.re) := by
    have hnn : 0 ≤ ∏ τ : X.Ψ, (((X.g : ℝ) * dE E ^ 2) ^ 2 * (Matrix.of (χ τ)).det.re) :=
      Finset.prod_nonneg fun τ _ => by have := (hdpos τ).1; positivity
    by_contra hlt
    push_neg at hlt
    have := pow_lt_one₀ hnn hlt (two_ne_zero)
    linarith

  have hq : ∀ τ : X.Ψ, (Matrix.of (χ τ)).det.re * Complex.normSq (a τ 1) ≤
      ν τ * (X.chiAt χ a τ).re := by
    intro τ
    have h := QuadraticCoefficientForms.quad2 (Matrix.of (χ τ)) (hPD τ).1 (a τ)
    simp only [Matrix.of_apply] at h
    rw [hcond τ, Complex.ofReal_re] at h
    exact h
  have hA : ∀ τ : X.Ψ, 1 / ((X.NC : ℝ) ^ 2 * X.k0 * ε) ≤ Complex.normSq (a τ 1) := by
    intro τ
    have h := ha1 τ
    have hm := hmpos τ
    have hme := hmaj τ
    have hNC : (0 : ℝ) < X.NC := by exact_mod_cast X.NC_pos
    have hk := X.minWeight_pos
    rw [div_le_iff₀ (by positivity)]
    have hns := Complex.normSq_nonneg (a τ 1)
    have : Complex.normSq (a τ 1) * ((X.NC : ℝ) ^ 2 * X.k0 * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) ≤
        Complex.normSq (a τ 1) * ((X.NC : ℝ) ^ 2 * X.k0 * ε) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hme (by positivity)) hns
    linarith
  have key := card_sq_div_le_two_mul_sum_of_bounds (fun τ : X.Ψ => (Matrix.of (χ τ)).det.re) ν (fun τ => Complex.normSq (a τ 1))
    (fun τ => (X.chiAt χ a τ).re) ((X.g : ℝ) * dE E ^ 2) (X.NC : ℝ) X.k0 c1 ε hNpos
    (by exact_mod_cast X.NC_pos) X.minWeight_pos X.k0_le hε hc1 (fun τ => (hdpos τ).1) hνpos hνc1 hprod hA hq
  rw [QuadraticCoefficientForms.card_Psi (X := X.toData)] at key
  exact key
end ReciprocityTheory.ChartRestriction.G.FD
