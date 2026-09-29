-- Prove2me | solution 1 for UpperHalfPlane.exists_localModel_pair_integral_mul_dbarLogDeriv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/941b0198-a338-5644-9302-e2949a592f44

import Mathlib
import Theorems.Thm_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_exists_localModel_pair_integral_mul_dbarLogDeriv_eq

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open Complex MeasureTheory Filter Set Metric
open scoped Real Topology Manifold ContDiff

namespace DipoleConstruction

set_option quotPrecheck false in
local notation "𝕌" => {z : ℂ | 0 < z.im}

def dbarL (T : ℂ →L[ℝ] ℂ) : ℂ := (T 1 + I * T I) / 2

def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2

theorem dbar_eq (f : ℂ → ℂ) (z : ℂ) : dbar f z = dbarL (fderiv ℝ f z) := rfl

theorem dbarL_add (T T' : ℂ →L[ℝ] ℂ) : dbarL (T + T') = dbarL T + dbarL T' := by
  simp only [dbarL, ContinuousLinearMap.add_apply]; ring

theorem dbarL_smul (c : ℂ) (T : ℂ →L[ℝ] ℂ) : dbarL (c • T) = c * dbarL T := by
  simp only [dbarL, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring

theorem dbarL_neg (T : ℂ →L[ℝ] ℂ) : dbarL (-T) = -dbarL T := by
  simp only [dbarL, ContinuousLinearMap.neg_apply]; ring

theorem dbarL_of_hasDerivAt {q : ℂ → ℂ} {q' z : ℂ} (h : HasDerivAt q q' z) :
    dbarL (fderiv ℝ q z) = 0 := by
  rw [h.complexToReal_fderiv.fderiv]
  simp only [dbarL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
  ring_nf; simp [I_sq]

section Core

variable {b s : ℂ} (hb : 0 < b.im) (hs : 0 < s.im) (hbs : b ≠ s)
  {χ : ℂ → ℝ} {O K : Set ℂ}
  (hχ : ContDiff ℝ 2 χ) (hO : IsOpen O) (hSeg : segment ℝ b s ⊆ O) (hχ1 : ∀ z ∈ O, χ z = 1)
  (hOK : O ⊆ K) (hK : IsClosed K) (hχK : tsupport χ ⊆ K) (h01 : ∀ z, χ z ∈ Icc (0 : ℝ) 1)

def χC (χ : ℂ → ℝ) (z : ℂ) : ℂ := (χ z : ℂ)

def dfun (b s : ℂ) (χ : ℂ → ℝ) (z : ℂ) : ℂ :=
  if z = b then 0 else 1 - χC χ z * (s - b) / (z - b)

def gfun (b s : ℂ) (χ : ℂ → ℝ) (z : ℂ) : ℂ := 1 - χC χ z * ((s - b) * (z - b)⁻¹)

def wfun (b s : ℂ) (χ : ℂ → ℝ) (z : ℂ) : ℂ := z - b - χC χ z * (s - b)

def Dχ (χ : ℂ → ℝ) (z : ℂ) : ℂ := dbar (χC χ) z

def Ffun (b s : ℂ) (χ : ℂ → ℝ) (z : ℂ) : ℂ := -Dχ χ z * (s - b) / wfun b s χ z

include hχ in
theorem contDiff_χC : ContDiff ℝ 2 (χC χ) := ofRealCLM.contDiff.comp hχ

theorem support_χC : Function.support (χC χ) = Function.support χ := by
  ext z; simp [χC]

theorem tsupport_χC : tsupport (χC χ) = tsupport χ := by
  rw [tsupport, tsupport, support_χC]

include hSeg hχ1 h01 in

theorem wfun_eq_zero_iff (z : ℂ) : wfun b s χ z = 0 ↔ z = s := by
  constructor
  · intro hw
    have hz : z = b + (χ z : ℂ) * (s - b) := by
      simp only [wfun, χC] at hw; linear_combination hw
    have hmem : z ∈ segment ℝ b s := by
      rw [segment_eq_image]
      refine ⟨χ z, h01 z, ?_⟩
      simp only [Complex.real_smul]
      push_cast
      linear_combination -hz
    have h1 : χ z = 1 := hχ1 z (hSeg hmem)
    calc z = b + (χ z : ℂ) * (s - b) := hz
      _ = s := by rw [h1]; push_cast; ring
  · intro hz
    subst hz
    have hmem : z ∈ segment ℝ b z := right_mem_segment _ _ _
    simp only [wfun, χC, hχ1 z (hSeg hmem)]; push_cast; ring

theorem dfun_of_ne {z : ℂ} (hz : z ≠ b) : dfun b s χ z = wfun b s χ z / (z - b) := by
  rw [dfun, if_neg hz, wfun, sub_div, div_self (sub_ne_zero.2 hz), mul_div_assoc]

theorem dfun_eq_gfun_of_ne {z : ℂ} (hz : z ≠ b) : dfun b s χ z = gfun b s χ z := by
  simp only [dfun, if_neg hz, gfun, div_eq_mul_inv, mul_assoc]

theorem dfun_eventuallyEq_gfun {z : ℂ} (hz : z ≠ b) : dfun b s χ =ᶠ[𝓝 z] gfun b s χ := by
  filter_upwards [isOpen_ne.mem_nhds hz] with w hw using dfun_eq_gfun_of_ne hw

include hχ in
theorem contDiffAt_gfun {z : ℂ} (hz : z ≠ b) : ContDiffAt ℝ 2 (gfun b s χ) z := by
  refine contDiffAt_const.sub ((contDiff_χC hχ).contDiffAt.mul ?_)
  exact contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.2 hz))

include hχ in
theorem contDiffAt_dfun {z : ℂ} (hz : z ≠ b) : ContDiffAt ℝ 2 (dfun b s χ) z :=
  (contDiffAt_gfun hχ hz).congr_of_eventuallyEq (dfun_eventuallyEq_gfun hz)

include hSeg hχ1 h01 in

theorem dfun_ne_zero {z : ℂ} (hzb : z ≠ b) (hzs : z ≠ s) : dfun b s χ z ≠ 0 := by
  rw [dfun_of_ne hzb]
  exact div_ne_zero (fun h => hzs ((wfun_eq_zero_iff hSeg hχ1 h01 z).1 h)) (sub_ne_zero.2 hzb)

include hχK in
theorem dfun_eq_one {z : ℂ} (hz : z ∉ K) (hbK : b ∈ K) : dfun b s χ z = 1 := by
  have hzb : z ≠ b := fun h => hz (h ▸ hbK)
  have hχ0 : χ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hχK h)
  simp [dfun, if_neg hzb, χC, hχ0]

include hO hSeg hχ1 in

theorem dfun_eq_near {z : ℂ} (hz : z ∈ O) (hzb : z ≠ b) : dfun b s χ z = (z - s) / (z - b) := by
  simp only [dfun, if_neg hzb, χC, hχ1 z hz]
  field_simp [sub_ne_zero.2 hzb]
  push_cast; ring

include hχ hO hSeg hχ1 h01 hbs in

theorem dfun_localModel (τ : ℂ) : ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
    dfun b s χ =ᶠ[𝓝 τ] fun z =>
      (z - τ) ^ ((if τ = s then (1 : ℤ) else 0) - (if τ = b then (1 : ℤ) else 0)) * Ψ z := by
  by_cases hτb : τ = b
  · subst hτb
    refine ⟨fun z => z - s, (contDiffAt_id.sub contDiffAt_const), sub_ne_zero.2 hbs, ?_⟩
    have hexp : ((if τ = s then (1 : ℤ) else 0) - (if τ = τ then (1 : ℤ) else 0)) = -1 := by
      simp [hbs]
    rw [hexp]
    have hbO : τ ∈ O := hSeg (left_mem_segment _ _ _)
    filter_upwards [hO.mem_nhds hbO] with z hz
    by_cases hzb : z = τ
    · subst hzb; simp [dfun]
    · rw [dfun_eq_near hO hSeg hχ1 hz hzb, zpow_neg, zpow_one, div_eq_mul_inv, mul_comm]
  by_cases hτs : τ = s
  · subst hτs
    refine ⟨fun z => (z - b)⁻¹, (contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.2 hτb),
      inv_ne_zero (sub_ne_zero.2 hτb), ?_⟩
    have hexp : ((if τ = τ then (1 : ℤ) else 0) - (if τ = b then (1 : ℤ) else 0)) = 1 := by
      simp [hτb]
    rw [hexp]
    have hsO : τ ∈ O := hSeg (right_mem_segment _ _ _)
    filter_upwards [hO.mem_nhds hsO, isOpen_ne.mem_nhds hτb] with z hz hzb
    rw [dfun_eq_near hO hSeg hχ1 hz hzb, div_eq_mul_inv, zpow_one]
  · refine ⟨dfun b s χ, (contDiffAt_dfun hχ hτb).of_le (by norm_num),
      dfun_ne_zero hSeg hχ1 h01 hτb hτs, ?_⟩
    simp only [if_neg hτs, if_neg hτb, sub_self, zpow_zero, one_mul]
    exact Filter.EventuallyEq.rfl

include hχ hO hχ1 in

theorem Dχ_eq_zero {z : ℂ} (hz : z ∈ O) : Dχ χ z = 0 := by
  have hev : χC χ =ᶠ[𝓝 z] fun _ => (1 : ℂ) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    simp [χC, hχ1 w hw]
  simp only [Dχ, dbar, hev.fderiv_eq, fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, mul_zero, add_zero, zero_div]

include hχ in
theorem continuous_Dχ : Continuous (Dχ χ) := by
  have h1 : Continuous (fderiv ℝ (χC χ)) := (contDiff_χC hχ).continuous_fderiv (by norm_num)
  show Continuous fun z => (fderiv ℝ (χC χ) z 1 + I * fderiv ℝ (χC χ) z I) / 2
  exact ((h1.clm_apply continuous_const).add
    (continuous_const.mul (h1.clm_apply continuous_const))).div_const _

include hχ in
theorem continuous_wfun : Continuous (wfun b s χ) := by
  show Continuous fun z => z - b - χC χ z * (s - b)
  exact (continuous_id.sub continuous_const).sub ((contDiff_χC hχ).continuous.mul continuous_const)

include hχ hO hSeg hχ1 h01 in

theorem continuous_Ffun : Continuous (Ffun b s χ) := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hw : wfun b s χ z = 0
  ·
    have hzs : z = s := (wfun_eq_zero_iff hSeg hχ1 h01 z).1 hw
    have hev : Ffun b s χ =ᶠ[𝓝 z] fun _ => 0 := by
      have hzO : z ∈ O := hzs ▸ hSeg (right_mem_segment _ _ _)
      filter_upwards [hO.mem_nhds hzO] with w hw
      simp [Ffun, Dχ_eq_zero hχ hO hχ1 hw]
    exact (continuousAt_congr hev).2 continuousAt_const
  · show ContinuousAt (fun z => -Dχ χ z * (s - b) / wfun b s χ z) z
    exact (((continuous_Dχ hχ).neg.mul continuous_const).continuousAt).div
      (continuous_wfun hχ).continuousAt hw

include hχK in
theorem support_Ffun_subset : Function.support (Ffun b s χ) ⊆ K := by
  intro z hz
  rw [Function.mem_support] at hz
  by_contra hzK
  apply hz
  have : Dχ χ z = 0 := by
    have hz' : z ∉ tsupport (χC χ) := by rw [tsupport_χC]; exact fun h => hzK (hχK h)
    have hev : χC χ =ᶠ[𝓝 z] fun _ => (0 : ℂ) := notMem_tsupport_iff_eventuallyEq.1 hz'
    simp only [Dχ, dbar, hev.fderiv_eq, fderiv_fun_const, Pi.zero_apply,
      ContinuousLinearMap.zero_apply, mul_zero, add_zero, zero_div]
  simp [Ffun, this]

include hχK hK in
theorem tsupport_Ffun_subset : tsupport (Ffun b s χ) ⊆ K :=
  closure_minimal (support_Ffun_subset hχK) hK

include hχ in
theorem dbar_gfun {z : ℂ} (hz : z ≠ b) : dbar (gfun b s χ) z = -(Dχ χ z * ((s - b) / (z - b))) := by
  set q : ℂ → ℂ := fun u => (s - b) * (u - b)⁻¹ with hq
  have hqd : HasDerivAt q ((s - b) * (-1 / (z - b) ^ 2)) z := by
    have h1 : HasDerivAt (fun u : ℂ => u - b) 1 z := (hasDerivAt_id z).sub_const b
    exact (h1.inv (sub_ne_zero.2 hz)).const_mul (s - b)
  have hqR : DifferentiableAt ℝ q z := hqd.differentiableAt.restrictScalars ℝ
  have hχd : DifferentiableAt ℝ (χC χ) z := (contDiff_χC hχ).differentiable (by norm_num) z
  have hg : gfun b s χ = fun u => 1 - χC χ u * q u := rfl
  rw [hg, dbar_eq, fderiv_const_sub, fderiv_fun_mul hχd hqR, dbarL_neg, dbarL_add, dbarL_smul,
    dbarL_smul, dbarL_of_hasDerivAt hqd, mul_zero, zero_add]
  simp only [Dχ, dbar_eq, hq, div_eq_mul_inv]; ring

include hχ hSeg hχ1 h01 hO in

theorem dbar_dfun_div {z : ℂ} (hz : z ≠ b) :
    (fderiv ℝ (dfun b s χ) z 1 + I * fderiv ℝ (dfun b s χ) z I) / 2 / dfun b s χ z = Ffun b s χ z := by
  have h1 : (fderiv ℝ (dfun b s χ) z 1 + I * fderiv ℝ (dfun b s χ) z I) / 2 = dbar (gfun b s χ) z := by
    simp only [dbar, (dfun_eventuallyEq_gfun (s := s) (χ := χ) hz).fderiv_eq]
  rw [h1, dbar_gfun hχ hz, dfun_of_ne hz, Ffun]
  have hzb : z - b ≠ 0 := sub_ne_zero.2 hz
  by_cases hw : wfun b s χ z = 0
  · have hzs : z = s := (wfun_eq_zero_iff hSeg hχ1 h01 z).1 hw
    have : Dχ χ z = 0 := Dχ_eq_zero hχ hO hχ1 (hzs ▸ hSeg (right_mem_segment _ _ _))
    simp [hw, this]
  · field_simp

variable {η : ℂ → ℂ} {O' : Set ℂ} (hη : ContDiff ℝ 2 η) (hηs : HasCompactSupport η)
  (hηU : tsupport η ⊆ 𝕌) (hO' : IsOpen O') (hKO' : K ⊆ O') (hη1 : ∀ z ∈ O', η z = 1)
  (hKU : K ⊆ 𝕌)

include hb hs hbs hχ hO hSeg hχ1 hOK hK hχK h01 hη hηs hηU hO' hKO' hη1 hKU in

theorem pairing (E E' : ℂ → ℂ) (hE : ∀ z : ℂ, 0 < z.im → HasDerivAt E (E' z) z) :
    Integrable (fun z => E' z * Ffun b s χ z) ∧
      ∫ z, E' z * Ffun b s χ z = π * (E s - E b) := by
  have hbK : b ∈ K := hOK (hSeg (left_mem_segment _ _ _))
  have hsK : s ∈ K := hOK (hSeg (right_mem_segment _ _ _))
  set nd : ℂ → ℤ := fun a => (if a = s then (1 : ℤ) else 0) - (if a = b then (1 : ℤ) else 0)
    with hnd
  have hUo : IsOpen (𝕌 : Set ℂ) := Complex.continuous_im.isOpen_preimage _ isOpen_Ioi
  obtain ⟨-, hI2, hId⟩ :=
    Complex.integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv 𝕌 hUo (dfun b s χ) nd
      (fun τ _ => dfun_localModel hbs hχ hO hSeg hχ1 h01 τ) E E' (fun z hz => hE z hz) η hη hηs hηU

  have hW : (fun z : ℂ => E z / dfun b s χ z *
      (fderiv ℝ (dfun b s χ) z 1 * fderiv ℝ η z I - fderiv ℝ (dfun b s χ) z I * fderiv ℝ η z 1)) =
      fun _ => 0 := by
    funext z
    by_cases hz : z ∈ O'
    · have hev : η =ᶠ[𝓝 z] fun _ => (1 : ℂ) := by
        filter_upwards [hO'.mem_nhds hz] with w hw using hη1 w hw
      simp [hev.fderiv_eq]
    · have hzK : z ∉ K := fun h => hz (hKO' h)
      have hev : dfun b s χ =ᶠ[𝓝 z] fun _ => (1 : ℂ) := by
        filter_upwards [hK.isOpen_compl.mem_nhds hzK] with w hw using dfun_eq_one hχK hw hbK
      simp [hev.fderiv_eq]

  have hpt : ∑ᶠ a : ℂ, (nd a : ℂ) * E a * η a = E s - E b := by
    have hsupp : (Function.support fun a : ℂ => (nd a : ℂ) * E a * η a) ⊆ ({s, b} : Finset ℂ) := by
      intro a ha
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra h
      push Not at h
      apply ha
      simp [hnd, h.1, h.2]
    rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_pair hbs.symm]
    simp [hnd, hbs, hbs.symm, hη1 s (hKO' hsK), hη1 b (hKO' hbK)]
    ring

  have haeF : (fun z : ℂ => E' z * η z *
      ((fderiv ℝ (dfun b s χ) z 1 + I * fderiv ℝ (dfun b s χ) z I) / 2 / dfun b s χ z)) =ᵐ[volume]
      fun z => E' z * Ffun b s χ z := by
    have : ∀ᵐ z : ℂ, z ≠ b := by
      have h0 : volume ({b} : Set ℂ) = 0 := measure_singleton b
      exact measure_eq_zero_iff_ae_notMem.1 h0
    filter_upwards [this] with z hz
    rw [mul_assoc, dbar_dfun_div hχ hO hSeg hχ1 h01 hz]
    congr 1
    by_cases hzK : z ∈ K
    · rw [hη1 z (hKO' hzK), one_mul]
    · have : Ffun b s χ z = 0 := by
        by_contra h
        exact hzK (support_Ffun_subset hχK (Function.mem_support.2 h))
      rw [this, mul_zero]
  refine ⟨hI2.congr haeF, ?_⟩
  rw [hW, hpt, integral_congr_ae haeF] at hId
  simp only [integral_zero, mul_zero, zero_add] at hId
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp at hId
  linear_combination -hId

end Core

theorem isCompact_segment (b s : ℂ) : IsCompact (segment ℝ b s) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by continuity)

theorem segment_subset_U {b s : ℂ} (hb : 0 < b.im) (hs : 0 < s.im) : segment ℝ b s ⊆ 𝕌 := by
  rw [segment_eq_image]
  rintro _ ⟨θ, ⟨h0, h1⟩, rfl⟩
  show 0 < ((1 - θ) • b + θ • s).im
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.sub_re, Complex.one_re]
  rcases eq_or_lt_of_le h1 with rfl | h1'
  · simpa using hs
  · nlinarith [mul_pos (sub_pos.2 h1') hb, mul_nonneg h0 hs.le]

theorem exists_cutoff {A B : Set ℂ} (hA : IsClosed A) (hB : IsOpen B) (hAB : A ⊆ B) :
    ∃ f : ℂ → ℝ, ContDiff ℝ 2 f ∧ (∀ z ∈ A, f z = 1) ∧ (∀ z ∉ B, f z = 0) ∧
      ∀ z, f z ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨f, h0, h1, h01⟩ := exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ, ℂ) hB.isClosed_compl hA
    (disjoint_compl_left_iff.2 hAB) (n := 2)
  exact ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, fun z hz => h1 hz, fun z hz => h0 hz, h01⟩

theorem main (b s : ℂ) (hb : 0 < b.im) (hs : 0 < s.im) (hbs : b ≠ s) :
    ∃ d F : ℂ → ℂ, ∃ K : Set ℂ, IsCompact K ∧ K ⊆ 𝕌 ∧
      (∀ z ∉ K, d z = 1) ∧
      (∀ τ : ℂ, 0 < τ.im → ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
        d =ᶠ[𝓝 τ] fun z =>
          (z - τ) ^ ((if τ = s then (1 : ℤ) else 0) - (if τ = b then (1 : ℤ) else 0)) * Ψ z) ∧
      Continuous F ∧ HasCompactSupport F ∧ tsupport F ⊆ K ∧
      (∀ z : ℂ, 0 < z.im → z ≠ b →
        (fderiv ℝ d z 1 + I * fderiv ℝ d z I) / 2 / d z = F z) ∧
      ∀ E E' : ℂ → ℂ, (∀ z : ℂ, 0 < z.im → HasDerivAt E (E' z) z) →
        Integrable (fun z : ℂ => E' z * F z) ∧ ∫ z : ℂ, E' z * F z = π * (E s - E b) := by
  have hUo : IsOpen (𝕌 : Set ℂ) := Complex.continuous_im.isOpen_preimage _ isOpen_Ioi
  set Seg := segment ℝ b s with hSegdef
  have hSegc : IsCompact Seg := isCompact_segment b s
  obtain ⟨δ, hδ, hδU⟩ := hSegc.exists_cthickening_subset_open hUo (segment_subset_U hb hs)
  set ε := δ / 4 with hε
  have hε0 : 0 < ε := by positivity

  set O := thickening ε Seg with hOdef
  set K := cthickening (2 * ε) Seg with hKdef
  set O' := thickening (3 * ε) Seg with hO'def
  have hO : IsOpen O := isOpen_thickening
  have hO'o : IsOpen O' := isOpen_thickening
  have hSegO : Seg ⊆ O := self_subset_thickening hε0 _
  have hOK : O ⊆ K := (thickening_mono (by linarith) _).trans (thickening_subset_cthickening _ _)
  have hKc : IsCompact K := hSegc.cthickening
  have hKO' : K ⊆ O' := cthickening_subset_thickening' (by linarith) (by linarith) _
  have hK4 : cthickening (4 * ε) Seg ⊆ 𝕌 := by
    have : 4 * ε = δ := by rw [hε]; ring
    rw [this]; exact hδU
  have hKU : K ⊆ 𝕌 := (cthickening_mono (by linarith) _).trans hK4

  obtain ⟨χ, hχ, hχ1, hχ0, h01⟩ := exists_cutoff (A := cthickening ε Seg) (B := thickening (2 * ε) Seg)
    isClosed_cthickening isOpen_thickening (cthickening_subset_thickening' (by linarith) (by linarith) _)
  have hχ1' : ∀ z ∈ O, χ z = 1 := fun z hz => hχ1 z (thickening_subset_cthickening _ _ hz)
  have hχK : tsupport χ ⊆ K := by
    refine closure_minimal (fun z hz => ?_) isClosed_cthickening
    exact thickening_subset_cthickening _ _ (by by_contra h; exact hz (hχ0 z h))
  obtain ⟨η₀, hη₀, hη1, hη0, -⟩ := exists_cutoff (A := cthickening (3 * ε) Seg)
    (B := thickening (4 * ε) Seg) isClosed_cthickening isOpen_thickening
    (cthickening_subset_thickening' (by linarith) (by linarith) _)
  set η : ℂ → ℂ := fun z => (η₀ z : ℂ) with hηdef
  have hη : ContDiff ℝ 2 η := ofRealCLM.contDiff.comp hη₀
  have hηt : tsupport η ⊆ cthickening (4 * ε) Seg := by
    have : tsupport η = tsupport η₀ := by
      simp only [tsupport, hηdef]; congr 1; ext z; simp
    rw [this]
    refine closure_minimal (fun z hz => ?_) isClosed_cthickening
    exact thickening_subset_cthickening _ _ (by by_contra h; exact hz (hη0 z h))
  have hηs : HasCompactSupport η := (hSegc.cthickening).of_isClosed_subset (isClosed_tsupport _) hηt
  have hηU : tsupport η ⊆ 𝕌 := hηt.trans hK4
  have hη1' : ∀ z ∈ O', η z = 1 := fun z hz => by
    simp [hηdef, hη1 z (thickening_subset_cthickening _ _ hz)]
  have hbK : b ∈ K := hOK (hSegO (left_mem_segment _ _ _))
  refine ⟨dfun b s χ, Ffun b s χ, K, hKc, hKU, fun z hz => dfun_eq_one hχK hz hbK,
    fun τ _ => dfun_localModel hbs hχ hO hSegO hχ1' h01 τ,
    continuous_Ffun hχ hO hSegO hχ1' h01,
    hKc.of_isClosed_subset (isClosed_tsupport _) (tsupport_Ffun_subset isClosed_cthickening hχK),
    tsupport_Ffun_subset isClosed_cthickening hχK,
    fun z _ hz => dbar_dfun_div hχ hO hSegO hχ1' h01 hz, fun E E' hE => ?_⟩
  exact pairing hb hs hbs hχ hO hSegO hχ1' hOK isClosed_cthickening hχK h01 hη hηs hηU hO'o hKO'
    hη1' hKU E E' hE

end DipoleConstruction

end

open Complex MeasureTheory
open scoped Real Topology

theorem solution
    (b s : ℂ) (hb : 0 < b.im) (hs : 0 < s.im) (hbs : b ≠ s) :
    ∃ d F : ℂ → ℂ, ∃ K : Set ℂ, IsCompact K ∧ K ⊆ {z : ℂ | 0 < z.im} ∧
      (∀ z ∉ K, d z = 1) ∧
      (∀ τ : ℂ, 0 < τ.im → ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
        d =ᶠ[𝓝 τ] fun z =>
          (z - τ) ^ ((if τ = s then (1 : ℤ) else 0) - (if τ = b then (1 : ℤ) else 0)) * Ψ z) ∧
      Continuous F ∧ HasCompactSupport F ∧ tsupport F ⊆ K ∧
      (∀ z : ℂ, 0 < z.im → z ≠ b →
        (fderiv ℝ d z 1 + I * fderiv ℝ d z I) / 2 / d z = F z) ∧
      ∀ E E' : ℂ → ℂ, (∀ z : ℂ, 0 < z.im → HasDerivAt E (E' z) z) →
        Integrable (fun z : ℂ => E' z * F z) ∧ ∫ z : ℂ, E' z * F z = π * (E s - E b) :=
  DipoleConstruction.main b s hb hs hbs

end S_UpperHalfPlane_exists_localModel_pair_integral_mul_dbarLogDeriv_eq
end P2MW
export P2MW.S_UpperHalfPlane_exists_localModel_pair_integral_mul_dbarLogDeriv_eq (solution)
