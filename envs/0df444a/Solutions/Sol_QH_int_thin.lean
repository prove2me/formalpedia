-- Prove2me | solution 1 for QH.int_thin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:20:08.25602+00:00
-- url     : https://prove2.me/submissions/48306265-dce7-47d1-a743-118dff3d6a0c

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_ZeroFreeRegionGl2PrimeChoiceResults
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_IntThin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace QH
private lemma thin_intH (b : ℝ) (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun v : ℝ => v ^ (2 : ℝ) * Real.exp (-b * v ^ (39 / 100 : ℝ)))
      (Set.Ioi 0) := by
  apply MeasureTheory.Integrable.of_integral_ne_zero
  rw [integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hb]
  have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < (2 + 1) / (39 / 100))
  positivity
private lemma thin_ptw (c v lam : ℝ) (hc : 0 < c) (hv : 1 ≤ v) (hl0 : 0 < lam)
    (hl : lam ≤ v ^ (61 / 100 : ℝ)) :
    (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      4 * (v ^ (2 : ℝ) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ))) := by
  have hv0 : 0 < v := by linarith
  have hb1 : v ^ (61 / 100 : ℝ) ≤ v := by
    have := Real.rpow_le_rpow_of_exponent_le hv (by norm_num : (61 / 100 : ℝ) ≤ 1)
    rwa [Real.rpow_one] at this
  have hs : Real.sqrt v ≤ v ^ (61 / 100 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hv (by norm_num)
  have hprod : v ^ (39 / 100 : ℝ) * v ^ (61 / 100 : ℝ) = v := by
    rw [← Real.rpow_add hv0]; norm_num
  have hsq : (v + lam) ^ 2 ≤ 4 * v ^ (2 : ℝ) := by
    rw [Real.rpow_two]; nlinarith
  have hs0 : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
  have hg0 : 0 < v ^ (39 / 100 : ℝ) := by positivity
  have hexp : Real.exp (-c * v / (lam + Real.sqrt v)) ≤ Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hden : 0 < lam + Real.sqrt v := by linarith
    have key : c / 2 * v ^ (39 / 100 : ℝ) ≤ c * v / (lam + Real.sqrt v) := by
      rw [le_div_iff₀ hden]
      calc c / 2 * v ^ (39 / 100 : ℝ) * (lam + Real.sqrt v)
          ≤ c / 2 * v ^ (39 / 100 : ℝ) * (2 * v ^ (61 / 100 : ℝ)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = c * (v ^ (39 / 100 : ℝ) * v ^ (61 / 100 : ℝ)) := by ring
        _ = c * v := by rw [hprod]
    have e1 : -c * v / (lam + Real.sqrt v) = -(c * v / (lam + Real.sqrt v)) := by ring
    rw [e1]; linarith
  calc (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))
      ≤ (4 * v ^ (2 : ℝ)) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ)) :=
        mul_le_mul hsq hexp (Real.exp_pos _).le (by positivity)
    _ = _ := by ring
private lemma thin_integral (ε c B : ℝ) (hε : 0 < ε) (hc : 0 < c) (hB : 0 < B) :
    ∃ c' x₀ : ℝ, 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x → ∀ V lam : ℝ, x ^ (ε / 3) / 2 ≤ V → 1 ≤ lam →
    lam ≤ B * x ^ (ε / 5) * Real.log x ^ 2 →
    MeasureTheory.IntegrableOn
      (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) (Set.Ioi V) ∧
    (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) ≤
      Real.exp (-c' * x ^ (13 * ε / 100)) := by
  set H : ℝ → ℝ := fun v => v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)) with hH
  have hHint : MeasureTheory.IntegrableOn H (Set.Ioi 0) := thin_intH (c / 4) (by positivity)
  set K : ℝ := ∫ v in Set.Ioi (0 : ℝ), H v with hK
  have E1 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := Filter.eventually_ge_atTop 1
  have E2 : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x ^ (ε / 3) :=
    (tendsto_rpow_atTop (by positivity : 0 < ε / 3)).eventually_ge_atTop 2
  have E3 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ 1 / (2 * B + 1) * ‖x ^ (ε / 600)‖ :=
    (isLittleO_log_rpow_atTop (by positivity : 0 < ε / 600)).bound (by positivity)
  have E4 : ∀ᶠ x : ℝ in Filter.atTop, 4 * K ≤ Real.exp (c / 16 * x ^ (13 * ε / 100)) :=
    (Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by positivity : 0 < 13 * ε / 100)).const_mul_atTop
      (by positivity : 0 < c / 16))).eventually_ge_atTop (4 * K)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 (E1.and (E2.and (E3.and E4)))
  refine ⟨c / 16, x₀, by positivity, fun x hx V lam hV hl1 hlam => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  set V0 : ℝ := x ^ (ε / 3) / 2 with hV0
  have hV01 : 1 ≤ V0 := by rw [hV0]; linarith
  have hV00 : 0 < V0 := by linarith
  have hlog : 2 * B * Real.log x ^ 2 ≤ x ^ (ε / 300) := by
    have e : x ^ (ε / 300) = x ^ (ε / 600) * x ^ (ε / 600) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have hp : 0 ≤ x ^ (ε / 600) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp] at h3
    have h5 : Real.log x ^ 2 = |Real.log x| ^ 2 := (sq_abs _).symm
    rw [e, h5]
    have h6 : (2 * B + 1) * |Real.log x| ≤ x ^ (ε / 600) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)] at h3
      linarith
    have h7 := abs_nonneg (Real.log x)
    have h8 : ((2 * B + 1) * |Real.log x|) * ((2 * B + 1) * |Real.log x|) ≤
        x ^ (ε / 600) * x ^ (ε / 600) := mul_self_le_mul_self (by positivity) h6
    have h9 : 0 ≤ (4 * B ^ 2 + 2 * B + 1) * |Real.log x| ^ 2 := by positivity
    nlinarith
  have h2b : (2 : ℝ) ^ (61 / 100 : ℝ) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (61 / 100 : ℝ) ≤ 1)
    rwa [Real.rpow_one] at this
  have h2g : (2 : ℝ) ^ (39 / 100 : ℝ) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (39 / 100 : ℝ) ≤ 1)
    rwa [Real.rpow_one] at this
  have hlamV0 : lam ≤ V0 ^ (61 / 100 : ℝ) := by
    have e : V0 ^ (61 / 100 : ℝ) = x ^ (ε / 5) * x ^ (ε / 300) / 2 ^ (61 / 100 : ℝ) := by
      rw [hV0, Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
      congr 2; ring
    have hp5 : 0 ≤ x ^ (ε / 5) := by positivity
    have hnum : 0 ≤ x ^ (ε / 5) * x ^ (ε / 300) := by positivity
    calc lam ≤ B * x ^ (ε / 5) * Real.log x ^ 2 := hlam
      _ = x ^ (ε / 5) * (2 * B * Real.log x ^ 2) / 2 := by ring
      _ ≤ x ^ (ε / 5) * x ^ (ε / 300) / 2 := by
          apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hp5) (by norm_num)
      _ ≤ x ^ (ε / 5) * x ^ (ε / 300) / 2 ^ (61 / 100 : ℝ) :=
          div_le_div_of_nonneg_left hnum (by positivity) h2b
      _ = V0 ^ (61 / 100 : ℝ) := e.symm
  have hV0g : x ^ (13 * ε / 100) / 2 ≤ V0 ^ (39 / 100 : ℝ) := by
    have e : V0 ^ (39 / 100 : ℝ) = x ^ (13 * ε / 100) / 2 ^ (39 / 100 : ℝ) := by
      rw [hV0, Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hx0.le]
      congr 2; ring
    have hle : x ^ (13 * ε / 100) ≤ x ^ (13 * ε / 100) :=
      le_rfl
    calc x ^ (13 * ε / 100) / 2 ≤ x ^ (13 * ε / 100) / 2 := by linarith
      _ ≤ x ^ (13 * ε / 100) / 2 ^ (39 / 100 : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h2g
      _ = _ := e.symm
  set A : ℝ := Real.exp (-(c / 8) * x ^ (13 * ε / 100)) with hA
  set F : ℝ → ℝ := fun v => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) with hF
  have hFnn : ∀ v, 0 ≤ F v := fun v => by rw [hF]; positivity
  have hpt : ∀ v ∈ Set.Ioi V, F v ≤ A * 4 * H v := by
    intro v hv
    have hvV0 : V0 ≤ v := le_trans hV (le_of_lt hv)
    have hv1 : 1 ≤ v := le_trans hV01 hvV0
    have hv0 : 0 < v := by linarith
    have hl : lam ≤ v ^ (61 / 100 : ℝ) :=
      le_trans hlamV0 (Real.rpow_le_rpow hV00.le hvV0 (by norm_num))
    have hg : x ^ (13 * ε / 100) / 2 ≤ v ^ (39 / 100 : ℝ) :=
      le_trans hV0g (Real.rpow_le_rpow hV00.le hvV0 (by norm_num))
    have hp := thin_ptw c v lam hc hv1 (by linarith) hl
    have hsplit : Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ)) ≤
        A * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)) := by
      rw [hA, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hv2 : 0 ≤ v ^ (2 : ℝ) := by positivity
    calc F v ≤ 4 * (v ^ (2 : ℝ) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ))) := hp
      _ ≤ 4 * (v ^ (2 : ℝ) * (A * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)))) := by
          apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsplit hv2) (by norm_num)
      _ = A * 4 * H v := by rw [hH]; ring
  have hV0' : (0 : ℝ) ≤ V := le_trans hV00.le hV
  have hsub : Set.Ioi V ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi hV0'
  have hgint0 : MeasureTheory.IntegrableOn (fun v => A * 4 * H v) (Set.Ioi 0) := hHint.const_mul _
  have hgint : MeasureTheory.IntegrableOn (fun v => A * 4 * H v) (Set.Ioi V) := hgint0.mono_set hsub
  have hFmeas : Measurable F := by rw [hF]; fun_prop
  have hFint : MeasureTheory.IntegrableOn F (Set.Ioi V) := by
    refine MeasureTheory.Integrable.mono' hgint hFmeas.aestronglyMeasurable ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun v hv => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn v)]
    exact hpt v hv
  refine ⟨hFint, ?_⟩
  have hApos : 0 < A := Real.exp_pos _
  have hgnn : ∀ v ∈ Set.Ioi (0 : ℝ), 0 ≤ A * 4 * H v := by
    intro v hv
    have : 0 < v := hv
    rw [hH]; positivity
  calc (∫ v in Set.Ioi V, F v) ≤ ∫ v in Set.Ioi V, A * 4 * H v :=
        MeasureTheory.setIntegral_mono_on hFint hgint measurableSet_Ioi hpt
    _ ≤ ∫ v in Set.Ioi (0 : ℝ), A * 4 * H v :=
        MeasureTheory.setIntegral_mono_set hgint0
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hgnn)
          (Filter.Eventually.of_forall hsub)
    _ = A * (4 * K) := by rw [MeasureTheory.integral_const_mul, hK]; ring
    _ ≤ A * Real.exp (c / 16 * x ^ (13 * ε / 100)) := mul_le_mul_of_nonneg_left h4 hApos.le
    _ = Real.exp (-(c / 16) * x ^ (13 * ε / 100)) := by
        rw [hA, ← Real.exp_add]; congr 1; ring
end QH
end

set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH
namespace QH
theorem _root_.solution :
    ∀ ε c C A c' : ℝ, 0 < ε → 0 < c → 0 < C → 0 < A → 0 < c' → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ (y lam : ℝ) (φ : ℝ → ℂ),
      Real.exp (x ^ (ε / 3)) / 3 ≤ y → 1 ≤ lam → lam ≤ A * x ^ (ε / 5) * Real.log x ^ 2 →
      (∀ u : ℝ, y ≤ u → ‖φ u‖ ≤ C * u * (Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))) →
      ‖(y : ℂ) * ∫ u in Set.Ioi y, φ u / (u : ℂ) ^ 2‖ ≤ y * Real.exp (-(c' * x ^ (ε / 8))) := by
  intro ε c C A c' hε hc hC hA hc'
  obtain ⟨c1, x1, hc1, hT⟩ := thin_integral ε c A hε hc hA
  obtain ⟨x2, hN⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop (by positivity : 0 < ε / 3)).eventually_ge_atTop 4).and
      (((tendsto_rpow_atTop (by positivity : 0 < ε / 200)).eventually_ge_atTop (2 * c' / c1)).and
        (Filter.eventually_gt_atTop 0)))
  obtain ⟨x3, hx3⟩ := Filter.eventually_atTop.1
    ((Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by positivity : 0 < 13 * ε / 100)).const_mul_atTop
      (by positivity : 0 < c1 / 2))).eventually_ge_atTop C)
  refine ⟨max x1 (max x2 x3), fun x hx y lam psi0 hy hl1 hlam hpsi => ?_⟩
  have hxx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hxx2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxx3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hCx : C ≤ Real.exp (c1 / 2 * x ^ (13 * ε / 100)) := hx3 x hxx3
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  set V : ℝ := Real.log y with hVdef
  obtain ⟨ha, hb, hx0⟩ := hN x hxx2
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hly : x ^ (ε / 3) - Real.log 3 ≤ Real.log y := by
    have := Real.log_le_log (by positivity) hy
    rwa [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at this
  have hV : x ^ (ε / 3) / 2 ≤ V := by linarith
  have hfin : c' * x ^ (ε / 8) ≤ c1 / 2 * x ^ (13 * ε / 100) := by
    have e : x ^ (13 * ε / 100) = x ^ (ε / 200) * x ^ (ε / 8) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have h1 : c' ≤ c1 / 2 * x ^ (ε / 200) := by
      rw [div_le_iff₀ hc1] at hb
      linarith
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  obtain ⟨hint, hbd⟩ := hT x hxx1 V lam hV hl1 hlam
  set F : ℝ → ℝ := fun v => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) with hF
  set G : ℝ → ℝ := fun u => F (Real.log u) / u with hG
  have himg : Real.exp '' Set.Ioi V = Set.Ioi y := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      have : V < v := hv
      show y < Real.exp v
      rw [← Real.exp_log hy0]
      exact Real.exp_lt_exp.mpr this
    · intro hu
      have hu' : y < u := hu
      have hu0 : 0 < u := lt_trans hy0 hu'
      exact ⟨Real.log u, Real.log_lt_log hy0 hu', Real.exp_log hu0⟩
  have hderiv : ∀ v ∈ Set.Ioi V, HasDerivWithinAt Real.exp (Real.exp v) (Set.Ioi V) v :=
    fun v _ => (Real.hasDerivAt_exp v).hasDerivWithinAt
  have hinj : Set.InjOn Real.exp (Set.Ioi V) := Real.exp_injective.injOn
  have hcomp : (fun v => |Real.exp v| • G (Real.exp v)) = F := by
    funext v
    have hp := Real.exp_pos v
    rw [hG]
    simp only [abs_of_pos hp, Real.log_exp, smul_eq_mul]
    field_simp
  have hGint : MeasureTheory.IntegrableOn G (Set.Ioi y) := by
    rw [← himg, MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      hderiv hinj, hcomp]
    exact hint
  have hGval : (∫ u in Set.Ioi y, G u) = ∫ v in Set.Ioi V, F v := by
    rw [← himg, MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      hderiv hinj, hcomp]
  have hnorm : ‖∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖ ≤ C * ∫ u in Set.Ioi y, G u := by
    calc ‖∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖
        ≤ ∫ u in Set.Ioi y, ‖psi0 u / (u : ℂ) ^ 2‖ := MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ u in Set.Ioi y, C * G u := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun _ => norm_nonneg _) (hGint.const_mul C)
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
          have hu' : y < u := hu
          have hu0 : 0 < u := lt_trans hy0 hu'
          have h1 := hpsi u hu'.le
          show ‖psi0 u / (u : ℂ) ^ 2‖ ≤ C * G u
          rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0,
            div_le_iff₀ (by positivity)]
          refine le_trans h1 (le_of_eq ?_)
          rw [hG, hF]
          field_simp
      _ = C * ∫ u in Set.Ioi y, G u := MeasureTheory.integral_const_mul _ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
  apply mul_le_mul_of_nonneg_left _ hy0.le
  calc ‖∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖ ≤ C * ∫ u in Set.Ioi y, G u := hnorm
    _ = C * ∫ v in Set.Ioi V, F v := by rw [hGval]
    _ ≤ C * Real.exp (-c1 * x ^ (13 * ε / 100)) := mul_le_mul_of_nonneg_left hbd hC.le
    _ ≤ Real.exp (c1 / 2 * x ^ (13 * ε / 100)) * Real.exp (-c1 * x ^ (13 * ε / 100)) :=
        mul_le_mul_of_nonneg_right hCx (Real.exp_pos _).le
    _ ≤ Real.exp (-(c' * x ^ (ε / 8))) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
end QH
