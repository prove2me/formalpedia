-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.integration_by_parts_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:02.974292+00:00
-- url     : https://prove2.me/submissions/2858ff2c-16c7-45f9-bc80-c93da5827d84

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsIbp
import Theorems.Thm_ReciprocityTheory_AnForm_A_contDiff_of_zero_outside
import Theorems.Thm_ReciprocityTheory_AnForm_A_contDiffOn_dz
import Theorems.Thm_ReciprocityTheory_AnForm_A_contDiffOn_dzb
import Theorems.Thm_ReciprocityTheory_AnForm_A_contDiffOn_cplx
import Theorems.Thm_ReciprocityTheory_AnForm_A_dz_mul
import Theorems.Thm_ReciprocityTheory_AnForm_A_dz_of_eventually_zero
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessCof_contDiffOn
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_fderiv_apply_of_cs
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_dz_formula
import Theorems.Thm_ReciprocityTheory_AnForm_A_piolaStatement_statement


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (a b : (Fin (n + 1) → ℂ) → ℝ)
    (U K : Set (Fin (n + 1) → ℂ)) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (ha : ContDiffOn ℝ 3 a U) (hb : ContDiffOn ℝ 3 b U) (hφ : ∀ i, ContDiffOn ℝ 3 (φ i) U)
    (h0 : ∀ y ∉ K, ∀ j k, (fun y => cplx a y * dzb k (cplx b) y) =ᶠ[𝓝 y] (fun _ => 0) ∧
      dz j (cplx a) y * dzb k (cplx b) y = 0 ∧ cplx a y * dz j (dzb k (cplx b)) y = 0) :
    Integrable (fun y => ∑ j, ∑ k, dz j (cplx a) y * dzb k (cplx b) y * hessCof φ y j k) ∧
    Integrable (fun y => cplx a y * ∑ j, ∑ k, hessCof φ y j k * dz j (dzb k (cplx b)) y) ∧
    (∫ y, ∑ j, ∑ k, dz j (cplx a) y * dzb k (cplx b) y * hessCof φ y j k) +
      (∫ y, cplx a y * ∑ j, ∑ k, hessCof φ y j k * dz j (dzb k (cplx b)) y) = 0 := by
  set X := fun y => ∑ j, ∑ k, dz j (cplx a) y * dzb k (cplx b) y * hessCof φ y j k with hX
  set Y := fun y => cplx a y * ∑ j, ∑ k, hessCof φ y j k * dz j (dzb k (cplx b)) y with hY
  set g : Fin (n + 1) → Fin (n + 1) → (Fin (n + 1) → ℂ) → ℂ :=
    fun j k y => cplx a y * dzb k (cplx b) y * hessCof φ y j k with hg
  have hA : ContDiffOn ℝ 3 (cplx a) U := contDiffOn_cplx ha
  have hB : ContDiffOn ℝ 3 (cplx b) U := contDiffOn_cplx hb
  have hdA : ∀ j, ContDiffOn ℝ 2 (dz j (cplx a)) U := fun j => contDiffOn_dz hU hA (by norm_num) j
  have hdB : ∀ k, ContDiffOn ℝ 2 (dzb k (cplx b)) U := fun k => contDiffOn_dzb hU hB (by norm_num) k
  have hddB : ∀ j k, ContDiffOn ℝ 1 (dz j (dzb k (cplx b))) U :=
    fun j k => contDiffOn_dz hU (hdB k) (by norm_num) j
  have hC : ∀ j k, ContDiffOn ℝ 1 (fun y => hessCof φ y j k) U :=
    fun j k => hessCof_contDiffOn φ U hU 1 (fun i => (hφ i).of_le (by norm_num)) j k
  have hg0 : ∀ j k, ∀ y ∉ K, g j k y = 0 := by
    intro j k y hy
    have h1 := (h0 y hy j k).1.self_of_nhds
    simp only at h1
    simp only [hg, h1, zero_mul]
  have hgC : ∀ j k, ContDiff ℝ 1 (g j k) := fun j k =>
    contDiff_of_zero_outside hU hK.isClosed hKU
      (((hA.of_le (by norm_num)).mul ((hdB k).of_le (by norm_num))).mul (hC j k)) (hg0 j k)
  have hgs : ∀ j k, HasCompactSupport (g j k) := fun j k => HasCompactSupport.intro hK (hg0 j k)
  have hint : ∀ j k, ∫ y, dz j (g j k) y = 0 := fun j k =>
    (integral_dz_formula _ j _ (hgC j k) (hgs j k)).1
  have hdzint : ∀ j k, Integrable (dz j (g j k)) := by
    intro j k
    have hi := integrable_fderiv_apply_of_cs (hgC j k) (hgs j k)
    unfold dz
    exact ((hi _).sub ((hi _).const_mul Complex.I)).div_const 2
  have hXz : ∀ y ∉ K, X y = 0 := by
    intro y hy
    simp only [hX]
    exact Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => by
      rw [(h0 y hy j k).2.1, zero_mul]
  have hYz : ∀ y ∉ K, Y y = 0 := by
    intro y hy
    simp only [hY]
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_left_comm, (h0 y hy j k).2.2, mul_zero]
  have hpt : ∀ y, X y + Y y = ∑ j, ∑ k, dz j (g j k) y := by
    intro y
    by_cases hy : y ∈ K
    · have hyU := hKU hy
      have hnh := hU.mem_nhds hyU
      have hAd : DifferentiableAt ℝ (cplx a) y :=
        (hA.contDiffAt hnh).differentiableAt (by norm_num)
      have hBd : ∀ k, DifferentiableAt ℝ (dzb k (cplx b)) y :=
        fun k => ((hdB k).contDiffAt hnh).differentiableAt (by norm_num)
      have hCd : ∀ j k, DifferentiableAt ℝ (fun y => hessCof φ y j k) y :=
        fun j k => ((hC j k).contDiffAt hnh).differentiableAt (by norm_num)
      have hexp : ∀ j k, dz j (g j k) y =
          dz j (cplx a) y * dzb k (cplx b) y * hessCof φ y j k +
            cplx a y * dz j (dzb k (cplx b)) y * hessCof φ y j k +
              cplx a y * dzb k (cplx b) y * dz j (fun y => hessCof φ y j k) y := by
        intro j k
        show dz j (fun y => (cplx a y * dzb k (cplx b) y) * hessCof φ y j k) y = _
        rw [dz_mul (hAd.fun_mul (hBd k)) (hCd j k), dz_mul hAd (hBd k)]
        ring
      have hpiola := (piolaStatement_statement n φ U hU hφ y hyU).1
      simp only [hexp, Finset.sum_add_distrib]
      have h3 : ∑ j, ∑ k, cplx a y * dzb k (cplx b) y * dz j (fun y => hessCof φ y j k) y = 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [← Finset.mul_sum, hpiola k, mul_zero]
      rw [h3, add_zero]
      simp only [hX, hY, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    · have hev : ∀ j k, g j k =ᶠ[𝓝 y] fun _ => 0 := fun j k =>
        (h0 y hy j k).1.mono fun x hx => by
          simp only at hx
          simp only [hg, hx, zero_mul]
      rw [hXz y hy, hYz y hy, add_zero]
      exact (Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ =>
        dz_of_eventually_zero (hev j k)).symm
  have hXi : Integrable X := by
    have hc : ContDiff ℝ 0 X := contDiff_of_zero_outside hU hK.isClosed hKU
      (ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ =>
        (((hdA j).of_le (by norm_num)).mul ((hdB k).of_le (by norm_num))).mul
          ((hC j k).of_le (by norm_num))) hXz
    exact (contDiff_zero.1 hc).integrable_of_hasCompactSupport (HasCompactSupport.intro hK hXz)
  have hYi : Integrable Y := by
    have hc : ContDiff ℝ 0 Y := contDiff_of_zero_outside hU hK.isClosed hKU
      ((hA.of_le (by norm_num)).mul (ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ =>
        ((hC j k).of_le (by norm_num)).mul ((hddB j k).of_le (by norm_num)))) hYz
    exact (contDiff_zero.1 hc).integrable_of_hasCompactSupport (HasCompactSupport.intro hK hYz)
  refine ⟨hXi, hYi, ?_⟩
  rw [← integral_add hXi hYi]
  have hfun : (fun y => X y + Y y) = fun y => ∑ j, ∑ k, dz j (g j k) y := funext hpt
  rw [hfun, integral_finset_sum _ (fun j _ => integrable_finset_sum _ fun k _ => hdzint j k)]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_finset_sum _ fun k _ => hdzint j k]
  exact Finset.sum_eq_zero fun k _ => hint j k
end ReciprocityTheory.AnForm.A
