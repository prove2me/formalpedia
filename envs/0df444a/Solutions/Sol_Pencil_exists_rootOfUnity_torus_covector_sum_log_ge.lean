-- Prove2me | solution 1 for Pencil.exists_rootOfUnity_torus_covector_sum_log_ge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/09a06dbc-a322-5b3f-bc15-3ee515da0e8e

import Mathlib
import Definitions.Def_MvPolynomial_LogMahlerMeasure
import Theorems.Thm_MvPolynomial_integrableOn_log_norm_eval_circleMap
import Theorems.Thm_MvPolynomial_log_norm_coeff_le_logMahlerMeasure_add
import Theorems.Thm_Pencil_norm_minor_le_two_mul_sup_minor_row
import Theorems.Thm_MvPolynomial_ae_restrict_torusBox_eval_circleMap_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Pencil_exists_rootOfUnity_torus_covector_sum_log_ge

open MeasureTheory Real

namespace Pencil
p2m_export "Pencil" "norm_minor_le_two_mul_sup_minor_row"
p2m_open "Pencil"

variable {r : ℕ}

noncomputable def linForm (c : Fin r → ℂ) : MvPolynomial (Fin r) ℂ :=
  ∑ j, MvPolynomial.C (c j) * MvPolynomial.X j

theorem eval_linForm (c z : Fin r → ℂ) : MvPolynomial.eval z (linForm c) = ∑ j, z j * c j := by
  simp [linForm, MvPolynomial.eval_C, MvPolynomial.eval_X, mul_comm]

theorem coeff_linForm_single (c : Fin r → ℂ) (l : Fin r) :
    MvPolynomial.coeff (Finsupp.single l 1) (linForm c) = c l := by
  classical
  simp only [linForm, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X',
    Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0), mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq']

theorem degreeOf_linForm_le (c : Fin r → ℂ) (i : Fin r) :
    MvPolynomial.degreeOf i (linForm c) ≤ if c i = 0 then 0 else 1 := by
  classical
  refine (MvPolynomial.degreeOf_sum_le i _ _).trans (Finset.sup_le fun j _ ↦ ?_)
  by_cases hj : c j = 0
  · simp [hj]
  · refine (MvPolynomial.degreeOf_C_mul_le _ _ _).trans ?_
    rw [MvPolynomial.degreeOf_X]
    by_cases hij : i = j
    · subst hij; simp [hj]
    · simp [hij]

theorem sum_degreeOf_linForm_le (c : Fin r → ℂ) {i₀ : Fin r} (h0 : c i₀ = 0) :
    (∑ i, (MvPolynomial.degreeOf i (linForm c) : ℝ)) ≤ r - 1 := by
  classical
  have h1 : ∀ i, (MvPolynomial.degreeOf i (linForm c) : ℝ) ≤ if i = i₀ then 0 else 1 := by
    intro i
    have := degreeOf_linForm_le c i
    split_ifs with hi
    · subst hi; rw [if_pos h0] at this; exact_mod_cast this
    · have h2 : MvPolynomial.degreeOf i (linForm c) ≤ 1 := this.trans (by split_ifs <;> norm_num)
      exact_mod_cast h2
  calc (∑ i, (MvPolynomial.degreeOf i (linForm c) : ℝ))
      ≤ ∑ i : Fin r, (if i = i₀ then (0 : ℝ) else 1) := Finset.sum_le_sum fun i _ ↦ h1 i
    _ = r - 1 := by
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
        have : (Finset.univ.filter fun i : Fin r ↦ ¬ i = i₀) = Finset.univ.erase i₀ := by
          ext i; simp
        rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
          Nat.cast_sub (Fin.pos i₀), Nat.cast_one]

end Pencil

theorem solution {r : ℕ} (v : Fin r → ℂ) {i₀ : Fin r}
    (hi₀ : ∀ i, ‖v i‖ ≤ ‖v i₀‖)
    {ι : Type*} (T : Finset ι) (w : ι → Fin r → ℂ) (n : ι → ℕ)
    (hw : ∀ t ∈ T, ∃ p : Fin r × Fin r, v p.1 * w t p.2 - v p.2 * w t p.1 ≠ 0) :
    ∃ z : Fin r → ℂ, (∀ j, ∃ m : ℕ, 0 < m ∧ z j ^ m = 1) ∧
      ∑ t ∈ T, (n t : ℝ) * Real.log (⨆ p : Fin r × Fin r, ‖v p.1 * w t p.2 - v p.2 * w t p.1‖)
          - (∑ t ∈ T, (n t : ℝ)) * (r * Real.log 2 + 1)
        ≤ ∑ t ∈ T, (n t : ℝ) * Real.log ‖∑ j, z j * (v i₀ * w t j - v j * w t i₀)‖ := by
  classical
  haveI : Nonempty (Fin r) := ⟨i₀⟩
  haveI : Nonempty (Fin r × Fin r) := ⟨(i₀, i₀)⟩

  let c : ι → Fin r → ℂ := fun t j ↦ v i₀ * w t j - v j * w t i₀
  have hc0 : ∀ t, c t i₀ = 0 := fun t ↦ by simp only [c]; ring
  let P : ι → MvPolynomial (Fin r) ℂ := fun t ↦ Pencil.linForm (c t)

  have hkey : ∀ t ∈ T, Real.log (⨆ p : Fin r × Fin r, ‖v p.1 * w t p.2 - v p.2 * w t p.1‖) ≤
      (P t).logMahlerMeasure + r * Real.log 2 := by
    intro t ht
    obtain ⟨l, hl⟩ := Finite.exists_max (fun l ↦ ‖c t l‖)
    have hPL : ∀ p : Fin r × Fin r, ‖v p.1 * w t p.2 - v p.2 * w t p.1‖ ≤ 2 * ‖c t l‖ := fun p ↦
      (Pencil.norm_minor_le_two_mul_sup_minor_row v (w t) hi₀ p.1 p.2).trans
        (mul_le_mul_of_nonneg_left (ciSup_le fun l' ↦ hl l') zero_le_two)
    obtain ⟨p₀, hp₀⟩ := hw t ht
    have hsup_pos : 0 < ⨆ p : Fin r × Fin r, ‖v p.1 * w t p.2 - v p.2 * w t p.1‖ :=
      lt_of_lt_of_le (norm_pos_iff.mpr hp₀)
        (le_ciSup (Finite.bddAbove_range fun p : Fin r × Fin r ↦ ‖v p.1 * w t p.2 - v p.2 * w t p.1‖) p₀)
    have hcl : c t l ≠ 0 := by
      intro h
      have := (norm_pos_iff.mpr hp₀).trans_le (hPL p₀)
      rw [h, norm_zero, mul_zero] at this
      exact lt_irrefl _ this
    have hsupp : Finsupp.single l 1 ∈ (P t).support := by
      rw [MvPolynomial.mem_support_iff]
      change MvPolynomial.coeff (Finsupp.single l 1) (Pencil.linForm (c t)) ≠ 0
      rw [Pencil.coeff_linForm_single]; exact hcl
    have hM3 := MvPolynomial.log_norm_coeff_le_logMahlerMeasure_add (P t) hsupp
    have hco : MvPolynomial.coeff (Finsupp.single l 1) (P t) = c t l := Pencil.coeff_linForm_single _ _
    rw [hco] at hM3
    have hdeg : (∑ i, ((P t).degreeOf i : ℝ)) ≤ r - 1 := Pencil.sum_degreeOf_linForm_le (c t) (hc0 t)
    have hdeg' := mul_le_mul_of_nonneg_right hdeg (Real.log_nonneg one_le_two)
    calc Real.log (⨆ p : Fin r × Fin r, ‖v p.1 * w t p.2 - v p.2 * w t p.1‖)
        ≤ Real.log (2 * ‖c t l‖) := Real.log_le_log hsup_pos (ciSup_le hPL)
      _ = Real.log 2 + Real.log ‖c t l‖ := Real.log_mul two_ne_zero (norm_ne_zero_iff.mpr hcl)
      _ ≤ Real.log 2 + ((P t).logMahlerMeasure + (r - 1) * Real.log 2) := by linarith
      _ = (P t).logMahlerMeasure + r * Real.log 2 := by ring

  have hsum : ∑ t ∈ T, (n t : ℝ) * Real.log (⨆ p : Fin r × Fin r, ‖v p.1 * w t p.2 - v p.2 * w t p.1‖)
        - (∑ t ∈ T, (n t : ℝ)) * (r * Real.log 2)
      ≤ ∑ t ∈ T, (n t : ℝ) * (P t).logMahlerMeasure := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun t ht ↦ ?_
    have h := mul_le_mul_of_nonneg_left (hkey t ht) (Nat.cast_nonneg (n t))
    linarith

  let f : (Fin r → ℝ) → ℝ := fun θ ↦
    ∑ t ∈ T, (n t : ℝ) * Real.log ‖MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ i)) (P t)‖
  have hfi : IntegrableOn f (MvPolynomial.torusBox r) :=
    MeasureTheory.integrable_finsetSum T fun t _ ↦
      (MvPolynomial.integrableOn_log_norm_eval_circleMap (P t)).const_mul _
  have havg : ⨍ θ in MvPolynomial.torusBox r, f θ = ∑ t ∈ T, (n t : ℝ) * (P t).logMahlerMeasure := by
    rw [MeasureTheory.setAverage_eq, MvPolynomial.volume_real_torusBox, smul_eq_mul,
      MeasureTheory.integral_finsetSum T (fun t _ ↦
        (MvPolynomial.integrableOn_log_norm_eval_circleMap (P t)).const_mul _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [MeasureTheory.integral_const_mul, MvPolynomial.logMahlerMeasure_def, inv_pow]
    ring

  have hP0 : ∀ t ∈ T, P t ≠ 0 := by
    intro t ht hPt
    obtain ⟨p₀, hp₀⟩ := hw t ht
    have h0 : ∀ l, v i₀ * w t l - v l * w t i₀ = 0 := fun l ↦ by
      change c t l = 0
      rw [← Pencil.coeff_linForm_single (c t) l]
      change MvPolynomial.coeff (Finsupp.single l 1) (P t) = 0
      rw [hPt, MvPolynomial.coeff_zero]
    have h := Pencil.norm_minor_le_two_mul_sup_minor_row v (w t) hi₀ p₀.1 p₀.2
    simp only [h0, norm_zero, ciSup_const, mul_zero, norm_le_zero_iff] at h
    exact hp₀ h

  let g : ι → (Fin r → ℝ) → ℂ := fun t θ ↦ MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ i)) (P t)
  have hg : ∀ t, Continuous (g t) := fun t ↦ MvPolynomial.continuous_eval_circleMap (P t)
  let U : Set (Fin r → ℝ) := ⋂ t ∈ T, {θ | g t θ ≠ 0}
  have hU : IsOpen U := isOpen_biInter_finset fun t _ ↦ isOpen_ne_fun (hg t) continuous_const
  let B : Set (Fin r → ℝ) := Set.pi Set.univ fun _ ↦ Set.Ioo (0 : ℝ) (2 * π)
  have hB : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo
  have hV : IsOpen (U ∩ B) := hU.inter hB
  have hfV : ContinuousOn f (U ∩ B) := by
    refine continuousOn_finsetSum T fun t ht ↦ continuousOn_const.mul ?_
    refine ((hg t).continuousOn.norm).log fun θ hθ ↦ ?_
    exact norm_ne_zero_iff.mpr (Set.mem_iInter₂.mp hθ.1 t ht)

  have hae : ∀ᵐ θ ∂(volume.restrict (MvPolynomial.torusBox r)), θ ∈ U ∩ B := by
    have h1 : ∀ᵐ θ ∂(volume.restrict (MvPolynomial.torusBox r)), ∀ t ∈ T, g t θ ≠ 0 :=
      (Finset.eventually_all T).mpr fun t ht ↦
        MvPolynomial.ae_restrict_torusBox_eval_circleMap_ne_zero (hP0 t ht)
    have hTB : MvPolynomial.torusBox r =ᵐ[volume] B :=
      MvPolynomial.torusBox_ae_eq_Icc.trans (by
        rw [volume_pi]; exact Measure.univ_pi_Ioo_ae_eq_Icc.symm)
    have h2 : ∀ᵐ θ ∂(volume.restrict (MvPolynomial.torusBox r)), θ ∈ B := by
      rw [Measure.restrict_congr_set hTB]
      exact ae_restrict_mem hB.measurableSet
    filter_upwards [h1, h2] with θ h1 h2
    exact ⟨Set.mem_iInter₂.mpr h1, h2⟩
  have hTV : (MvPolynomial.torusBox r ∩ (U ∩ B) : Set (Fin r → ℝ)) =ᵐ[volume]
      MvPolynomial.torusBox r := by
    have h := (ae_restrict_iff' MvPolynomial.measurableSet_torusBox).mp hae
    refine Filter.eventuallyEq_set.mpr ?_
    filter_upwards [h] with θ hθ
    exact ⟨fun h' ↦ h'.1, fun h' ↦ ⟨h', hθ h'⟩⟩

  obtain ⟨θ₀, hθ₀, hle⟩ := MeasureTheory.exists_setAverage_le (μ := volume)
    (s := MvPolynomial.torusBox r ∩ (U ∩ B)) (f := f)
    (by rw [measure_congr hTV]; exact MvPolynomial.volume_torusBox_ne_zero)
    ((measure_mono Set.inter_subset_left).trans_lt MvPolynomial.volume_torusBox_lt_top).ne
    (hfi.mono_set Set.inter_subset_left)
  rw [setAverage_congr hTV, havg] at hle

  have hS : IsOpen ((U ∩ B) ∩ f ⁻¹' Set.Ioi (f θ₀ - 1)) := hfV.isOpen_inter_preimage hV isOpen_Ioi
  have hθ₀S : θ₀ ∈ (U ∩ B) ∩ f ⁻¹' Set.Ioi (f θ₀ - 1) := ⟨hθ₀.2, by simp⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS θ₀ hθ₀S
  have hq : ∀ j, ∃ q : ℚ, dist (2 * π * (q : ℝ)) (θ₀ j) < ε := by
    intro j
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
      (div_lt_div_of_pos_right (show θ₀ j - ε < θ₀ j + ε by linarith) two_pi_pos)
    rw [div_lt_iff₀ two_pi_pos] at hq1
    rw [lt_div_iff₀ two_pi_pos] at hq2
    refine ⟨q, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [mul_comm (q : ℝ) (2 * π)]
  choose q hq using hq
  have hθS : (fun j ↦ 2 * π * (q j : ℝ)) ∈ (U ∩ B) ∩ f ⁻¹' Set.Ioi (f θ₀ - 1) :=
    hball (Metric.mem_ball.mpr ((dist_pi_lt_iff hε).mpr hq))
  have hlt : f θ₀ - 1 < f (fun j ↦ 2 * π * (q j : ℝ)) := hθS.2
  refine ⟨fun j ↦ circleMap 0 1 (2 * π * (q j : ℝ)), fun j ↦ ⟨(q j).den, (q j).den_pos, ?_⟩, ?_⟩
  ·
    show circleMap 0 1 (2 * π * (q j : ℝ)) ^ (q j).den = 1
    rw [circleMap_zero, Complex.ofReal_one, one_mul, ← Complex.exp_nat_mul]
    have hqd : ((q j : ℚ) : ℂ) * ((q j).den : ℂ) = ((q j).num : ℂ) := by
      exact_mod_cast (q j).mul_den_eq_num
    have : ((q j).den : ℂ) * (((2 * π * (q j : ℝ) : ℝ) : ℂ) * Complex.I) =
        ((q j).num : ℂ) * (2 * π * Complex.I) := by
      push_cast
      linear_combination (2 * (π : ℂ) * Complex.I) * hqd
    rw [this]
    exact Complex.exp_int_mul_two_pi_mul_I _
  · have hfθ : f (fun j ↦ 2 * π * (q j : ℝ)) = ∑ t ∈ T, (n t : ℝ) *
        Real.log ‖∑ j, circleMap 0 1 (2 * π * (q j : ℝ)) * (v i₀ * w t j - v j * w t i₀)‖ := by
      simp only [f, P, Pencil.eval_linForm, c]
    rw [← hfθ]
    rcases Nat.eq_zero_or_pos (∑ t ∈ T, n t) with hN | hN
    ·
      have hn0 : ∀ t ∈ T, (n t : ℝ) = 0 := fun t ht ↦ by
        exact_mod_cast Finset.sum_eq_zero_iff.mp hN t ht
      have hL : ∑ t ∈ T, (n t : ℝ) *
          Real.log (⨆ p : Fin r × Fin r, ‖v p.1 * w t p.2 - v p.2 * w t p.1‖) = 0 :=
        Finset.sum_eq_zero fun t ht ↦ by rw [hn0 t ht, zero_mul]
      have hR : f (fun j ↦ 2 * π * (q j : ℝ)) = 0 :=
        Finset.sum_eq_zero fun t ht ↦ by rw [hn0 t ht, zero_mul]
      have hN' : ∑ t ∈ T, (n t : ℝ) = 0 := Finset.sum_eq_zero hn0
      rw [hL, hR, hN', zero_mul, sub_zero]
    · have hN' : (1 : ℝ) ≤ ∑ t ∈ T, (n t : ℝ) := by exact_mod_cast hN
      rw [mul_add, mul_one]
      linarith

end S_Pencil_exists_rootOfUnity_torus_covector_sum_log_ge
end P2MW
export P2MW.S_Pencil_exists_rootOfUnity_torus_covector_sum_log_ge (solution)
