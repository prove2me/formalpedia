-- Prove2me | solution 1 for OnlineBeckFiala.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:50:33.389828+00:00
-- url     : https://prove2.me/submissions/73d18a0d-d3ac-43ba-bebd-edd1165b9e4c

import Mathlib
import Definitions.Def_OnlineBeckFiala_walkLaw
import Definitions.Def_OnlineBeckFiala_W
import Theorems.Thm_OnlineBeckFiala_lemma_2_5
import Definitions.Def_OnlineBeckFiala_OnlineSigner
import Theorems.Thm_OnlineBeckFiala_proposition_2_7
import Theorems.Thm_OnlineBeckFiala_lemma_3_1
import Theorems.Thm_OnlineBeckFiala_lemma_4_1

section
open MeasureTheory Set

namespace OnlineBeckFiala
namespace Dev.T11

theorem lintegral_pi_prod (μ : Measure ℝ) [SigmaFinite μ] :
    ∀ (n : ℕ) (g : Fin n → ℝ → ENNReal), (∀ i, Measurable (g i)) →
      ∫⁻ x, ∏ i, g i (x i) ∂Measure.pi (fun _ : Fin n => μ) = ∏ i, ∫⁻ t, g i t ∂μ := by
  intro n
  induction n with
  | zero => intro g hg; simp
  | succ n ih =>
    intro g hg
    have h := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
    have h2 : ∫⁻ x, ∏ i, g i (x i) ∂Measure.pi (fun _ : Fin (n+1) => μ)
        = ∫⁻ p, ∏ i, g i ((e.symm p) i) ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) := by
      rw [← h.lintegral_comp_emb e.measurableEmbedding]
      refine lintegral_congr fun a => ?_
      exact congrArg (fun z : Fin (n+1) → ℝ => ∏ i, g i (z i)) (e.symm_apply_apply a).symm
    rw [h2, Fin.prod_univ_succ]
    have h3 : ∀ p : ℝ × (Fin n → ℝ), ∏ i, g i ((e.symm p) i) =
        g 0 p.1 * ∏ i : Fin n, g i.succ (p.2 i) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
    simp_rw [h3]
    rw [lintegral_prod_mul (f := g 0) (g := fun y : Fin n → ℝ => ∏ i : Fin n, g i.succ (y i))
      (hg 0).aemeasurable
      (Finset.measurable_prod _ fun i _ => (hg _).comp (measurable_pi_apply i)).aemeasurable,
      ih (fun i => g i.succ) (fun i => hg _)]

theorem pi_withDensity (μ : Measure ℝ) [SigmaFinite μ] (n : ℕ) (f : ℝ → ENNReal)
    (hf : Measurable f) [SigmaFinite (μ.withDensity f)] :
    Measure.pi (fun _ : Fin n => μ.withDensity f) =
      (Measure.pi (fun _ : Fin n => μ)).withDensity (fun x => ∏ i, f (x i)) := by
  refine Measure.pi_eq (μ := fun _ : Fin n => μ.withDensity f) fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs)]
  have : ∀ x : Fin n → ℝ, (Set.univ.pi s).indicator (fun x => ∏ i, f (x i)) x =
      ∏ i, (s i).indicator f (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i trivial)]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Set.indicator_of_notMem hi])).symm
  simp_rw [this]
  rw [lintegral_pi_prod μ n (fun i => (s i).indicator f) (fun i => hf.indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]

end Dev.T11
end OnlineBeckFiala
end

section
open MeasureTheory Set

namespace OnlineBeckFiala
namespace Dev.T11

theorem A_meas (η : ℝ) : Measurable (A η) := by
  unfold A; fun_prop

theorem u_meas (η : ℝ) : Measurable (u η) := by
  unfold u; exact Real.measurable_exp.comp (A_meas η)

theorem W_meas (η M : ℝ) : Measurable (W η M) := by
  unfold W
  exact (measurable_const.mul (u_meas η)).mul ((A_meas η).pow_const _)

theorem u_pos (η y : ℝ) : 0 < u η y := Real.exp_pos _

theorem integrableOn_exp_neg_u (η : ℝ) :
    IntegrableOn (fun y => Real.exp (-u η y)) (Ioo (-1) 1) := by
  refine Measure.integrableOn_of_bounded (M := 1) (by simp) ?_ ?_
  · exact (Real.measurable_exp.comp (u_meas η).neg).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith [u_pos η y])

theorem Z_pos (η : ℝ) : 0 < Zu (u η) := by
  unfold Zu
  rw [integral_pos_iff_support_of_nonneg (fun y => (Real.exp_pos _).le)
    (integrableOn_exp_neg_u η)]
  have : Function.support (fun y => Real.exp (-u η y)) = univ := by
    ext y; simp
  rw [this]
  simp

theorem uRho_meas (η L : ℝ) : Measurable (uRho (u η) L) := by
  unfold uRho
  refine Measurable.indicator ?_ measurableSet_Ioo
  exact measurable_const.mul (Real.measurable_exp.comp ((u_meas η).comp
    (measurable_id.div_const L)).neg)

theorem uRho_nonneg (η L : ℝ) (x : ℝ) (hL : 0 < L) : 0 ≤ uRho (u η) L x := by
  unfold uRho
  refine Set.indicator_nonneg (fun y _ => ?_) x
  have := Z_pos η
  positivity

theorem uRho_scale (η L y : ℝ) (hL : 0 < L) :
    uRho (u η) L (L * y) = L⁻¹ * uRho (u η) 1 y := by
  unfold uRho
  have hmem : L * y ∈ Ioo (-L) L ↔ y ∈ Ioo (-1 : ℝ) 1 := by
    simp only [mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  by_cases hy : y ∈ Ioo (-1 : ℝ) 1
  · rw [Set.indicator_of_mem (hmem.mpr hy), Set.indicator_of_mem hy]
    have : L * y / L = y := by field_simp
    rw [this]
    simp only [div_one, one_mul]
    rw [mul_inv]
    ring
  · rw [Set.indicator_of_notMem (fun h => hy (hmem.mp h)), Set.indicator_of_notMem hy]
    simp

theorem rho1_prob (η : ℝ) : IsProbabilityMeasure (rho1 η) := by
  constructor
  unfold rho1 potLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : Integrable (uRho (u η) 1) := by
    unfold uRho
    rw [integrable_indicator_iff measurableSet_Ioo]
    have := integrableOn_exp_neg_u η
    simpa [IntegrableOn] using this.const_mul ((1 * Zu (u η))⁻¹)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall
    (fun x => uRho_nonneg η 1 x one_pos))]
  have : ∫ x, uRho (u η) 1 x = 1 := by
    unfold uRho
    rw [integral_indicator measurableSet_Ioo]
    simp only [div_one]
    rw [integral_const_mul]
    have := Z_pos η
    unfold Zu at this ⊢
    simp only [one_mul]
    field_simp
  rw [this]; simp

theorem scale1D (η L : ℝ) (hL : 0 < L) :
    volume.withDensity (fun x => ENNReal.ofReal (uRho (u η) L x)) =
      (rho1 η).map (fun y => L * y) := by
  ext A hA
  rw [withDensity_apply _ hA, Measure.map_apply (measurable_const_mul L) hA]
  unfold rho1 potLaw
  rw [withDensity_apply _ ((measurable_const_mul L) hA)]
  set h : ℝ → ENNReal := A.indicator (fun x => ENNReal.ofReal (uRho (u η) L x)) with hh
  have hhm : Measurable h := (ENNReal.measurable_ofReal.comp (uRho_meas η L)).indicator hA
  rw [← lintegral_indicator hA, ← lintegral_indicator ((measurable_const_mul L) hA)]
  have hpt : ∀ y : ℝ, ((fun y => L * y) ⁻¹' A).indicator
      (fun y => ENNReal.ofReal (uRho (u η) 1 y)) y = ENNReal.ofReal L * h (L * y) := by
    intro y
    have e1 : ENNReal.ofReal (uRho (u η) 1 y) =
        ENNReal.ofReal L * ENNReal.ofReal (uRho (u η) L (L * y)) := by
      rw [uRho_scale η L y hL, ← ENNReal.ofReal_mul hL.le, ← mul_assoc,
        mul_inv_cancel₀ hL.ne', one_mul]
    by_cases hy : L * y ∈ A
    · rw [Set.indicator_of_mem (show y ∈ (fun y => L * y) ⁻¹' A from hy), hh,
        Set.indicator_of_mem hy, e1]
    · rw [Set.indicator_of_notMem (show y ∉ (fun y => L * y) ⁻¹' A from hy), hh,
        Set.indicator_of_notMem hy]
      simp
  simp_rw [hpt]
  rw [lintegral_const_mul (ENNReal.ofReal L)
    (show Measurable (fun a : ℝ => h (L * a)) from hhm.comp (measurable_const_mul L))]
  have hm : (volume : Measure ℝ).map (fun y => L * y) =
      ENNReal.ofReal |L⁻¹| • volume := Real.map_volume_mul_left hL.ne'
  have := lintegral_map (μ := (volume : Measure ℝ)) hhm (measurable_const_mul L)
  rw [← this, hm, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hL.le,
    abs_of_pos (inv_pos.mpr hL), mul_inv_cancel₀ hL.ne']
  simp [hh]

end Dev.T11
end OnlineBeckFiala
end

section
open MeasureTheory Set

namespace OnlineBeckFiala
namespace Dev.T11

theorem densityLaw_uDensity (η : ℝ) (n : ℕ) (L : ℝ) (hL : 0 < L) :
    densityLaw (uDensity (u η) L : (Fin n → ℝ) → ℝ) =
      (Measure.pi (fun _ : Fin n => rho1 η)).map (fun y i => L * y i) := by
  haveI := rho1_prob η
  have h1 : densityLaw (uDensity (u η) L : (Fin n → ℝ) → ℝ) =
      Measure.pi (fun _ : Fin n => volume.withDensity (fun x => ENNReal.ofReal (uRho (u η) L x))) := by
    haveI : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (uRho (u η) L x))) := by
      rw [scale1D η L hL]; exact Measure.isProbabilityMeasure_map (measurable_const_mul L).aemeasurable
    rw [pi_withDensity volume n (fun x => ENNReal.ofReal (uRho (u η) L x))
      (ENNReal.measurable_ofReal.comp (uRho_meas η L))]
    unfold densityLaw uDensity prodDensity
    rw [← volume_pi]
    congr 1
    ext x
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => uRho_nonneg η L (x i) hL)]
  rw [h1]
  simp_rw [scale1D η L hL]
  have := rho1_prob η
  exact (Measure.pi_map_pi (μ := fun _ : Fin n => rho1 η) (f := fun _ y => L * y)
    (fun _ => (measurable_const_mul L).aemeasurable)).symm

theorem uDensity_meas (η : ℝ) (n : ℕ) (L : ℝ) : Measurable (uDensity (u η) L : (Fin n → ℝ) → ℝ) := by
  unfold uDensity prodDensity
  exact Finset.measurable_prod _ fun i _ => (uRho_meas η L).comp (measurable_pi_apply i)

theorem uDensity_pos (η : ℝ) (n : ℕ) (L : ℝ) (hL : 0 < L) :
    ∀ x ∈ cube (n := n) L, 0 < (uDensity (u η) L : (Fin n → ℝ) → ℝ) x := by
  intro x hx
  unfold uDensity prodDensity
  refine Finset.prod_pos fun i _ => ?_
  unfold uRho
  rw [Set.indicator_of_mem (hx i)]
  have := Z_pos η
  positivity

theorem uDensity_zero (η : ℝ) (n : ℕ) (L : ℝ) :
    ∀ x ∉ cube (n := n) L, (uDensity (u η) L : (Fin n → ℝ) → ℝ) x = 0 := by
  intro x hx
  simp only [cube, Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨i, hi⟩ := hx
  unfold uDensity prodDensity
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  unfold uRho
  rw [Set.indicator_of_notMem hi]

theorem uDensity_int (η : ℝ) (n : ℕ) (L : ℝ) (hL : 0 < L) :
    ∫ x, (uDensity (u η) L : (Fin n → ℝ) → ℝ) x = 1 := by
  haveI := rho1_prob η
  have hnn : ∀ x, 0 ≤ (uDensity (u η) L : (Fin n → ℝ) → ℝ) x := fun x => by
    unfold uDensity prodDensity
    exact Finset.prod_nonneg fun i _ => uRho_nonneg η L (x i) hL
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
    (uDensity_meas η n L).aestronglyMeasurable]
  have : ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (uDensity (u η) L x : ℝ) = densityLaw (uDensity (u η) L : (Fin n → ℝ) → ℝ) univ := by
    unfold densityLaw
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [this, densityLaw_uDensity η n L hL]
  haveI : IsProbabilityMeasure (Measure.pi (fun _ : Fin n => rho1 η)) := inferInstance
  have hm : Measurable (fun (y : Fin n → ℝ) (i : Fin n) => L * y i) :=
    measurable_pi_lambda _ fun i => (measurable_const_mul L).comp (measurable_pi_apply i)
  rw [Measure.map_apply hm MeasurableSet.univ]
  simp

theorem restr_pi (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (n r : ℕ) (e : Fin r → Fin n)
    (he : Function.Injective e) :
    (Measure.pi (fun _ : Fin n => ρ)).map (fun y j => y (e j)) =
      Measure.pi (fun _ : Fin r => ρ) := by
  have hind : ProbabilityTheory.iIndepFun (fun (i : Fin n) (y : Fin n → ℝ) => y i)
      (Measure.pi (fun _ : Fin n => ρ)) :=
    ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have h2 := hind.precomp he
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun j => (measurable_pi_apply (e j)).aemeasurable)] at h2
  rw [h2]
  congr 1
  ext1 j
  exact (measurePreserving_eval (fun _ : Fin n => ρ) (e j)).map_eq

end Dev.T11
end OnlineBeckFiala
end

section
open MeasureTheory Set

namespace OnlineBeckFiala
namespace Dev.T11

theorem W_pos (η M : ℝ) (hM : 1 ≤ M) (y : ℝ) (hy : y ∈ Ioo (-1 : ℝ) 1) : 0 < W η M y := by
  unfold W A
  have h1 : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have := u_pos η y
  positivity

theorem mul_mem_Ioo_iff (L t : ℝ) (hL : 0 < L) : L * t ∈ Ioo (-L) L ↔ t ∈ Ioo (-1 : ℝ) 1 := by
  simp only [mem_Ioo]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩

theorem rho1_compl (η : ℝ) : rho1 η (Ioo (-1 : ℝ) 1)ᶜ = 0 := by
  unfold rho1 potLaw
  rw [withDensity_apply _ measurableSet_Ioo.compl]
  rw [setLIntegral_congr_fun measurableSet_Ioo.compl (g := fun _ => 0)]
  · simp
  · intro x hx
    have : uRho (u η) 1 x = 0 := by
      unfold uRho; exact Set.indicator_of_notMem hx _
    show ENNReal.ofReal (uRho (u η) 1 x) = 0
    rw [this]; simp

/-- deterministic part -/
theorem balanced_of_good (η M K : ℝ) (hM : 1 ≤ M)
    (h16 : ∀ y ∈ Ioo (-1 : ℝ) 1, ∀ s : ℝ, s ^ 2 * W η M y ≤ 1 →
        y + s ∈ Ioo (-1 : ℝ) 1 ∧ y - s ∈ Ioo (-1 : ℝ) 1 ∧
        u η (y + s) + u η (y - s) - 2 * u η y ≤ s ^ 2 * W η M y)
    {n : ℕ} (d : ℕ) (L : ℝ) (hL : 0 < L) (hLsq : L ^ 2 * (2 * Real.log 2) = K * d)
    (v : Fin n → ℝ) (hv : ∀ i, |v i| ≤ 1)
    (y : Fin n → ℝ) (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1)
    (hmax : ∀ i, v i ≠ 0 → W η M (y i) ≤ L ^ 2)
    (hsum : ∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), W η M (y i) ≤ K * d) :
    IsBalanced L (uDensity (u η) L) v (fun i => L * y i) := by
  set S := Finset.univ.filter (fun i => v i ≠ 0) with hS
  have hL2 : 0 < L ^ 2 := by positivity
  have key : ∀ i, y i + v i / L ∈ Ioo (-1 : ℝ) 1 ∧ y i - v i / L ∈ Ioo (-1 : ℝ) 1 ∧
      u η (y i + v i / L) + u η (y i - v i / L) - 2 * u η (y i) ≤
        if v i ≠ 0 then W η M (y i) / L ^ 2 else 0 := by
    intro i
    by_cases hi : v i = 0
    · simp [hi, hy i]; linarith
    · have hW := W_pos η M hM (y i) (hy i)
      have hs : (v i / L) ^ 2 ≤ 1 / L ^ 2 := by
        rw [div_pow]
        exact div_le_div_of_nonneg_right (by nlinarith [abs_le.mp (hv i), sq_abs (v i)]) hL2.le
      have hsW : (v i / L) ^ 2 * W η M (y i) ≤ W η M (y i) / L ^ 2 := by
        calc _ ≤ 1 / L ^ 2 * W η M (y i) := mul_le_mul_of_nonneg_right hs hW.le
          _ = _ := by ring
      have hle1 : W η M (y i) / L ^ 2 ≤ 1 := by
        rw [div_le_one hL2]; exact hmax i hi
      obtain ⟨a, b, c⟩ := h16 (y i) (hy i) (v i / L) (hsW.trans hle1)
      exact ⟨a, b, by rw [if_pos hi]; exact c.trans hsW⟩
  have hD : Dv (u η) L (fun i => L * y i) v ≤ 2 * Real.log 2 := by
    unfold Dv Delta
    rw [← Finset.sum_add_distrib]
    have : ∀ i, (u η ((L * y i + 1 * v i) / L) - u η (L * y i / L)) +
        (u η ((L * y i + -1 * v i) / L) - u η (L * y i / L)) ≤
        if v i ≠ 0 then W η M (y i) / L ^ 2 else 0 := by
      intro i
      have e1 : (L * y i + 1 * v i) / L = y i + v i / L := by field_simp
      have e2 : (L * y i + -1 * v i) / L = y i - v i / L := by field_simp; ring
      have e3 : L * y i / L = y i := by field_simp
      rw [e1, e2, e3]
      have := (key i).2.2
      linarith
    refine (Finset.sum_le_sum fun i _ => this i).trans ?_
    rw [← Finset.sum_filter, ← Finset.sum_div]
    calc _ ≤ (K * d) / L ^ 2 := div_le_div_of_nonneg_right hsum hL2.le
      _ = 2 * Real.log 2 := by rw [← hLsq]; field_simp
  have hcube : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      (fun i => L * y i) + σ • v ∈ cube L := by
    intro σ hσ i
    have h := (key i)
    have : ((fun i => L * y i) + σ • v) i = L * (y i + σ * (v i / L)) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; field_simp
    rw [this, mul_mem_Ioo_iff L _ hL]
    rcases hσ with rfl | rfl
    · simpa using h.1
    · simpa [sub_eq_add_neg] using h.2.1
  have hplus : (fun i => L * y i) + v ∈ cube L := by simpa using hcube 1 (Or.inl rfl)
  have hminus : (fun i => L * y i) - v ∈ cube L := by
    simpa [sub_eq_add_neg] using hcube (-1) (Or.inr rfl)
  exact OnlineBeckFiala.lemma_2_5 (u η) L (integrableOn_exp_neg_u η) _ v hplus hminus hD

end Dev.T11
end OnlineBeckFiala
end

section
open MeasureTheory Set

namespace OnlineBeckFiala
namespace Dev.T11

theorem bad_prob (η M K c1 C1 c2 C2 : ℝ) (hM : 1 ≤ M) (hK : 1 ≤ K)
    (h15 : ∀ x : ℝ, 1 ≤ x →
        rho1 η {y | x < W η M y} ≤
          ENNReal.ofReal (C1 * Real.exp (-(c1 * x) / (Real.log (Real.exp 1 * x)) ^ (2 + η))))
    (h16 : ∀ y ∈ Ioo (-1 : ℝ) 1, ∀ s : ℝ, s ^ 2 * W η M y ≤ 1 →
        y + s ∈ Ioo (-1 : ℝ) 1 ∧ y - s ∈ Ioo (-1 : ℝ) 1 ∧
        u η (y + s) + u η (y - s) - 2 * u η y ≤ s ^ 2 * W η M y)
    (h17 : ∀ d : ℝ, 2 ≤ d → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ d →
        (Measure.pi (fun _ : Fin r => rho1 η)) {y | K * d < ∑ i, W η M (y i)} ≤
          ENNReal.ofReal (C2 * Real.exp (-(c2 * d) / (Real.log (Real.exp 1 * d)) ^ (2 + η))))
    {n : ℕ} (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 0 < L) (hLsq : L ^ 2 * (2 * Real.log 2) = K * d)
    (v : Fin n → ℝ) (hv : ∀ i, |v i| ≤ 1)
    (hcard : (Finset.univ.filter (fun i => v i ≠ 0)).card ≤ d) :
    densityLaw (uDensity (u η) L : (Fin n → ℝ) → ℝ)
        {x | ¬ IsBalanced L (uDensity (u η) L) v x} ≤
      (d : ENNReal) * ENNReal.ofReal (C1 * Real.exp (-(c1 * L ^ 2) /
          (Real.log (Real.exp 1 * L ^ 2)) ^ (2 + η))) +
        ENNReal.ofReal (C2 * Real.exp (-(c2 * d) / (Real.log (Real.exp 1 * d)) ^ (2 + η))) := by
  haveI := rho1_prob η
  set S := Finset.univ.filter (fun i => v i ≠ 0) with hS
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hL1 : 1 ≤ L ^ 2 := by
    have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  let Φ : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrRight (fun _ => MeasurableEquiv.mulLeft₀ L hL.ne')
  have hΦ : ∀ y i, Φ y i = L * y i := fun y i => rfl
  rw [densityLaw_uDensity η n L hL]
  have hmap : (Measure.pi (fun _ : Fin n => rho1 η)).map (fun y i => L * y i) =
      (Measure.pi (fun _ : Fin n => rho1 η)).map Φ := rfl
  rw [hmap, Φ.map_apply]
  set E1 : Set (Fin n → ℝ) := ⋃ i ∈ S, {y | L ^ 2 < W η M (y i)}
  set E2 : Set (Fin n → ℝ) := {y | K * d < ∑ i ∈ S, W η M (y i)}
  set E3 : Set (Fin n → ℝ) := ⋃ i, {y | y i ∈ (Ioo (-1 : ℝ) 1)ᶜ}
  have hsub : Φ ⁻¹' {x | ¬ IsBalanced L (uDensity (u η) L) v x} ⊆ (E1 ∪ E2) ∪ E3 := by
    intro y hy
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨⟨h1, h2⟩, h3⟩ := hnot
    apply hy
    have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := by
      intro i; by_contra hi; exact h3 (mem_iUnion.mpr ⟨i, hi⟩)
    have := balanced_of_good η M K hM h16 d L hL hLsq v hv y hy'
      (fun i hi => by
        by_contra hlt; push_neg at hlt
        exact h1 (mem_iUnion₂.mpr ⟨i, by simp [hS, hi], hlt⟩))
      (by simpa [E2] using h2)
    exact this
  set Q := Measure.pi (fun _ : Fin n => rho1 η) with hQ
  have hE3 : Q E3 = 0 := by
    refine measure_iUnion_null fun i => ?_
    have := (measurePreserving_eval (fun _ : Fin n => rho1 η) i).measure_preimage
      (s := (Ioo (-1 : ℝ) 1)ᶜ) measurableSet_Ioo.compl.nullMeasurableSet
    exact this.trans (rho1_compl η)
  have hE1 : Q E1 ≤ (d : ENNReal) * ENNReal.ofReal (C1 * Real.exp (-(c1 * L ^ 2) /
          (Real.log (Real.exp 1 * L ^ 2)) ^ (2 + η))) := by
    refine (measure_biUnion_finset_le S _).trans ?_
    have hb : ∀ i ∈ S, Q {y | L ^ 2 < W η M (y i)} ≤ ENNReal.ofReal (C1 * Real.exp (-(c1 * L ^ 2) /
          (Real.log (Real.exp 1 * L ^ 2)) ^ (2 + η))) := by
      intro i _
      have := (measurePreserving_eval (fun _ : Fin n => rho1 η) i).measure_preimage
        (s := {w | L ^ 2 < W η M w})
        (measurableSet_lt measurable_const (W_meas η M)).nullMeasurableSet
      exact (le_of_eq this).trans (h15 _ hL1)
    refine (Finset.sum_le_card_nsmul S _ _ hb).trans ?_
    rw [nsmul_eq_mul]
    exact mul_le_mul' (by exact_mod_cast hcard) le_rfl
  have hE2 : Q E2 ≤ ENNReal.ofReal (C2 * Real.exp (-(c2 * d) / (Real.log (Real.exp 1 * d)) ^ (2 + η))) := by
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · have : E2 = ∅ := by
        rw [Finset.card_eq_zero] at h0
        ext y
        simp only [E2, h0, Finset.sum_empty, mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
        positivity
      rw [this]; simp
    · set r := S.card with hr
      let eqv : Fin r ≃ S := (finCongr hr).trans S.equivFin.symm
      let e : Fin r → Fin n := fun j => (eqv j : Fin n)
      have he : Function.Injective e := Subtype.val_injective.comp eqv.injective
      have hrestr := restr_pi (rho1 η) n r e he
      have hmeasR : Measurable (fun (y : Fin n → ℝ) (j : Fin r) => y (e j)) :=
        measurable_pi_lambda _ fun j => measurable_pi_apply _
      set F : Set (Fin r → ℝ) := {z | K * d < ∑ j, W η M (z j)} with hF
      have hFm : MeasurableSet F := measurableSet_lt measurable_const
        (Finset.measurable_sum _ fun j _ => (W_meas η M).comp (measurable_pi_apply j))
      have hEq : E2 = (fun (y : Fin n → ℝ) (j : Fin r) => y (e j)) ⁻¹' F := by
        ext y
        have : ∑ j : Fin r, W η M (y (e j)) = ∑ i ∈ S, W η M (y i) := by
          rw [← Finset.sum_coe_sort S (fun i => W η M (y i))]
          exact Equiv.sum_comp eqv (fun i : S => W η M (y i))
        simp only [E2, F, mem_setOf_eq, mem_preimage, this]
      rw [hEq, ← Measure.map_apply hmeasR hFm, hrestr]
      exact h17 d hdR r hpos (by exact_mod_cast hcard)
  refine ((measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add (measure_union_le _ _) le_rfl))).trans ?_
  rw [hE3, add_zero]
  exact add_le_add hE1 hE2

end Dev.T11
end OnlineBeckFiala
end

section
open Set

namespace OnlineBeckFiala
namespace Dev.T11

theorem log_e_mul (d : ℝ) (hd : 0 < d) : Real.log (Real.exp 1 * d) = 1 + Real.log d := by
  rw [Real.log_mul (Real.exp_pos 1).ne' hd.ne', Real.log_exp]

theorem ratio_mono (p : ℝ) (hp : 0 ≤ p) (d0 d : ℝ) (hd0 : 1 ≤ d0) (hdd : d0 ≤ d)
    (ht : p ≤ Real.log (Real.exp 1 * d0)) :
    d0 / (Real.log (Real.exp 1 * d0)) ^ p ≤ d / (Real.log (Real.exp 1 * d)) ^ p := by
  have hd0' : 0 < d0 := by linarith
  have hd' : 0 < d := by linarith
  have hlog0 : 0 ≤ Real.log d0 := Real.log_nonneg hd0
  set t0 := Real.log (Real.exp 1 * d0) with ht0
  have ht0e : t0 = 1 + Real.log d0 := log_e_mul d0 hd0'
  have ht0pos : 0 < t0 := by linarith
  set r := d / d0 with hr
  have hr1 : 1 ≤ r := (one_le_div hd0').mpr hdd
  have hlr : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hlogd : Real.log (Real.exp 1 * d) = t0 * (1 + Real.log r / t0) := by
    rw [log_e_mul d hd', ht0e, hr, Real.log_div hd'.ne' hd0'.ne']
    field_simp
    rw [← ht0e]; ring_nf; rw [ht0e]; ring
  have hz : (1 + Real.log r / t0) ^ p ≤ r := by
    calc (1 + Real.log r / t0) ^ p ≤ (Real.exp (Real.log r / t0)) ^ p :=
          Real.rpow_le_rpow (by positivity) (by linarith [Real.add_one_le_exp (Real.log r / t0)]) hp
      _ = Real.exp (p * (Real.log r / t0)) := by rw [← Real.exp_mul]; ring_nf
      _ ≤ Real.exp (Real.log r) := by
          apply Real.exp_le_exp.mpr
          have : p * (Real.log r / t0) = (p / t0) * Real.log r := by ring
          rw [this]
          have : p / t0 ≤ 1 := by rw [div_le_one ht0pos]; exact ht
          nlinarith
      _ = r := Real.exp_log (by linarith)
  have hp0 : 0 < t0 ^ p := Real.rpow_pos_of_pos ht0pos p
  have hpd : 0 < (Real.log (Real.exp 1 * d)) ^ p := by
    rw [hlogd]; exact Real.rpow_pos_of_pos (by positivity) p
  rw [div_le_div_iff₀ (by positivity) hpd, hlogd, Real.mul_rpow ht0pos.le (by positivity)]
  have hdr : d = d0 * r := by rw [hr]; field_simp
  calc d0 * (t0 ^ p * (1 + Real.log r / t0) ^ p) ≤ d0 * (t0 ^ p * r) := by gcongr
    _ = d * t0 ^ p := by rw [hdr]; ring

theorem d_exp_le (p a : ℝ) (hp : 0 ≤ p) (ha : 0 < a) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ d : ℝ, 2 ≤ d →
      d * Real.exp (-(a * d) / (Real.log (Real.exp 1 * d)) ^ p) ≤ B := by
  set N := p + 1 with hN
  have hN1 : 1 ≤ N := by linarith
  set c0 := (2 * N) ^ N * Real.sqrt (Real.exp 1) / a with hc0
  have hc0pos : 0 < c0 := by positivity
  refine ⟨max 1 (max 2 (c0 ^ 2)), le_max_left _ _, fun d hd => ?_⟩
  have hdpos : 0 < d := by linarith
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  have hlpos : 0 < Real.log (Real.exp 1 * d) := by rw [log_e_mul d hdpos]; linarith
  have hl1 : 1 ≤ Real.log (Real.exp 1 * d) := by rw [log_e_mul d hdpos]; linarith
  have hlp : 0 < (Real.log (Real.exp 1 * d)) ^ p := Real.rpow_pos_of_pos hlpos p
  by_cases hbig : c0 ^ 2 ≤ d
  · -- d large: exponent ≥ log d
    have hsq : c0 ≤ Real.sqrt d := Real.le_sqrt_of_sq_le hbig
    set t := Real.log (Real.exp 1 * d) with ht
    have h1 : t ≤ (Real.exp 1 * d) ^ (1 / (2 * N)) / (1 / (2 * N)) :=
      Real.log_le_rpow_div (by positivity) (by positivity)
    have h2 : t ^ N ≤ (2 * N) ^ N * Real.sqrt (Real.exp 1 * d) := by
      calc t ^ N ≤ ((Real.exp 1 * d) ^ (1 / (2 * N)) / (1 / (2 * N))) ^ N :=
            Real.rpow_le_rpow hlpos.le h1 (by linarith)
        _ = (2 * N) ^ N * ((Real.exp 1 * d) ^ (1 / (2 * N))) ^ N := by
            have hinv : (1 / (2 * N)) ^ N = ((2 * N) ^ N)⁻¹ := by
              rw [one_div, Real.inv_rpow (by positivity)]
            rw [Real.div_rpow (by positivity) (by positivity), hinv, div_inv_eq_mul, mul_comm]
        _ = _ := by
            rw [← Real.rpow_mul (by positivity)]
            have : 1 / (2 * N) * N = 1 / 2 := by field_simp
            rw [this, Real.sqrt_eq_rpow]
    have h3 : t ^ N ≤ a * d := by
      have e1 : (2 * N) ^ N * Real.sqrt (Real.exp 1 * d) =
          ((2 * N) ^ N * Real.sqrt (Real.exp 1)) * Real.sqrt d := by
        rw [Real.sqrt_mul (Real.exp_pos 1).le]; ring
      have e2 : (2 * N) ^ N * Real.sqrt (Real.exp 1) ≤ a * Real.sqrt d := by
        have := (div_le_iff₀ ha).mp hsq
        linarith
      calc t ^ N ≤ _ := h2
        _ = _ := e1
        _ ≤ (a * Real.sqrt d) * Real.sqrt d := by gcongr
        _ = a * d := by rw [mul_assoc, Real.mul_self_sqrt hdpos.le]
    have h4 : t ^ N = t ^ p * t := by
      rw [hN, Real.rpow_add hlpos, Real.rpow_one]
    have h5 : t ≤ a * d / t ^ p := by
      rw [le_div_iff₀ hlp]; nlinarith
    have h6 : Real.exp (-(a * d) / t ^ p) ≤ d⁻¹ := by
      have : d⁻¹ = Real.exp (-Real.log d) := by rw [Real.exp_neg, Real.exp_log hdpos]
      rw [this]
      apply Real.exp_le_exp.mpr
      have h7 : t = 1 + Real.log d := log_e_mul d hdpos
      rw [neg_div]; linarith
    calc d * Real.exp (-(a * d) / t ^ p) ≤ d * d⁻¹ := by gcongr
      _ = 1 := by field_simp
      _ ≤ _ := le_max_left _ _
  · push Not at hbig
    have hexp : Real.exp (-(a * d) / (Real.log (Real.exp 1 * d)) ^ p) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ a * d / (Real.log (Real.exp 1 * d)) ^ p := by positivity
      rw [neg_div]; linarith
    calc d * Real.exp (-(a * d) / (Real.log (Real.exp 1 * d)) ^ p) ≤ d * 1 := by gcongr
      _ = d := mul_one d
      _ ≤ c0 ^ 2 := hbig.le
      _ ≤ _ := (le_max_right _ _).trans' (le_max_right _ _)

theorem theta_bound (p K c1 C1 c2 C2 : ℝ) (hp : 0 ≤ p) (hK : 1 ≤ K) (hc1 : 0 < c1) (hC1 : 0 < C1)
    (hc2 : 0 < c2) (hC2 : 0 < C2) :
    ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧ ∀ d : ℕ, 2 ≤ d → ∀ L : ℝ, 0 < L →
      L ^ 2 * (2 * Real.log 2) = K * d →
      (d : ℝ) * (C1 * Real.exp (-(c1 * L ^ 2) / (Real.log (Real.exp 1 * L ^ 2)) ^ p)) +
        C2 * Real.exp (-(c2 * d) / (Real.log (Real.exp 1 * d)) ^ p) ≤
        C' * Real.exp (-(c' * d) / (Real.log (Real.exp 1 * d)) ^ p) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  set κ := K / (2 * Real.log 2) with hκ
  have hκpos : 0 < κ := by positivity
  set m := 1 + |Real.log κ| with hm
  have hm1 : 1 ≤ m := by have := abs_nonneg (Real.log κ); linarith
  have hmp : 0 < m ^ p := Real.rpow_pos_of_pos (by linarith) p
  set c3 := c1 * κ / m ^ p with hc3
  have hc3pos : 0 < c3 := by positivity
  obtain ⟨B, hB1, hB⟩ := d_exp_le p (c3 / 2) hp (by positivity)
  refine ⟨min (c3 / 2) c2, C1 * B + C2, lt_min (by positivity) hc2, by positivity, ?_⟩
  intro d hd L hL hLsq
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hL2 : L ^ 2 = κ * d := by
    rw [hκ]; field_simp; linarith
  have hκ12 : 1 ≤ κ * d := by
    have : 1 / 2 < κ := by
      rw [hκ, lt_div_iff₀ (by positivity)]; nlinarith
    nlinarith
  have hl : 0 < Real.log (Real.exp 1 * d) := by rw [log_e_mul d hdpos]; have := Real.log_nonneg (show (1:ℝ) ≤ d by linarith); linarith
  have hl1 : 1 ≤ Real.log (Real.exp 1 * d) := by rw [log_e_mul d hdpos]; have := Real.log_nonneg (show (1:ℝ) ≤ d by linarith); linarith
  have hlp : 0 < (Real.log (Real.exp 1 * d)) ^ p := Real.rpow_pos_of_pos hl p
  have hX : Real.log (Real.exp 1 * L ^ 2) = 1 + Real.log κ + Real.log d := by
    rw [log_e_mul _ (by positivity), hL2, Real.log_mul hκpos.ne' hdpos.ne']; ring
  have hXpos : 0 < Real.log (Real.exp 1 * L ^ 2) := by
    rw [log_e_mul _ (by positivity)]
    have := Real.log_nonneg (show (1:ℝ) ≤ L ^ 2 by rw [hL2]; exact hκ12)
    linarith
  have hXle : Real.log (Real.exp 1 * L ^ 2) ≤ m * Real.log (Real.exp 1 * d) := by
    rw [hX, log_e_mul d hdpos, hm]
    have h1 := le_abs_self (Real.log κ)
    have h2 := Real.log_nonneg (show (1:ℝ) ≤ d by linarith)
    have h3 := abs_nonneg (Real.log κ)
    nlinarith
  have hXp : (Real.log (Real.exp 1 * L ^ 2)) ^ p ≤ m ^ p * (Real.log (Real.exp 1 * d)) ^ p := by
    rw [← Real.mul_rpow (by linarith) hl.le]
    exact Real.rpow_le_rpow hXpos.le hXle hp
  have hXp0 : 0 < (Real.log (Real.exp 1 * L ^ 2)) ^ p := Real.rpow_pos_of_pos hXpos p
  set ℓ := (Real.log (Real.exp 1 * d)) ^ p with hℓ
  have hfrac : c3 * d / ℓ ≤ c1 * L ^ 2 / (Real.log (Real.exp 1 * L ^ 2)) ^ p := by
    have : c3 * d / ℓ = c1 * L ^ 2 / (m ^ p * ℓ) := by
      rw [hc3, hL2]; field_simp
    rw [this]
    exact div_le_div_of_nonneg_left (by positivity) hXp0 hXp
  have hterm1 : Real.exp (-(c1 * L ^ 2) / (Real.log (Real.exp 1 * L ^ 2)) ^ p) ≤
      Real.exp (-(c3 / 2 * d) / ℓ) * Real.exp (-(c3 / 2 * d) / ℓ) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : -(c3 / 2 * d) / ℓ + -(c3 / 2 * d) / ℓ = -(c3 * d / ℓ) := by ring
    rw [this, neg_div]
    linarith
  have hnn : 0 ≤ (d : ℝ) / ℓ := by positivity
  have hmono : ∀ a : ℝ, a ≤ c3 / 2 → Real.exp (-(c3 / 2 * d) / ℓ) ≤ Real.exp (-(a * d) / ℓ) := by
    intro a ha
    apply Real.exp_le_exp.mpr
    have : -(a * d) / ℓ = -(a * (d / ℓ)) := by ring
    have h2 : -(c3 / 2 * d) / ℓ = -(c3 / 2 * (d / ℓ)) := by ring
    rw [this, h2]
    nlinarith
  have hmono2 : ∀ a : ℝ, a ≤ c2 → Real.exp (-(c2 * d) / ℓ) ≤ Real.exp (-(a * d) / ℓ) := by
    intro a ha
    apply Real.exp_le_exp.mpr
    have : -(a * d) / ℓ = -(a * (d / ℓ)) := by ring
    have h2 : -(c2 * d) / ℓ = -(c2 * (d / ℓ)) := by ring
    rw [this, h2]
    nlinarith
  have hBd := hB d hdR
  set E := Real.exp (-(c3 / 2 * d) / ℓ) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hEm := hmono (min (c3 / 2) c2) (min_le_left _ _)
  have hEm2 := hmono2 (min (c3 / 2) c2) (min_le_right _ _)
  have hB' : (d : ℝ) * E ≤ B := by simpa [hE, hℓ, neg_div] using hBd
  have hfin : (d : ℝ) * (C1 * Real.exp (-(c1 * L ^ 2) / (Real.log (Real.exp 1 * L ^ 2)) ^ p)) ≤
      C1 * B * E := by
    calc _ ≤ (d : ℝ) * (C1 * (E * E)) := by gcongr
      _ = C1 * ((d : ℝ) * E) * E := by ring
      _ ≤ C1 * B * E := by gcongr
  calc _ ≤ C1 * B * E + C2 * Real.exp (-(c2 * d) / ℓ) := by gcongr
    _ ≤ C1 * B * Real.exp (-(min (c3 / 2) c2 * d) / ℓ) + C2 * Real.exp (-(min (c3 / 2) c2 * d) / ℓ) := by gcongr
    _ = _ := by ring

theorem clause2_arith (p : ℝ) (hp : 0 < p) (c' Cθ : ℝ) (hc : 0 < c') (hC : 0 < Cθ) :
    ∃ C3 T0 : ℝ, 0 < C3 ∧ 0 < T0 ∧ ∀ T : ℕ, T0 ≤ T → ∀ d : ℕ,
      C3 * Real.log T * (Real.log (Real.log T)) ^ p ≤ d →
      3 * (T : ℝ) * (Cθ * Real.exp (-(c' * d) / (Real.log (Real.exp 1 * d)) ^ p)) ≤ 1 / (T : ℝ) := by
  have h3p : 0 < (3 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  set C3 := max 1 (3 * 3 ^ p / c') with hC3
  have hC31 : 1 ≤ C3 := le_max_left _ _
  have hC3c : 3 * 3 ^ p ≤ c' * C3 := by
    have : 3 * 3 ^ p / c' ≤ C3 := le_max_right _ _
    rw [div_le_iff₀ hc] at this; linarith
  set μ0 := 1 + |Real.log C3| + p * |Real.log (2 * p)| + p with hμ0
  have hμ0p : p ≤ μ0 := by
    have := abs_nonneg (Real.log C3); have : 0 ≤ p * |Real.log (2 * p)| := by positivity
    linarith
  have hμ01 : 1 ≤ μ0 := by
    have := abs_nonneg (Real.log C3); have : 0 ≤ p * |Real.log (2 * p)| := by positivity
    linarith
  refine ⟨C3, max (Real.exp (Real.exp μ0)) (3 * Cθ), by linarith, lt_max_of_lt_right (by positivity), ?_⟩
  intro T hT d hd
  have hT1 : Real.exp (Real.exp μ0) ≤ T := (le_max_left _ _).trans hT
  have hT2 : 3 * Cθ ≤ T := (le_max_right _ _).trans hT
  have hTpos : 0 < (T : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hT1
  set lam := Real.log T with hlam
  have hlam1 : Real.exp μ0 ≤ lam := (Real.le_log_iff_exp_le hTpos).mpr hT1
  have hexp : μ0 + 1 ≤ Real.exp μ0 := by linarith [Real.add_one_le_exp μ0]
  have hlampos : 0 < lam := by linarith
  have hlam2 : 1 ≤ lam := by linarith
  set μ := Real.log lam with hμ
  have hμ1 : μ0 ≤ μ := (Real.le_log_iff_exp_le hlampos).mpr hlam1
  have hμpos : 0 < μ := by linarith
  have hμp1 : 1 ≤ μ ^ p := Real.one_le_rpow (by linarith) hp.le
  set d0 := C3 * lam * μ ^ p with hd0
  have hd01 : 1 ≤ d0 := by
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC31 hlam2) hμp1
  have hd0pos : 0 < d0 := by linarith
  have hlogd0 : Real.log d0 = Real.log C3 + μ + p * Real.log μ := by
    rw [hd0, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hμpos]
  have hlogμ : 0 ≤ Real.log μ := Real.log_nonneg (by linarith)
  have hlogC : 0 ≤ Real.log C3 := Real.log_nonneg hC31
  have ht0 : Real.log (Real.exp 1 * d0) = 1 + Real.log C3 + μ + p * Real.log μ := by
    rw [log_e_mul d0 hd0pos, hlogd0]; ring
  have hlogle : Real.log μ ≤ Real.log (2 * p) + μ / (2 * p) - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < μ / (2 * p) by positivity)
    rw [Real.log_div hμpos.ne' (by positivity)] at h
    linarith
  have ht0le : Real.log (Real.exp 1 * d0) ≤ 3 * μ := by
    rw [ht0]
    have h1 : p * Real.log μ ≤ p * (Real.log (2 * p) + μ / (2 * p) - 1) :=
      mul_le_mul_of_nonneg_left hlogle hp.le
    have h2 : p * (μ / (2 * p)) = μ / 2 := by field_simp
    have h3 := le_abs_self (Real.log C3)
    have h4 := le_abs_self (Real.log (2 * p))
    have h5 : p * Real.log (2 * p) ≤ p * |Real.log (2 * p)| :=
      mul_le_mul_of_nonneg_left h4 hp.le
    have h6 : p * (Real.log (2 * p) + μ / (2 * p) - 1) = p * Real.log (2 * p) + μ / 2 - p := by
      rw [mul_sub, mul_add, h2]; ring
    linarith
  have ht0ge : p ≤ Real.log (Real.exp 1 * d0) := by
    rw [ht0]; have : 0 ≤ p * Real.log μ := by positivity
    linarith
  have hdd0 : d0 ≤ d := by
    have : C3 * lam * μ ^ p = C3 * Real.log T * (Real.log (Real.log T)) ^ p := by rw [hlam, hμ, hlam]
    rw [hd0, this]; exact hd
  have hmono := ratio_mono p hp.le d0 d hd01 hdd0 ht0ge
  have hℓ0 : (Real.log (Real.exp 1 * d0)) ^ p ≤ 3 ^ p * μ ^ p := by
    rw [← Real.mul_rpow (by norm_num) hμpos.le]
    exact Real.rpow_le_rpow (by linarith) ht0le hp.le
  have hℓ0pos : 0 < (Real.log (Real.exp 1 * d0)) ^ p := Real.rpow_pos_of_pos (by linarith) p
  have hlow : C3 * lam / 3 ^ p ≤ d0 / (Real.log (Real.exp 1 * d0)) ^ p := by
    have : C3 * lam / 3 ^ p = d0 / (3 ^ p * μ ^ p) := by
      rw [hd0]; field_simp
    rw [this]
    exact div_le_div_of_nonneg_left hd0pos.le hℓ0pos hℓ0
  have hdpos : (0 : ℝ) < d := by linarith
  have hℓpos : 0 < (Real.log (Real.exp 1 * d)) ^ p := by
    rw [log_e_mul d hdpos]
    exact Real.rpow_pos_of_pos (by have := Real.log_nonneg (show (1:ℝ) ≤ d by linarith); linarith) p
  have hkey : 3 * lam ≤ c' * d / (Real.log (Real.exp 1 * d)) ^ p := by
    have h1 : c' * (C3 * lam / 3 ^ p) ≤ c' * (d / (Real.log (Real.exp 1 * d)) ^ p) :=
      mul_le_mul_of_nonneg_left (hlow.trans hmono) hc.le
    have h2 : 3 * lam ≤ c' * (C3 * lam / 3 ^ p) := by
      rw [← mul_div_assoc, le_div_iff₀ h3p]
      have := mul_le_mul_of_nonneg_right hC3c hlampos.le
      linarith
    calc 3 * lam ≤ _ := h2
      _ ≤ _ := h1
      _ = _ := by ring
  have hexp1 : Real.exp (-(c' * d) / (Real.log (Real.exp 1 * d)) ^ p) ≤ (T : ℝ)⁻¹ ^ 3 := by
    have : (T : ℝ)⁻¹ ^ 3 = Real.exp (-(3 * lam)) := by
      rw [hlam, Real.exp_neg, show 3 * Real.log T = ((3 : ℕ) : ℝ) * Real.log T by norm_num,
        Real.exp_nat_mul, Real.exp_log hTpos, inv_pow]
    rw [this]
    apply Real.exp_le_exp.mpr
    rw [neg_div]; linarith
  calc 3 * (T : ℝ) * (Cθ * Real.exp (-(c' * d) / (Real.log (Real.exp 1 * d)) ^ p))
      ≤ 3 * (T : ℝ) * (Cθ * (T : ℝ)⁻¹ ^ 3) := by gcongr
    _ = 3 * Cθ / (T : ℝ) ^ 2 := by field_simp
    _ ≤ 1 / (T : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hTpos, one_mul, sq]
      exact mul_le_mul_of_nonneg_right hT2 hTpos.le

end Dev.T11
end OnlineBeckFiala
end

section
open MeasureTheory

/-
PLAN (reduction to Proposition 2.7).  Fix η.  Lemma 3.1 gives M, c1, C1 (tail (15) and curvature (16));
Lemma 4.1 (with that M) gives K, C2, c2.  Put κ = K/(2 log 2) and L = √(κ d), so L²·2 log 2 = K d.
T11a-T11c: the density µ = uDensity (u η) L is measurable, positive on the cube, zero off it, has
  integral 1, and densityLaw µ is the image of Measure.pi (rho1 η) under y ↦ L•y (change of variables
  on ℝ, `pi_withDensity`); the restriction of the product law to r coordinates is the r-fold product.
T11d: if every y_i ∈ (-1,1), W(y_i) ≤ L² on supp v and ∑_{supp v} W(y_i) ≤ K d, then x = L y is
  v-balanced (Lemma 3.1 (16) with s_i = v_i/L, summing, then Lemma 2.5).
T11e: hence P_µ{not v-balanced} ≤ d·C1 exp(-c1 L²/log^p(e L²)) + C2 exp(-c2 d/log^p(e d)) (union
  bound, (15), (17) via the r-coordinate marginal).
T11f: this is ≤ C' exp(-c' d/ℓ(d)) (absorbing the factor d), and the arithmetic of the second clause
  (monotonicity of d/ℓ(d), explicit C3 and T0).
Here: Prop. 2.7 with V = {sparse box vectors} gives the algorithm with P{max prefix > 6L} ≤ 3Tθ;
  6L = 6√κ √d, and both clauses follow.
-/

namespace OnlineBeckFiala

theorem chk_theorem_1_1 :
    ∀ η : ℝ, 0 < η → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ C₃ C' T₀ : ℝ, 0 < C₃ ∧ 0 < C' ∧ 0 < T₀ ∧
      ∀ (n d : ℕ), 2 ≤ d → ∃ alg : OnlineSigner n,
        (∀ (T : ℕ) (a : ℕ → (Fin n → ℝ)), IsSparseBox d T a →
          alg.P {ω | ∃ t < T, C * Real.sqrt d < ‖prefixSum alg a t ω‖} ≤
            ENNReal.ofReal
              (C * T * Real.exp (-(c * d) / (Real.log (Real.exp 1 * d)) ^ (2 + η)))) ∧
        (∀ T : ℕ, T₀ ≤ T → C₃ * Real.log T * (Real.log (Real.log T)) ^ (2 + η) ≤ d →
          ∀ a : ℕ → (Fin n → ℝ), IsSparseBox d T a →
            1 - (T : ENNReal)⁻¹ ≤ alg.P {ω | ∀ t < T, ‖prefixSum alg a t ω‖ ≤ C' * Real.sqrt d}) := by
  intro η hη
  obtain ⟨M, hM, c1, C1, hc1, hC1, h15, h16⟩ := lemma_3_1 η hη
  obtain ⟨K, hK, C2, c2, hC2, hc2, h17⟩ := lemma_4_1 η hη M hM
  obtain ⟨c', Cθ, hc', hCθ, hθ⟩ := Dev.T11.theta_bound (2 + η) K c1 C1 c2 C2 (by linarith) hK hc1 hC1
    hc2 hC2
  obtain ⟨C3, T0, hC3, hT0, hcl2⟩ := Dev.T11.clause2_arith (2 + η) (by linarith) c' Cθ hc' hCθ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set κ := K / (2 * Real.log 2) with hκ
  have hκpos : 0 < κ := by positivity
  set C0 := 6 * Real.sqrt κ with hC0
  have hC0pos : 0 < C0 := by positivity
  refine ⟨c', max C0 (3 * Cθ), hc', lt_max_of_lt_left hC0pos, C3, C0, T0, hC3, hC0pos, hT0, ?_⟩
  intro n d hd
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  set L := Real.sqrt (κ * d) with hL
  have hLpos : 0 < L := Real.sqrt_pos.mpr (by positivity)
  have hL2 : L ^ 2 = κ * d := Real.sq_sqrt (by positivity)
  have hLsq : L ^ 2 * (2 * Real.log 2) = K * d := by
    rw [hL2, hκ]; field_simp
  have h6L : 6 * L = C0 * Real.sqrt d := by
    rw [hL, Real.sqrt_mul hκpos.le, hC0]; ring
  set ℓ := (Real.log (Real.exp 1 * d)) ^ (2 + η) with hℓ
  set V : Set (Fin n → ℝ) :=
    {v | (∀ i, |v i| ≤ 1) ∧ (Finset.univ.filter (fun i => v i ≠ 0)).card ≤ d} with hV
  have h8 : ∀ v ∈ V, densityLaw (uDensity (u η) L : (Fin n → ℝ) → ℝ)
      {x | ¬ IsBalanced L (uDensity (u η) L) v x} ≤
        ENNReal.ofReal (Cθ * Real.exp (-(c' * d) / ℓ)) := by
    intro v hv
    refine (Dev.T11.bad_prob η M K c1 C1 c2 C2 hM hK h15 h16 h17 d hd L hLpos hLsq v hv.1 hv.2).trans ?_
    have hA : 0 ≤ C1 * Real.exp (-(c1 * L ^ 2) / (Real.log (Real.exp 1 * L ^ 2)) ^ (2 + η)) := by
      positivity
    have hB : 0 ≤ C2 * Real.exp (-(c2 * d) / ℓ) := by positivity
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add
      (by positivity) hB]
    exact ENNReal.ofReal_le_ofReal (hθ d hd L hLpos hLsq)
  obtain ⟨alg, halg⟩ := proposition_2_7 V L hLpos (uDensity (u η) L) (Dev.T11.uDensity_meas η n L)
    (Dev.T11.uDensity_pos η n L hLpos) (Dev.T11.uDensity_zero η n L)
    (Dev.T11.uDensity_int η n L hLpos) _ h8
  refine ⟨alg, ?_, ?_⟩
  · intro T a ha
    have h := halg T a (fun t ht => ⟨(ha t ht).1, (ha t ht).2⟩)
    refine (measure_mono ?_).trans (h.trans ?_)
    · intro ω ⟨t, ht, hlt⟩
      refine ⟨t, ht, ?_⟩
      rw [h6L]
      exact lt_of_le_of_lt (by gcongr; exact le_max_left _ _) hlt
    · rw [(ENNReal.ofReal_ofNat 3).symm, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have : 0 ≤ (T : ℝ) * Real.exp (-(c' * d) / ℓ) := by positivity
      calc 3 * (T : ℝ) * (Cθ * Real.exp (-(c' * d) / ℓ)) = (3 * Cθ) * ((T : ℝ) * Real.exp (-(c' * d) / ℓ)) := by ring
        _ ≤ max C0 (3 * Cθ) * ((T : ℝ) * Real.exp (-(c' * d) / ℓ)) := by
            gcongr; exact le_max_right _ _
        _ = _ := by ring
  · intro T hT hdT a ha
    have h := halg T a (fun t ht => ⟨(ha t ht).1, (ha t ht).2⟩)
    have hTpos : (0 : ℝ) < T := lt_of_lt_of_le hT0 hT
    have hbound : alg.P {ω | ∃ k < T, 6 * L < ‖prefixSum alg a k ω‖} ≤ (T : ENNReal)⁻¹ := by
      refine h.trans ?_
      rw [(ENNReal.ofReal_ofNat 3).symm, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      have h2 := hcl2 T hT d hdT
      calc _ ≤ ENNReal.ofReal (1 / (T : ℝ)) := ENNReal.ofReal_le_ofReal h2
        _ = _ := by
          rw [one_div, ENNReal.ofReal_inv_of_pos hTpos]
    have hcov : (Set.univ : Set alg.Ω) ⊆
        {ω | ∀ t < T, ‖prefixSum alg a t ω‖ ≤ C0 * Real.sqrt d} ∪
          {ω | ∃ k < T, 6 * L < ‖prefixSum alg a k ω‖} := by
      intro ω _
      by_cases hω : ∃ k < T, 6 * L < ‖prefixSum alg a k ω‖
      · exact Or.inr hω
      · left
        intro t ht
        push Not at hω
        rw [← h6L]
        exact hω t ht
    have h1 : 1 ≤ alg.P {ω | ∀ t < T, ‖prefixSum alg a t ω‖ ≤ C0 * Real.sqrt d} +
        (T : ENNReal)⁻¹ := by
      calc (1 : ENNReal) = alg.P Set.univ := measure_univ.symm
        _ ≤ alg.P ({ω | ∀ t < T, ‖prefixSum alg a t ω‖ ≤ C0 * Real.sqrt d} ∪
          {ω | ∃ k < T, 6 * L < ‖prefixSum alg a k ω‖}) := measure_mono hcov
        _ ≤ _ := (measure_union_le _ _).trans (add_le_add le_rfl hbound)
    exact tsub_le_iff_right.mpr h1

end OnlineBeckFiala
end

theorem solution : type_of% @OnlineBeckFiala.chk_theorem_1_1 := @OnlineBeckFiala.chk_theorem_1_1
