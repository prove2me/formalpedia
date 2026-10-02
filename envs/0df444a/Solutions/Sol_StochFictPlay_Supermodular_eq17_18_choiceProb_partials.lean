-- Prove2me | solution 1 for StochFictPlay.Supermodular.eq17_18_choiceProb_partials
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T18:06:00.597349+00:00
-- url     : https://prove2.me/submissions/6c0f7bad-7f66-45a2-91b4-67f7f7922cfd

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace CexEdad0fc3

/-- CDF of the payoff-difference shock: `F x = 1/2 + arctan (x^3) / π`. Its derivative vanishes at 0. -/
noncomputable def F (x : ℝ) : ℝ := 1 / 2 + Real.arctan (x ^ 3) / Real.pi

/-- Density of the difference shock (the derivative of `F`). -/
noncomputable def g (x : ℝ) : ℝ := 1 / (1 + (x ^ 3) ^ 2) * (3 * x ^ 2) / Real.pi

/-- `g` patched at the single point `0` to be strictly positive everywhere. -/
noncomputable def gt (x : ℝ) : ℝ := if x = 0 then 1 else g x

lemma hasDerivAt_F (x : ℝ) : HasDerivAt F (g x) x := by
  have h := (((Real.hasDerivAt_arctan (x ^ 3)).comp x (hasDerivAt_pow 3 x)).div_const
    Real.pi).const_add (1 / 2)
  exact h.congr_deriv (by simp [g])

lemma g_nonneg (x : ℝ) : 0 ≤ g x := by
  unfold g; have := Real.pi_pos; positivity

lemma g_zero : g 0 = 0 := by simp [g]

lemma g_neg (x : ℝ) : g (-x) = g x := by
  unfold g; ring

lemma F_neg (x : ℝ) : F (-x) = 1 - F x := by
  unfold F
  rw [show (-x) ^ 3 = -(x ^ 3) by ring, Real.arctan_neg]
  ring

lemma F_nonneg (x : ℝ) : 0 ≤ F x := by
  unfold F
  have h1 := Real.neg_pi_div_two_lt_arctan (x ^ 3)
  have hp := Real.pi_pos
  have : -(1 / 2 : ℝ) < Real.arctan (x ^ 3) / Real.pi := by
    rw [lt_div_iff₀ hp]; linarith
  linarith

lemma one_sub_F_nonneg (x : ℝ) : 0 ≤ 1 - F x := by
  rw [← F_neg]; exact F_nonneg _

lemma gt_pos (x : ℝ) : 0 < gt x := by
  unfold gt
  split_ifs with h
  · exact one_pos
  · unfold g
    have := Real.pi_pos
    have : 0 < x ^ 2 := by positivity
    positivity

lemma measurable_g : Measurable g := by
  unfold g; fun_prop

lemma measurable_gt : Measurable gt := by
  unfold gt
  exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_g

lemma F_atTop : Tendsto F atTop (𝓝 1) := by
  have h1 : Tendsto (fun x : ℝ => x ^ 3) atTop atTop := tendsto_pow_atTop (by norm_num)
  have h2 := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1
  have h3 := (h2.div_const Real.pi).const_add (1 / 2)
  have hp := Real.pi_pos.ne'
  have e : (1 : ℝ) = 1 / 2 + Real.pi / 2 / Real.pi := by field_simp; ring
  rw [e]
  exact h3

lemma integrableOn_g_Ioi (x : ℝ) : IntegrableOn g (Ioi x) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun y _ => hasDerivAt_F y) (fun y _ => g_nonneg y) F_atTop

lemma integral_Ioi_g (x : ℝ) : ∫ u in Ioi x, g u = 1 - F x :=
  integral_Ioi_of_hasDerivAt_of_tendsto' (fun y _ => hasDerivAt_F y) (integrableOn_g_Ioi x) F_atTop

lemma lint_Ioi (x : ℝ) : ∫⁻ u in Ioi x, ENNReal.ofReal (g u) = ENNReal.ofReal (1 - F x) := by
  rw [← integral_Ioi_g, ofReal_integral_eq_lintegral_ofReal (integrableOn_g_Ioi x)
    (Eventually.of_forall (fun y => g_nonneg y))]

lemma lint_Iio (x : ℝ) : ∫⁻ u in Iio x, ENNReal.ofReal (g u) = ENNReal.ofReal (F x) := by
  have h := setLIntegral_map (μ := (volume : Measure ℝ)) (f := fun u => ENNReal.ofReal (g u))
    (g := fun u : ℝ => -u) (s := Iio x) measurableSet_Iio
    (ENNReal.measurable_ofReal.comp measurable_g) measurable_neg
  rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at h
  rw [h]
  have hpre : (fun u : ℝ => -u) ⁻¹' Iio x = Ioi (-x) := by
    ext u; simp
  rw [hpre]
  simp_rw [g_neg]
  rw [lint_Ioi, F_neg]
  congr 1; ring

lemma lint_univ : ∫⁻ u, ENNReal.ofReal (g u) = 1 := by
  rw [← lintegral_add_compl (fun u => ENNReal.ofReal (g u)) (measurableSet_Iio (a := (0 : ℝ))),
    compl_Iio, setLIntegral_congr (Ioi_ae_eq_Ici (a := (0 : ℝ))).symm, lint_Iio, lint_Ioi,
    ← ENNReal.ofReal_add (F_nonneg 0) (one_sub_F_nonneg 0)]
  simp

lemma ae_ne_zero : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 0 := by
  have : ({(0 : ℝ)}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) :=
    compl_mem_ae_iff.mpr (measure_singleton 0)
  filter_upwards [this] with u hu
  simpa using hu

lemma lint_gt_eq (s : Set ℝ) :
    ∫⁻ u in s, ENNReal.ofReal (gt u) = ∫⁻ u in s, ENNReal.ofReal (g u) := by
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae ae_ne_zero] with u hu
  simp [gt, hu]

lemma lint_gt_univ : ∫⁻ u, ENNReal.ofReal (gt u) = 1 := by
  have := lint_gt_eq univ
  simp only [Measure.restrict_univ] at this
  rw [this, lint_univ]

/-- The counterexample density on `ℝ²`: `e 0` has density `gt`, and `e 1 - e 0` independently
has density `gt` (equal to `g` almost everywhere). -/
noncomputable def fc (e : Fin 2 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gt (e 0)) * ENNReal.ofReal (gt (e 1 - e 0))

lemma measurable_fc : Measurable fc := by
  unfold fc
  have hm := ENNReal.measurable_ofReal.comp measurable_gt
  exact (hm.comp (measurable_pi_apply 0)).mul
    (hm.comp ((measurable_pi_apply 1).sub (measurable_pi_apply 0)))

lemma main (A : Set ℝ) (hA : MeasurableSet A) :
    (volume.withDensity fc) {e : Fin 2 → ℝ | e 1 - e 0 ∈ A} =
      ∫⁻ u in A, ENNReal.ofReal (g u) := by
  have hS : MeasurableSet {e : Fin 2 → ℝ | e 1 - e 0 ∈ A} :=
    ((measurable_pi_apply 1).sub (measurable_pi_apply 0)) hA
  rw [withDensity_apply _ hS, ← lintegral_indicator hS]
  set H : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (gt p.1) * A.indicator (fun u => ENNReal.ofReal (gt u)) (p.2 - p.1) with hH
  have hm : Measurable (fun u => ENNReal.ofReal (gt u)) :=
    ENNReal.measurable_ofReal.comp measurable_gt
  have hHm : Measurable H := by
    refine (hm.comp measurable_fst).mul ?_
    exact (hm.indicator hA).comp (measurable_snd.sub measurable_fst)
  have hEq : (fun e : Fin 2 → ℝ => {e : Fin 2 → ℝ | e 1 - e 0 ∈ A}.indicator fc e) =
      fun e => H (MeasurableEquiv.finTwoArrow e) := by
    funext e
    simp only [hH, MeasurableEquiv.finTwoArrow_apply, fc]
    by_cases hc : e 1 - e 0 ∈ A
    · rw [indicator_of_mem (show e ∈ {e : Fin 2 → ℝ | e 1 - e 0 ∈ A} from hc),
        indicator_of_mem hc]
      rfl
    · rw [indicator_of_notMem (show e ∉ {e : Fin 2 → ℝ | e 1 - e 0 ∈ A} from hc),
        indicator_of_notMem hc, mul_zero]
  rw [hEq, (volume_preserving_finTwoArrow ℝ).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _) H, Measure.volume_eq_prod,
    lintegral_prod H hHm.aemeasurable]
  have hinner : ∀ a : ℝ, ∫⁻ b, H (a, b) =
      ENNReal.ofReal (gt a) * ∫⁻ u in A, ENNReal.ofReal (g u) := by
    intro a
    simp only [hH]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_sub_right_eq_self (A.indicator (fun u => ENNReal.ofReal (gt u))) a,
      lintegral_indicator hA, lint_gt_eq]
  simp_rw [hinner]
  rw [lintegral_mul_const _ hm, lint_gt_univ, one_mul]

lemma choice0 (π : Fin 2 → ℝ) : StochFictPlay.Supermodular.choiceProb fc π 0 = F (π 0 - π 1) := by
  unfold StochFictPlay.Supermodular.choiceProb
  have hset : {e : Fin 2 → ℝ | ∀ j, j ≠ 0 → π j + e j < π 0 + e 0} =
      {e : Fin 2 → ℝ | e 1 - e 0 ∈ Iio (π 0 - π 1)} := by
    ext e
    simp only [Fin.forall_fin_two, mem_setOf_eq, mem_Iio, ne_eq, not_true_eq_false,
      IsEmpty.forall_iff, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, not_false_eq_true,
      forall_const, true_and]
    constructor <;> intro h <;> linarith
  rw [hset, main _ measurableSet_Iio, lint_Iio, ENNReal.toReal_ofReal (F_nonneg _)]

lemma choice1 (π : Fin 2 → ℝ) :
    StochFictPlay.Supermodular.choiceProb fc π 1 = 1 - F (π 0 - π 1) := by
  unfold StochFictPlay.Supermodular.choiceProb
  have hset : {e : Fin 2 → ℝ | ∀ j, j ≠ 1 → π j + e j < π 1 + e 1} =
      {e : Fin 2 → ℝ | e 1 - e 0 ∈ Ioi (π 0 - π 1)} := by
    ext e
    simp only [Fin.forall_fin_two, mem_setOf_eq, mem_Ioi, ne_eq, not_true_eq_false,
      IsEmpty.forall_iff, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true,
      forall_const, and_true]
    constructor <;> intro h <;> linarith
  rw [hset, main _ measurableSet_Ioi, lint_Ioi, ENNReal.toReal_ofReal (one_sub_F_nonneg _)]

noncomputable def Cf (π : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then F (π 0 - π 1) else 1 - F (π 0 - π 1)

lemma choice_eq : StochFictPlay.Supermodular.choiceProb fc = Cf := by
  funext π i
  fin_cases i
  · simp [Cf, choice0]
  · simp [Cf, choice1]

lemma contDiff_F : ContDiff ℝ 1 F := by
  unfold F
  exact contDiff_const.add ((Real.contDiff_arctan.comp (contDiff_id.pow 3)).div_const _)

lemma contDiff_Cf : ContDiff ℝ 1 Cf := by
  have hd : ContDiff ℝ 1 (fun π : Fin 2 → ℝ => π 0 - π 1) :=
    (contDiff_apply ℝ ℝ 0).sub (contDiff_apply ℝ ℝ 1)
  have h0 : ContDiff ℝ 1 (fun π : Fin 2 → ℝ => F (π 0 - π 1)) := contDiff_F.comp hd
  refine contDiff_pi.2 fun i => ?_
  by_cases hi : i = 0
  · simpa [Cf, hi] using h0
  · simpa [Cf, hi] using contDiff_const.sub h0

lemma hasFDerivAt_Cf : HasFDerivAt Cf (0 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) 0 := by
  have L : HasFDerivAt (fun π : Fin 2 → ℝ => π 0 - π 1)
      ((ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.proj 1) 0 :=
    (hasFDerivAt_apply 0 0).sub (hasFDerivAt_apply 1 0)
  have hg0 : HasDerivAt F 0 ((fun π : Fin 2 → ℝ => π 0 - π 1) 0) := by
    simpa [g_zero] using hasDerivAt_F 0
  have h0 := hg0.comp_hasFDerivAt (0 : Fin 2 → ℝ) L
  simp only [zero_smul] at h0
  rw [hasFDerivAt_pi']
  intro i
  rw [ContinuousLinearMap.comp_zero]
  by_cases hi : i = 0
  · simpa [Cf, hi, Function.comp_def] using h0
  · have h1 := h0.const_sub (1 : ℝ)
    simp only [neg_zero] at h1
    simpa [Cf, hi, Function.comp_def] using h1

lemma regular : StochFictPlay.Supermodular.IsRegularDensity fc := by
  refine ⟨measurable_fc, fun e => ?_, fun e => ?_, ?_, ?_⟩
  · unfold fc
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (gt_pos _)).ne'
      (ENNReal.ofReal_pos.2 (gt_pos _)).ne'
  · unfold fc
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · have h := main univ MeasurableSet.univ
    simp only [mem_univ, setOf_true, Measure.restrict_univ] at h
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    rw [h, lint_univ]
  · rw [choice_eq]; exact contDiff_Cf

lemma fderiv_zero :
    fderiv ℝ (StochFictPlay.Supermodular.choiceProb fc) 0 = 0 := by
  rw [choice_eq]; exact hasFDerivAt_Cf.fderiv

end CexEdad0fc3

open StochFictPlay.Supermodular in
theorem solution : ¬ (∀ (m : ℕ) (f : (Fin m → ℝ) → ℝ≥0∞)
    (hf : IsRegularDensity f) (π : Fin m → ℝ),
    (∀ k l : Fin m, k.val + 1 < m → l.val + 1 < m →
      0 < ∑ i : Fin m, ∑ j : Fin m,
        (if i ≤ k ∧ j ≤ l then fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i else 0)) ∧
    (∀ i : Fin m, ∑ j : Fin m, fderiv ℝ (choiceProb f) π (Pi.single j (1 : ℝ)) i = 0)) := by
  intro h
  have h1 := (h 2 CexEdad0fc3.fc CexEdad0fc3.regular 0).1 0 0 (by decide) (by decide)
  rw [CexEdad0fc3.fderiv_zero] at h1
  simp at h1
