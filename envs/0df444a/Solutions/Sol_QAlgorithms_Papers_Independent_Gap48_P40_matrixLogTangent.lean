-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.matrixLogTangent
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-27T13:38:45.432755+00:00
-- url     : https://prove2.me/submissions/0f94512d-38ff-43e1-a33e-36b7ee973178

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator
open QAlgorithms.Papers.Independent.Information100.P44 (Mat)
open MeasureTheory Set Filter

namespace P40Aux

/-- Scalar log integral: `∫₀^∞ ((1+x)⁻¹ - (t+x)⁻¹) dx = log t` for `t > 0`. -/
lemma scalar_log {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => (1 + x)⁻¹ - (t + x)⁻¹) (Ioi 0) ∧
    ∫ x in Ioi (0:ℝ), ((1 + x)⁻¹ - (t + x)⁻¹) = Real.log t := by
  have hder : ∀ x ∈ Ici (0:ℝ), HasDerivAt (fun x => Real.log (1 + x) - Real.log (t + x))
      ((1 + x)⁻¹ - (t + x)⁻¹) x := by
    intro x hx
    have hx' : (0:ℝ) ≤ x := hx
    have h1 : (1 + x) ≠ 0 := by positivity
    have h2 : (t + x) ≠ 0 := by positivity
    have e1 := ((hasDerivAt_id x).const_add 1).log h1
    have e2 := ((hasDerivAt_id x).const_add t).log h2
    exact (e1.sub e2).congr_deriv (by simp [one_div])
  have hlim : Tendsto (fun x => Real.log (1 + x) - Real.log (t + x)) atTop (𝓝 0) := by
    have hr : Tendsto (fun x : ℝ => 1 + (1 - t) * (t + x)⁻¹) atTop (𝓝 (1 + (1 - t) * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ t tendsto_id)))
    rw [mul_zero, add_zero] at hr
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp hr
    rw [Real.log_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp]
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  have hint : IntegrableOn (fun x : ℝ => (1 + x)⁻¹ - (t + x)⁻¹) (Ioi 0) := by
    rcases le_total 1 t with h | h
    · refine integrableOn_Ioi_deriv_of_nonneg' hder (fun x hx => ?_) hlim
      have hx' : (0:ℝ) < x := hx
      rw [sub_nonneg]; exact inv_anti₀ (by positivity) (by linarith)
    · refine integrableOn_Ioi_deriv_of_nonpos' hder (fun x hx => ?_) hlim
      have hx' : (0:ℝ) < x := hx
      rw [sub_nonpos]; exact inv_anti₀ (by positivity) (by linarith)
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hder 0 (le_refl (0:ℝ))).continuousAt.continuousWithinAt
    (fun x hx => hder x (Ioi_subset_Ici_self hx)) hint hlim]
  simp

lemma inv_sq_integrable {m : ℝ} (hm : 0 < m) :
    IntegrableOn (fun x : ℝ => ((m + x) ^ 2)⁻¹) (Ioi 0) := by
  have hder : ∀ x ∈ Ici (0:ℝ), HasDerivAt (fun x => -(m + x)⁻¹) (((m + x) ^ 2)⁻¹) x := by
    intro x hx
    have hx' : (0:ℝ) ≤ x := hx
    have := ((hasDerivAt_id x).const_add m).inv (by positivity)
    exact this.neg.congr_deriv (by simp only [id, neg_div, neg_neg, one_div])
  refine integrableOn_Ioi_deriv_of_nonneg' hder (fun x hx => by positivity) (l := 0) ?_
  have := (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ m tendsto_id)).neg
  simpa using this

set_option linter.unusedSectionVars false

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

lemma spec_bound {a : A} (ha : IsStrictlyPositive a) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ t ∈ spectrum ℝ a, m ≤ t := by
  rcases (spectrum ℝ a).eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, le_rfl, by simp [h]⟩
  · obtain ⟨t0, ht0, hmin⟩ := (spectrum.isCompact a).exists_isMinOn h continuousOn_id
    exact ⟨min t0 1, lt_min (ha.spectrum_pos ht0) one_pos, min_le_right _ _,
      fun t ht => (min_le_left _ _).trans (hmin ht)⟩

lemma cfc_inv_shift {a : A} (ha : IsStrictlyPositive a) {x : ℝ} (hx : 0 ≤ x) :
    cfc (fun t : ℝ => (t + x)⁻¹) a = Ring.inverse (a + algebraMap ℝ A x) := by
  rw [cfc_inv (fun t : ℝ => t + x) a (fun t ht => by have := ha.spectrum_pos ht; show t + x ≠ 0; positivity),
    cfc_add_const x (fun t : ℝ => t) a, cfc_id' ℝ a]

lemma norm_inv_shift {a : A} (ha : IsStrictlyPositive a) {m : ℝ} (hm0 : 0 < m)
    (hm : ∀ t ∈ spectrum ℝ a, m ≤ t) {x : ℝ} (hx : 0 ≤ x) :
    ‖Ring.inverse (a + algebraMap ℝ A x)‖ ≤ (m + x)⁻¹ := by
  rw [← cfc_inv_shift ha hx]
  refine norm_cfc_le (by positivity) fun t ht => ?_
  have := hm t ht
  have ht0 := ha.spectrum_pos ht
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact inv_anti₀ (by positivity) (by linarith)

/-- Integral representation of the CFC logarithm. -/
lemma log_rep {a : A} (ha : IsStrictlyPositive a) :
    IntegrableOn (fun x : ℝ => algebraMap ℝ A (1 + x)⁻¹ - Ring.inverse (a + algebraMap ℝ A x))
      (Ioi 0) ∧
    ∫ x in Ioi (0:ℝ), (algebraMap ℝ A (1 + x)⁻¹ - Ring.inverse (a + algebraMap ℝ A x)) =
      cfc Real.log a := by
  obtain ⟨m, hm0, hm1, hm⟩ := spec_bound ha
  set f : ℝ → ℝ → ℝ := fun x t => (1 + x)⁻¹ - (t + x)⁻¹ with hf
  have hcfc : EqOn (fun x => cfc (f x) a)
      (fun x => algebraMap ℝ A (1 + x)⁻¹ - Ring.inverse (a + algebraMap ℝ A x)) (Ioi 0) := by
    intro x hx
    have hx' : (0:ℝ) ≤ x := le_of_lt hx
    simp only [hf]
    rw [cfc_sub (fun _ : ℝ => (1 + x)⁻¹) (fun t : ℝ => (t + x)⁻¹) a continuousOn_const
      ((continuousOn_id.add continuousOn_const).inv₀
        (fun t ht => by have := ha.spectrum_pos ht; show t + x ≠ 0; positivity)),
      cfc_const _ a ha.isSelfAdjoint, cfc_inv_shift ha hx']
  have hcont : ContinuousOn (Function.uncurry f) (Ioi 0 ×ˢ spectrum ℝ a) := by
    apply ContinuousOn.sub
    · exact (continuous_const.add continuous_fst).continuousOn.inv₀
        (fun p hp => by have : (0:ℝ) < p.1 := hp.1; show 1 + p.1 ≠ 0; positivity)
    · exact (continuous_snd.add continuous_fst).continuousOn.inv₀
        (fun p hp => by
          have : (0:ℝ) < p.1 := hp.1
          have := ha.spectrum_pos hp.2
          show p.2 + p.1 ≠ 0; positivity)
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioi (0:ℝ))), ∀ t ∈ spectrum ℝ a,
      ‖f x t‖ ≤ (‖a‖ + 1) * ((m + x) ^ 2)⁻¹ := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx t ht => ?_
    have hx' : (0:ℝ) < x := hx
    have ht0 := ha.spectrum_pos ht
    have htm := hm t ht
    have htn : t ≤ ‖a‖ := by
      have := spectrum.norm_le_norm_of_mem ht
      rwa [Real.norm_of_nonneg ht0.le] at this
    simp only [hf]
    rw [inv_sub_inv (by positivity) (by positivity), Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : 0 < (1 + x) * (t + x)), div_eq_mul_inv]
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · rw [abs_le]; constructor <;> linarith [norm_nonneg a]
    · apply inv_anti₀ (by positivity); nlinarith
  have hbint := (inv_sq_integrable hm0).const_mul (‖a‖ + 1)
  have key := cfc_setIntegral measurableSet_Ioi f _ a hcont hbound hbint.2 ha.isSelfAdjoint
  have hint := integrableOn_cfc measurableSet_Ioi f _ a hcont hbound hbint.2 ha.isSelfAdjoint
  refine ⟨hint.congr_fun hcfc measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hcfc, ← key]
  exact cfc_congr fun t ht => (scalar_log (ha.spectrum_pos ht)).2

lemma star_inv_self {X : A} (hX : IsUnit X) (hXsa : IsSelfAdjoint X) :
    star (Ring.inverse X) = Ring.inverse X := by
  have h1 : star (Ring.inverse X) * X = 1 := by
    rw [show star (Ring.inverse X) * X = star (X * Ring.inverse X) by rw [star_mul, hXsa.star_eq],
      Ring.mul_inverse_cancel X hX, star_one]
  calc star (Ring.inverse X) = star (Ring.inverse X) * (X * Ring.inverse X) := by
        rw [Ring.mul_inverse_cancel X hX, mul_one]
    _ = Ring.inverse X := by rw [← mul_assoc, h1, one_mul]

/-- Pointwise algebra: `R d R - (R - S) = (d R)^* S (d R)` with `R = X⁻¹`, `S = (X+d)⁻¹`. -/
lemma pointwise (X d : A) (hX : IsUnit X) (hXd : IsUnit (X + d)) (hXsa : IsSelfAdjoint X)
    (hd : IsSelfAdjoint d) (hS : 0 ≤ Ring.inverse (X + d)) :
    0 ≤ Ring.inverse X * d * Ring.inverse X - (Ring.inverse X - Ring.inverse (X + d)) := by
  set R := Ring.inverse X
  set S := Ring.inverse (X + d)
  have hRX : R * X = 1 := Ring.inverse_mul_cancel X hX
  have hSY : S * (X + d) = 1 := Ring.inverse_mul_cancel _ hXd
  have hXR : X * R = 1 := Ring.mul_inverse_cancel X hX
  have hYS : (X + d) * S = 1 := Ring.mul_inverse_cancel _ hXd
  have e2 : R - S = S * d * R := by
    have : S * d * R = S * (X + d) * R - S * (X * R) := by noncomm_ring
    rw [this, hSY, hXR, one_mul, mul_one]
  have e1 : R - S = R * d * S := by
    have : R * d * S = R * ((X + d) * S) - R * X * S := by noncomm_ring
    rw [this, hYS, hRX, mul_one, one_mul]
  have hRs : star R = R := star_inv_self hX hXsa
  have : R * d * R - (R - S) = star (d * R) * S * (d * R) := by
    rw [star_mul, hRs, hd.star_eq]
    calc R * d * R - (R - S) = R * d * R - R * d * S := by rw [← e1]
      _ = R * d * (R - S) := by noncomm_ring
      _ = R * d * (S * d * R) := by rw [← e2]
      _ = R * d * S * (d * R) := by noncomm_ring
  rw [this]
  exact star_left_conjugate_nonneg hS _

theorem general (a d : A) (ha : IsStrictlyPositive a) (hd : IsSelfAdjoint d)
    (had : IsStrictlyPositive (a + d)) :
    IntegrableOn (fun x : ℝ => Ring.inverse (a + algebraMap ℝ A x) * d *
      Ring.inverse (a + algebraMap ℝ A x)) (Ioi 0) ∧
    0 ≤ (∫ x in Ioi (0:ℝ), Ring.inverse (a + algebraMap ℝ A x) * d *
      Ring.inverse (a + algebraMap ℝ A x)) - (cfc Real.log (a + d) - cfc Real.log a) := by
  obtain ⟨m, hm0, hm1, hm⟩ := spec_bound ha
  have hpos : ∀ x : ℝ, 0 ≤ x → IsStrictlyPositive (a + algebraMap ℝ A x) :=
    fun x hx => ha.add_nonneg (algebraMap_nonneg A hx)
  have hpos' : ∀ x : ℝ, 0 ≤ x → IsStrictlyPositive (a + d + algebraMap ℝ A x) :=
    fun x hx => had.add_nonneg (algebraMap_nonneg A hx)
  have hcontR : ContinuousOn (fun x : ℝ => Ring.inverse (a + algebraMap ℝ A x)) (Ici 0) := by
    intro x hx
    have hc := NormedRing.inverse_continuousAt (hpos x hx).isUnit.unit
    rw [IsUnit.unit_spec] at hc
    have hg : Continuous (fun y : ℝ => a + algebraMap ℝ A y) :=
      continuous_const.add (algebraMap_isometry ℝ A).continuous
    exact (ContinuousAt.comp (g := Ring.inverse) (f := fun y : ℝ => a + algebraMap ℝ A y) (x := x) hc hg.continuousAt).continuousWithinAt
  have hg_int : IntegrableOn (fun x : ℝ => Ring.inverse (a + algebraMap ℝ A x) * d *
      Ring.inverse (a + algebraMap ℝ A x)) (Ioi 0) := by
    refine Integrable.mono' ((inv_sq_integrable hm0).const_mul ‖d‖)
      ((((hcontR.mono Ioi_subset_Ici_self).mul continuousOn_const).mul
        (hcontR.mono Ioi_subset_Ici_self)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
    have hx' : (0:ℝ) ≤ x := le_of_lt hx
    have hn := norm_inv_shift ha hm0 hm hx'
    calc _ ≤ ‖Ring.inverse (a + algebraMap ℝ A x)‖ * ‖d‖ *
          ‖Ring.inverse (a + algebraMap ℝ A x)‖ := norm_mul₃_le
      _ ≤ (m + x)⁻¹ * ‖d‖ * (m + x)⁻¹ := by gcongr
      _ = ‖d‖ * ((m + x) ^ 2)⁻¹ := by rw [← inv_pow]; ring
  obtain ⟨hAi, hAe⟩ := log_rep ha
  obtain ⟨hBi, hBe⟩ := log_rep had
  refine ⟨hg_int, ?_⟩
  have hBA : IntegrableOn (fun x : ℝ =>
      (algebraMap ℝ A (1 + x)⁻¹ - Ring.inverse (a + d + algebraMap ℝ A x)) -
      (algebraMap ℝ A (1 + x)⁻¹ - Ring.inverse (a + algebraMap ℝ A x))) (Ioi 0) := hBi.sub hAi
  rw [← hAe, ← hBe, ← integral_sub hBi hAi, ← integral_sub hg_int hBA]
  refine integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
  have hx' : (0:ℝ) ≤ x := le_of_lt hx
  have hS : 0 ≤ Ring.inverse (a + algebraMap ℝ A x + d) := by
    rw [add_right_comm, ← cfc_inv_shift had hx']
    exact cfc_nonneg fun t ht => by have := had.spectrum_pos ht; positivity
  have := pointwise (a + algebraMap ℝ A x) d (hpos x hx').isUnit
    (by rw [add_right_comm]; exact (hpos' x hx').isUnit) (hpos x hx').isSelfAdjoint hd hS
  simp only [Pi.zero_apply, sub_sub_sub_cancel_left]
  rwa [add_right_comm] at this

end P40Aux

open scoped MatrixOrder in
/-- Lemma 6 (tangent bound for the matrix logarithm), via `P40Aux.general`. -/
theorem solution {d : ℕ} (hd : 0 < d) (A D : Mat d)
    (hA : A.PosDef) (hD : D.IsHermitian) (hAD : (A + D).PosDef) :
    Integrable (fun x : ℝ => (A + (x : ℂ) • (1 : Mat d))⁻¹ * D *
      (A + (x : ℂ) • (1 : Mat d))⁻¹) (volume.restrict (Set.Ioi 0)) ∧
    ((∫ x : ℝ in Set.Ioi 0, (A + (x : ℂ) • (1 : Mat d))⁻¹ * D *
      (A + (x : ℂ) • (1 : Mat d))⁻¹) -
      (cfc Real.log (A + D) - cfc Real.log A)).PosSemidef := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hR : ∀ x : ℝ, (A + (x : ℂ) • (1 : Mat d))⁻¹ = Ring.inverse (A + algebraMap ℝ (Mat d) x) := by
    intro x
    rw [Matrix.nonsing_inv_eq_ringInverse, Algebra.algebraMap_eq_smul_one]
    rfl
  simp only [hR]
  obtain ⟨h1, h2⟩ := P40Aux.general A D hA.isStrictlyPositive hD hAD.isStrictlyPositive
  exact ⟨h1, Matrix.nonneg_iff_posSemidef.mp h2⟩
