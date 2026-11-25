-- Prove2me | solution 1 for PI.VolStabW.submLB_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:04:27.075727+00:00
-- url     : https://prove2.me/submissions/18fcbc1b-525a-4b4f-a7ad-4a1c52e42ee3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LBSubm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Topology Set Filter
open scoped ENNReal
namespace PI.VolStabW
theorem _root_.solution : SubmLB := by
  intro n m μ ν hμ hν f hf x0 hx0 W hW hxW
  let A := fderiv ℝ f x0
  obtain ⟨B, hB⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hx0)
  have hRI : Function.RightInverse B A := fun y => by
    simpa using congrArg (fun L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => L y) hB
  let T := ContinuousLinearEquiv.equivOfRightInverse A B hRI
  have hT1 : ∀ x, (T x).1 = A x := fun x => rfl
  let Θ : (Fin n → ℝ) → (Fin n → ℝ) := fun x => T.symm (f x, (T x).2)
  have hΘc : ContDiff ℝ 1 Θ :=
    T.symm.contDiff.comp (hf.prodMk (contDiff_snd.comp T.contDiff))
  have hfA : ∀ x, A (Θ x) = f x := by
    intro x
    rw [← hT1]; simp [Θ]
  have hd : ∀ x, HasFDerivAt Θ (fderiv ℝ Θ x) x :=
    fun x => ((hΘc.differentiable one_ne_zero) x).hasFDerivAt
  have hid : fderiv ℝ Θ x0 = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    let P := (ContinuousLinearMap.snd ℝ (Fin m → ℝ) A.ker).comp T.toContinuousLinearMap
    have hP : HasFDerivAt (fun x => (T x).2) P x0 := P.hasFDerivAt
    have h1 : HasFDerivAt (fun x => (f x, (T x).2)) ((fderiv ℝ f x0).prod P) x0 :=
      ((hf.differentiable one_ne_zero) x0).hasFDerivAt.prodMk hP
    have h2 := T.symm.toContinuousLinearMap.hasFDerivAt.comp x0 h1
    rw [show fderiv ℝ Θ x0 = T.symm.toContinuousLinearMap.comp ((fderiv ℝ f x0).prod P) from
      h2.fderiv]
    ext1 y
    change T.symm ((fderiv ℝ f x0) y, (T y).2) = y
    have : ((fderiv ℝ f x0) y, (T y).2) = T y := Prod.ext (hT1 y).symm rfl
    rw [this, ContinuousLinearEquiv.symm_apply_apply]
  have hs : HasStrictFDerivAt Θ
      ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x0 := by
    have := hΘc.contDiffAt.hasStrictFDerivAt (x := x0) one_ne_zero
    rw [hid] at this
    exact this
  let PH := hs.toOpenPartialHomeomorph Θ

  have hO : IsOpen (PH.source ∩ W) := PH.open_source.inter hW
  have hxO : x0 ∈ PH.source ∩ W := ⟨hs.mem_toOpenPartialHomeomorph_source, hxW⟩
  obtain ⟨K0, hK0c, hxK0, hK0O⟩ := exists_compact_subset hO hxO

  have hDc : Continuous fun x => (fderiv ℝ Θ x).det :=
    ContinuousLinearMap.continuous_det.comp (hΘc.continuous_fderiv one_ne_zero)
  obtain ⟨Dm, hDm⟩ := hK0c.exists_bound_of_continuousOn hDc.continuousOn
  set D' : ℝ≥0∞ := ENNReal.ofReal (max Dm 1) with hD'
  have hD'0 : D' ≠ 0 := by
    rw [hD', Ne, ENNReal.ofReal_eq_zero, not_le]
    exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hD'top : D' ≠ ⊤ := ENNReal.ofReal_ne_top

  let V0 := PH '' interior K0
  have hV0o : IsOpen V0 := PH.isOpen_image_of_subset_source isOpen_interior
    (interior_subset.trans (hK0O.trans inter_subset_left))
  have hΘx0 : Θ x0 ∈ V0 := ⟨x0, hxK0, rfl⟩

  have hTV : T '' V0 ∈ 𝓝 (T (Θ x0)) :=
    (T.toHomeomorph.isOpenMap _ hV0o).mem_nhds ⟨_, hΘx0, rfl⟩
  rw [nhds_prod_eq] at hTV
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.1 hTV
  let lam : Measure A.ker := Measure.addHaar
  set Bk := interior v with hBk
  have hBk0 : lam Bk ≠ 0 :=
    (isOpen_interior.measure_pos lam ⟨_, mem_interior_iff_mem_nhds.2 hv⟩).ne'
  have hμT : (μ.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  obtain ⟨c0, hsm⟩ : ∃ c : ENNReal, μ.map T = c • (ν.prod lam) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hc0 : c0 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hsm
    have := (isOpen_univ.measure_pos (μ.map T) univ_nonempty).ne'
    rw [hsm] at this
    exact this rfl
  refine ⟨min (D'⁻¹ * c0 * lam Bk) 1,
    lt_min (pos_iff_ne_zero.2 (mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.2 hD'top) hc0) hBk0))
      one_pos,
    ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _), u, ?_, fun S hSu hSm => ?_⟩
  · have e : (T (Θ x0)).1 = f x0 := by rw [hT1, hfA]
    rw [← e]
    exact hu
  · let s := K0 ∩ Θ ⁻¹' (A ⁻¹' S)
    have hsm' : MeasurableSet s := hK0c.isClosed.measurableSet.inter
      ((A.continuous.comp hΘc.continuous).measurable hSm)
    have hs_sub : s ⊆ f ⁻¹' S ∩ W := fun x hx =>
      ⟨by show f x ∈ S; rw [← hfA]; exact hx.2, (hK0O hx.1).2⟩
    have hsrc : s ⊆ PH.source := fun x hx => (hK0O hx.1).1
    have hcv := lintegral_abs_det_fderiv_eq_addHaar_image μ hsm'
      (fun x _ => (hd x).hasFDerivWithinAt) (PH.injOn.mono hsrc)
    have hbound : μ (Θ '' s) ≤ D' * μ s := by
      rw [← hcv, ← setLIntegral_const]
      refine setLIntegral_mono measurable_const fun x hx => ENNReal.ofReal_le_ofReal ?_
      have h := hDm x hx.1
      rw [Real.norm_eq_abs] at h
      exact h.trans (le_max_left _ _)
    have hsub2 : T ⁻¹' (S ×ˢ Bk) ⊆ Θ '' s := by
      intro z hz
      obtain ⟨z', hz'V, hTz⟩ := huv ⟨hSu hz.1, interior_subset hz.2⟩
      have hzz : z' = z := T.injective hTz
      subst hzz
      obtain ⟨x, hxK, rfl⟩ := hz'V
      refine ⟨x, ⟨interior_subset hxK, ?_⟩, rfl⟩
      show A (Θ x) ∈ S
      rw [← hT1]
      exact hz.1
    have hmeasT : μ (T ⁻¹' (S ×ˢ Bk)) = c0 * (ν S * lam Bk) := by
      rw [← Measure.map_apply T.continuous.measurable (hSm.prod isOpen_interior.measurableSet),
        hsm, Measure.smul_apply, Measure.prod_prod, smul_eq_mul]
    calc min (D'⁻¹ * c0 * lam Bk) 1 * ν S ≤ D'⁻¹ * c0 * lam Bk * ν S :=
          mul_le_mul_left (min_le_left _ _) _
      _ = D'⁻¹ * μ (T ⁻¹' (S ×ˢ Bk)) := by rw [hmeasT]; ring
      _ ≤ D'⁻¹ * μ (Θ '' s) := mul_le_mul_right (measure_mono hsub2) _
      _ ≤ D'⁻¹ * (D' * μ s) := mul_le_mul_right hbound _
      _ = μ s := by rw [← mul_assoc, ENNReal.inv_mul_cancel hD'0 hD'top, one_mul]
      _ ≤ μ (f ⁻¹' S ∩ W) := measure_mono hs_sub
end PI.VolStabW
