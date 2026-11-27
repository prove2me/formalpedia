-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_WeightedAreaFormula_proof_2ab425f92cfa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:12:39.966067+00:00
-- url     : https://prove2.me/submissions/b2407398-d24a-4622-b807-f2300d4049f2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeightedAreaFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeightedAreaFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Set Filter Function Topology
open scoped ENNReal NNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace WeightedAreaFormula
theorem _root_.solution : WeightedAreaFormula.Statement := by
  intro E _ _ _ _ _ μ _ A f H hA hf hfin hint
  classical
  have hder : ∀ x ∈ A, HasFDerivAt f (fderiv ℝ f x) x := fun x hx =>
    ((hf x hx).differentiableAt (hA.mem_nhds hx)).hasFDerivAt
  set B : Set E := {x ∈ A | (fderiv ℝ f x).det ≠ 0} with hBdef
  have hBA : B ⊆ A := sep_subset _ _

  have hBm : MeasurableSet B := by
    have hm : Measurable fun x => (fderiv ℝ f x).det :=
      ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ f)
    exact hA.measurableSet.inter (hm (measurableSet_singleton 0).compl)

  have hZ : μ (f '' {x ∈ A | (fderiv ℝ f x).det = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx => (hder x hx.1).hasFDerivWithinAt) (fun x hx => hx.2)

  let r : (E →L[ℝ] E) → ℝ≥0 := fun L => (‖L.inverse‖₊ + 1)⁻¹
  obtain ⟨t, L, htd, htm, hcov, happ, hL⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B (fderiv ℝ f)
      (fun x hx => (hder x hx.1).hasFDerivWithinAt) r (fun _ => inv_ne_zero (by positivity))
  set P : ℕ → Set E := fun n => B ∩ t n with hPdef
  have hPm : ∀ n, MeasurableSet (P n) := fun n => hBm.inter (htm n)
  have hPd : Pairwise (Disjoint on P) := fun m n hmn =>
    (htd hmn).mono inter_subset_right inter_subset_right
  have hPA : ∀ n, P n ⊆ A := fun n => inter_subset_left.trans hBA
  have hderP : ∀ n, ∀ x ∈ P n, HasFDerivWithinAt f (fderiv ℝ f x) (P n) x := fun n x hx =>
    (hder x (hPA n hx)).hasFDerivWithinAt
  have hinj : ∀ n, InjOn f (P n) := by
    intro n
    rcases (P n).eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [h]; exact injOn_empty f
    obtain ⟨y, hy, hLy⟩ := hL ⟨x, hx.1⟩ n
    set e := (fderiv ℝ f y).toContinuousLinearEquivOfDetNeZero hy.2
    have he : (e : E →L[ℝ] E) = L n := by
      rw [hLy]; exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
    have ha := happ n
    rw [← he] at ha
    refine ha.injOn ?_
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    right
    have hr : r (e : E →L[ℝ] E) = (‖(e.symm : E →L[ℝ] E)‖₊ + 1)⁻¹ := by
      simp only [r, ContinuousLinearMap.inverse_equiv]
    rw [hr]
    have hpos : 0 < ‖(e.symm : E →L[ℝ] E)‖₊ := by
      rw [pos_iff_ne_zero, ne_eq, nnnorm_eq_zero]
      intro h0
      obtain ⟨z, hz⟩ := exists_ne (0 : E)
      apply hz
      simpa using congrArg (fun T : E →L[ℝ] E => T (e z)) h0
    exact (inv_lt_inv₀ (by positivity) hpos).2 (lt_add_one _)
  have hBU : B = ⋃ n, P n := by
    rw [← inter_iUnion]; exact (inter_eq_left.2 hcov).symm
  have himg : ∀ n, MeasurableSet (f '' P n) := fun n =>
    measurable_image_of_fderivWithin (hPm n) (hderP n) (hinj n)

  let g : ℕ → E → ℝ := fun n y => H (invFunOn f (P n) y)
  have hgP : ∀ n, ∀ x ∈ P n, g n (f x) = H x := fun n x hx =>
    congrArg H (hinj n (invFunOn_mem ⟨x, hx, rfl⟩) hx (invFunOn_eq ⟨x, hx, rfl⟩))
  let F : ℕ → E → ℝ := fun n => (f '' P n).indicator (g n)
  have hFint : ∀ n, Integrable (F n) μ := fun n =>
    (integrable_indicator_iff (himg n)).2
      ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ (hPm n) (hderP n) (hinj n)
        (g n)).2 ((hint.mono_set (hPA n)).congr_fun
          (fun x hx => by simp only [smul_eq_mul, hgP n x hx]) (hPm n)))
  have hFint_eq : ∀ n, ∫ y, F n y ∂μ = ∫ x in P n, |(fderiv ℝ f x).det| * H x ∂μ := fun n => by
    calc ∫ y, F n y ∂μ = ∫ y in f '' P n, g n y ∂μ := integral_indicator (himg n)
      _ = ∫ x in P n, |(fderiv ℝ f x).det| • g n (f x) ∂μ :=
        integral_image_eq_integral_abs_det_fderiv_smul μ (hPm n) (hderP n) (hinj n) (g n)
      _ = ∫ x in P n, |(fderiv ℝ f x).det| * H x ∂μ :=
        setIntegral_congr_fun (hPm n) fun x hx => by simp only [smul_eq_mul, hgP n x hx]
  have hFlint : ∀ n, ∫⁻ y, ‖F n y‖ₑ ∂μ = ∫⁻ x in P n, ‖|(fderiv ℝ f x).det| * H x‖ₑ ∂μ :=
    fun n => by
    calc ∫⁻ y, ‖F n y‖ₑ ∂μ = ∫⁻ y, (f '' P n).indicator (fun z => ‖g n z‖ₑ) y ∂μ :=
          lintegral_congr fun y => enorm_indicator_eq_indicator_enorm (g n) y
      _ = ∫⁻ y in f '' P n, ‖g n y‖ₑ ∂μ := lintegral_indicator (himg n) _
      _ = ∫⁻ x in P n, ENNReal.ofReal |(fderiv ℝ f x).det| * ‖g n (f x)‖ₑ ∂μ :=
        lintegral_image_eq_lintegral_abs_det_fderiv_mul μ (hPm n) (hderP n) (hinj n)
          (fun z => ‖g n z‖ₑ)
      _ = ∫⁻ x in P n, ‖|(fderiv ℝ f x).det| * H x‖ₑ ∂μ := by
        refine setLIntegral_congr_fun (hPm n) fun x hx => ?_
        simp only [hgP n x hx, enorm_mul, Real.enorm_eq_ofReal_abs, abs_abs]
  have hsumlint : ∑' n, ∫⁻ y, ‖F n y‖ₑ ∂μ ≠ ∞ := by
    simp_rw [hFlint]
    rw [← lintegral_iUnion hPm hPd, ← hBU]
    exact (lt_of_le_of_lt (lintegral_mono_set hBA) (hasFiniteIntegral_iff_enorm.1 hint.2)).ne

  have hinjT : ∀ y, InjOn (fun n => invFunOn f (P n) y) {n | y ∈ f '' P n} := by
    intro y m hm n hn hmn
    by_contra hne
    refine Set.disjoint_left.1 (hPd hne) (invFunOn_mem hm) ?_
    simp only at hmn
    rw [hmn]; exact invFunOn_mem hn
  have hT : ∀ y, {n | y ∈ f '' P n}.Finite := by
    intro y
    refine Set.Finite.of_finite_image ((hfin y).subset ?_) (hinjT y)
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨hPA n (invFunOn_mem hn), invFunOn_eq hn⟩
  have hsum : ∀ y, HasSum (fun n => F n y) (∑ n ∈ (hT y).toFinset, F n y) := fun y =>
    hasSum_sum_of_ne_finset_zero fun n hn =>
      show (f '' P n).indicator (g n) y = 0 from
        indicator_of_notMem (s := f '' P n) (fun h => hn ((hT y).mem_toFinset.2 h)) (g n)

  have hae : ∀ᵐ y ∂μ, ∑' n, F n y = ∑ᶠ x ∈ {x | x ∈ A ∧ f x = y}, H x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ] with y hy
    have hbij : BijOn (fun n => invFunOn f (P n) y) {n | y ∈ f '' P n}
        {x | x ∈ A ∧ f x = y} := by
      refine ⟨fun n hn => ⟨hPA n (invFunOn_mem hn), invFunOn_eq hn⟩, hinjT y, ?_⟩
      rintro x ⟨hxA, hxy⟩
      have hxB : x ∈ B := ⟨hxA, fun hd => hy ⟨x, ⟨hxA, hd⟩, hxy⟩⟩
      obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov hxB)
      have hxP : x ∈ P n := ⟨hxB, hn⟩
      have hyn : y ∈ f '' P n := ⟨x, hxP, hxy⟩
      exact ⟨n, hyn, hinj n (invFunOn_mem hyn) hxP ((invFunOn_eq hyn).trans hxy.symm)⟩
    rw [(hsum y).tsum_eq]
    change _ = ∑ᶠ (x : E) (_ : x ∈ {x | x ∈ A ∧ f x = y}), H x
    rw [← finsum_mem_eq_of_bijOn _ hbij
      (f := fun n => H (invFunOn f (P n) y)) (fun n _ => rfl),
      finsum_mem_eq_finite_toFinset_sum _ (hT y)]
    exact Finset.sum_congr rfl fun n hn =>
      indicator_of_mem (s := f '' P n) ((hT y).mem_toFinset.1 hn) (g n)

  have hGm : AEStronglyMeasurable (fun y => ∑' n, F n y) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => (integrable_finsetSum (Finset.range N) fun n _ => hFint n).1)
      (ae_of_all _ fun y => (hsum y).summable.hasSum.tendsto_sum_nat)
  have hGfin : HasFiniteIntegral (fun y => ∑' n, F n y) μ := by
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ y, ‖∑' n, F n y‖ₑ ∂μ ≤ ∫⁻ y, ∑' n, ‖F n y‖ₑ ∂μ := by
          refine lintegral_mono fun y => ?_
          rw [(hsum y).tsum_eq]
          exact (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)
      _ = ∑' n, ∫⁻ y, ‖F n y‖ₑ ∂μ := lintegral_tsum fun n => (hFint n).1.enorm
      _ < ∞ := hsumlint.lt_top

  have hIA : ∫ x in A, |(fderiv ℝ f x).det| * H x ∂μ =
      ∫ x in B, |(fderiv ℝ f x).det| * H x ∂μ :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hA.measurableSet hBA fun x hx => by
      have h0 : (fderiv ℝ f x).det = 0 := by
        by_contra h; exact hx.2 ⟨hx.1, h⟩
      simp [h0]
  have hBint : IntegrableOn (fun x => |(fderiv ℝ f x).det| * H x) (⋃ n, P n) μ := by
    rw [← hBU]; exact hint.mono_set hBA
  refine ⟨Integrable.congr (⟨hGm, hGfin⟩ : Integrable (fun y => ∑' n, F n y) μ) hae, ?_⟩
  rw [← integral_congr_ae hae, integral_tsum (fun n => (hFint n).1) hsumlint, hIA, hBU]
  simp_rw [hFint_eq]
  exact (hasSum_integral_iUnion hPm hPd hBint).tsum_eq
end WeightedAreaFormula
end GroundTheory.Heights₂.Heights
