-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_sphereMean_eq_integral_c09b214a98e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:07.089202+00:00
-- url     : https://prove2.me/submissions/6e49f6bc-06bf-4a50-b4bf-6ef5b9f84f7b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_formNorm_transpose_mulVec_0c324087ff6f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_map_equiv_0dc281ebe645
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_smul_f954aab74cd5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_congr_set_753e0bb205c1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_map_curry_volume_16d414f95811
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_volume_normSq_eq_one_e3f936075ac2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_formNorm_9c335fffca42
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_normSq_f96758e0920b

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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
variable {k : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsHeight
theorem _root_.solution (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (h : HermNorm n)
    (hh : ∀ u, h.norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) (g : (Fin k × Fin n → ℂ) → ℝ)
    (hg : Measurable g) :
    sphereMean h k g = ∫ u, g u ∂IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S k := by
  have hN : h.norm = IndefiniteRowSideFullHecke.ArithBezout.formNorm S := funext hh

  let E := blockEquiv (k := k) S hS
  let F : (Fin k × Fin n → ℂ) ≃ᵐ (Fin k × Fin n → ℂ) :=
    E.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hF : ⇑F = blockMul Sᵀ := rfl
  let Nf : (Fin k × Fin n → ℂ) → (Fin k × Fin n → ℂ) := fun u ij =>
    ((IndefiniteRowSideFullHecke.ArithBezout.formNorm S fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij
  let R : (Fin n → ℂ) → (Fin n → ℂ) := fun u => (Real.sqrt (IndefiniteRowSideFullHecke.ArithBezout.normSq u))⁻¹ • u
  let T : (Fin k → Fin n → ℂ) → (Fin k × Fin n → ℂ) := fun v p => (Sᵀ *ᵥ v p.1) p.2
  let Bc : Set (Fin n → ℂ) := {u | IndefiniteRowSideFullHecke.ArithBezout.normSq u ≤ 1}
  let BC : Set (Fin k × Fin n → ℂ) :=
    MeasurableEquiv.curry (Fin k) (Fin n) ℂ ⁻¹' Set.univ.pi fun _ => Bc
  let BA : Set (Fin k × Fin n → ℂ) := {u | ∀ i, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (fun j => u (i, j)) < 1}

  have hNf : Measurable Nf := by
    refine measurable_pi_lambda _ fun ij => ?_
    exact ((Complex.measurable_ofReal.comp ((continuous_formNorm S).comp
      (continuous_pi fun j => continuous_apply (ij.1, j))).measurable).inv).mul
      (measurable_pi_apply ij)
  have hR : Measurable R :=
    ((continuous_normSq.sqrt).measurable.inv).smul measurable_id
  have hT : Measurable T := by
    refine (continuous_pi fun p => ?_).measurable
    exact (continuous_apply p.2).comp
      (Continuous.matrix_mulVec continuous_const (continuous_apply p.1))

  have hBc : MeasurableSet Bc := measurableSet_le continuous_normSq.measurable measurable_const
  have hBc0 : (volume : Measure (Fin n → ℂ)) Bc ≠ 0 := by
    have hO : IsOpen {u : Fin n → ℂ | IndefiniteRowSideFullHecke.ArithBezout.normSq u < 1} :=
      isOpen_lt continuous_normSq continuous_const
    have hne : ({u : Fin n → ℂ | IndefiniteRowSideFullHecke.ArithBezout.normSq u < 1}).Nonempty :=
      ⟨0, by simp [IndefiniteRowSideFullHecke.ArithBezout.normSq]⟩
    exact (lt_of_lt_of_le (hO.measure_pos volume hne)
      (measure_mono (Set.ofPred_subset_ofPred.mpr fun _ h => h.le))).ne'
  have hBctop : (volume : Measure (Fin n → ℂ)) Bc ≠ ⊤ := by
    have hcl : IsClosed Bc := isClosed_le continuous_normSq continuous_const
    have hbd : Bornology.IsBounded Bc := by
      rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun v hv => ?_⟩
      have hv' : IndefiniteRowSideFullHecke.ArithBezout.normSq v ≤ 1 := hv
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have h1 : ‖v i‖ ^ 2 ≤ IndefiniteRowSideFullHecke.ArithBezout.normSq v :=
        Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ i)
      nlinarith [norm_nonneg (v i), hv']
    exact (Metric.isCompact_of_isClosed_isBounded hcl hbd).measure_lt_top.ne
  have : IsProbabilityMeasure (cond (volume : Measure (Fin n → ℂ)) Bc) :=
    cond_isProbabilityMeasure_of_finite hBc0 hBctop

  have hB : IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S k =
      (cond (volume : Measure (Fin k × Fin n → ℂ)) BC).map
        (T ∘ (fun v i => R (v i)) ∘ MeasurableEquiv.curry (Fin k) (Fin n) ℂ) := by
    have h1 : IndefiniteRowSideFullHecke.ArithBezout.sphereLaw n = (cond volume Bc).map R := rfl
    have : ∀ _ : Fin k, SigmaFinite ((cond (volume : Measure (Fin n → ℂ)) Bc).map R) :=
      fun _ => by
        have := Measure.isProbabilityMeasure_map (μ := cond (volume : Measure (Fin n → ℂ)) Bc)
          hR.aemeasurable
        infer_instance
    have h2 : Measure.pi (fun _ : Fin k => IndefiniteRowSideFullHecke.ArithBezout.sphereLaw n) =
        (Measure.pi fun _ : Fin k => cond (volume : Measure (Fin n → ℂ)) Bc).map
          (fun v i => R (v i)) := by
      rw [h1, Measure.pi_map_pi fun _ => hR.aemeasurable]
    have h3 : Measure.pi (fun _ : Fin k => cond (volume : Measure (Fin n → ℂ)) Bc) =
        (cond (volume : Measure (Fin k × Fin n → ℂ)) BC).map
          (MeasurableEquiv.curry (Fin k) (Fin n) ℂ) := by
      rw [cond_map_equiv, map_curry_volume]
      refine Measure.pi_eq fun s hs => ?_
      rw [cond_apply (MeasurableSet.univ_pi fun _ => hBc), Measure.pi_pi,
        ← Set.pi_inter_distrib, Measure.pi_pi]
      simp_rw [cond_apply hBc]
      rw [Finset.prod_mul_distrib, ENNReal.prod_inv_distrib]
      exact fun _ _ _ _ _ => Or.inr hBctop
    have hRk : Measurable fun (v : Fin k → Fin n → ℂ) i => R (v i) :=
      measurable_pi_lambda _ fun i => hR.comp (measurable_pi_apply i)
    rw [IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw, h2, h3, Measure.map_map hRk (MeasurableEquiv.measurable _),
      Measure.map_map hT (hRk.comp (MeasurableEquiv.measurable _))]

  have hA : sphereMean h k g = ∫ u, g (Nf u) ∂cond volume BA := by
    unfold sphereMean
    rw [hN]
    simp only [MeasureTheory.average, Measure.restrict_apply_univ]
    rfl

  have hc := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (Fin k × Fin n → ℂ))) (f := E.toLinearMap) E.isUnit_det'.ne_zero
  have hcF : (volume : Measure (Fin k × Fin n → ℂ)).map F =
      ENNReal.ofReal |(LinearMap.det E.toLinearMap)⁻¹| • volume := by
    have hFE : ⇑F = ⇑E.toLinearMap := by
      funext x
      rfl
    rw [hFE]
    exact hc
  have hc0 : ENNReal.ofReal |(LinearMap.det E.toLinearMap)⁻¹| ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.mpr (inv_ne_zero E.isUnit_det'.ne_zero)
  have hmem : ∀ w, w ∈ F ⁻¹' BA ↔ ∀ i, IndefiniteRowSideFullHecke.ArithBezout.normSq (fun j => w (i, j)) < 1 := by
    intro w
    simp only [Set.mem_preimage, BA, Set.mem_ofPred_eq, hF]
    refine forall_congr' fun i => ?_
    rw [show (fun j => blockMul Sᵀ w (i, j)) = Sᵀ *ᵥ fun j => w (i, j) from rfl,
      formNorm_transpose_mulVec hS, Real.sqrt_lt' one_pos, one_pow]
  have hmemC : ∀ w, w ∈ BC ↔ ∀ i, IndefiniteRowSideFullHecke.ArithBezout.normSq (fun j => w (i, j)) ≤ 1 := by
    intro w
    simp only [BC, Bc, Set.mem_preimage, Set.mem_univ_pi]
    rfl
  have hnull : ∀ i : Fin k, (volume : Measure (Fin k × Fin n → ℂ))
      {w | IndefiniteRowSideFullHecke.ArithBezout.normSq (fun j => w (i, j)) = 1} = 0 := by
    intro i
    have h1 := Measure.pi_eval_preimage_null (fun _ : Fin k => (volume : Measure (Fin n → ℂ)))
      (i := i) volume_normSq_eq_one
    rw [← map_curry_volume, MeasurableEquiv.map_apply] at h1
    exact h1
  have hpre : F ⁻¹' BA =ᵐ[volume] BC := by
    refine ae_eq_set.mpr ⟨?_, ?_⟩
    · rw [Set.sdiff_eq_empty.mpr fun w hw => (hmemC w).mpr fun i => ((hmem w).mp hw i).le,
        measure_empty]
    · refine measure_mono_null (fun w hw => ?_) (measure_iUnion_null hnull)
      obtain ⟨hC, hA'⟩ := hw
      rw [hmem] at hA'
      push Not at hA'
      obtain ⟨i, hi⟩ := hA'
      exact Set.mem_iUnion.mpr ⟨i, le_antisymm ((hmemC w).mp hC i) hi⟩
  have hpt : ∀ w, Nf (F w) = (T ∘ (fun v i => R (v i)) ∘ MeasurableEquiv.curry (Fin k) (Fin n) ℂ) w := by
    intro w
    funext ij
    show ((IndefiniteRowSideFullHecke.ArithBezout.formNorm S (fun j => blockMul Sᵀ w (ij.1, j)) : ℝ) : ℂ)⁻¹ *
        blockMul Sᵀ w ij =
      (Sᵀ *ᵥ ((√(IndefiniteRowSideFullHecke.ArithBezout.normSq fun j => w (ij.1, j)))⁻¹ • fun j => w (ij.1, j))) ij.2
    rw [show (fun j => blockMul Sᵀ w (ij.1, j)) = Sᵀ *ᵥ fun j => w (ij.1, j) from rfl,
      formNorm_transpose_mulVec hS, mulVec_smul, Pi.smul_apply, Complex.real_smul,
      Complex.ofReal_inv]
    rfl
  have hmeas : Measurable (T ∘ (fun v i => R (v i)) ∘ MeasurableEquiv.curry (Fin k) (Fin n) ℂ) :=
    hT.comp ((measurable_pi_lambda _ fun i => hR.comp (measurable_pi_apply i)).comp
      (MeasurableEquiv.measurable _))
  calc sphereMean h k g = ∫ u, g (Nf u) ∂cond volume BA := hA
    _ = ∫ u, g (Nf u) ∂cond (volume.map F) BA := by
      rw [hcF, cond_smul _ _ hc0 ENNReal.ofReal_ne_top]
    _ = ∫ u, g (Nf u) ∂(cond volume (F ⁻¹' BA)).map F := by rw [cond_map_equiv]
    _ = ∫ u, g (Nf u) ∂(cond volume BC).map F := by rw [cond_congr_set _ hpre]
    _ = ∫ w, g (Nf (F w)) ∂cond volume BC :=
      integral_map F.measurable.aemeasurable (hg.comp hNf).aestronglyMeasurable
    _ = ∫ w, g ((T ∘ (fun v i => R (v i)) ∘ MeasurableEquiv.curry (Fin k) (Fin n) ℂ) w)
          ∂cond volume BC := by
      simp_rw [hpt]
    _ = ∫ u, g u ∂IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S k := by
      rw [hB, integral_map hmeas.aemeasurable hg.aestronglyMeasurable]
end GroundTheory.Heights₂.Heights.ObjectsHeight
