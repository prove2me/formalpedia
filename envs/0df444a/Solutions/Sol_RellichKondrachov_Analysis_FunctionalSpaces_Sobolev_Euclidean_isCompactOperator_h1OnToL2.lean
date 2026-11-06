-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:05:03.51086+00:00
-- url     : https://prove2.me/submissions/84515c2b-45bf-4a44-ac3c-d7c9acb25788

import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Kernels
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_TranslationIntegral
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_norm_extendByZeroL2
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_norm_translateL2_sub_h1ToL2_le
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_exists_kernel_tsupport_subset_ball_integral_eq_one
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small
import Theorems.Thm_P2M_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_extendByZeroL2_eq_extendByZero___cc8208de3560
set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpaceRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableAddRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableNegRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instFactOneLeTwoSobolevEuclideanRellich

set_option maxHeartbeats 2000000 in
theorem solution {K : Set E} (_hK : IsCompact K) (hKm : MeasurableSet K) :
    IsCompactOperator (h1OnToL2 (E := E) K hKm) := by
  classical
  have hr : (0 : ℝ) < 1 := by norm_num
  let H1vol : Type _ := ↥(h1 (μ := (volume : Measure E)) (E := E))
  let T : ↥(h1On (E := E) K hKm) →L[ℝ] (E →₂[(volume : Measure E)] ℝ) :=
    h1OnToL2 (E := E) K hKm
  let A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ((volume : Measure E).restrict K)) :=
    {u |
      L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u ∈
        T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1}
  let C : ℝ :=
    ‖h1ToL2 (μ := (volume : Measure E)) (E := E)‖
  have hCnonneg : 0 ≤ C := by
    exact norm_nonneg (h1ToL2 (μ := (volume : Measure E)) (E := E))
  have hA_ball :
      A ⊆
        Metric.closedBall
          (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ((volume : Measure E).restrict K))
          C := by
    intro u hu
    rcases hu with ⟨x, hx, hxEq⟩
    have hx' : ‖(x : H1vol)‖ ≤ (1 : ℝ) := by
      change ‖x‖ ≤ (1 : ℝ)
      simpa only [Metric.mem_closedBall, dist_zero_right x] using hx
    have hTx' : ‖T x‖ ≤ C := by
      have hTx : ‖T x‖ ≤ C * ‖(x : H1vol)‖ := by
        have h :=
          (h1ToL2 (μ := (volume : Measure E)) (E := E)).le_opNorm (x : H1vol)
        simpa [T, h1OnToL2, C] using h
      refine hTx.trans ?_
      have : C * ‖(x : H1vol)‖ ≤ C * (1 : ℝ) := mul_le_mul_of_nonneg_left hx' hCnonneg
      simpa [mul_one] using this
    have hnorm_ext :
        ‖L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ = ‖u‖ :=
      L2Compactness.norm_extendByZeroL2 (E := E) (K := K) hKm u
    have hu' : ‖u‖ ≤ C := by
      have : ‖L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ C := by
        simpa [hxEq] using hTx'
      simpa [hnorm_ext] using this
    simpa [Metric.closedBall, dist_eq_norm] using hu'
  have hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u)
                    - L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂L2Compactness.kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2 := by
    intro ε hε
    have hδ : 0 < ε / 2 := by linarith
    rcases
        L2Compactness.exists_kernel_tsupport_subset_ball_integral_eq_one
          (E := E) (deltaLoss := ε / 2) hδ with
      ⟨ψ, hψc, hψcs, hψ0, hψint, hψsupp⟩
    refine ⟨ψ, hψc, hψcs, hψ0, hψint, ?_⟩
    intro u huA
    rcases huA with ⟨x, hx, hxEq⟩
    have hxH1 : ‖(x : H1vol)‖ ≤ (1 : ℝ) := by
      change ‖x‖ ≤ (1 : ℝ)
      simpa only [Metric.mem_closedBall, dist_zero_right x] using hx
    have hmod :
        ∀ t : E, t ∈ Metric.ball (0 : E) (ε / 2) →
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) (T x) - T x‖ ≤ ε / 2 := by
      intro t ht
      have ht' : ‖t‖ ≤ ε / 2 := le_of_lt (by
        simpa [Metric.ball, dist_eq_norm, mem_ofPred_eq] using ht)
      have hgrad_le :
          ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ ‖(x : H1vol)‖ := by
        let V : Type _ := (E →₂[(volume : Measure E)] ℝ) × (E →₂[(volume : Measure E)] E)
        simpa [h1ToL2Grad, V] using (norm_snd_le (x := ((x : H1vol) : V)))
      have hgrad_le_one :
          ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ (1 : ℝ) :=
        hgrad_le.trans hxH1
      have htr :=
        norm_translateL2_sub_h1ToL2_le (μ := (volume : Measure E)) (E := E) (-t) (x : H1vol)
      have htr' :
          ‖(translateL2 (μ := (volume : Measure E)) (-t))
                (h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol))
              - h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤
            ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ := by
        simpa [neg_neg] using htr
      have hle :
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) (T x) - T x‖ ≤
            ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ := by
        simpa [T, h1OnToL2, hxEq] using htr'
      refine hle.trans ?_
      have :
          ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ (ε / 2) * 1 := by
        refine (mul_le_mul_of_nonneg_right ht' (norm_nonneg _)).trans ?_
        refine mul_le_mul_of_nonneg_left hgrad_le_one (by linarith)
      simpa [mul_one] using this
    have hη : 0 ≤ ε / 2 := le_of_lt hδ
    have hbound :=
      L2Compactness.integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
        (E := E) (ψ := ψ) hψc hψcs hψ0 hψint (deltaLoss := ε / 2) (η := ε / 2) hη hψsupp (T x) hmod
    simpa [hxEq] using hbound
  have hcomp : IsCompact (closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1)) := by
    have hR : 0 ≤ C := hCnonneg
    have hA_eq :
        T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1 =
          L2Compactness.extendByZeroL2 (E := E) (K := K) hKm '' A := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, hx, rfl⟩
        have hxRange :
            (h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol)) ∈
              LinearMap.range
                ((MeasureTheory.Lp.extendByZeroₗᵢ
                      (μ := (volume : Measure E)) (E := ℝ)
                      (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap) := by
          have hxmem :
              (x : H1vol) ∈ h1On (E := E) K hKm := x.property
          dsimp [h1On] at hxmem
          change
              ((h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
                    (x : H1vol)) ∈
                LinearMap.range
                  ((MeasureTheory.Lp.extendByZeroₗᵢ
                        (μ := (volume : Measure E)) (E := ℝ)
                        (p := (2 : ℝ≥0∞))
                        (s := K) hKm).toLinearMap)
          exact hxmem
        rcases hxRange with ⟨u, hu⟩
        have hu0 :
            (MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm) u =
              h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol) := by
          simpa using hu
        have hTx : T x = L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u := by
          calc
            T x = h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol) := by
                  simp [T, h1OnToL2]
            _ = (MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm) u := by
                  simpa using hu0.symm
            _ = L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u := by
                  simpa using
                    (L2Compactness.extendByZeroL2_eq_extendByZeroₗᵢ (E := E) (K := K) hKm u).symm
        refine ⟨u, ?_, hTx.symm⟩
        exact ⟨x, hx, hTx⟩
      · intro hy
        rcases hy with ⟨u, huA, rfl⟩
        exact huA
    have : IsCompact
        (closure (L2Compactness.extendByZeroL2 (E := E) (K := K) hKm '' A)) :=
    L2Compactness.isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small
      (E := E) (K := K) (hK := (_hK : IsCompact K))
      (hKm := hKm) hR hA_ball hApprox
    simpa [hA_eq] using this
  refine ⟨closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1), hcomp, ?_⟩
  have hball :
      Metric.ball (0 : ↥(h1On (E := E) K hKm)) 1 ⊆
        T ⁻¹' closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1) := by
    intro x hx
    refine subset_closure ?_
    refine ⟨x, ?_, rfl⟩
    exact Metric.ball_subset_closedBall hx
  exact Filter.mem_of_superset
    (Metric.ball_mem_nhds (x := (0 : ↥(h1On (E := E) K hKm))) (ε := (1 : ℝ)) hr) hball
