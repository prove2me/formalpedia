-- Prove2me | solution 1 for QFS.localPoincare_planar
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:13:29.752799+00:00
-- url     : https://prove2.me/submissions/e595546a-35a7-414a-a5f4-ac0754a79915

import Theorems.Thm_QFS_lintegral_swap_planar
import Theorems.Thm_QFS_lintegral_swap_planar_prime
import Theorems.Thm_QFS_measurableSet_planarBall
import Theorems.Thm_QFS_osc_weighted_le_planar
import Theorems.Thm_QFS_unitBallVol_ne_top


import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Section1
import Definitions.Def_QFS_ThinCones
import Definitions.Def_QFS_Section3Kernel
import Definitions.Def_QFS_LebesgueDiff
import Definitions.Def_QFS_LebesgueDiff2
import Definitions.Def_QFS_Renormalization
import Definitions.Def_QFS_FirstJump
import Definitions.Def_QFS_Assembly
import Definitions.Def_QFS_PathAssembly
import Definitions.Def_QFS_BlockPaths
import Definitions.Def_QFS_Section6
import Definitions.Def_QFS_Rescaling
import Definitions.Def_QFS_Section32
import Definitions.Def_QFS_AppendixA
import Definitions.Def_QFS_BeyondThePaper
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Metric Set MeasureTheory
open scoped Real InnerProductSpace ENNReal

open QFS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]



namespace QFSNextProof_localPoincare_planar

lemma measurableSet_planarBall_graph (vs vt : EuclideanSpace ℝ (Fin 2)) (ϑ : ℝ) :
    MeasurableSet {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) | q.2 ∈ planarBall vs vt ϑ q.1.1 q.1.2} := by
  have hne : MeasurableSet {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) | q.1.1 ≠ q.1.2} := by
    have h : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.1 ≠ p.2} := by
      have he : {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) | p.1 ≠ p.2}
          = {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) | p.1 = p.2}ᶜ := rfl
      rw [he]
      exact (measurableSet_eq_fun measurable_fst measurable_snd).compl
    exact measurable_fst h
  have h2 : MeasurableSet {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) | q.1.2 - q.1.1 ∉ doubleCone vs ϑ} :=
    ((isOpen_doubleCone vs ϑ).preimage (by fun_prop)).measurableSet.compl
  have h3 : MeasurableSet {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) | q.1.2 - q.1.1 ∉ doubleCone vt ϑ} :=
    ((isOpen_doubleCone vt ϑ).preimage (by fun_prop)).measurableSet.compl
  have h4 : MeasurableSet {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) | q.2 ∈ closedBall (planarCtr vs vt q.1.1 q.1.2)
        (‖q.1.2 - q.1.1‖ * Real.sin ϑ ^ 2 / 2)} := by
    have hc1 : Continuous fun q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
        EuclideanSpace ℝ (Fin 2) => dist q.2 (planarCtr vs vt q.1.1 q.1.2) := by
      unfold planarCtr planarA cross2; fun_prop
    have hc2 : Continuous fun q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
        EuclideanSpace ℝ (Fin 2) => ‖q.1.2 - q.1.1‖ * Real.sin ϑ ^ 2 / 2 := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le hc1 hc2).measurableSet
  have hEq : {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) | q.2 ∈ planarBall vs vt ϑ q.1.1 q.1.2}
      = ({q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
            EuclideanSpace ℝ (Fin 2) | q.1.1 ≠ q.1.2} ∩
          {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
            EuclideanSpace ℝ (Fin 2) | q.1.2 - q.1.1 ∉ doubleCone vs ϑ} ∩
          {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
            EuclideanSpace ℝ (Fin 2) | q.1.2 - q.1.1 ∉ doubleCone vt ϑ}) ∩
        {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
          EuclideanSpace ℝ (Fin 2) | q.2 ∈ closedBall (planarCtr vs vt q.1.1 q.1.2)
            (‖q.1.2 - q.1.1‖ * Real.sin ϑ ^ 2 / 2)} := by
    ext q
    simp only [planarBall, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [hEq]
  exact ((hne.inter h2).inter h3).inter h4

theorem measurable_param_planarBall (vs vt : EuclideanSpace ℝ (Fin 2)) (ϑ : ℝ)
    {H : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hH : Measurable H) :
    Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ∫⁻ z in planarBall vs vt ϑ p.1 p.2, H (p, z) := by
  have hset := measurableSet_planarBall_graph vs vt ϑ
  have heq : (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ∫⁻ z in planarBall vs vt ϑ p.1 p.2, H (p, z))
      = fun p => ∫⁻ z, {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
          EuclideanSpace ℝ (Fin 2) | q.2 ∈ planarBall vs vt ϑ q.1.1 q.1.2}.indicator H (p, z) := by
    funext p
    rw [← lintegral_indicator (QFS.measurableSet_planarBall ϑ p.1 p.2)]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ planarBall vs vt ϑ p.1 p.2
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem
        (show (p, z) ∈ {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
          EuclideanSpace ℝ (Fin 2) | q.2 ∈ planarBall vs vt ϑ q.1.1 q.1.2} from hz)]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem
        (show (p, z) ∉ {q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
          EuclideanSpace ℝ (Fin 2) | q.2 ∈ planarBall vs vt ϑ q.1.1 q.1.2} from hz)]
  rw [heq]
  exact (hH.indicator hset).lintegral_prod_right'




end QFSNextProof_localPoincare_planar
open QFSNextProof_localPoincare_planar

set_option autoImplicit false

theorem solution {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1)
    (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α)
    (hD : cross2 vs vt ≠ 0) {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : Measurable f)
    (U U' : Set (EuclideanSpace ℝ (Fin 2))) {P : Set (EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 2))} (hPm : MeasurableSet P) (hPsub : P ⊆ U ×ˢ U')
    (hP : ∀ p ∈ P, p.1 ≠ p.2 ∧ p.2 - p.1 ∉ doubleCone vs ϑ ∧
      p.2 - p.1 ∉ doubleCone vt ϑ) :
    ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2 *
        ∫⁻ p in P, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))
      ≤ ENNReal.ofReal (planarConst vs vt ϑ α) * unitBallVol 2 *
          (∫⁻ s in U, ∫⁻ z in {z | z - s ∈ doubleCone vs ϑ},
            ENNReal.ofReal (2 * (f z - f s) ^ 2) *
              ENNReal.ofReal (‖z - s‖ ^ (-(2 : ℝ) - α)))
        + ENNReal.ofReal (planarConst vs vt ϑ α) * unitBallVol 2 *
          (∫⁻ t in U', ∫⁻ z in {z | z - t ∈ doubleCone vt ϑ},
            ENNReal.ofReal (2 * (f t - f z) ^ 2) *
              ENNReal.ofReal (‖z - t‖ ^ (-(2 : ℝ) - α))) := by
  set A : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(4 : ℝ) - α)) *
      ∫⁻ z in planarBall vs vt ϑ p.1 p.2, ENNReal.ofReal (2 * (f z - f p.1) ^ 2) with hAdef
  set B : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(4 : ℝ) - α)) *
      ∫⁻ z in planarBall vs vt ϑ p.1 p.2, ENNReal.ofReal (2 * (f p.2 - f z) ^ 2) with hBdef
  have hw2m : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(4 : ℝ) - α)) := by fun_prop
  have hHA : Measurable fun q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) => ENNReal.ofReal (2 * (f q.2 - f q.1.1) ^ 2) := by fun_prop
  have hHB : Measurable fun q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanSpace ℝ (Fin 2) => ENNReal.ofReal (2 * (f q.1.2 - f q.2) ^ 2) := by fun_prop
  have hGs : ∀ s : EuclideanSpace ℝ (Fin 2),
      Measurable fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2) := by intro s; fun_prop
  have hGt : ∀ t : EuclideanSpace ℝ (Fin 2),
      Measurable fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2) := by intro t; fun_prop
  have hAm : Measurable A := by
    rw [hAdef]; exact hw2m.mul (measurable_param_planarBall vs vt ϑ hHA)
  have hBm : Measurable B := by
    rw [hBdef]; exact hw2m.mul (measurable_param_planarBall vs vt ϑ hHB)
  have hptwise : ∀ p ∈ P, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
      ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α)) *
        (ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2) ≤ A p + B p := by
    rintro ⟨s, t⟩ hp
    obtain ⟨hne, h1, h2⟩ := hP _ hp
    refine le_trans (QFS.osc_weighted_le_planar f hne h1 h2) (le_of_eq ?_)
    rw [hAdef, hBdef, ← mul_add]
    congr 1
    rw [← lintegral_add_left (by fun_prop)]
    refine setLIntegral_congr_fun (QFS.measurableSet_planarBall ϑ s t) fun z _ => ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  calc ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2 *
        ∫⁻ p in P, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))
      = ∫⁻ p in P, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α)) *
          (ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2) := by
        rw [← lintegral_const_mul' _ _
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top QFS.unitBallVol_ne_top)]
        exact lintegral_congr fun p => by ring
    _ ≤ ∫⁻ p in P, (A p + B p) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hPm] with p hp using hptwise p hp
    _ ≤ ∫⁻ p in U ×ˢ U', (A p + B p) := lintegral_mono_set hPsub
    _ = (∫⁻ p in U ×ˢ U', A p) + ∫⁻ p in U ×ˢ U', B p := lintegral_add_left hAm _
    _ ≤ ENNReal.ofReal (planarConst vs vt ϑ α) * unitBallVol 2 *
          (∫⁻ s in U, ∫⁻ z in {z | z - s ∈ doubleCone vs ϑ},
            ENNReal.ofReal (2 * (f z - f s) ^ 2) *
              ENNReal.ofReal (‖z - s‖ ^ (-(2 : ℝ) - α)))
        + ENNReal.ofReal (planarConst vs vt ϑ α) * unitBallVol 2 *
          (∫⁻ t in U', ∫⁻ z in {z | z - t ∈ doubleCone vt ϑ},
            ENNReal.ofReal (2 * (f t - f z) ^ 2) *
              ENNReal.ofReal (‖z - t‖ ^ (-(2 : ℝ) - α))) := by
        refine add_le_add ?_ ?_
        · rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
            lintegral_prod _ hAm.aemeasurable,
            ← lintegral_const_mul' _ _
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top QFS.unitBallVol_ne_top)]
          refine lintegral_mono fun s => ?_
          exact le_trans (lintegral_mono' Measure.restrict_le_self le_rfl)
            (QFS.lintegral_swap_planar hvs hvt hϑ hϑ' hα hD s (hGs s))
        · rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
            lintegral_prod_symm _ hBm.aemeasurable,
            ← lintegral_const_mul' _ _
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top QFS.unitBallVol_ne_top)]
          refine lintegral_mono fun t => ?_
          exact le_trans (lintegral_mono' Measure.restrict_le_self le_rfl)
            (QFS.lintegral_swap_planar_prime hvs hvt hϑ hϑ' hα hD t (hGt t))
#print axioms solution
