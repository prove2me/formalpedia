-- Prove2me | solution 1 for QFS.lintegral_swap_planar
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:09:11.733706+00:00
-- url     : https://prove2.me/submissions/6797e6eb-e5ff-4984-895f-c7911c78786f

import Theorems.Thm_QFS_lintegral_planarBall_fibre_le
import Theorems.Thm_QFS_lintegral_swap_of_fibre_bound
import Theorems.Thm_QFS_measurableSet_planarBall
import Theorems.Thm_QFS_mem_two_cones_of_mem_planarBall
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



namespace QFSNextProof_lintegral_swap_planar

theorem mem_two_cones_of_mem_planarBall' {vs vt : EuclideanSpace ℝ (Fin 2)}
    (hvs : ‖vs‖ = 1) (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    (hD : cross2 vs vt ≠ 0) {s t z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ planarBall vs vt ϑ s t) :
    z - s ∈ doubleCone vs ϑ ∧ z - t ∈ doubleCone vt ϑ :=
  QFS.mem_two_cones_of_mem_planarBall hvs hvt hϑ hϑ' hz.1 hD hz.2.1 hz.2.2.1 hz.2.2.2

lemma measurableSet_planarBall_fibre {vs vt : EuclideanSpace ℝ (Fin 2)} (ϑ : ℝ)
    (s z : EuclideanSpace ℝ (Fin 2)) :
    MeasurableSet {t : EuclideanSpace ℝ (Fin 2) | z ∈ planarBall vs vt ϑ s t} := by
  have h1 : MeasurableSet {t : EuclideanSpace ℝ (Fin 2) | s ≠ t} :=
    (measurableSet_singleton s).compl.congr (by ext t; simp [eq_comm, Set.mem_compl_iff])
  have h2 : MeasurableSet {t : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vs ϑ} :=
    ((isOpen_doubleCone vs ϑ).preimage (by fun_prop)).measurableSet.compl
  have h3 : MeasurableSet {t : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vt ϑ} :=
    ((isOpen_doubleCone vt ϑ).preimage (by fun_prop)).measurableSet.compl
  have h4 : MeasurableSet {t : EuclideanSpace ℝ (Fin 2) |
      z ∈ closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2)} := by
    have hc1 : Continuous fun t : EuclideanSpace ℝ (Fin 2) =>
        dist z (planarCtr vs vt s t) := by unfold planarCtr planarA cross2; fun_prop
    have hc2 : Continuous fun t : EuclideanSpace ℝ (Fin 2) =>
        ‖t - s‖ * Real.sin ϑ ^ 2 / 2 := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le hc1 hc2).measurableSet
  have hEq : {t : EuclideanSpace ℝ (Fin 2) | z ∈ planarBall vs vt ϑ s t}
      = ({t : EuclideanSpace ℝ (Fin 2) | s ≠ t} ∩
          {t : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vs ϑ} ∩
          {t : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vt ϑ}) ∩
        {t : EuclideanSpace ℝ (Fin 2) |
          z ∈ closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2)} := by
    ext t
    simp only [planarBall, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [hEq]
  exact ((h1.inter h2).inter h3).inter h4



end QFSNextProof_lintegral_swap_planar
open QFSNextProof_lintegral_swap_planar

set_option autoImplicit false

theorem solution {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1)
    (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α)
    (hD : cross2 vs vt ≠ 0) (s : EuclideanSpace ℝ (Fin 2))
    {G : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ t, ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) *
        ∫⁻ z in planarBall vs vt ϑ s t, G z
      ≤ ENNReal.ofReal (planarConst vs vt ϑ α) * unitBallVol 2 *
        ∫⁻ z in {z | z - s ∈ doubleCone vs ϑ},
          G z * ENNReal.ofReal (‖z - s‖ ^ (-(2 : ℝ) - α)) := by
  have hs0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hDpos : 0 < |cross2 vs vt| := abs_pos.mpr hD
  have hconeMeas : MeasurableSet {z : EuclideanSpace ℝ (Fin 2) | z - s ∈ doubleCone vs ϑ} :=
    ((isOpen_doubleCone vs ϑ).preimage (by fun_prop)).measurableSet
  have hcc : 0 ≤ planarConst vs vt ϑ α := by
    unfold planarConst
    positivity
  have hwm : Measurable fun t : EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) := by fun_prop
  have hgraph : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
      p.2 ∈ planarBall vs vt ϑ s p.1} := by
    have hne : MeasurableSet {t : EuclideanSpace ℝ (Fin 2) | s ≠ t} := by
      have he : {t : EuclideanSpace ℝ (Fin 2) | s ≠ t}
          = ({s} : Set (EuclideanSpace ℝ (Fin 2)))ᶜ := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq]
        exact ⟨fun h hc => h hc.symm, fun h hc => h hc.symm⟩
      rw [he]
      exact (measurableSet_singleton s).compl
    have h1 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        s ≠ p.1} := measurable_fst hne
    have h2 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.1 - s ∉ doubleCone vs ϑ} :=
      ((isOpen_doubleCone vs ϑ).preimage (by fun_prop)).measurableSet.compl
    have h3 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.1 - s ∉ doubleCone vt ϑ} :=
      ((isOpen_doubleCone vt ϑ).preimage (by fun_prop)).measurableSet.compl
    have h4 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.2 ∈ closedBall (planarCtr vs vt s p.1) (‖p.1 - s‖ * Real.sin ϑ ^ 2 / 2)} := by
      have hc1 : Continuous fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          dist p.2 (planarCtr vs vt s p.1) := by unfold planarCtr planarA cross2; fun_prop
      have hc2 : Continuous fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          ‖p.1 - s‖ * Real.sin ϑ ^ 2 / 2 := by fun_prop
      simpa [Metric.mem_closedBall] using (isClosed_le hc1 hc2).measurableSet
    have hEq : {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.2 ∈ planarBall vs vt ϑ s p.1}
        = ({p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) | s ≠ p.1} ∩
            {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
              p.1 - s ∉ doubleCone vs ϑ} ∩
            {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
              p.1 - s ∉ doubleCone vt ϑ}) ∩
          {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
            p.2 ∈ closedBall (planarCtr vs vt s p.1) (‖p.1 - s‖ * Real.sin ϑ ^ 2 / 2)} := by
      ext p
      simp only [planarBall, Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto
    rw [hEq]
    exact ((h1.inter h2).inter h3).inter h4
  set Ψ : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := fun z =>
    {z : EuclideanSpace ℝ (Fin 2) | z - s ∈ doubleCone vs ϑ}.indicator
      (fun z => ENNReal.ofReal (planarConst vs vt ϑ α * ‖z - s‖ ^ (-(2 : ℝ) - α)) *
        unitBallVol 2) z with hΨ
  have hfib : ∀ z, ∫⁻ t in {t | z ∈ planarBall vs vt ϑ s t},
      ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) ≤ Ψ z := by
    intro z
    simp only [hΨ]
    by_cases hzc : z - s ∈ doubleCone vs ϑ
    · rw [Set.indicator_of_mem (show z ∈ {z : EuclideanSpace ℝ (Fin 2) |
        z - s ∈ doubleCone vs ϑ} from hzc)]
      exact QFS.lintegral_planarBall_fibre_le hvs hvt hϑ hϑ' hα hD s z
    · rw [Set.indicator_of_notMem (show z ∉ {z : EuclideanSpace ℝ (Fin 2) |
        z - s ∈ doubleCone vs ϑ} from hzc)]
      have hempty : {t : EuclideanSpace ℝ (Fin 2) | z ∈ planarBall vs vt ϑ s t} = ∅ := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hz
        exact hzc (mem_two_cones_of_mem_planarBall' hvs hvt hϑ hϑ' hD hz).1
      rw [hempty, MeasureTheory.setLIntegral_empty]
  refine le_trans (QFS.lintegral_swap_of_fibre_bound
    (W := fun t => planarBall vs vt ϑ s t)
    (w := fun t => ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)))
    (fun t => QFS.measurableSet_planarBall ϑ s t) hgraph hwm hG
    (fun z => measurableSet_planarBall_fibre ϑ s z) hfib) ?_
  have hprod : ∀ z, G z * Ψ z
      = {z : EuclideanSpace ℝ (Fin 2) | z - s ∈ doubleCone vs ϑ}.indicator
        (fun z => G z * (ENNReal.ofReal (planarConst vs vt ϑ α * ‖z - s‖ ^ (-(2 : ℝ) - α)) *
          unitBallVol 2)) z := by
    intro z
    simp only [hΨ]
    by_cases hzc : z - s ∈ doubleCone vs ϑ
    · rw [Set.indicator_of_mem (show z ∈ {z : EuclideanSpace ℝ (Fin 2) |
        z - s ∈ doubleCone vs ϑ} from hzc), Set.indicator_of_mem
        (show z ∈ {z : EuclideanSpace ℝ (Fin 2) | z - s ∈ doubleCone vs ϑ} from hzc)]
    · rw [Set.indicator_of_notMem (show z ∉ {z : EuclideanSpace ℝ (Fin 2) |
        z - s ∈ doubleCone vs ϑ} from hzc), Set.indicator_of_notMem
        (show z ∉ {z : EuclideanSpace ℝ (Fin 2) | z - s ∈ doubleCone vs ϑ} from hzc), mul_zero]
  rw [lintegral_congr hprod, lintegral_indicator hconeMeas,
    ← lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top QFS.unitBallVol_ne_top)]
  refine le_of_eq (lintegral_congr fun z => ?_)
  rw [ENNReal.ofReal_mul hcc]
  ring
#print axioms solution
