-- Prove2me | solution 1 for QFS.formHs_le_form_planar_cross
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:21:10.353713+00:00
-- url     : https://prove2.me/submissions/469013ed-f17c-425f-8147-e4a7e13291bc

import Theorems.Thm_QFS_jumpKernel_le_of_mem_coneAt
import Theorems.Thm_QFS_localPoincare_planar


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


set_option autoImplicit false

theorem solution {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1)
    (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α)
    (hD : cross2 vs vt ≠ 0)
    {Γ : Configuration (EuclideanSpace ℝ (Fin 2))} {Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k)
    {U U' : Set (EuclideanSpace ℝ (Fin 2))} (hUm : MeasurableSet U) (hU'm : MeasurableSet U')
    (hUs : ∀ x ∈ U, doubleCone vs ϑ ⊆ (Γ x).carrier)
    (hUt : ∀ y ∈ U', doubleCone vt ϑ ⊆ (Γ y).carrier)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2 *
        ∫⁻ p in U ×ˢ U', ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))
      ≤ ENNReal.ofReal (planarConst vs vt ϑ α) * unitBallVol 2 *
            (ENNReal.ofReal (2 * Λ) * form Set.univ k f)
        + ENNReal.ofReal (planarConst vs vt ϑ α) * unitBallVol 2 *
            (ENNReal.ofReal (2 * Λ) * form Set.univ k f)
        + ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2 * ENNReal.ofReal Λ *
            form Set.univ k f := by
  have hΛ : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hk.one_le
  have hform : form Set.univ k f
      = ∫⁻ p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2 := by
    rw [form, Set.univ_prod_univ, setLIntegral_univ]
  -- the bad pairs
  set Bad : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
    (U ×ˢ U') ∩ {p | p.1 ≠ p.2 ∧ p.2 - p.1 ∉ doubleCone vs ϑ ∧
      p.2 - p.1 ∉ doubleCone vt ϑ} with hBaddef
  have hBadm : MeasurableSet Bad := by
    rw [hBaddef]
    refine (hUm.prod hU'm).inter ?_
    have h1 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.1 ≠ p.2} := (measurableSet_eq_fun measurable_fst measurable_snd).compl
    have h2 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.2 - p.1 ∉ doubleCone vs ϑ} :=
      ((isOpen_doubleCone vs ϑ).preimage (by fun_prop)).measurableSet.compl
    have h3 : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        p.2 - p.1 ∉ doubleCone vt ϑ} :=
      ((isOpen_doubleCone vt ϑ).preimage (by fun_prop)).measurableSet.compl
    have hEq : {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) | p.1 ≠ p.2 ∧
        p.2 - p.1 ∉ doubleCone vs ϑ ∧ p.2 - p.1 ∉ doubleCone vt ϑ}
        = {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) | p.1 ≠ p.2} ∩
          ({p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
            p.2 - p.1 ∉ doubleCone vs ϑ} ∩
           {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
            p.2 - p.1 ∉ doubleCone vt ϑ}) := rfl
    rw [hEq]
    exact h1.inter (h2.inter h3)
  -- on the good pairs the jump kernel is already dominated by `Λ k`
  have hgood : ∀ p ∈ (U ×ˢ U') \ Bad,
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))
        ≤ ENNReal.ofReal Λ * (ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) := by
    rintro ⟨s, t⟩ ⟨hmem, hnb⟩
    have hcases : s = t ∨ t - s ∈ doubleCone vs ϑ ∨ t - s ∈ doubleCone vt ϑ := by
      by_contra hc
      simp only [not_or] at hc
      exact hnb ⟨hmem, hc.1, hc.2.1, hc.2.2⟩
    have hjkeq : ENNReal.ofReal (‖s - t‖ ^ (-(2 : ℝ) - α)) = jumpKernel 2 α s t := by
      rw [jumpKernel]; norm_num
    rcases hcases with rfl | hc | hc
    · simp
    · have hmem2 : t ∈ coneAt Γ s := hUs s hmem.1 hc
      rw [hjkeq]
      calc ENNReal.ofReal ((f t - f s) ^ 2) * jumpKernel 2 α s t
          ≤ ENNReal.ofReal ((f t - f s) ^ 2) * (ENNReal.ofReal Λ * k s t) :=
            mul_le_mul' le_rfl (QFS.jumpKernel_le_of_mem_coneAt hk hmem2)
        _ = ENNReal.ofReal Λ * (ENNReal.ofReal ((f t - f s) ^ 2) * k s t) := by ring
    · have hneg : s - t ∈ doubleCone vt ϑ := by
        rw [mem_doubleCone_iff] at hc ⊢
        rw [show s - t = -(t - s) from by abel, neg_neg]
        exact hc.symm
      have hmem2 : s ∈ coneAt Γ t := hUt t hmem.2 hneg
      have hjk : jumpKernel 2 α s t ≤ ENNReal.ofReal Λ * k s t := by
        have h0 : jumpKernel 2 α s t = jumpKernel 2 α t s := by
          rw [jumpKernel, jumpKernel, norm_sub_rev]
        rw [h0, hk.symm s t]
        exact QFS.jumpKernel_le_of_mem_coneAt hk hmem2
      rw [hjkeq]
      calc ENNReal.ofReal ((f t - f s) ^ 2) * jumpKernel 2 α s t
          ≤ ENNReal.ofReal ((f t - f s) ^ 2) * (ENNReal.ofReal Λ * k s t) :=
            mul_le_mul' le_rfl hjk
        _ = ENNReal.ofReal Λ * (ENNReal.ofReal ((f t - f s) ^ 2) * k s t) := by ring
  -- the cone-restricted terms convert by the same lower bound
  have hterm : ∀ (V : Set (EuclideanSpace ℝ (Fin 2))) (W : Set (EuclideanSpace ℝ (Fin 2))),
      MeasurableSet V → (∀ x ∈ V, W ⊆ (Γ x).carrier) → IsOpen W →
      ∀ (g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ),
      (∀ x y, (g x y) ^ 2 = (f y - f x) ^ 2) →
      (∫⁻ x in V, ∫⁻ y in {y | y - x ∈ W},
          ENNReal.ofReal (2 * (g x y) ^ 2) * ENNReal.ofReal (‖y - x‖ ^ (-(2 : ℝ) - α)))
        ≤ ENNReal.ofReal (2 * Λ) * form Set.univ k f := by
    intro V W hVm hcommon hWopen g hg
    rw [hform, Measure.volume_eq_prod, lintegral_prod _ hkm.aemeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans (lintegral_mono_ae ?_) (lintegral_mono' Measure.restrict_le_self le_rfl)
    filter_upwards [ae_restrict_mem hVm] with x hxV
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hWm : MeasurableSet {y : EuclideanSpace ℝ (Fin 2) | y - x ∈ W} :=
      (hWopen.preimage (by fun_prop)).measurableSet
    calc ∫⁻ y in {y | y - x ∈ W},
          ENNReal.ofReal (2 * (g x y) ^ 2) * ENNReal.ofReal (‖y - x‖ ^ (-(2 : ℝ) - α))
        ≤ ∫⁻ y in {y | y - x ∈ W},
            ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hWm] with y hyc
          have hmem : y ∈ coneAt Γ x := hcommon x hxV hyc
          have hjk : ENNReal.ofReal (‖y - x‖ ^ (-(2 : ℝ) - α)) ≤ ENNReal.ofReal Λ * k x y := by
            have h0 : ENNReal.ofReal (‖y - x‖ ^ (-(2 : ℝ) - α)) = jumpKernel 2 α x y := by
              rw [jumpKernel, norm_sub_rev]
              norm_num
            rw [h0]; exact QFS.jumpKernel_le_of_mem_coneAt hk hmem
          calc ENNReal.ofReal (2 * (g x y) ^ 2) *
                ENNReal.ofReal (‖y - x‖ ^ (-(2 : ℝ) - α))
              ≤ ENNReal.ofReal (2 * (f y - f x) ^ 2) * (ENNReal.ofReal Λ * k x y) := by
                rw [hg]; exact mul_le_mul' le_rfl hjk
            _ = ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) := by
                rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
                  ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
                ring
      _ ≤ ∫⁻ y, ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) :=
          lintegral_mono' Measure.restrict_le_self le_rfl
  -- split and combine
  set F : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
      ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α)) with hFdef
  have hsplit : ∫⁻ p in U ×ˢ U', F p
      = (∫⁻ p in Bad, F p) + ∫⁻ p in (U ×ˢ U') \ Bad, F p := by
    have hdisj : Disjoint Bad ((U ×ˢ U') \ Bad) := Set.disjoint_sdiff_right
    have hunion : Bad ∪ ((U ×ˢ U') \ Bad) = U ×ˢ U' := by
      rw [Set.union_sdiff_cancel]
      rw [hBaddef]
      exact Set.inter_subset_left
    calc ∫⁻ p in U ×ˢ U', F p
        = ∫⁻ p in Bad ∪ ((U ×ˢ U') \ Bad), F p := by rw [hunion]
      _ = (∫⁻ p in Bad, F p) + ∫⁻ p in (U ×ˢ U') \ Bad, F p :=
          lintegral_union ((hUm.prod hU'm).diff hBadm) hdisj
  rw [hsplit, mul_add]
  refine add_le_add ?_ ?_
  · refine le_trans (QFS.localPoincare_planar hvs hvt hϑ hϑ' hα hD hf U U' hBadm
      (by rw [hBaddef]; exact Set.inter_subset_left) (fun p hp => hp.2)) ?_
    exact add_le_add
      (mul_le_mul' le_rfl (hterm U (doubleCone vs ϑ) hUm hUs (isOpen_doubleCone vs ϑ)
        (fun x y => f y - f x) (fun x y => rfl)))
      (mul_le_mul' le_rfl (hterm U' (doubleCone vt ϑ) hU'm hUt (isOpen_doubleCone vt ϑ)
        (fun x y => f x - f y) (fun x y => by ring)))
  · have hg : ∫⁻ p in (U ×ˢ U') \ Bad, F p
        ≤ ENNReal.ofReal Λ * form Set.univ k f := by
      rw [hform, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine le_trans (lintegral_mono_ae ?_) (lintegral_mono' Measure.restrict_le_self le_rfl)
      filter_upwards [ae_restrict_mem ((hUm.prod hU'm).diff hBadm)] with p hp
      exact hgood p hp
    calc ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2 * ∫⁻ p in (U ×ˢ U') \ Bad, F p
        ≤ ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2 *
            (ENNReal.ofReal Λ * form Set.univ k f) := mul_le_mul' le_rfl hg
      _ = ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2 * ENNReal.ofReal Λ *
            form Set.univ k f := by ring
#print axioms solution
