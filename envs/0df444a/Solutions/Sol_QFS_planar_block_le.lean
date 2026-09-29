-- Prove2me | solution 1 for QFS.planar_block_le
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:25:08.756778+00:00
-- url     : https://prove2.me/submissions/0d03a4a7-1a7b-4acf-add8-f9eb8e5915f0

import Theorems.Thm_QFS_doubleCone_neg
import Theorems.Thm_QFS_formHs_le_form_of_commonDirection_on
import Theorems.Thm_QFS_formHs_le_form_planar_cross
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



namespace QFSNextProof_planar_block_le

@[simp] lemma perp2_apply_zero (w : EuclideanSpace ℝ (Fin 2)) : perp2 w 0 = -(w 1) := rfl

@[simp] lemma perp2_apply_one (w : EuclideanSpace ℝ (Fin 2)) : perp2 w 1 = w 0 := rfl

lemma real_inner_eq_two (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

lemma norm_sq_eq_two (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, real_inner_eq_two]
  ring

lemma decomp_two {w : EuclideanSpace ℝ (Fin 2)} (hw : ‖w‖ = 1)
    (x : EuclideanSpace ℝ (Fin 2)) :
    x = ⟪w, x⟫_ℝ • w + ⟪perp2 w, x⟫_ℝ • perp2 w := by
  have hw2 : (w 0) ^ 2 + (w 1) ^ 2 = 1 := by
    rw [← norm_sq_eq_two, hw]; norm_num
  refine euclidean_ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · simp only [real_inner_eq_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      perp2_apply_zero, perp2_apply_one]
    linear_combination (-(x 0)) * hw2
  · simp only [real_inner_eq_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      perp2_apply_zero, perp2_apply_one]
    linear_combination (-(x 1)) * hw2

lemma inner_perp2_eq_neg_cross (u x : EuclideanSpace ℝ (Fin 2)) :
    ⟪perp2 u, x⟫_ℝ = -cross2 x u := by
  rw [real_inner_eq_two, cross2]
  simp
  ring

lemma eq_or_eq_neg_of_cross2_eq_zero {v w : EuclideanSpace ℝ (Fin 2)} (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1) (h : cross2 v w = 0) : w = v ∨ w = -v := by
  have hperp : ⟪perp2 v, w⟫_ℝ = 0 := by
    rw [inner_perp2_eq_neg_cross]
    have hswap : cross2 w v = -cross2 v w := by rw [cross2, cross2]; ring
    rw [hswap, h, neg_zero, neg_zero]
  have hdec := decomp_two hv w
  rw [hperp, zero_smul, add_zero] at hdec
  have hnorm : |⟪v, w⟫_ℝ| = 1 := by
    have h1 : ‖w‖ = |⟪v, w⟫_ℝ| * ‖v‖ := by
      conv_lhs => rw [hdec]
      rw [norm_smul, Real.norm_eq_abs]
    rw [hv, hw, mul_one] at h1
    exact h1.symm
  rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hnorm with h1 | h1
  · left; rw [hdec, h1, one_smul]
  · right; rw [hdec, h1, neg_one_smul]

theorem cross2_ne_zero_or_carrier_eq {v w : EuclideanSpace ℝ (Fin 2)} (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1) (ϑ : ℝ) :
    cross2 v w ≠ 0 ∨ doubleCone w ϑ = doubleCone v ϑ := by
  by_cases h : cross2 v w = 0
  · refine Or.inr ?_
    rcases eq_or_eq_neg_of_cross2_eq_zero hv hw h with rfl | rfl
    · rfl
    · exact QFS.doubleCone_neg v ϑ
  · exact Or.inl h

lemma unitBallVol_ne_zero (d : ℕ) : unitBallVol d ≠ 0 := by
  rw [unitBallVol]
  exact (measure_closedBall_pos volume (0 : EuclideanSpace ℝ (Fin d)) one_pos).ne'



end QFSNextProof_planar_block_le
open QFSNextProof_planar_block_le

set_option autoImplicit false

theorem solution {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α)
    {Γ : Configuration (EuclideanSpace ℝ (Fin 2))} {Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (hmeas : CondMeas Γ)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2)
    (V W : DCone (EuclideanSpace ℝ (Fin 2))) (hVW : V.apex = W.apex) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∫⁻ p in {x | V.carrier ⊆ (Γ x).carrier} ×ˢ {x | W.carrier ⊆ (Γ x).carrier},
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
            ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))
        ≤ C * form Set.univ k f := by
  have hVpos : 0 < V.apex := V.apex_pos
  have hVle : V.apex ≤ π / 2 := V.apex_le
  have hUVm : MeasurableSet {x | V.carrier ⊆ (Γ x).carrier} := hmeas _
  have hUWm : MeasurableSet {x | W.carrier ⊆ (Γ x).carrier} := hmeas _
  have hsin : 0 < Real.sin V.apex :=
    Real.sin_pos_of_pos_of_lt_pi hVpos (by linarith [Real.pi_pos])
  rcases cross2_ne_zero_or_carrier_eq V.norm_axis W.norm_axis V.apex with hD | hcar
  · -- the axes are not parallel: a cross block
    have hUs : ∀ x ∈ {x | V.carrier ⊆ (Γ x).carrier}, doubleCone V.axis V.apex ⊆ (Γ x).carrier :=
      fun x hx => hx
    have hUt : ∀ y ∈ {x | W.carrier ⊆ (Γ x).carrier}, doubleCone W.axis V.apex ⊆ (Γ y).carrier := by
      intro y hy
      rw [hVW]
      exact hy
    have hmain := QFS.formHs_le_form_planar_cross V.norm_axis W.norm_axis hVpos hVle hα hD hk
      hUVm hUWm hUs hUt hf hkm
    set κ : ℝ≥0∞ := ENNReal.ofReal (Real.sin V.apex ^ 4 / 4) * unitBallVol 2 with hκ
    have hκ0 : κ ≠ 0 := by
      rw [hκ]
      exact mul_ne_zero (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)
        (unitBallVol_ne_zero 2)
    have hκtop : κ ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top QFS.unitBallVol_ne_top
    refine ⟨κ⁻¹ * (ENNReal.ofReal (planarConst V.axis W.axis V.apex α) * unitBallVol 2 *
        ENNReal.ofReal (2 * Λ) + ENNReal.ofReal (planarConst V.axis W.axis V.apex α) *
        unitBallVol 2 * ENNReal.ofReal (2 * Λ) +
        ENNReal.ofReal (Real.sin V.apex ^ 4 / 4) * unitBallVol 2 * ENNReal.ofReal Λ), ?_, ?_⟩
    · refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hκ0) ?_
      refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨?_, ?_⟩, ?_⟩ <;>
        exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top QFS.unitBallVol_ne_top)
          ENNReal.ofReal_ne_top
    · calc ∫⁻ p in {x | V.carrier ⊆ (Γ x).carrier} ×ˢ {x | W.carrier ⊆ (Γ x).carrier},
            ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
              ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))
          = κ⁻¹ * (κ * ∫⁻ p in {x | V.carrier ⊆ (Γ x).carrier} ×ˢ
              {x | W.carrier ⊆ (Γ x).carrier},
              ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
                ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hκ0 hκtop, one_mul]
        _ ≤ κ⁻¹ * (ENNReal.ofReal (planarConst V.axis W.axis V.apex α) * unitBallVol 2 *
              (ENNReal.ofReal (2 * Λ) * form Set.univ k f)
            + ENNReal.ofReal (planarConst V.axis W.axis V.apex α) * unitBallVol 2 *
              (ENNReal.ofReal (2 * Λ) * form Set.univ k f)
            + ENNReal.ofReal (Real.sin V.apex ^ 4 / 4) * unitBallVol 2 * ENNReal.ofReal Λ *
              form Set.univ k f) := mul_le_mul' le_rfl hmain
        _ = κ⁻¹ * (ENNReal.ofReal (planarConst V.axis W.axis V.apex α) * unitBallVol 2 *
              ENNReal.ofReal (2 * Λ) + ENNReal.ofReal (planarConst V.axis W.axis V.apex α) *
              unitBallVol 2 * ENNReal.ofReal (2 * Λ) +
              ENNReal.ofReal (Real.sin V.apex ^ 4 / 4) * unitBallVol 2 * ENNReal.ofReal Λ) *
            form Set.univ k f := by ring
  · -- the two cones coincide: a diagonal block
    have hcarrier : W.carrier = V.carrier := by
      rw [DCone.carrier, DCone.carrier, ← hVW]
      exact hcar
    have hsets : {x | W.carrier ⊆ (Γ x).carrier} = {x | V.carrier ⊆ (Γ x).carrier} := by
      rw [hcarrier]
    have hcommon : ∀ x ∈ {x | V.carrier ⊆ (Γ x).carrier},
        cone V.axis V.apex ⊆ (Γ x).carrier :=
      fun x hx => le_trans Set.subset_union_left hx
    have hmain := QFS.formHs_le_form_of_commonDirection_on V.norm_axis hVpos hVle hα two_pos hk
      hUVm hcommon hf hkm
    refine ⟨(unitBallVol 2)⁻¹ * (ENNReal.ofReal (2 * Λ) *
      (ENNReal.ofReal (chainConst 2 V.apex α) + ENNReal.ofReal (chainConst_prime 2 V.apex α)) *
      unitBallVol 2), ?_, ?_⟩
    · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (unitBallVol_ne_zero 2))
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩))
          QFS.unitBallVol_ne_top)
    · rw [hsets]
      have hconv : ∫⁻ p in {x | V.carrier ⊆ (Γ x).carrier} ×ˢ
          {x | V.carrier ⊆ (Γ x).carrier},
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
            ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 : ℝ) - α))
          = ∫⁻ p in {x | V.carrier ⊆ (Γ x).carrier} ×ˢ {x | V.carrier ⊆ (Γ x).carrier},
            ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel 2 α p.1 p.2 := by
        refine lintegral_congr fun p => ?_
        rw [jumpKernel]
        norm_num
      rw [hconv]
      calc ∫⁻ p in {x | V.carrier ⊆ (Γ x).carrier} ×ˢ {x | V.carrier ⊆ (Γ x).carrier},
            ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel 2 α p.1 p.2
          = (unitBallVol 2)⁻¹ * (unitBallVol 2 *
              ∫⁻ p in {x | V.carrier ⊆ (Γ x).carrier} ×ˢ {x | V.carrier ⊆ (Γ x).carrier},
                ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel 2 α p.1 p.2) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel (unitBallVol_ne_zero 2) QFS.unitBallVol_ne_top,
              one_mul]
        _ ≤ (unitBallVol 2)⁻¹ * (ENNReal.ofReal (2 * Λ) *
              (ENNReal.ofReal (chainConst 2 V.apex α) +
                ENNReal.ofReal (chainConst_prime 2 V.apex α)) *
              unitBallVol 2 * form Set.univ k f) := mul_le_mul' le_rfl hmain
        _ = (unitBallVol 2)⁻¹ * (ENNReal.ofReal (2 * Λ) *
              (ENNReal.ofReal (chainConst 2 V.apex α) +
                ENNReal.ofReal (chainConst_prime 2 V.apex α)) * unitBallVol 2) *
            form Set.univ k f := by ring
#print axioms solution
