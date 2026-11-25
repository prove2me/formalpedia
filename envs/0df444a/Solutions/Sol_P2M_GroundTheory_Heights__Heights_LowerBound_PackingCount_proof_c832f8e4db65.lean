-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_PackingCount_proof_c832f8e4db65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:07:59.625914+00:00
-- url     : https://prove2.me/submissions/348828d5-113d-4088-8a70-e56bacb664ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PPackingCount
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBound_PackingCount_card_mul_le_f6acee0bf2de

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
open MeasureTheory Metric
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBound
namespace PackingCount
theorem _root_.solution : PackingCount.Statement := by
  intro V _ _ L W lam r a h
  classical
  have : FiniteDimensional ℝ W :=
    Module.finite_of_finrank_pos (by rw [h.finrank_eq]; exact h.one_le_a)
  have hlam := h.lam_pos
  have hr : 0 < r := lt_of_lt_of_le hlam h.lam_le_r
  set B : ℝ := (1 + 2 * r / lam) ^ a with hB
  set S : Set V := {v | v ∈ L ∧ ‖v‖ < r} with hS

  have key : ∀ T : Finset V, ↑T ⊆ S → (T.card : ℝ) ≤ B := by
    intro T hT
    have hW : ∀ v ∈ T, v ∈ W := fun v hv => h.short_mem v (hT hv).1 (hT hv).2
    set T' : Finset W := T.subtype (· ∈ W)
    have hcard : T'.card = T.card := by
      rw [Finset.card_subtype, Finset.filter_true_of_mem hW]
    have hbd := PackingCount.card_mul_le T' hlam hr.le
      (fun x hx => by
        rw [Finset.mem_subtype] at hx
        rw [Submodule.coe_norm]
        exact (hT hx).2)
      (fun x hx y hy hxy => by
        rw [Finset.mem_subtype] at hx hy
        rw [Submodule.coe_norm, Submodule.coe_sub]
        apply h.lam_le_norm _ (h.sub_mem _ (hT hx).1 _ (hT hy).1)
        intro h0
        exact hxy (Subtype.ext (sub_eq_zero.mp h0)))
    rw [hcard, h.finrank_eq] at hbd
    have hpos : 0 < (lam / 2) ^ a := by positivity
    rw [← le_div_iff₀ hpos, ← div_pow] at hbd
    have he : (r + lam / 2) / (lam / 2) = 1 + 2 * r / lam := by
      field_simp
      ring
    rwa [he] at hbd
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨T, hT, hTc⟩ := (Set.not_finite.mp hinf).exists_subset_card_eq (⌈B⌉₊ + 1)
    have := key T hT
    rw [hTc] at this
    push_cast at this
    linarith [Nat.le_ceil B]
  have hsub : {v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ < r} ⊆ S := fun v hv => ⟨hv.1, hv.2.2⟩
  have hSB : (S.ncard : ℝ) ≤ B := by
    rw [Set.ncard_eq_toFinset_card S hfin]
    exact key _ (by simp)
  have hB3 : B ≤ (3 * r / lam) ^ a := by
    apply pow_le_pow_left₀ (by positivity)
    have : lam ≤ r := h.lam_le_r
    rw [show (1 : ℝ) + 2 * r / lam = (lam + 2 * r) / lam by field_simp]
    exact div_le_div_of_nonneg_right (by linarith) hlam.le
  refine ⟨hfin.subset hsub, ?_⟩
  calc (({v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ < r} : Set V).ncard : ℝ) ≤ S.ncard := by
        exact_mod_cast Set.ncard_le_ncard hsub hfin
    _ ≤ B := hSB
    _ ≤ (3 * r / lam) ^ a := hB3
end PackingCount
end GroundTheory.Heights₂.Heights.LowerBound
