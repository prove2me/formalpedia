-- Prove2me | solution 1 for PositivityTheory.ThKF0.Grow.sobAbs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:09:56.739683+00:00
-- url     : https://prove2.me/submissions/77e4549c-175c-47da-b2dd-0f8cf4d8d30f

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSobA
import Theorems.Thm_PositivityTheory_ThKF0_Grow_oneD
import Theorems.Thm_PositivityTheory_ThKF0_Grow_lintegral_fin_succ
import Theorems.Thm_PositivityTheory_ThKF0_Grow_continuous_sumSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Grow
open scoped ENNReal
open MeasureTheory
variable {X W : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
namespace PositivityTheory.ThKF0.Grow
theorem _root_.solution {S : Set (X → ℂ)} (hS : ∀ Θ ∈ S, Continuous Θ) {dd : W → (X → ℂ) → X → ℂ}
    (hd : ∀ w, ∀ Θ ∈ S, dd w Θ ∈ S) (D : ℕ) : ∀ (ws : Fin D → W) (e : Fin D → ℝ →+ X), (∀ i, Continuous (e i)) →
      (∀ i, ∀ Θ ∈ S, ∀ x, HasDerivAt (fun t => Θ (x + e i t)) (dd (ws i) Θ x) 0) →
      ∃ L : List (List W), ∀ Θ ∈ S, ∀ x, ‖Θ x‖ₑ ^ 2 ≤ 2 ^ D * ∫⁻ t : Fin D → ℝ, sumSq dd L Θ (x + ∑ i, e i (t i)) := by
  induction D with
  | zero =>
    intro ws e _ _
    refine ⟨[[]], fun Θ _ x => ?_⟩
    simp [sumSq, volume_pi]
  | succ D ih =>
    intro ws e he hder
    obtain ⟨L, hL⟩ := ih (fun i => ws i.succ) (fun i => e i.succ) (fun i => he _) (fun i => hder _)
    refine ⟨L ++ L.map (· ++ [ws 0]), fun Θ hΘ x => ?_⟩
    have hΘ' := hd (ws 0) Θ hΘ
    have hline : Continuous fun s => x + e 0 s := continuous_const.add (he 0)
    have h1 := oneD (fun s => Θ (x + e 0 s)) (fun s => dd (ws 0) Θ (x + e 0 s)) ((hS _ hΘ').comp hline) fun t => by
      have h := hder 0 Θ hΘ (x + e 0 t)
      have h' : HasDerivAt (fun r => Θ (x + e 0 t + e 0 r)) (dd (ws 0) Θ (x + e 0 t)) (t - t) := by rwa [sub_self]
      have h'' := h'.comp_sub_const t t
      refine h''.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
      simp only [map_sub]
      congr 1
      abel
    simp only [map_zero, add_zero] at h1
    have hsum : ∀ y, sumSq dd (L ++ L.map (· ++ [ws 0])) Θ y = sumSq dd L Θ y + sumSq dd L (dd (ws 0) Θ) y := fun y => by
      simp [sumSq, List.map_map, Function.comp_def, List.foldr_append]
    have hc : ∀ {D : ℕ} (e : Fin D → ℝ →+ X), (∀ i, Continuous (e i)) → ∀ x : X,
        Continuous fun t : Fin D → ℝ => x + ∑ i, e i (t i) := fun e he x =>
      continuous_const.add (continuous_finsetSum _ fun i _ => (he i).comp (continuous_apply i))
    have hm : ∀ {D : ℕ} (e : Fin D → ℝ →+ X), (∀ i, Continuous (e i)) → ∀ (x : X) (L : List (List W)),
        Measurable fun t : Fin D → ℝ => sumSq dd L Θ (x + ∑ i, e i (t i)) := fun e he x L =>
      ((continuous_sumSq hS hd L hΘ).comp (hc e he x)).measurable
    rw [lintegral_fin_succ _ (hm e he x _)]
    refine h1.trans ?_
    rw [pow_succ', mul_assoc]
    gcongr
    rw [← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono fun s => ?_
    refine (add_le_add (hL Θ hΘ _) (hL _ hΘ' _)).trans (le_of_eq ?_)
    rw [← mul_add, ← lintegral_add_left (hm (fun i => e i.succ) (fun i => he _) _ _)]
    congr 1
    refine lintegral_congr fun t => ?_
    simp only [hsum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_assoc]
end PositivityTheory.ThKF0.Grow
