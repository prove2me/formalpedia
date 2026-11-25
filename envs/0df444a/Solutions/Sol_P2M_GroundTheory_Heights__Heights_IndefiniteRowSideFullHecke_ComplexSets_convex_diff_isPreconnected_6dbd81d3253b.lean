-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_convex_diff_isPreconnected_6dbd81d3253b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:09.542484+00:00
-- url     : https://prove2.me/submissions/97c691f2-5cbe-49ef-9074-f0de897030e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHausdorffNullComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHausdorffNullComplementConnected
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_segment_hits_image_null_7f2307f5f41c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Metric MeasureTheory Set Relation
open scoped NNReal ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution [FiniteDimensional ℝ E] {k : ℕ}
    (hk : Module.finrank ℝ E = k + 1) {C : Set E} (hC : μH[(k : ℝ)] C = 0) {B : Set E}
    (hBo : IsOpen B) (hBc : Convex ℝ B) : IsPreconnected (B \ C) := by
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  by_cases hxy : x = y
  · subst hxy
    exact ⟨{x}, singleton_subset_iff.2 hx, rfl, rfl, isPreconnected_singleton⟩
  let φ : E ≃L[ℝ] (Fin (k + 1) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [hk, Module.finrank_fin_fun])
  obtain ⟨i, hi⟩ : ∃ i, φ x i ≠ φ y i := by
    by_contra h
    push Not at h
    exact hxy (φ.injective (funext h))
  let ℓ : E →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp (φ : E →L[ℝ] (Fin (k + 1) → ℝ))
  let g : E →L[ℝ] (Fin k → ℝ) :=
    (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (i.succAbove j)).comp
      (φ : E →L[ℝ] (Fin (k + 1) → ℝ))
  have hℓ : ∀ z, ℓ z = φ z i := fun z => rfl
  have hg : ∀ z, g z = Fin.removeNth i (φ z) := fun z => rfl
  have hαx : (φ x i + φ y i) / 2 ≠ ℓ x := by rw [hℓ]; intro h; apply hi; linarith
  have hαy : (φ x i + φ y i) / 2 ≠ ℓ y := by rw [hℓ]; intro h; apply hi; linarith
  have hvol : (volume : Measure (Fin k → ℝ)) = μH[(k : ℝ)] := by
    have := hausdorffMeasure_pi_real (ι := Fin k)
    rw [Fintype.card_fin] at this
    exact this.symm
  have hS0 : volume (g '' {m | ℓ m = (φ x i + φ y i) / 2 ∧ (segment ℝ x m ∩ C).Nonempty} ∪
      g '' {m | ℓ m = (φ x i + φ y i) / 2 ∧ (segment ℝ y m ∩ C).Nonempty}) = 0 := by
    rw [hvol]
    exact measure_union_null (segment_hits_image_null hx.2 ℓ hαx g (Nat.cast_nonneg k) hC)
      (segment_hits_image_null hy.2 ℓ hαy g (Nat.cast_nonneg k) hC)
  let ψ : (Fin k → ℝ) → E := fun w => φ.symm (Fin.insertNth i ((φ x i + φ y i) / 2) w)
  have hψc : Continuous ψ :=
    φ.symm.continuous.comp (continuous_const.finInsertNth i continuous_id)
  have hz₀ : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ B :=
    hBc hx.1 hy.1 (by norm_num) (by norm_num) (by norm_num)
  have hψz₀ : ψ (g ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y := by
    have h1 : φ ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) i = (φ x i + φ y i) / 2 := by
      simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    simp only [ψ, hg]
    rw [← h1, Fin.insertNth_self_removeNth, ContinuousLinearEquiv.symm_apply_apply]
  have hWpos : 0 < volume (ψ ⁻¹' B) :=
    (hBo.preimage hψc).measure_pos volume ⟨_, show ψ _ ∈ B from hψz₀ ▸ hz₀⟩
  obtain ⟨w, hwB, hwS⟩ := nonempty_of_measure_ne_zero
    ((measure_sdiff_null hS0).symm ▸ hWpos.ne' : volume (ψ ⁻¹' B \ _) ≠ 0)
  have hφm : φ (ψ w) = Fin.insertNth i ((φ x i + φ y i) / 2) w := by
    simp only [ψ, ContinuousLinearEquiv.apply_symm_apply]
  have hℓm : ℓ (ψ w) = (φ x i + φ y i) / 2 := by rw [hℓ, hφm, Fin.insertNth_apply_same]
  have hgm : g (ψ w) = w := by rw [hg, hφm, Fin.removeNth_insertNth]
  have hxm : segment ℝ x (ψ w) ⊆ B \ C := fun c hc =>
    ⟨hBc.segment_subset hx.1 hwB hc, fun hcC => hwS (Or.inl ⟨ψ w, ⟨hℓm, c, hc, hcC⟩, hgm⟩)⟩
  have hmy : segment ℝ (ψ w) y ⊆ B \ C := fun c hc =>
    ⟨hBc.segment_subset hwB hy.1 hc, fun hcC =>
      hwS (Or.inr ⟨ψ w, ⟨hℓm, c, segment_symm ℝ (ψ w) y ▸ hc, hcC⟩, hgm⟩)⟩
  exact ⟨segment ℝ x (ψ w) ∪ segment ℝ (ψ w) y, union_subset hxm hmy,
    Or.inl (left_mem_segment ℝ x (ψ w)), Or.inr (right_mem_segment ℝ (ψ w) y),
    (convex_segment x (ψ w)).isPreconnected.union (ψ w) (right_mem_segment ℝ x (ψ w))
      (left_mem_segment ℝ (ψ w) y) (convex_segment (ψ w) y).isPreconnected⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
