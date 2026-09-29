-- Prove2me | solution 1 for VectorPayoffs.Convex.convex_blackwell_condition
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:28:03.263359+00:00
-- url     : https://prove2.me/submissions/b8375f8e-2169-462b-ad5a-9f3f2a90176f

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game

open MeasureTheory

namespace VectorPayoffs.Convex

theorem aux_cbc_minimax {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (a : Fin r → Fin s → ℝ) (c : ℝ)
    (h : ∀ q ∈ stdSimplex ℝ (Fin s), ∃ l ∈ stdSimplex ℝ (Fin r),
      ∑ i, l i * ∑ j, q j * a i j ≤ c) :
    ∃ p ∈ stdSimplex ℝ (Fin r), ∀ j, ∑ i, p i * a i j ≤ c := by
  set f : (Fin r → ℝ) → (Fin s → ℝ) → ℝ := fun p q => ∑ i, p i * ∑ j, q j * a i j with hf
  have neX : (stdSimplex ℝ (Fin r)).Nonempty :=
    ⟨Pi.single ⟨0, hr⟩ 1, single_mem_stdSimplex ℝ _⟩
  have neY : (stdSimplex ℝ (Fin s)).Nonempty :=
    ⟨Pi.single ⟨0, hs⟩ 1, single_mem_stdSimplex ℝ _⟩
  have hfy : ∀ y ∈ stdSimplex ℝ (Fin s),
      LowerSemicontinuousOn (fun x => f x y) (stdSimplex ℝ (Fin r)) := by
    intro y _
    have : Continuous (fun x => f x y) := by simp only [hf]; fun_prop
    exact this.lowerSemicontinuous.lowerSemicontinuousOn _
  have hfx : ∀ x ∈ stdSimplex ℝ (Fin r),
      UpperSemicontinuousOn (fun y => f x y) (stdSimplex ℝ (Fin s)) := by
    intro x _
    have : Continuous (fun y => f x y) := by simp only [hf]; fun_prop
    exact this.upperSemicontinuous.upperSemicontinuousOn _
  have hfy' : ∀ y ∈ stdSimplex ℝ (Fin s),
      QuasiconvexOn ℝ (stdSimplex ℝ (Fin r)) (fun x => f x y) := by
    intro y _
    refine ConvexOn.quasiconvexOn ⟨convex_stdSimplex ℝ _, ?_⟩
    intro x₁ _ x₂ _ α β _ _ _
    apply le_of_eq
    simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  have hfx' : ∀ x ∈ stdSimplex ℝ (Fin r),
      QuasiconcaveOn ℝ (stdSimplex ℝ (Fin s)) (fun y => f x y) := by
    intro x _
    refine ConcaveOn.quasiconcaveOn ⟨convex_stdSimplex ℝ _, ?_⟩
    intro y₁ _ y₂ _ α β _ _ _
    apply le_of_eq
    simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm]
  obtain ⟨p, hp, q, hq, hsad⟩ := Sion.exists_isSaddlePointOn neX (convex_stdSimplex ℝ _)
    (isCompact_stdSimplex ℝ _) hfy hfy' (convex_stdSimplex ℝ _) neY (isCompact_stdSimplex ℝ _)
    hfx hfx'
  obtain ⟨l, hl, hlc⟩ := h q hq
  refine ⟨p, hp, fun j => ?_⟩
  have h1 := hsad l hl (Pi.single j 1) (single_mem_stdSimplex ℝ j)
  have e : f p (Pi.single j 1) = ∑ i, p i * a i j := by
    simp [hf, Pi.single_apply]
  rw [← e]
  exact h1.trans hlc

theorem aux_cbc_hull_mem {N r : ℕ} (v : Fin r → E N) (z : E N)
    (hz : z ∈ convexHull ℝ (Set.range v)) :
    ∃ l ∈ stdSimplex ℝ (Fin r), z = ∑ i, l i • v i := by
  have hsub : convexHull ℝ (Set.range v) ⊆
      {z | ∃ l ∈ stdSimplex ℝ (Fin r), z = ∑ i, l i • v i} := by
    refine convexHull_min ?_ ?_
    · rintro _ ⟨i, rfl⟩
      exact ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, by simp [Pi.single_apply]⟩
    · rintro _ ⟨l₁, hl₁, rfl⟩ _ ⟨l₂, hl₂, rfl⟩ α β hα hβ hαβ
      refine ⟨α • l₁ + β • l₂, convex_stdSimplex ℝ _ hl₁ hl₂ hα hβ hαβ, ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
        Finset.sum_add_distrib, Finset.smul_sum]
  exact hsub hz

end VectorPayoffs.Convex

open MeasureTheory
open VectorPayoffs.Convex

theorem solution {N r s : ℕ} (G : Game N r s) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (S : Set (E N)) (hS : IsClosed S) (hSc : Convex ℝ S)
    (hT : ∀ q ∈ stdSimplex ℝ (Fin s), (S ∩ G.T q).Nonempty) :
    ∀ x ∉ S, ∃ p ∈ stdSimplex ℝ (Fin r), G.BlackwellCondition S p x := by
  intro x _
  have hSne : S.Nonempty := by
    obtain ⟨z, hz, _⟩ := hT (Pi.single ⟨0, hs⟩ 1) (single_mem_stdSimplex ℝ _)
    exact ⟨z, hz⟩
  obtain ⟨y, hyS, hy⟩ := exists_norm_eq_iInf_of_complete_convex hSne hS.isComplete hSc x
  have hproj := (norm_eq_iInf_iff_real_inner_le_zero hSc hyS).1 hy
  obtain ⟨p, hp, hpj⟩ := aux_cbc_minimax hr hs (fun i j => inner ℝ (x - y) (G.mbar i j))
    (inner ℝ (x - y) y) (by
      intro q hq
      obtain ⟨z, hzS, hzT⟩ := hT q hq
      obtain ⟨l, hl, rfl⟩ := aux_cbc_hull_mem _ z hzT
      refine ⟨l, hl, ?_⟩
      have h1 := hproj _ hzS
      rw [inner_sub_right] at h1
      simp only [inner_sum, inner_smul_right] at h1
      linarith)
  refine ⟨p, hp, y, hyS, ?_, ?_⟩
  · intro z hz
    rw [dist_eq_norm, dist_eq_norm, hy]
    exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨z, hz⟩ : S)
  · intro w hw
    have hlin : IsLinearMap ℝ (fun w : E N => inner ℝ (x - y) w) :=
      ⟨fun a b => inner_add_right _ a b, fun c a => by simp [inner_smul_right]⟩
    have hsub : G.R p ⊆ {w | inner ℝ (x - y) w ≤ inner ℝ (x - y) y} := by
      refine convexHull_min ?_ (convex_halfSpace_le hlin _)
      rintro _ ⟨j, rfl⟩
      simp only [Set.mem_ofPred_eq, inner_sum, inner_smul_right]
      exact hpj j
    have h2 := hsub hw
    simp only [Set.mem_ofPred_eq] at h2
    rw [inner_sub_right]
    linarith
