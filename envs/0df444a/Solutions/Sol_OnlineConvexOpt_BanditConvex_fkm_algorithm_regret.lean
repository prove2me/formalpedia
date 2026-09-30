-- Prove2me | solution 1 for OnlineConvexOpt.BanditConvex.fkm_algorithm_regret
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T22:11:47.730593+00:00
-- url     : https://prove2.me/submissions/fecf0797-22c8-4005-ac9c-fcc2d95a95da

import Mathlib
import Definitions.Def_OnlineConvexOpt_BanditConvex_UniformOnUnitSphere
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open MeasureTheory


namespace OnlineConvexOpt.BanditConvex

abbrev E1 := EuclideanSpace ℝ (Fin 1)

lemma e1_eq (v : E1) : v = (v 0) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
  ext i; fin_cases i; simp

lemma iso_single (L : E1 ≃ₗᵢ[ℝ] E1) :
    L (EuclideanSpace.single 0 1) = EuclideanSpace.single 0 1 ∨
    L (EuclideanSpace.single 0 1) = -EuclideanSpace.single 0 1 := by
  set a : E1 := EuclideanSpace.single 0 1 with ha
  have hn : ‖L a‖ = 1 := by rw [L.norm_map]; simp [a]
  have h1 := e1_eq (L a)
  rw [h1, norm_smul] at hn
  have : ‖a‖ = 1 := by simp [a]
  rw [this, mul_one, Real.norm_eq_abs] at hn
  rcases abs_eq (zero_le_one) |>.mp hn with h | h
  · left; rw [h1, h, one_smul]
  · right; rw [h1, h, neg_one_smul]

universe uΩ

theorem fkm_counter : ¬ (∀
    {n : ℕ} (hn : 0 < n)
    {Ω : Type uΩ} [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (K Kδ : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K)
    (hKball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    (D G : ℝ) (hDpos : 0 < D) (hGpos : 0 < G)
    (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (T : ℕ) (hT : 1 ≤ T)
    (η δ : ℝ) (hη : η = D / ((n : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ)))
    (hδ : δ = 1 / (T : ℝ) ^ (1 / 4 : ℝ))
    (hKδ : ∀ z : EuclideanSpace ℝ (Fin n), z ∈ Kδ ↔ (1 - δ)⁻¹ • z ∈ K)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfG : ∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y)
    (hfbdd : ∀ t, ∀ x ∈ K, |f t x| ≤ 1)
    (x y u g : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (hx0 : ∀ ω, x 0 ω = 0)
    (hu : ∀ t, IsUniformOnUnitSphere Prob (u t))
    (hy : ∀ t ω, y t ω = x t ω + δ • u t ω)
    (hg : ∀ t ω, g t ω = ((n : ℝ) / δ * f t (y t ω)) • u t ω)
    (hstep : ∀ t ω,
      OnlineConvexOpt.FirstOrder.IsMetricProjection Kδ (x t ω - η • g t ω) (x (t + 1) ω))
    (hint : ∀ t, Integrable (fun ω => f t (y t ω)) Prob),
    (∑ t ∈ Finset.range T, ∫ ω, f t (y t ω) ∂Prob) - ⨅ z ∈ K, ∑ t ∈ Finset.range T, f t z ≤
      9 * n * D * G * (T : ℝ) ^ (3 / 4 : ℝ)) := by
  intro H
  let a : E1 := EuclideanSpace.single 0 1
  have ha : ‖a‖ = 1 := by simp [a]
  let Ω : Type uΩ := ULift.{uΩ} Bool
  let _ : MeasurableSpace Ω := ⊤
  let U : Ω → E1 := fun ω => if ω.down then a else -a
  have hUm : Measurable U := fun _ _ => trivial
  let P : Measure Ω := (1/2 : ENNReal) • (Measure.dirac ⟨true⟩ + Measure.dirac ⟨false⟩)
  have hP1 : P Set.univ = 1 := by
    simp only [P, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two, ENNReal.div_mul_cancel] <;> norm_num
  have : IsProbabilityMeasure P := ⟨hP1⟩
  have hmapU : Measure.map U P = (1/2 : ENNReal) • (Measure.dirac a + Measure.dirac (-a)) := by
    simp only [P, Measure.map_smul, Measure.map_add _ _ hUm, Measure.map_dirac' hUm]
    simp [U]
  have hunif : IsUniformOnUnitSphere P U := by
    refine ⟨Filter.Eventually.of_forall (fun ω => ?_), fun L => ?_⟩
    · simp only [U, mem_sphere_iff_norm, sub_zero]
      split_ifs <;> simp [ha]
    · have hLm : Measurable (fun ω => L (U ω)) := fun _ _ => trivial
      have hL : Measurable L := L.continuous.measurable
      rw [hmapU, show (fun ω => L (U ω)) = L ∘ U from rfl, ← Measure.map_map hL hUm, hmapU,
        Measure.map_smul, Measure.map_add _ _ hL, Measure.map_dirac' hL, Measure.map_dirac' hL]
      simp only [map_neg]
      rcases iso_single L with h | h
      · rw [h]
      · rw [h, neg_neg, add_comm]
  have h := H (n := 1) one_pos (Prob := P) (Metric.closedBall 0 1) Set.univ
    (convex_closedBall 0 1) subset_rfl 2 (1/100) two_pos (by norm_num)
    (fun p hp q hq => by
      rw [Metric.mem_closedBall] at hp hq
      linarith [dist_triangle_right p q 0])
    1 le_rfl 2 1 (by simp) (by simp)
    (fun z => by simp)
    (fun _ _ => 1) (fun t p _ q _ => by simp) (fun t p _ => by simp)
    (fun t ω => -((2:ℝ) * t) • U ω) (fun t ω => -((2:ℝ) * t) • U ω + (1:ℝ) • U ω)
    (fun _ => U) (fun _ => U) (fun ω => by simp) (fun _ => hunif) (fun t ω => rfl)
    (fun t ω => by simp)
    (fun t ω => ⟨trivial, fun z _ => by
      rw [show -((2:ℝ) * t) • U ω - (2:ℝ) • U ω = -((2:ℝ) * ((t + 1 : ℕ) : ℝ)) • U ω by
        push_cast; module]
      simp⟩)
    (fun t => integrable_const _)
  have hbdd : BddBelow (Set.range fun z : E1 =>
      ⨅ (_ : z ∈ Metric.closedBall (0 : E1) 1),
        ∑ t ∈ Finset.range 1, (fun (_ : ℕ) (_ : E1) => (1:ℝ)) t z) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨z, rfl⟩
    dsimp only
    by_cases hz : z ∈ Metric.closedBall (0 : E1) 1
    · rw [ciInf_pos hz]; simp
    · rw [ciInf_neg hz]; simp
  have hout : (2 : ℝ) • a ∉ Metric.closedBall (0 : E1) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, ha]; norm_num
  have hle : (⨅ z ∈ Metric.closedBall (0 : E1) 1,
      ∑ t ∈ Finset.range 1, (fun (_ : ℕ) (_ : E1) => (1:ℝ)) t z) ≤ 0 := by
    refine (ciInf_le hbdd ((2 : ℝ) • a)).trans ?_
    rw [ciInf_neg hout, Real.sInf_empty]
  simp at h hle
  norm_num at h
  linarith

end OnlineConvexOpt.BanditConvex

open OnlineConvexOpt.BanditConvex


theorem solution : ¬ (∀
    {n : ℕ} (hn : 0 < n)
    {Ω : Type} [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (K Kδ : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K)
    (hKball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    (D G : ℝ) (hDpos : 0 < D) (hGpos : 0 < G)
    (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (T : ℕ) (hT : 1 ≤ T)
    (η δ : ℝ) (hη : η = D / ((n : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ)))
    (hδ : δ = 1 / (T : ℝ) ^ (1 / 4 : ℝ))
    (hKδ : ∀ z : EuclideanSpace ℝ (Fin n), z ∈ Kδ ↔ (1 - δ)⁻¹ • z ∈ K)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfG : ∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y)
    (hfbdd : ∀ t, ∀ x ∈ K, |f t x| ≤ 1)
    (x y u g : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (hx0 : ∀ ω, x 0 ω = 0)
    (hu : ∀ t, IsUniformOnUnitSphere Prob (u t))
    (hy : ∀ t ω, y t ω = x t ω + δ • u t ω)
    (hg : ∀ t ω, g t ω = ((n : ℝ) / δ * f t (y t ω)) • u t ω)
    (hstep : ∀ t ω,
      OnlineConvexOpt.FirstOrder.IsMetricProjection Kδ (x t ω - η • g t ω) (x (t + 1) ω))
    (hint : ∀ t, Integrable (fun ω => f t (y t ω)) Prob),
    (∑ t ∈ Finset.range T, ∫ ω, f t (y t ω) ∂Prob) - ⨅ z ∈ K, ∑ t ∈ Finset.range T, f t z ≤
      9 * n * D * G * (T : ℝ) ^ (3 / 4 : ℝ)) :=
  OnlineConvexOpt.BanditConvex.fkm_counter.{0}
