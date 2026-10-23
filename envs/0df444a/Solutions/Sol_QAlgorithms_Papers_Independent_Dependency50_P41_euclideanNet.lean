-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P41.euclideanNet
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:59:18.708739+00:00
-- url     : https://prove2.me/submissions/040e4078-ca96-44df-8251-8a9ed1fac217

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41

noncomputable section

namespace X7VNet

open MeasureTheory Metric Module

attribute [local instance] Classical.propDecidable Classical.decEq

variable {d : ℕ}

local notation "E" => EuclideanSpace ℂ (Fin d)

lemma finrank_E : finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]

def Sep (eps : ℝ) (S : Finset (EuclideanSpace ℂ (Fin d))) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, s ≠ t → eps < ‖s - t‖

lemma packing (D eps : ℝ) (hD : 0 < D) (heps : 0 < eps)
    (S : Finset (EuclideanSpace ℂ (Fin d))) (hS : ∀ s ∈ S, ‖s‖ ≤ D) (hsep : Sep eps S) :
    (S.card : ℝ) ≤ (2 * D / eps + 1) ^ (2 * d) := by
  let μ : Measure (EuclideanSpace ℂ (Fin d)) := Measure.addHaar
  set r := eps / 2 with hr
  have hr0 : 0 < r := by positivity
  set R := D + eps / 2 with hR
  have hR0 : 0 < R := by positivity
  have hdisj : (S : Set (EuclideanSpace ℂ (Fin d))).PairwiseDisjoint (fun s => ball s r) := by
    intro s hs t ht hst
    rw [Function.onFun, Set.disjoint_left]
    intro x hxs hxt
    rw [mem_ball] at hxs hxt
    have := hsep s hs t ht hst
    have h2 : ‖s - t‖ ≤ dist x s + dist x t := by
      rw [dist_eq_norm, dist_eq_norm]
      calc ‖s - t‖ = ‖(x - t) - (x - s)‖ := by congr 1; abel
        _ ≤ ‖x - t‖ + ‖x - s‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    linarith
  have hsub : (⋃ s ∈ S, ball s r) ⊆ ball (0 : EuclideanSpace ℂ (Fin d)) R := by
    intro x hx
    simp only [Set.mem_iUnion, mem_ball] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    rw [mem_ball, dist_zero_right]
    have := hS s hs
    rw [dist_eq_norm] at hxs
    calc ‖x‖ = ‖(x - s) + s‖ := by congr 1; abel
      _ ≤ ‖x - s‖ + ‖s‖ := norm_add_le _ _
      _ < r + D := by linarith
      _ = R := by rw [hR, hr]; ring
  have hmeas := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hdisj (fun s _ => measurableSet_ball)] at hmeas
  simp only [Measure.addHaar_ball_of_pos μ _ hr0, Measure.addHaar_ball_of_pos μ _ hR0,
    Finset.sum_const, nsmul_eq_mul] at hmeas
  set c := μ (ball 0 1)
  have hc0 : c ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hct : c ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc] at hmeas
  have h1 := (ENNReal.mul_le_mul_iff_left hc0 hct).mp hmeas
  rw [show ((S.card : ENNReal)) = ENNReal.ofReal (S.card : ℝ) by simp,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  rw [finrank_E] at h1
  have hrn : 0 < r ^ (2 * d) := by positivity
  have : (2 * D / eps + 1) = R / r := by
    rw [hR, hr]; field_simp
  rw [this, div_pow, le_div_iff₀ hrn]
  exact h1

lemma main (D eps : ℝ) (hD : 0 < D) (heps : 0 < eps)
    (T : Set (EuclideanSpace ℂ (Fin d))) (hT : ∀ v ∈ T, ‖v‖ ≤ D) :
    ∃ net : Finset (EuclideanSpace ℂ (Fin d)),
      (∀ w ∈ net, w ∈ T) ∧
      (net.card : ℝ) ≤ (2 * D / eps + 1) ^ (2 * d) ∧
      ∀ v ∈ T, ∃ w ∈ net, ‖v - w‖ ≤ eps := by
  let N : ℕ := ⌊(2 * D / eps + 1) ^ (2 * d)⌋₊
  let P : ℕ → Prop := fun n => ∃ S : Finset (EuclideanSpace ℂ (Fin d)),
    (∀ w ∈ S, w ∈ T) ∧ Sep eps S ∧ S.card = n
  have hbound : ∀ S : Finset (EuclideanSpace ℂ (Fin d)), (∀ w ∈ S, w ∈ T) → Sep eps S →
      S.card ≤ N := by
    intro S hST hS
    apply Nat.le_floor
    exact packing D eps hD heps S (fun s hs => hT s (hST s hs)) hS
  have hP0 : P 0 := ⟨∅, by simp, by simp [Sep], rfl⟩
  have hm : P (Nat.findGreatest P N) := Nat.findGreatest_spec (Nat.zero_le N) hP0
  obtain ⟨S, hST, hS, hcard⟩ := hm
  refine ⟨S, hST, packing D eps hD heps S (fun s hs => hT s (hST s hs)) hS, ?_⟩
  intro v hv
  by_contra hcon
  push Not at hcon
  have hvS : v ∉ S := by
    intro hvS
    have := hcon v hvS
    simp at this
    linarith
  have hsep' : Sep eps (insert v S) := by
    intro s hs t ht hst
    rw [Finset.mem_insert] at hs ht
    rcases hs with rfl | hs <;> rcases ht with rfl | ht
    · exact absurd rfl hst
    · exact hcon t ht
    · rw [norm_sub_rev]; exact hcon s hs
    · exact hS s hs t ht hst
  have hST' : ∀ w ∈ insert v S, w ∈ T := by
    intro w hw
    rw [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact hv
    · exact hST w hw
  have hc' : (insert v S).card = Nat.findGreatest P N + 1 := by
    rw [Finset.card_insert_of_notMem hvS, hcard]
  have hle : Nat.findGreatest P N + 1 ≤ N := hc' ▸ hbound _ hST' hsep'
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hle ⟨_, hST', hsep', hc'⟩

end X7VNet

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P41

open scoped ComplexConjugate Matrix ComplexOrder

open Filter

end QAlgorithms.Papers.Independent.Dependency50.P41

open scoped ComplexConjugate Matrix ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (d : ℕ) (hd : 0 < d) (D epsilon : ℝ)
    (hD : 0 < D) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (T : Set (EuclideanSpace ℂ (Fin d))) (hT : ∀ v ∈ T, ‖v‖ ≤ D) :
    ∃ net : Finset (EuclideanSpace ℂ (Fin d)),
      (∀ w ∈ net, w ∈ T) ∧
      (net.card : ℝ) ≤ (2 * D / epsilon + 1) ^ (2 * d) ∧
      ∀ v ∈ T, ∃ w ∈ net, ‖v - w‖ ≤ epsilon :=
  X7VNet.main D epsilon hD hepsilon T hT

end
