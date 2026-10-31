-- Prove2me | solution 1 for SpectralSparsify.Sampling.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-30T18:45:36.119833+00:00
-- url     : https://prove2.me/submissions/99ebf37c-6be3-4104-9cb6-2b9e1549c1b1

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_WeightedGraph
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset
import Definitions.Def_SpectralSparsify_Sampling_SpectralNotions
import Definitions.Def_SpectralSparsify_Sampling_EdgeSampling
import Definitions.Def_SpectralSparsify_Sampling_Sample

section

open scoped BigOperators
open Matrix

namespace SpectralSparsify.Sampling.SSFresh

noncomputable def quad {V : Type*} [Fintype V] (A : Matrix V V ℝ) (x : V → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x)

noncomputable def sqNorm {V : Type*} [Fintype V] (x : V → ℝ) : ℝ := x ⬝ᵥ x

noncomputable def edgeNoise {V : Type*} [DecidableEq V] (q : Sym2 V → ℝ)
    (T : Finset (Sym2 V)) (e : Sym2 V) : ℝ :=
  (if e ∈ T then 1 / q e else 0) - 1

noncomputable def symError {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (q : Sym2 V → ℝ) (T : Finset (Sym2 V)) : Matrix S S ℝ :=
  fun i j => if G.Adj i j then
    edgeNoise q T s(i.val, j.val) / (Real.sqrt (G.degree i) * Real.sqrt (G.degree j)) else 0

noncomputable def rowError {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (q : Sym2 V → ℝ) (T : Finset (Sym2 V)) : Matrix S S ℝ :=
  fun i j => if G.Adj i j then edgeNoise q T s(i.val, j.val) / (G.degree i : ℝ) else 0

end SpectralSparsify.Sampling.SSFresh
end

section

namespace SpectralSparsify.Sampling.SSFresh

lemma sample_trace_threshold (k : ℕ) (hk : 0 < k) (eps lam : ℝ)
    (he : 0 < eps) (hl : 0 < lam) :
    4 * (k : ℝ) / Real.sqrt (sampleUpsilon k eps lam) = eps * lam / 3 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [sampleUpsilon, Real.sqrt_sq (by positivity)]
  field_simp
  ring

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

noncomputable def firstIndex {E : Type*} [DecidableEq E] {k : ℕ}
    (e : Fin k → E) (i : Fin k) : Fin k :=
  (Finset.univ.filter (fun j => e j = e i)).min' ⟨i, by simp⟩

lemma firstIndex_edge {E : Type*} [DecidableEq E] {k : ℕ}
    (e : Fin k → E) (i : Fin k) : e (firstIndex e i) = e i := by
  have h := Finset.min'_mem (Finset.univ.filter (fun j => e j = e i)) ⟨i, by simp⟩
  exact (Finset.mem_filter.mp h).2

lemma firstIndex_le {E : Type*} [DecidableEq E] {k : ℕ}
    (e : Fin k → E) (i : Fin k) : firstIndex e i ≤ i := by
  exact Finset.min'_le _ _ (by simp)

lemma firstIndex_eq_of_edge_eq {E : Type*} [DecidableEq E] {k : ℕ}
    (e : Fin k → E) {i j : Fin k} (h : e i = e j) : firstIndex e i = firstIndex e j := by
  unfold firstIndex
  simp only [h]

lemma firstIndex_eq_iff {E : Type*} [DecidableEq E] {k : ℕ}
    (e : Fin k → E) (i j : Fin k) : firstIndex e i = firstIndex e j ↔ e i = e j := by
  constructor
  · intro h
    rw [← firstIndex_edge e i, ← firstIndex_edge e j, h]
  · exact firstIndex_eq_of_edge_eq e

lemma firstIndex_idempotent {E : Type*} [DecidableEq E] {k : ℕ}
    (e : Fin k → E) (i : Fin k) : firstIndex e (firstIndex e i) = firstIndex e i :=
  firstIndex_eq_of_edge_eq e (firstIndex_edge e i)

lemma edge_image_card_le_half {E : Type*} [DecidableEq E] {k : ℕ}
    (e : Fin k → E)
    (hrep : ∀ a ∈ Finset.univ.image e, 2 ≤ (Finset.univ.filter (fun i => e i = a)).card) :
    2 * (Finset.univ.image e).card ≤ k := by
  have hc := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin k)))
    (t := Finset.univ.image e) (f := e) (fun i hi => Finset.mem_image_of_mem e hi)
  have hs := Finset.sum_le_sum hrep
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin] at hc hs
  omega

lemma number_edge_codes (k : ℕ) : Fintype.card (Fin k → Fin k) = k ^ k := by
  simp

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

variable {α : Type*} [DecidableEq α]

lemma outcomeProb_nonneg (E : Finset α) (p : α → ℝ)
    (hp0 : ∀ e ∈ E, 0 ≤ p e) (hp1 : ∀ e ∈ E, p e ≤ 1)
    {T : Finset α} (hT : T ⊆ E) : 0 ≤ outcomeProb E p T := by
  unfold outcomeProb
  exact mul_nonneg (Finset.prod_nonneg fun e he => hp0 e (hT he))
    (Finset.prod_nonneg fun e he => sub_nonneg.mpr (hp1 e (Finset.mem_sdiff.mp he).1))

lemma outcomeProb_sum (E : Finset α) (p : α → ℝ) :
    ∑ T ∈ E.powerset, outcomeProb E p T = 1 := by
  simpa only [outcomeProb, add_sub_cancel, Finset.prod_const_one] using
    (Finset.prod_add p (fun e => 1 - p e) E).symm

lemma expect_const (E : Finset α) (p : α → ℝ) (c : ℝ) :
    expect E p (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, outcomeProb_sum, one_mul]

lemma expect_add (E : Finset α) (p : α → ℝ) (f g : Finset α → ℝ) :
    expect E p (fun T => f T + g T) = expect E p f + expect E p g := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

lemma expect_mul_const (E : Finset α) (p : α → ℝ) (f : Finset α → ℝ) (c : ℝ) :
    expect E p (fun T => f T * c) = expect E p f * c := by
  simp only [expect, ← mul_assoc, Finset.sum_mul]

lemma expect_mono (E : Finset α) (p : α → ℝ)
    (hp0 : ∀ e ∈ E, 0 ≤ p e) (hp1 : ∀ e ∈ E, p e ≤ 1)
    {f g : Finset α → ℝ} (hfg : ∀ T ⊆ E, f T ≤ g T) :
    expect E p f ≤ expect E p g := by
  apply Finset.sum_le_sum
  intro T hT
  exact mul_le_mul_of_nonneg_left (hfg T (Finset.mem_powerset.mp hT))
    (outcomeProb_nonneg E p hp0 hp1 (Finset.mem_powerset.mp hT))

lemma prod_mem_partition (E T : Finset α) (hT : T ⊆ E) (f g : α → ℝ) :
    (∏ e ∈ E, if e ∈ T then f e else g e) =
      (∏ e ∈ T, f e) * ∏ e ∈ E \ T, g e := by
  rw [← Finset.prod_sdiff hT]
  have h1 : (∏ e ∈ T, if e ∈ T then f e else g e) = ∏ e ∈ T, f e := by
    apply Finset.prod_congr rfl
    intro e he
    simp only [he, ite_true]
  have h2 : (∏ e ∈ E \ T, if e ∈ T then f e else g e) = ∏ e ∈ E \ T, g e := by
    apply Finset.prod_congr rfl
    intro e he
    simp only [(Finset.mem_sdiff.mp he).2, ite_false]
  rw [h1, h2, mul_comm]

lemma expect_prod (E : Finset α) (p f g : α → ℝ) :
    expect E p (fun T => ∏ e ∈ E, if e ∈ T then f e else g e) =
      ∏ e ∈ E, (p e * f e + (1 - p e) * g e) := by
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro T hT
  change outcomeProb E p T * (∏ e ∈ E, if e ∈ T then f e else g e) = _
  rw [prod_mem_partition E T (Finset.mem_powerset.mp hT)]
  simp only [outcomeProb, Finset.prod_mul_distrib]
  ring

lemma expect_exp_sum (E : Finset α) (p f g : α → ℝ) :
    expect E p (fun T => Real.exp (∑ e ∈ E, if e ∈ T then f e else g e)) =
      ∏ e ∈ E, (p e * Real.exp (f e) + (1 - p e) * Real.exp (g e)) := by
  have h : (fun T : Finset α => Real.exp (∑ e ∈ E, if e ∈ T then f e else g e)) =
      (fun T => ∏ e ∈ E, if e ∈ T then Real.exp (f e) else Real.exp (g e)) := by
    funext T
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro e he
    split_ifs <;> rfl
  rw [h, expect_prod]

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

lemma expect_index_product {α I : Type*} [DecidableEq α] [Fintype I]
    (E : Finset α) (p : α → ℝ) (e : I → α) (he : ∀ i, e i ∈ E) (f g : I → ℝ) :
    expect E p (fun T => ∏ i, if e i ∈ T then f i else g i) =
      ∏ a ∈ E, (p a * (∏ i ∈ Finset.univ.filter (fun i => e i = a), f i) +
        (1 - p a) * (∏ i ∈ Finset.univ.filter (fun i => e i = a), g i)) := by
  classical
  have hf (T : Finset α) :
      (∏ i, if e i ∈ T then f i else g i) =
      ∏ a ∈ E, if a ∈ T then (∏ i ∈ Finset.univ.filter (fun i => e i = a), f i)
        else (∏ i ∈ Finset.univ.filter (fun i => e i = a), g i) := by
    rw [← Finset.prod_fiberwise_of_maps_to (fun i (_ : i ∈ Finset.univ) => he i)]
    apply Finset.prod_congr rfl
    intro a ha
    by_cases hat : a ∈ T
    · simp only [hat, ite_true]
      apply Finset.prod_congr rfl
      intro i hi
      simp only [(Finset.mem_filter.mp hi).2, hat, ite_true]
    · simp only [hat, ite_false]
      apply Finset.prod_congr rfl
      intro i hi
      simp only [(Finset.mem_filter.mp hi).2, hat, ite_false]
  simp_rw [hf]
  exact expect_prod E p _ _

lemma expect_noise_product {α I : Type*} [DecidableEq α] [Fintype I]
    (E : Finset α) (p : α → ℝ) (e : I → α) (he : ∀ i, e i ∈ E) :
    expect E p (fun T => ∏ i, ((if e i ∈ T then 1 / p (e i) else 0) - 1)) =
      ∏ a ∈ E, (p a * (1 / p a - 1) ^ (Finset.univ.filter (fun i => e i = a)).card +
        (1 - p a) * (-1) ^ (Finset.univ.filter (fun i => e i = a)).card) := by
  classical
  have h (T : Finset α) (i : I) : ((if e i ∈ T then 1 / p (e i) else 0) - 1) =
      if e i ∈ T then 1 / p (e i) - 1 else -1 := by split_ifs <;> ring
  simp_rw [h]
  rw [expect_index_product E p e he]
  apply Finset.prod_congr rfl
  intro a ha
  have hf : (∏ i ∈ Finset.univ.filter (fun i => e i = a), (1 / p (e i) - 1)) =
      (1 / p a - 1) ^ (Finset.univ.filter (fun i => e i = a)).card := by
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  rw [hf, Finset.prod_const]

lemma expect_noise_product_singleton {α I : Type*} [DecidableEq α] [Fintype I]
    (E : Finset α) (p : α → ℝ) (e : I → α) (he : ∀ i, e i ∈ E)
    {a : α} (ha : a ∈ E) (hpa : p a ≠ 0)
    (hsingle : (Finset.univ.filter (fun i => e i = a)).card = 1) :
    expect E p (fun T => ∏ i, ((if e i ∈ T then 1 / p (e i) else 0) - 1)) = 0 := by
  classical
  rw [expect_noise_product E p e he]
  apply Finset.prod_eq_zero ha
  rw [hsingle, pow_one, pow_one]
  field_simp [hpa]
  ring

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

noncomputable def edgeReps {E : Type*} [DecidableEq E] {k : ℕ} (e : Fin k → E) : Finset (Fin k) :=
  Finset.univ.filter (fun i => firstIndex e i = i)

lemma firstIndex_mem_reps {E : Type*} [DecidableEq E] {k : ℕ}
    (e : Fin k → E) (i : Fin k) : firstIndex e i ∈ edgeReps e := by
  simp only [edgeReps, Finset.mem_filter, Finset.mem_univ, true_and, firstIndex_idempotent]

lemma reps_fiber_eq {E : Type*} [DecidableEq E] {k : ℕ}
    (e : Fin k → E) {r : Fin k} (hr : r ∈ edgeReps e) :
    Finset.univ.filter (fun i => firstIndex e i = r) =
      Finset.univ.filter (fun i => e i = e r) := by
  have hfix := (Finset.mem_filter.mp hr).2
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simpa only [hfix] using firstIndex_eq_iff e i r

lemma prod_reps_fibers {E : Type*} [DecidableEq E] {k : ℕ}
    (e : Fin k → E) (f : Fin k → ℝ) :
    (∏ r ∈ edgeReps e, ∏ i ∈ Finset.univ.filter (fun i => e i = e r), f i) = ∏ i, f i := by
  calc
    _ = ∏ r ∈ edgeReps e, ∏ i ∈ Finset.univ.filter (fun i => firstIndex e i = r), f i := by
      apply Finset.prod_congr rfl
      intro r hr
      rw [reps_fiber_eq e hr]
    _ = _ := Finset.prod_fiberwise_of_maps_to (fun i _ => firstIndex_mem_reps e i) f

lemma prod_reps_eq_image {E : Type*} [DecidableEq E] {k : ℕ}
    (e : Fin k → E) (f : E → ℝ) :
    (∏ r ∈ edgeReps e, f (e r)) = ∏ a ∈ Finset.univ.image e, f a := by
  apply Finset.prod_bij (fun r _ => e r)
  · intro r hr
    exact Finset.mem_image_of_mem e (Finset.mem_univ r)
  · intro r hr s hs hrs
    have h := (firstIndex_eq_iff e r s).mpr hrs
    simpa only [(Finset.mem_filter.mp hr).2, (Finset.mem_filter.mp hs).2] using h
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨firstIndex e i, firstIndex_mem_reps e i, firstIndex_edge e i⟩
  · intro r hr
    rfl

lemma reps_card_twice_le {E : Type*} [DecidableEq E] {k : ℕ}
    (e : Fin k → E)
    (hm : ∀ r ∈ edgeReps e, 2 ≤ (Finset.univ.filter (fun i => e i = e r)).card) :
    2 * (edgeReps e).card ≤ k := by
  have hc := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin k)))
    (t := edgeReps e) (f := firstIndex e) (fun i _ => firstIndex_mem_reps e i)
  have hs : ∑ r ∈ edgeReps e, 2 ≤ ∑ r ∈ edgeReps e,
      (Finset.univ.filter (fun i => firstIndex e i = r)).card := by
    apply Finset.sum_le_sum
    intro r hr
    rw [reps_fiber_eq e hr]
    exact hm r hr
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin] at hc hs
  omega

lemma first_weight_reps {E : Type*} [DecidableEq E] {k : ℕ}
    (e : Fin k → E) (d : Fin k → ℝ) :
    (∏ i : Fin k, if firstIndex e i = i then 1 / d i else 1) =
      ∏ i ∈ edgeReps e, 1 / d i := by
  classical
  simp only [Finset.prod_ite, Finset.prod_const_one, mul_one, edgeReps]

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

lemma expect_noise_product_image {α I : Type*} [DecidableEq α] [Fintype I]
    (E : Finset α) (p : α → ℝ) (e : I → α) (he : ∀ i, e i ∈ E) :
    expect E p (fun T => ∏ i, ((if e i ∈ T then 1 / p (e i) else 0) - 1)) =
      ∏ a ∈ Finset.univ.image e,
        (p a * (1 / p a - 1) ^ (Finset.univ.filter (fun i => e i = a)).card +
        (1 - p a) * (-1) ^ (Finset.univ.filter (fun i => e i = a)).card) := by
  classical
  rw [expect_noise_product E p e he]
  symm
  apply Finset.prod_subset
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact he i
  · intro a ha hnot
    have hf : Finset.univ.filter (fun i : I => e i = a) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi hea
      exact hnot (Finset.mem_image.mpr ⟨i, hi, hea⟩)
    rw [hf]
    simp

lemma expect_scaled_noise_product {α : Type*} [DecidableEq α] {k : ℕ}
    (E : Finset α) (p : α → ℝ) (e : Fin k → α) (he : ∀ i, e i ∈ E)
    (d : Fin k → ℝ) :
    expect E p (fun T => ∏ i, (((if e i ∈ T then 1 / p (e i) else 0) - 1) / d i)) =
      ∏ r ∈ edgeReps e,
        ((p (e r) * (1 / p (e r) - 1) ^ (Finset.univ.filter (fun i => e i = e r)).card +
        (1 - p (e r)) * (-1) ^ (Finset.univ.filter (fun i => e i = e r)).card) *
          ∏ i ∈ Finset.univ.filter (fun i => e i = e r), 1 / d i) := by
  classical
  have hf (T : Finset α) :
      (∏ i, (((if e i ∈ T then 1 / p (e i) else 0) - 1) / d i)) =
      (∏ i, ((if e i ∈ T then 1 / p (e i) else 0) - 1)) * ∏ i, 1 / d i := by
    simp only [div_eq_mul_inv, one_mul, Finset.prod_mul_distrib]
  simp_rw [hf]
  rw [expect_mul_const, expect_noise_product_image E p e he,
    ← prod_reps_eq_image e, ← prod_reps_fibers e (fun i => 1 / d i), ← Finset.prod_mul_distrib]

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh
variable {α : Type*} [DecidableEq α]

lemma expect_coordinate (E : Finset α) (p : α → ℝ) {e : α} (he : e ∈ E) (a b : ℝ) :
    expect E p (fun T => if e ∈ T then a else b) = p e * a + (1 - p e) * b := by
  classical
  have hprod (T : Finset α) :
      (∏ j ∈ E, if j ∈ T then (if j = e then a else 1) else (if j = e then b else 1)) =
        if e ∈ T then a else b := by
    calc
      _ = ∏ j ∈ E, if j = e then (if e ∈ T then a else b) else 1 := by
        apply Finset.prod_congr rfl
        intro j hj
        by_cases hje : j = e
        · subst j
          simp only [ite_true]
        · simp only [hje, ite_false, ite_self]
      _ = _ := by simp [he]
  have h := expect_prod E p (fun j => if j = e then a else 1)
    (fun j => if j = e then b else 1)
  simp_rw [hprod] at h
  rw [h]
  calc
    _ = ∏ j ∈ E, if j = e then p e * a + (1 - p e) * b else 1 := by
      apply Finset.prod_congr rfl
      intro j hj
      by_cases hje : j = e
      · subst j
        simp only [ite_true]
      · simp only [hje, ite_false, mul_one]
        ring
    _ = _ := by simp [he]

lemma expect_single_function (E : Finset α) (p : α → ℝ) {e : α} (he : e ∈ E)
    (f : Bool → ℝ) :
    expect E p (fun T => f (decide (e ∈ T))) = p e * f true + (1 - p e) * f false := by
  have h : (fun T : Finset α => f (decide (e ∈ T))) =
      (fun T => if e ∈ T then f true else f false) := by
    funext T
    by_cases hT : e ∈ T <;> simp [hT]
  rw [h, expect_coordinate E p he]

lemma expect_centered (E : Finset α) (p : α → ℝ) {e : α} (he : e ∈ E)
    (hp : p e ≠ 0) :
    expect E p (fun T => (if e ∈ T then 1 / p e else 0) - 1) = 0 := by
  have h : (fun T : Finset α => (if e ∈ T then 1 / p e else 0) - 1) =
      (fun T => if e ∈ T then 1 / p e - 1 else -1) := by
    funext T
    split_ifs <;> ring
  rw [h, expect_coordinate E p he]
  field_simp [hp]
  ring

lemma expect_centered_sq (E : Finset α) (p : α → ℝ) {e : α} (he : e ∈ E)
    (hp : p e ≠ 0) :
    expect E p (fun T => ((if e ∈ T then 1 / p e else 0) - 1)^2) =
      (1 - p e) / p e := by
  have h : (fun T : Finset α => ((if e ∈ T then 1 / p e else 0) - 1)^2) =
      (fun T => if e ∈ T then (1 / p e - 1)^2 else 1) := by
    funext T
    split_ifs <;> ring
  rw [h, expect_coordinate E p he]
  field_simp [hp]
  ring

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

lemma abs_pow_le_sq_mul (z R : ℝ) (hR : |z| ≤ R) (n : ℕ) :
    |z| ^ (n + 2) ≤ R ^ n * z ^ 2 := by
  rw [pow_add, sq_abs]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg z) hR n) (sq_nonneg z)

lemma bernoulli_noise_abs_le (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (b : Bool) :
    |(if b then 1 / q else 0) - 1| ≤ 1 / q := by
  have hr : 1 ≤ 1 / q := (le_div_iff₀ hq0).mpr (by simpa using hq1)
  cases b
  · simpa using hr
  · simp only [ite_true]
    rw [abs_of_nonneg (by linarith)]
    linarith

lemma expect_noise_abs_pow {α : Type*} [DecidableEq α]
    (E : Finset α) (p : α → ℝ) {e : α} (he : e ∈ E)
    (hp0 : 0 < p e) (hp1 : p e ≤ 1) (n : ℕ) :
    expect E p (fun T => |(if e ∈ T then 1 / p e else 0) - 1| ^ (n + 2)) ≤
      (1 / p e) ^ (n + 1) := by
  have hfun : (fun T : Finset α => |(if e ∈ T then 1 / p e else 0) - 1| ^ (n + 2)) =
      (fun T => if e ∈ T then |1 / p e - 1| ^ (n + 2) else 1) := by
    funext T
    by_cases h : e ∈ T <;> simp [h]
  rw [hfun, expect_coordinate E p he]
  have hpos := abs_pow_le_sq_mul (1 / p e - 1) (1 / p e)
    (bernoulli_noise_abs_le (p e) hp0 hp1 true) n
  have hneg := abs_pow_le_sq_mul (-1) (1 / p e)
    (by simpa using bernoulli_noise_abs_le (p e) hp0 hp1 false) n
  have hv : p e * (1 / p e - 1) ^ 2 + (1 - p e) = (1 - p e) / p e := by
    field_simp
    ring
  calc
    _ ≤ p e * ((1 / p e)^n * (1 / p e - 1)^2) +
        (1 - p e) * ((1 / p e)^n * (-1)^2) :=
      add_le_add (mul_le_mul_of_nonneg_left hpos hp0.le)
        (mul_le_mul_of_nonneg_left (by simpa using hneg) (sub_nonneg.mpr hp1))
    _ = (1 / p e)^n * ((1 - p e) / p e) := by rw [← hv]; ring
    _ ≤ (1 / p e)^n * (1 / p e) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (one_div_pos.mpr hp0).le n)
      exact (div_le_div_iff_of_pos_right hp0).mpr (by linarith)
    _ = _ := (pow_succ (1 / p e) n).symm

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

lemma scalar_abs_moment_bound (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 2 ≤ m) :
    |q * (1 / q - 1)^m + (1 - q) * (-1)^m| ≤ (1 / q)^(m - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm 2 n]
  have h := expect_noise_abs_pow ({()} : Finset Unit) (fun _ => q) (e := ()) (by simp) hq0 hq1 n
  have hf : (fun T : Finset Unit => |(if () ∈ T then 1 / q else 0) - 1| ^ (n + 2)) =
      (fun T => if () ∈ T then |1 / q - 1|^(n+2) else 1) := by
    funext T
    by_cases ht : () ∈ T <;> simp [ht]
  change expect ({()} : Finset Unit) (fun _ => q)
    (fun T => |(if () ∈ T then 1 / q else 0) - 1| ^ (n + 2)) ≤ _ at h
  rw [hf, expect_coordinate _ _ (by simp)] at h
  have ha := abs_add_le (q * (1 / q - 1)^(n+2)) ((1-q)*(-1)^(n+2))
  simp only [abs_mul, abs_pow, abs_of_pos hq0,
    abs_of_nonneg (sub_nonneg.mpr hq1), abs_neg, abs_one, one_pow, mul_one] at ha
  have h' : q * |1 / q - 1|^(n+2) + (1-q) ≤ (1/q)^(n+1) := by
    simpa only [mul_one] using h
  simpa using ha.trans h'

lemma local_moment_product_bound {I : Type*} [DecidableEq I]
    (F : Finset I) (d : I → ℝ) (q U : ℝ) (r : I) (hr : r ∈ F)
    (hd : ∀ i ∈ F, 0 < d i) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hU : 0 < U) (hqd : ∀ i ∈ F, U ≤ q * d i) (hF : 2 ≤ F.card) :
    |q * (1 / q - 1)^F.card + (1 - q) * (-1)^F.card| * (∏ i ∈ F, 1 / d i) ≤
      (1 / d r) * (1 / U)^(F.card - 1) := by
  have hm := scalar_abs_moment_bound q hq0 hq1 F.card hF
  have hinv (i : I) (hi : i ∈ F) : 1 / d i ≤ q / U := by
    apply (div_le_div_iff₀ (hd i hi) hU).mpr
    simpa only [one_mul] using hqd i hi
  have hp : (∏ i ∈ F.erase r, 1 / d i) ≤ (q / U)^(F.card - 1) := by
    calc
      _ ≤ ∏ _i ∈ F.erase r, q / U := Finset.prod_le_prod
        (fun i hi => (one_div_pos.mpr (hd i (Finset.mem_erase.mp hi).2)).le)
        (fun i hi => hinv i (Finset.mem_erase.mp hi).2)
      _ = _ := by rw [Finset.prod_const, Finset.card_erase_of_mem hr]
  have hprod : (∏ i ∈ F, 1 / d i) = (1 / d r) * ∏ i ∈ F.erase r, 1 / d i := by
    exact (Finset.mul_prod_erase F (fun i => 1 / d i) hr).symm
  rw [hprod]
  calc
    _ ≤ (1 / q)^(F.card-1) * ((1 / d r) * (q / U)^(F.card-1)) :=
      mul_le_mul hm (mul_le_mul_of_nonneg_left hp (one_div_pos.mpr (hd r hr)).le)
        (mul_nonneg (one_div_pos.mpr (hd r hr)).le
          (Finset.prod_nonneg fun i hi => (one_div_pos.mpr (hd i (Finset.mem_erase.mp hi).2)).le))
        (pow_nonneg (one_div_pos.mpr hq0).le _)
    _ = _ := by
      have he : (1 / q) * (q / U) = 1 / U := by field_simp
      calc
        _ = (1 / d r) * ((1 / q)^(F.card-1) * (q / U)^(F.card-1)) := by ring
        _ = _ := by rw [← mul_pow, he]

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

lemma reps_multiplicity_pos {E : Type*} [DecidableEq E] {k : ℕ}
    (e : Fin k → E) (r : Fin k) :
    0 < (Finset.univ.filter (fun i => e i = e r)).card := by
  exact Finset.card_pos.mpr ⟨r, by simp⟩

lemma reps_exponent_sum {E : Type*} [DecidableEq E] {k : ℕ}
    (e : Fin k → E) :
    (∑ r ∈ edgeReps e, ((Finset.univ.filter (fun i => e i = e r)).card - 1)) +
      (edgeReps e).card = k := by
  have hc := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin k)))
    (t := edgeReps e) (f := firstIndex e) (fun i _ => firstIndex_mem_reps e i)
  have he : (∑ r ∈ edgeReps e, ((Finset.univ.filter (fun i => e i = e r)).card - 1)) +
      (edgeReps e).card = ∑ r ∈ edgeReps e, (Finset.univ.filter (fun i => e i = e r)).card := by
    have hcard : (edgeReps e).card = ∑ _r ∈ edgeReps e, (1 : ℕ) := by simp
    rw [hcard]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have hp := reps_multiplicity_pos e r
    omega
  rw [he]
  symm
  simpa only [Finset.card_univ, Fintype.card_fin] using hc.trans (Finset.sum_congr rfl
    (fun r hr => congrArg Finset.card (reps_fiber_eq e hr)))

lemma reps_power_bound {E : Type*} [DecidableEq E] {k : ℕ}
    (e : Fin k → E) (d : Fin k → ℝ) (hd : ∀ i, 0 < d i) (U : ℝ) (hU : 1 ≤ U)
    (hm : ∀ r ∈ edgeReps e, 2 ≤ (Finset.univ.filter (fun i => e i = e r)).card) :
    (∏ r ∈ edgeReps e, (1 / d r) * (1 / U)^((Finset.univ.filter (fun i => e i = e r)).card-1)) ≤
      (∏ r ∈ edgeReps e, 1 / d r) * (1 / U)^(k/2) := by
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => (one_div_pos.mpr (hd i)).le)
  have hcount := reps_card_twice_le e hm
  have hsum := reps_exponent_sum e
  have hex : k / 2 ≤ ∑ r ∈ edgeReps e,
      ((Finset.univ.filter (fun i => e i = e r)).card - 1) := by omega
  exact pow_le_pow_of_le_one (by positivity) (by simpa using (one_div_le_one_div_of_le (by norm_num) hU)) hex

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

lemma scaled_noise_product_bound {α : Type*} [DecidableEq α] {k : ℕ}
    (E : Finset α) (p : α → ℝ) (e : Fin k → α) (he : ∀ i, e i ∈ E)
    (d : Fin k → ℝ) (hd : ∀ i, 0 < d i)
    (hp0 : ∀ i, 0 < p (e i)) (hp1 : ∀ i, p (e i) ≤ 1)
    (U : ℝ) (hU : 1 ≤ U)
    (hqd : ∀ i, p (e i) < 1 → U ≤ p (e i) * d i) :
    expect E p (fun T => ∏ i, (((if e i ∈ T then 1 / p (e i) else 0) - 1) / d i)) ≤
      (∏ i : Fin k, if firstIndex e i = i then 1 / d i else 1) * (1 / U)^(k / 2) := by
  classical
  rw [expect_scaled_noise_product E p e he d, first_weight_reps]
  have hR : 0 ≤ (∏ r ∈ edgeReps e, 1 / d r) * (1 / U)^(k/2) := by
    apply mul_nonneg (Finset.prod_nonneg fun i _ => (one_div_pos.mpr (hd i)).le)
    positivity
  by_cases hb : ∃ r ∈ edgeReps e,
      (Finset.univ.filter (fun i => e i = e r)).card = 1 ∨ p (e r) = 1
  · obtain ⟨r, hr, hm | hq⟩ := hb
    · have hz : (p (e r) * (1 / p (e r) - 1) ^ (Finset.univ.filter (fun i => e i = e r)).card +
          (1 - p (e r)) * (-1) ^ (Finset.univ.filter (fun i => e i = e r)).card) = 0 := by
        rw [hm, pow_one, pow_one]
        field_simp [ne_of_gt (hp0 r)]
        ring
      rw [Finset.prod_eq_zero hr (by rw [hz, zero_mul])]
      exact hR
    · have hm := reps_multiplicity_pos e r
      have hz : (p (e r) * (1 / p (e r) - 1) ^ (Finset.univ.filter (fun i => e i = e r)).card +
          (1 - p (e r)) * (-1) ^ (Finset.univ.filter (fun i => e i = e r)).card) = 0 := by
        simp [hq, Nat.ne_of_gt hm]
      rw [Finset.prod_eq_zero hr (by rw [hz, zero_mul])]
      exact hR
  · have hm (r : Fin k) (hr : r ∈ edgeReps e) :
        2 ≤ (Finset.univ.filter (fun i => e i = e r)).card := by
      have hpos := reps_multiplicity_pos e r
      have hne : (Finset.univ.filter (fun i => e i = e r)).card ≠ 1 :=
        fun h => hb ⟨r, hr, Or.inl h⟩
      omega
    have hq (r : Fin k) (hr : r ∈ edgeReps e) : p (e r) < 1 :=
      lt_of_le_of_ne (hp1 r) (fun h => hb ⟨r, hr, Or.inr h⟩)
    calc
      _ ≤ |∏ r ∈ edgeReps e,
        ((p (e r) * (1 / p (e r) - 1) ^ (Finset.univ.filter (fun i => e i = e r)).card +
        (1 - p (e r)) * (-1) ^ (Finset.univ.filter (fun i => e i = e r)).card) *
          ∏ i ∈ Finset.univ.filter (fun i => e i = e r), 1 / d i)| := le_abs_self _
      _ ≤ ∏ r ∈ edgeReps e,
          (1 / d r) * (1 / U)^((Finset.univ.filter (fun i => e i = e r)).card - 1) := by
        rw [Finset.abs_prod]
        apply Finset.prod_le_prod (fun r _ => abs_nonneg _)
        intro r hr
        rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ => (one_div_pos.mpr (hd i)).le)]
        apply local_moment_product_bound _ d (p (e r)) U r (by simp)
          (fun i _ => hd i) (hp0 r) (hp1 r) (by linarith) _ (hm r hr)
        intro i hi
        have hei := (Finset.mem_filter.mp hi).2
        rw [← hei]
        exact hqd i (by simpa only [hei] using hq r hr)
      _ ≤ _ := reps_power_bound e d hd U hU hm

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

noncomputable def pathWeight {V : Type*} (w : List V → V → ℝ) :
    (n : ℕ) → List V → (Fin n → V) → ℝ
  | 0, _, _ => 1
  | n + 1, h, x => w h (x 0) * pathWeight w n (x 0 :: h) (Fin.tail x)

lemma pathWeight_nonneg {V : Type*} (w : List V → V → ℝ)
    (hw : ∀ h v, 0 ≤ w h v) (n : ℕ) (h : List V) (x : Fin n → V) :
    0 ≤ pathWeight w n h x := by
  induction n generalizing h with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hw h (x 0)) (ih (x 0 :: h) (Fin.tail x))

lemma sum_pathWeight_succ {V : Type*} [Fintype V] (w : List V → V → ℝ)
    (n : ℕ) (h : List V) :
    (∑ x : Fin (n + 1) → V, pathWeight w (n + 1) h x) =
      ∑ v : V, w h v * ∑ x : Fin n → V, pathWeight w n (v :: h) x := by
  classical
  calc
    _ = ∑ y : V × (Fin n → V), pathWeight w (n + 1) h (Fin.cons y.1 y.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => V)).symm
      intro x
      simp only [Fin.consEquiv_symm_apply, Fin.cons_self_tail]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [pathWeight, Fin.cons_zero, Fin.tail_cons, Finset.mul_sum]

lemma sum_pathWeight_le_one {V : Type*} [Fintype V] (w : List V → V → ℝ)
    (hw : ∀ h v, 0 ≤ w h v) (hs : ∀ h, ∑ v, w h v ≤ 1)
    (n : ℕ) (h : List V) : (∑ x : Fin n → V, pathWeight w n h x) ≤ 1 := by
  classical
  induction n generalizing h with
  | zero => simp [pathWeight]
  | succ n ih =>
      rw [sum_pathWeight_succ]
      calc
        _ ≤ ∑ v : V, w h v * 1 := Finset.sum_le_sum fun v _ =>
          mul_le_mul_of_nonneg_left (ih (v :: h)) (hw h v)
        _ ≤ 1 := by simpa only [mul_one] using hs h

lemma sum_pathWeight_filter_le_one {V : Type*} [Fintype V]
    (w : List V → V → ℝ) (hw : ∀ h v, 0 ≤ w h v)
    (hs : ∀ h, ∑ v, w h v ≤ 1) (n : ℕ) (h : List V)
    (P : (Fin n → V) → Prop) [DecidablePred P] :
    (∑ x : Fin n → V, if P x then pathWeight w n h x else 0) ≤ 1 := by
  apply le_trans _ (sum_pathWeight_le_one w hw hs n h)
  apply Finset.sum_le_sum
  intro x hx
  split_ifs
  · exact le_rfl
  · exact pathWeight_nonneg w hw n h x

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

noncomputable def walkProduct {V : Type*} (A : Matrix V V ℝ) :
    (n : ℕ) → V → (Fin n → V) → ℝ
  | 0, _, _ => 1
  | n + 1, a, x => A a (x 0) * walkProduct A n (x 0) (Fin.tail x)

def walkEnd {V : Type*} : (n : ℕ) → V → (Fin n → V) → V
  | 0, a, _ => a
  | n + 1, _, x => walkEnd n (x 0) (Fin.tail x)

lemma sum_fin_cons {V : Type*} [Fintype V] (n : ℕ) (f : (Fin (n + 1) → V) → ℝ) :
    (∑ x, f x) = ∑ a : V, ∑ x : Fin n → V, f (Fin.cons a x) := by
  classical
  calc
    _ = ∑ y : V × (Fin n → V), f (Fin.cons y.1 y.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => V)).symm
      intro x
      simp only [Fin.consEquiv_symm_apply, Fin.cons_self_tail]
    _ = _ := Fintype.sum_prod_type _

lemma matrix_pow_walks {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (n : ℕ) (a b : V) :
    (A^n) a b = ∑ x : Fin n → V, if walkEnd n a x = b then walkProduct A n a x else 0 := by
  classical
  induction n generalizing a with
  | zero =>
      by_cases h : a = b <;> simp [walkEnd, walkProduct, h]
  | succ n ih =>
      rw [pow_succ', Matrix.mul_apply, sum_fin_cons]
      apply Finset.sum_congr rfl
      intro v hv
      rw [ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [walkEnd, walkProduct, Fin.cons_zero, Fin.tail_cons]
      split_ifs <;> simp

lemma trace_pow_walks {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (n : ℕ) :
    Matrix.trace (A^n) = ∑ a : V, ∑ x : Fin n → V,
      if walkEnd n a x = a then walkProduct A n a x else 0 := by
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro a ha
  exact matrix_pow_walks A n a a

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

/-- A previously recorded unoriented edge determines at most one next endpoint.
Invalid records are harmless: the kernel is only an upper bound on compatible walks. -/
def forcedNext {V : Type*} [DecidableEq V] (a : V) (h : List V) (j : ℕ) : V :=
  let current := h.headD a
  let source := (a :: h.reverse).getD j a
  let target := h.reverse.getD j a
  if current = source then target else source

noncomputable def codeKernel {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : V → ℝ)
    (a : V) (c : ℕ → ℕ) (h : List V) (v : V) : ℝ :=
  if c h.length = h.length then
    if G.Adj (h.headD a) v then 1 / d (h.headD a) else 0
  else if v = forcedNext a h (c h.length) then 1 else 0

lemma codeKernel_nonneg {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : V → ℝ)
    (hd : ∀ v, 0 < d v) (a : V) (c : ℕ → ℕ) (h : List V) (v : V) :
    0 ≤ codeKernel G d a c h v := by
  unfold codeKernel
  split_ifs
  · exact (one_div_pos.mpr (hd _)).le
  · exact le_rfl
  · exact zero_le_one
  · exact le_rfl

lemma codeKernel_sum_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : V → ℝ)
    (hd : ∀ v, 0 < d v) (hg : ∀ v, (G.degree v : ℝ) ≤ d v)
    (a : V) (c : ℕ → ℕ) (h : List V) :
    ∑ v, codeKernel G d a c h v ≤ 1 := by
  classical
  unfold codeKernel
  split_ifs with hc
  · have hs : (∑ v : V, if G.Adj (h.headD a) v then 1 / d (h.headD a) else 0) =
        (G.degree (h.headD a) : ℝ) / d (h.headD a) := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_const, nsmul_eq_mul]
      have hf : Finset.univ.filter (G.Adj (h.headD a)) = G.neighborFinset (h.headD a) := by
        ext v
        simp
      rw [hf, SimpleGraph.card_neighborFinset_eq_degree]
      ring
    rw [hs]
    exact (div_le_one (hd _)).mpr (hg _)
  · simp

lemma code_path_mass_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : V → ℝ)
    (hd : ∀ v, 0 < d v) (hg : ∀ v, (G.degree v : ℝ) ≤ d v)
    (a : V) (c : ℕ → ℕ) (k : ℕ) :
    (∑ x : Fin k → V, pathWeight (codeKernel G d a c) k [] x) ≤ 1 :=
  sum_pathWeight_le_one _ (codeKernel_nonneg G d hd a c)
    (codeKernel_sum_le_one G d hd hg a c) k []

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

def prefixHistory {V : Type*} {n : ℕ} (x : Fin n → V) (i : ℕ) : List V :=
  ((List.ofFn x).take i).reverse

lemma prefixHistory_zero {V : Type*} {n : ℕ} (x : Fin n → V) : prefixHistory x 0 = [] := by
  simp [prefixHistory]

lemma prefixHistory_cons {V : Type*} {n : ℕ} (a : V) (x : Fin n → V) (i : ℕ) :
    prefixHistory (Fin.cons a x) (i + 1) = prefixHistory x i ++ [a] := by
  simp [prefixHistory]

lemma prefixHistory_length {V : Type*} {n : ℕ} (x : Fin n → V) (i : ℕ) (hi : i ≤ n) :
    (prefixHistory x i).length = i := by
  simp [prefixHistory, Nat.min_eq_left hi]

lemma pathWeight_eq_prod {V : Type*} (w : List V → V → ℝ)
    (n : ℕ) (h : List V) (x : Fin n → V) :
    pathWeight w n h x = ∏ i : Fin n, w (prefixHistory x i ++ h) (x i) := by
  induction n generalizing h with
  | zero => simp [pathWeight]
  | succ n ih =>
      rw [pathWeight, ih, Fin.prod_univ_succ]
      simp only [Fin.val_zero, prefixHistory_zero, List.nil_append]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      have hx : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
      conv_rhs => rw [hx]
      simp only [Fin.cons_succ, Fin.val_succ, prefixHistory_cons, List.append_assoc,
        List.singleton_append]

lemma forcedNext_of_edge_eq {V : Type*} [DecidableEq V]
    (a : V) (h : List V) (j : ℕ) (v : V)
    (he : s(h.headD a, v) = s((a :: h.reverse).getD j a, h.reverse.getD j a)) :
    forcedNext a h j = v := by
  unfold forcedNext
  dsimp only
  rcases Sym2.eq_iff.mp he with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · simp only [hs, ite_true]
    exact ht.symm
  · split_ifs with h
    · exact ht.symm.trans (h.trans hs.symm)
    · exact hs.symm

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

lemma walkProduct_eq_pathWeight {V : Type*} (A : Matrix V V ℝ)
    (n : ℕ) (a : V) (h : List V) (x : Fin n → V) :
    walkProduct A n (h.headD a) x =
      pathWeight (fun h v => A (h.headD a) v) n h x := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
      simp only [walkProduct, pathWeight]
      rw [← ih]
      rfl

lemma walkProduct_eq_prod {V : Type*} (A : Matrix V V ℝ)
    (n : ℕ) (a : V) (x : Fin n → V) :
    walkProduct A n a x = ∏ i : Fin n, A ((prefixHistory x i).headD a) (x i) := by
  have h := walkProduct_eq_pathWeight A n a [] x
  rw [pathWeight_eq_prod] at h
  simpa only [List.headD_nil, List.append_nil] using h

lemma firstIndex_injective_map {E F : Type*} [DecidableEq E] [DecidableEq F]
    {k : ℕ} (e : Fin k → E) (f : E → F) (hf : Function.Injective f) :
    firstIndex (fun i => f (e i)) = firstIndex e := by
  funext i
  unfold firstIndex
  simp only [hf.eq_iff]

lemma expect_sum {α β : Type*} [DecidableEq α]
    (E : Finset α) (p : α → ℝ) (I : Finset β) (f : β → Finset α → ℝ) :
    expect E p (fun T => ∑ i ∈ I, f i T) = ∑ i ∈ I, expect E p (f i) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

open scoped Classical in
lemma expect_ite_const {α : Type*} [DecidableEq α]
    (E : Finset α) (p : α → ℝ) (P : Prop) (f : Finset α → ℝ) :
    expect E p (fun T => if P then f T else 0) = if P then expect E p f else 0 := by
  classical
  by_cases h : P
  · simp only [h, ite_true]
  · simp only [h, ite_false, expect_const]

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

lemma reverse_take_headD {V : Type*} (l : List V) (a : V) (i : ℕ) (hi : i ≤ l.length) :
    (l.take i).reverse.headD a = (a :: l).getD i a := by
  induction i generalizing l a with
  | zero => simp
  | succ i ih =>
      cases l with
      | nil => simp only [List.length_nil] at hi; omega
      | cons b l =>
          have hh (r : List V) : (r ++ [b]).headD a = r.headD b := by
            cases r <;> rfl
          simp only [List.take_succ_cons, List.reverse_cons, hh]
          have hi' : i ≤ l.length := by simpa using hi
          rw [ih l b hi']
          simp only [List.getD_cons_succ]
          rw [List.getD_eq_getElem _ _ (by simp; omega),
            List.getD_eq_getElem _ _ (by simp; omega)]

lemma getD_take_of_lt {V : Type*} (l : List V) (a : V) (i j : ℕ) (h : j < i) :
    (l.take i).getD j a = l.getD j a := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

lemma prefixHistory_current {V : Type*} {n : ℕ} (a : V) (x : Fin n → V) (i : ℕ) (hi : i ≤ n) :
    (prefixHistory x i).headD a = (a :: List.ofFn x).getD i a :=
  reverse_take_headD (List.ofFn x) a i (by simpa using hi)

def walkEdge {V : Type*} {n : ℕ} (a : V) (x : Fin n → V) (i : Fin n) : Sym2 V :=
  s((prefixHistory x i).headD a, x i)

lemma prefixHistory_record_target {V : Type*} {n : ℕ} (a : V) (x : Fin n → V)
    (i : ℕ) (j : Fin n) (hji : j.val < i) :
    (prefixHistory x i).reverse.getD j a = x j := by
  simp only [prefixHistory, List.reverse_reverse]
  rw [getD_take_of_lt _ _ _ _ hji]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

lemma prefixHistory_record_source {V : Type*} {n : ℕ} (a : V) (x : Fin n → V)
    (i : ℕ) (j : Fin n) (hji : j.val < i) :
    (a :: (prefixHistory x i).reverse).getD j a = (prefixHistory x j).headD a := by
  rw [prefixHistory_current a x j j.isLt.le]
  simp only [prefixHistory, List.reverse_reverse]
  have h : a :: (List.ofFn x).take i = (a :: List.ofFn x).take (i + 1) := by simp
  rw [h, getD_take_of_lt _ _ _ _ (by omega)]

lemma code_forces_next {V : Type*} [DecidableEq V] {n : ℕ}
    (a : V) (x : Fin n → V) (i : Fin n)
    (hi : firstIndex (walkEdge a x) i ≠ i) :
    forcedNext a (prefixHistory x i) (firstIndex (walkEdge a x) i).val = x i := by
  have hlt : firstIndex (walkEdge a x) i < i :=
    lt_of_le_of_ne (firstIndex_le (walkEdge a x) i) hi
  apply forcedNext_of_edge_eq
  rw [prefixHistory_record_source a x i _ hlt, prefixHistory_record_target a x i _ hlt]
  exact (firstIndex_edge (walkEdge a x) i).symm

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

noncomputable def extendCode {n : ℕ} (c : Fin n → Fin n) (i : ℕ) : ℕ :=
  if h : i < n then (c ⟨i, h⟩).val else i

lemma extendCode_apply {n : ℕ} (c : Fin n → Fin n) (i : Fin n) :
    extendCode c i = (c i).val := by simp [extendCode]

noncomputable def firstWeight {V : Type*} [DecidableEq V] {n : ℕ}
    (d : V → ℝ) (a : V) (x : Fin n → V) : ℝ :=
  ∏ i : Fin n, if firstIndex (walkEdge a x) i = i then
    1 / d ((prefixHistory x i).headD a) else 1

lemma canonical_pathWeight {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : V → ℝ)
    {n : ℕ} (a : V) (x : Fin n → V)
    (hx : ∀ i : Fin n, G.Adj ((prefixHistory x i).headD a) (x i)) :
    pathWeight (codeKernel G d a (extendCode (firstIndex (walkEdge a x)))) n [] x =
      firstWeight d a x := by
  rw [pathWeight_eq_prod]
  unfold firstWeight
  apply Finset.prod_congr rfl
  intro i hi
  simp only [List.append_nil, codeKernel, prefixHistory_length x i i.isLt.le, extendCode_apply]
  by_cases hc : firstIndex (walkEdge a x) i = i
  · simp only [hc, hx i, ite_true]
  · have hval : (firstIndex (walkEdge a x) i).val ≠ i.val :=
      fun h => hc (Fin.ext h)
    simp only [hval, hc, ite_false, code_forces_next a x i hc, ite_true]

lemma code_mass_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : V → ℝ)
    (hd : ∀ v, 0 < d v) (hg : ∀ v, (G.degree v : ℝ) ≤ d v)
    (n : ℕ) (a : V) (c : Fin n → Fin n) :
    (∑ x : Fin n → V, if (∀ i : Fin n, G.Adj ((prefixHistory x i).headD a) (x i)) ∧
      firstIndex (walkEdge a x) = c then firstWeight d a x else 0) ≤ 1 := by
  classical
  apply le_trans _ (code_path_mass_le_one G d hd hg a (extendCode c) n)
  apply Finset.sum_le_sum
  intro x hx
  split_ifs with h
  · rw [← h.2]
    exact (canonical_pathWeight G d a x h.1).ge
  · exact pathWeight_nonneg _ (codeKernel_nonneg G d hd a (extendCode c)) n [] x

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

lemma all_code_mass_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : V → ℝ)
    (hd : ∀ v, 0 < d v) (hg : ∀ v, (G.degree v : ℝ) ≤ d v)
    (n : ℕ) (a : V) :
    (∑ x : Fin n → V, if (∀ i : Fin n, G.Adj ((prefixHistory x i).headD a) (x i))
      then firstWeight d a x else 0) ≤ (n : ℝ)^n := by
  classical
  have he : (∑ x : Fin n → V, if (∀ i : Fin n, G.Adj ((prefixHistory x i).headD a) (x i))
      then firstWeight d a x else 0) =
      ∑ c : Fin n → Fin n, ∑ x : Fin n → V,
        if (∀ i : Fin n, G.Adj ((prefixHistory x i).headD a) (x i)) ∧ firstIndex (walkEdge a x) = c
        then firstWeight d a x else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : ∀ i : Fin n, G.Adj ((prefixHistory x i).headD a) (x i)
    · simp only [h]
      simp
    · simp only [h, false_and, ite_false, Finset.sum_const_zero]
  rw [he]
  calc
    _ ≤ ∑ _c : Fin n → Fin n, (1 : ℝ) :=
      Finset.sum_le_sum fun c _ => code_mass_le_one G d hd hg n a c
    _ = _ := by simp

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

noncomputable def labelNoiseMatrix {V α : Type*} [DecidableEq α]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : V → ℝ)
    (label : Sym2 V → α) (p : α → ℝ) (T : Finset α) : Matrix V V ℝ :=
  fun i j => if G.Adj i j then ((if label s(i,j) ∈ T then 1 / p (label s(i,j)) else 0) - 1) / d i else 0

lemma expected_walk_bound {V α : Type*} [DecidableEq V] [DecidableEq α]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : V → ℝ) (hd : ∀ v, 0 < d v)
    (label : Sym2 V → α) (hinj : Function.Injective label)
    (E : Finset α) (p : α → ℝ)
    (he : ∀ i j, G.Adj i j → label s(i,j) ∈ E)
    (hp0 : ∀ i j, G.Adj i j → 0 < p (label s(i,j)))
    (hp1 : ∀ i j, G.Adj i j → p (label s(i,j)) ≤ 1)
    (U : ℝ) (hU : 1 ≤ U)
    (hqd : ∀ i j, G.Adj i j → p (label s(i,j)) < 1 → U ≤ p (label s(i,j)) * d i)
    (k : ℕ) (a : V) (x : Fin k → V) :
    expect E p (fun T => walkProduct (labelNoiseMatrix G d label p T) k a x) ≤
      if (∀ i : Fin k, G.Adj ((prefixHistory x i).headD a) (x i))
      then firstWeight d a x * (1 / U)^(k/2) else 0 := by
  classical
  by_cases hx : ∀ i : Fin k, G.Adj ((prefixHistory x i).headD a) (x i)
  · rw [if_pos hx]
    have hf : (fun T => walkProduct (labelNoiseMatrix G d label p T) k a x) =
        (fun T => ∏ i : Fin k,
          (((if label (walkEdge a x i) ∈ T then 1 / p (label (walkEdge a x i)) else 0) - 1) /
            d ((prefixHistory x i).headD a))) := by
      funext T
      rw [walkProduct_eq_prod]
      apply Finset.prod_congr rfl
      intro i hi
      simp only [labelNoiseMatrix, hx i, ite_true, walkEdge]
      by_cases ht : label s((prefixHistory x i).headD a, x i) ∈ T
      · simp only [ht, ite_true]
      · simp only [ht, ite_false]
    rw [hf]
    have h := scaled_noise_product_bound E p (fun i => label (walkEdge a x i))
      (fun i => he _ _ (hx i)) (fun i => d ((prefixHistory x i).headD a))
      (fun i => hd _) (fun i => hp0 _ _ (hx i)) (fun i => hp1 _ _ (hx i)) U hU
      (fun i => hqd _ _ (hx i))
    rw [firstIndex_injective_map (walkEdge a x) label hinj] at h
    exact h
  · rw [if_neg hx]
    have hf : (fun T => walkProduct (labelNoiseMatrix G d label p T) k a x) = (fun _ => 0) := by
      funext T
      rw [walkProduct_eq_prod]
      push Not at hx
      obtain ⟨i, hi⟩ := hx
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [labelNoiseMatrix, hi, ite_false]
    rw [hf, expect_const]

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

lemma firstWeight_nonneg {V : Type*} [DecidableEq V] (d : V → ℝ)
    (hd : ∀ v, 0 < d v) {k : ℕ} (a : V) (x : Fin k → V) : 0 ≤ firstWeight d a x := by
  unfold firstWeight
  apply Finset.prod_nonneg
  intro i hi
  split_ifs
  · exact (one_div_pos.mpr (hd _)).le
  · exact zero_le_one

lemma labelled_trace_moment {V α : Type*} [Fintype V] [DecidableEq V] [DecidableEq α]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : V → ℝ)
    (hd : ∀ v, 0 < d v) (hg : ∀ v, (G.degree v : ℝ) ≤ d v)
    (label : Sym2 V → α) (hinj : Function.Injective label)
    (E : Finset α) (p : α → ℝ)
    (he : ∀ i j, G.Adj i j → label s(i,j) ∈ E)
    (hp0 : ∀ i j, G.Adj i j → 0 < p (label s(i,j)))
    (hp1 : ∀ i j, G.Adj i j → p (label s(i,j)) ≤ 1)
    (U : ℝ) (hU : 1 ≤ U)
    (hqd : ∀ i j, G.Adj i j → p (label s(i,j)) < 1 → U ≤ p (label s(i,j)) * d i)
    (k : ℕ) :
    expect E p (fun T => Matrix.trace ((labelNoiseMatrix G d label p T)^k)) ≤
      (Fintype.card V : ℝ) * (k : ℝ)^k * (1 / U)^(k/2) := by
  classical
  have hf : (fun T => Matrix.trace ((labelNoiseMatrix G d label p T)^k)) =
      (fun T => ∑ a : V, ∑ x : Fin k → V, if walkEnd k a x = a then
        walkProduct (labelNoiseMatrix G d label p T) k a x else 0) := by
    funext T
    exact trace_pow_walks _ _
  rw [hf, expect_sum]
  simp_rw [expect_sum]
  have hR : 0 ≤ (1 / U)^(k/2) := by positivity
  calc
    _ ≤ ∑ a : V, ∑ x : Fin k → V,
        (if (∀ i : Fin k, G.Adj ((prefixHistory x i).headD a) (x i)) then firstWeight d a x else 0) *
          (1 / U)^(k/2) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro x hx
      by_cases hc : walkEnd k a x = a
      · simp only [hc, ite_true]
        have h := expected_walk_bound G d hd label hinj E p he hp0 hp1 U hU hqd k a x
        simpa only [ite_mul, zero_mul] using h
      · simp only [hc, ite_false, expect_const]
        apply mul_nonneg _ hR
        split_ifs
        · exact firstWeight_nonneg d hd a x
        · exact le_rfl
    _ ≤ ∑ _a : V, (k : ℝ)^k * (1 / U)^(k/2) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (all_code_mass_le G d hd hg k a) hR
    _ = _ := by simp [mul_assoc]

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma mem_inducedEdges_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (i j : V) :
    s(i,j) ∈ inducedEdges G S ↔ G.Adj i j ∧ i ∈ S ∧ j ∈ S := by
  simp [inducedEdges]

lemma inducedDegree_le_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (i : V) : inducedDegree G S i ≤ G.degree i := by
  unfold inducedDegree
  simpa using Finset.card_le_card (Finset.inter_subset_left :
    G.neighborFinset i ∩ S ⊆ G.neighborFinset i)

lemma inducedDegree_pos_of_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {i j : V} (h : s(i,j) ∈ inducedEdges G S) :
    0 < inducedDegree G S i := by
  obtain ⟨hij, _, hj⟩ := (mem_inducedEdges_iff G S i j).mp h
  exact Finset.card_pos.mpr ⟨j, Finset.mem_inter.mpr ⟨by simpa using hij, hj⟩⟩

lemma induced_sampleProb_valid (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {U : ℝ} (hU : 0 < U) {e : Sym2 V}
    (he : e ∈ inducedEdges G S) :
    0 < sampleProb (fun v => (inducedDegree G S v : ℝ)) U e ∧
    sampleProb (fun v => (inducedDegree G S v : ℝ)) U e ≤ 1 := by
  induction e using Sym2.ind with
  | _ i j =>
    have hi : (0 : ℝ) < inducedDegree G S i := by
      exact_mod_cast inducedDegree_pos_of_edge G S he
    have hj : (0 : ℝ) < inducedDegree G S j := by
      have he' : s(j,i) ∈ inducedEdges G S := by simpa only [Sym2.eq_swap] using he
      exact_mod_cast inducedDegree_pos_of_edge G S he'
    change 0 < min 1 (U / min (inducedDegree G S i : ℝ) (inducedDegree G S j : ℝ)) ∧ _
    exact ⟨lt_min zero_lt_one (div_pos hU (lt_min hi hj)), min_le_left _ _⟩

lemma sampleSubgraphProb_valid (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (k : ℕ) (ε lam : ℝ) (hU : 0 < sampleUpsilon k ε lam)
    {e : Sym2 V} (he : e ∈ inducedEdges G S) :
    0 < sampleSubgraphProb G S k ε lam e ∧ sampleSubgraphProb G S k ε lam e ≤ 1 :=
  induced_sampleProb_valid G S hU he

end SpectralSparsify.Sampling.SSFresh
end

section

namespace SpectralSparsify.Sampling.SSFresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma induced_sampleProb_ge_ambient (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {U : ℝ} (hU : 0 ≤ U) {i j : V}
    (he : s(i,j) ∈ inducedEdges G S) :
    min 1 (U / min (G.degree i : ℝ) (G.degree j : ℝ)) ≤
      sampleProb (fun v => (inducedDegree G S v : ℝ)) U s(i,j) := by
  have hi : (0 : ℝ) < inducedDegree G S i := by
    exact_mod_cast inducedDegree_pos_of_edge G S he
  have hj : (0 : ℝ) < inducedDegree G S j := by
    have he' : s(j,i) ∈ inducedEdges G S := by simpa only [Sym2.eq_swap] using he
    exact_mod_cast inducedDegree_pos_of_edge G S he'
  have hi' : (inducedDegree G S i : ℝ) ≤ G.degree i := by
    exact_mod_cast inducedDegree_le_degree G S i
  have hj' : (inducedDegree G S j : ℝ) ≤ G.degree j := by
    exact_mod_cast inducedDegree_le_degree G S j
  change min 1 _ ≤ min 1 _
  exact min_le_min_left 1 (div_le_div_of_nonneg_left hU (lt_min hi hj)
    (min_le_min hi' hj'))

lemma induced_sampleProb_inverse_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {U : ℝ} (hU : 0 < U) {i j : V}
    (he : s(i,j) ∈ inducedEdges G S)
    (hq : sampleProb (fun v => (inducedDegree G S v : ℝ)) U s(i,j) < 1) :
    1 / sampleProb (fun v => (inducedDegree G S v : ℝ)) U s(i,j) ≤
      (G.degree i : ℝ) / U := by
  have hi : (0 : ℝ) < inducedDegree G S i := by
    exact_mod_cast inducedDegree_pos_of_edge G S he
  have hj : (0 : ℝ) < inducedDegree G S j := by
    have he' : s(j,i) ∈ inducedEdges G S := by simpa only [Sym2.eq_swap] using he
    exact_mod_cast inducedDegree_pos_of_edge G S he'
  have hm : 0 < min (inducedDegree G S i : ℝ) (inducedDegree G S j : ℝ) := lt_min hi hj
  have hratio : U / min (inducedDegree G S i : ℝ) (inducedDegree G S j : ℝ) < 1 := by
    change min 1 _ < 1 at hq
    exact (min_lt_iff.mp hq).resolve_left (lt_irrefl _)
  change 1 / min 1 _ ≤ _
  rw [min_eq_right hratio.le, one_div_div]
  exact div_le_div_of_nonneg_right
    ((min_le_left _ _).trans (by exact_mod_cast inducedDegree_le_degree G S i)) hU.le

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
open Matrix Unitary

namespace SpectralSparsify.Sampling.SSFresh

variable {V : Type*} [Fintype V]

lemma sqNorm_nonneg (x : V → ℝ) : 0 ≤ sqNorm x := by
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

lemma sqNorm_pos {x : V → ℝ} (hx : x ≠ 0) : 0 < sqNorm x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  apply Finset.sum_pos'
  · intro j _; exact mul_self_nonneg (x j)
  · exact ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩

lemma quad_conjugate (U A : Matrix V V ℝ) (x : V → ℝ) :
    quad (U * A * Uᵀ) x = quad A (Uᵀ *ᵥ x) := by
  unfold quad
  simp only [← mulVec_mulVec]
  rw [dotProduct_mulVec]
  have h : x ᵥ* U = Uᵀ *ᵥ x := by
    simpa only [transpose_transpose] using vecMul_transpose Uᵀ x
  rw [h]

variable [DecidableEq V]

lemma quad_diagonal (d x : V → ℝ) :
    quad (diagonal d) x = ∑ i, d i * x i ^ 2 := by
  simp only [quad, mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma trace_pow_eigenvalues (A : Matrix V V ℝ) (hA : A.IsHermitian) (k : ℕ) :
    Matrix.trace (A ^ k) = ∑ i, hA.eigenvalues i ^ k := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self, one_mul]
  simp [diagonal_pow, trace_diagonal]

lemma quad_eigenvalues (A : Matrix V V ℝ) (hA : A.IsHermitian) (x : V → ℝ) :
    quad A x = ∑ i, hA.eigenvalues i *
      ((hA.eigenvectorUnitary : Matrix V V ℝ)ᵀ *ᵥ x) i ^ 2 := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [conjStarAlgAut_apply]
  simp only [RCLike.ofReal_real_eq_id,
    star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  exact (quad_conjugate _ _ _).trans (quad_diagonal _ _)

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
open Matrix

namespace SpectralSparsify.Sampling.SSFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma conjugate_pow (P Q A : Matrix V V ℝ) (hpq : P * Q = 1) (hqp : Q * P = 1)
    (k : ℕ) : (P * A * Q) ^ k = P * A ^ k * Q := by
  induction k with
  | zero => simp [hpq]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc
      P * A ^ k * Q * (P * A * Q) = P * A ^ k * (Q * P) * A * Q := by noncomm_ring
      _ = P * (A ^ k * A) * Q := by rw [hqp]; simp only [mul_one, mul_assoc]

lemma trace_conjugate_pow (P Q A : Matrix V V ℝ) (hpq : P * Q = 1) (hqp : Q * P = 1)
    (k : ℕ) : Matrix.trace ((P * A * Q) ^ k) = Matrix.trace (A ^ k) := by
  rw [conjugate_pow P Q A hpq hqp, trace_mul_cycle, hqp, one_mul]

lemma symError_trace_eq_rowError (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ i, 0 < G.degree i) (S : Finset V) (q : Sym2 V → ℝ)
    (T : Finset (Sym2 V)) (k : ℕ) :
    Matrix.trace (symError G S q T ^ k) = Matrix.trace (rowError G S q T ^ k) := by
  let P : Matrix S S ℝ := diagonal fun i => Real.sqrt (G.degree i)
  let Q : Matrix S S ℝ := diagonal fun i => 1 / Real.sqrt (G.degree i)
  have hn (i : S) : Real.sqrt (G.degree i : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.2 (hdeg i)))
  have hpq : P * Q = 1 := by
    simp only [P, Q, diagonal_mul_diagonal, mul_one_div]
    have hf : (fun i : S => Real.sqrt (G.degree i) / Real.sqrt (G.degree i)) = fun _ => (1 : ℝ) := by
      funext i; exact div_self (hn i)
    rw [hf, diagonal_one]
  have hqp : Q * P = 1 := by
    simp only [P, Q, diagonal_mul_diagonal]
    have hf : (fun i : S => (1 / Real.sqrt (G.degree i)) * Real.sqrt (G.degree i)) = fun _ => (1 : ℝ) := by
      funext i; exact one_div_mul_cancel (hn i)
    rw [hf, diagonal_one]
  have heq : symError G S q T = P * rowError G S q T * Q := by
    ext i j
    simp only [P, Q, diagonal_mul, mul_diagonal, symError, rowError]
    split_ifs
    · have hs := Real.sq_sqrt (show 0 ≤ (G.degree i : ℝ) by positivity)
      have hd : (G.degree i : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.2 (hdeg i))
      field_simp [hn i, hn j]
      rw [hs]
    · ring
  rw [heq]
  exact trace_conjugate_pow P Q _ hpq hqp k

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

lemma induced_degree_le_ambient {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : S) :
    (G.induce (S : Set V)).degree v ≤ G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  let f : (G.induce (S : Set V)).neighborSet v → G.neighborSet v :=
    fun w => ⟨w.val.val, w.property⟩
  apply Fintype.card_le_of_injective f
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : G.neighborSet v => z.val) h

lemma rowError_trace_moment {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v)
    (S : Finset V) (U : ℝ) (hU : 1 ≤ U) (k : ℕ) :
    expect (inducedEdges G S) (sampleProb (fun v => (inducedDegree G S v : ℝ)) U)
      (fun T => Matrix.trace ((rowError G S (sampleProb (fun v => (inducedDegree G S v : ℝ)) U) T)^k)) ≤
      (S.card : ℝ) * (k : ℝ)^k * (1 / U)^(k/2) := by
  classical
  let H := G.induce (S : Set V)
  let d : S → ℝ := fun i => (G.degree i : ℝ)
  let label : Sym2 S → Sym2 V := Sym2.map Subtype.val
  let p := sampleProb (fun v => (inducedDegree G S v : ℝ)) U
  have hU0 : 0 < U := by linarith
  have hd (i : S) : 0 < d i := by
    dsimp only [d]
    exact_mod_cast hdeg i
  have hg (i : S) : (H.degree i : ℝ) ≤ d i := by
    dsimp only [H, d]
    exact_mod_cast induced_degree_le_ambient G S i
  have he (i j : S) (hij : H.Adj i j) : label s(i,j) ∈ inducedEdges G S := by
    exact (mem_inducedEdges_iff G S i j).mpr ⟨hij, i.property, j.property⟩
  have hp (i j : S) (hij : H.Adj i j) : 0 < p (label s(i,j)) ∧ p (label s(i,j)) ≤ 1 :=
    induced_sampleProb_valid G S hU0 (he i j hij)
  have hqd (i j : S) (hij : H.Adj i j) (hq : p (label s(i,j)) < 1) :
      U ≤ p (label s(i,j)) * d i := by
    have hb := induced_sampleProb_inverse_bound G S hU0 (he i j hij) hq
    have hc := (div_le_div_iff₀ (hp i j hij).1 hU0).mp hb
    simpa only [one_mul, mul_one, mul_comm, d] using hc
  have h := labelled_trace_moment H d hd hg label (Sym2.map.injective Subtype.val_injective)
    (inducedEdges G S) p he (fun i j hij => (hp i j hij).1) (fun i j hij => (hp i j hij).2)
    U hU hqd k
  have hA (T : Finset (Sym2 V)) : labelNoiseMatrix H d label p T = rowError G S p T := by
    rfl
  simp_rw [hA] at h
  have hcard : Fintype.card (↑(S : Set V)) = S.card := Fintype.card_coe S
  rw [hcard] at h
  exact h

lemma sample_rowError_trace_moment {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v)
    (S : Finset V) (k : ℕ) (ε lam : ℝ) (hU : 1 ≤ sampleUpsilon k ε lam) :
    expect (inducedEdges G S) (sampleSubgraphProb G S k ε lam)
      (fun T => Matrix.trace ((rowError G S (sampleSubgraphProb G S k ε lam) T)^k)) ≤
      (S.card : ℝ) * (k : ℝ)^k * (1 / sampleUpsilon k ε lam)^(k/2) :=
  rowError_trace_moment G hdeg S (sampleUpsilon k ε lam) hU k

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
open Matrix Unitary WithLp

namespace SpectralSparsify.Sampling.SSFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma sqNorm_unitary_coords (U : Matrix.unitaryGroup V ℝ) (x : V → ℝ) :
    sqNorm ((U : Matrix V V ℝ)ᵀ *ᵥ x) = sqNorm x := by
  have h := quad_conjugate (U : Matrix V V ℝ) (1 : Matrix V V ℝ) x
  have hu : (U : Matrix V V ℝ) * (U : Matrix V V ℝ)ᵀ = 1 := by
    simpa only [coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      (coe_mul_star_self U)
  simpa only [mul_one, hu, quad, one_mulVec, sqNorm] using h.symm

lemma eigenvalues_abs_le_of_normLE (A : Matrix V V ℝ) (hA : A.IsHermitian)
    {t : ℝ} (ht : NormLE A t) (i : V) : |hA.eigenvalues i| ≤ t := by
  apply ht _ _
  · exact (ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero i)
  · exact hA.mulVec_eigenvectorBasis i

lemma abs_quad_le_of_normLE (A : Matrix V V ℝ) (hA : A.IsHermitian)
    {t : ℝ} (ht : NormLE A t) (x : V → ℝ) : |quad A x| ≤ t * sqNorm x := by
  rw [quad_eigenvalues A hA]
  calc
    |∑ i, hA.eigenvalues i * ((hA.eigenvectorUnitary : Matrix V V ℝ)ᵀ *ᵥ x) i ^ 2| ≤
        ∑ i, |hA.eigenvalues i * ((hA.eigenvectorUnitary : Matrix V V ℝ)ᵀ *ᵥ x) i ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, t * ((hA.eigenvectorUnitary : Matrix V V ℝ)ᵀ *ᵥ x) i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_pow, sq_abs]
      exact mul_le_mul_of_nonneg_right (eigenvalues_abs_le_of_normLE A hA ht i) (sq_nonneg _)
    _ = t * sqNorm x := by
      rw [← Finset.mul_sum]
      have hn := sqNorm_unitary_coords hA.eigenvectorUnitary x
      simp only [sqNorm, dotProduct, ← pow_two] at hn
      rw [hn]
      simp only [sqNorm, dotProduct, pow_two]

lemma trace_pow_nonneg (A : Matrix V V ℝ) (hA : A.IsHermitian)
    {k : ℕ} (hk : Even k) : 0 ≤ Matrix.trace (A ^ k) := by
  rw [trace_pow_eigenvalues A hA]
  exact Finset.sum_nonneg fun i _ => hk.pow_nonneg _

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
open Matrix

namespace SpectralSparsify.Sampling.SSFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma eigenvalue_eq_eigenvalues (A : Matrix V V ℝ) (hA : A.IsHermitian)
    {mu : ℝ} {x : V → ℝ} (hx : x ≠ 0) (he : A *ᵥ x = mu • x) :
    ∃ i, hA.eigenvalues i = mu := by
  have hmem : mu ∈ spectrum ℝ A := by
    rw [← Matrix.spectrum_toLin']
    apply Module.End.HasEigenvalue.mem_spectrum
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := x)
    exact ⟨Module.End.mem_eigenspace_iff.mpr he, hx⟩
  rwa [hA.spectrum_real_eq_range_eigenvalues] at hmem

lemma eigenvalue_pow_le_trace (A : Matrix V V ℝ) (hA : A.IsHermitian)
    {k : ℕ} (hk : Even k) {mu : ℝ} {x : V → ℝ}
    (hx : x ≠ 0) (he : A *ᵥ x = mu • x) : |mu| ^ k ≤ Matrix.trace (A ^ k) := by
  obtain ⟨i, rfl⟩ := eigenvalue_eq_eigenvalues A hA hx he
  rw [trace_pow_eigenvalues A hA, ← abs_pow, abs_of_nonneg (hk.pow_nonneg _)]
  exact Finset.single_le_sum (fun j _ => hk.pow_nonneg _) (Finset.mem_univ i)

lemma normGE_implies_trace (A : Matrix V V ℝ) (hA : A.IsHermitian)
    {k : ℕ} (hk : Even k) {t : ℝ} (ht : 0 ≤ t) (h : NormGE A t) :
    t ^ k ≤ Matrix.trace (A ^ k) := by
  obtain ⟨mu, x, hx, he, hm⟩ := h
  exact (pow_le_pow_left₀ ht hm k).trans (eigenvalue_pow_le_trace A hA hk hx he)

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh
variable {α : Type*} [DecidableEq α]

open scoped Classical in
lemma prob_eq_expect (E : Finset α) (p : α → ℝ) (P : Finset α → Prop) :
    prob E p P = expect E p (fun T => if P T then 1 else 0) := by
  classical
  unfold prob expect
  apply Finset.sum_congr rfl
  intro T hT
  by_cases h : P T <;> simp [h]

lemma prob_nonneg (E : Finset α) (p : α → ℝ)
    (hp0 : ∀ e ∈ E, 0 ≤ p e) (hp1 : ∀ e ∈ E, p e ≤ 1)
    (P : Finset α → Prop) : 0 ≤ prob E p P := by
  classical
  unfold prob
  apply Finset.sum_nonneg
  intro T hT
  split_ifs
  · exact outcomeProb_nonneg E p hp0 hp1 (Finset.mem_powerset.mp hT)
  · exact le_rfl

lemma prob_mono (E : Finset α) (p : α → ℝ)
    (hp0 : ∀ e ∈ E, 0 ≤ p e) (hp1 : ∀ e ∈ E, p e ≤ 1)
    {P Q : Finset α → Prop} (hPQ : ∀ T ⊆ E, P T → Q T) :
    prob E p P ≤ prob E p Q := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  apply expect_mono E p hp0 hp1
  intro T hT
  by_cases hP : P T
  · simp only [hP, hPQ T hT hP, ite_true, le_refl]
  · simp only [hP, ite_false]
    split_ifs <;> norm_num

lemma prob_le_one (E : Finset α) (p : α → ℝ)
    (hp0 : ∀ e ∈ E, 0 ≤ p e) (hp1 : ∀ e ∈ E, p e ≤ 1)
    (P : Finset α → Prop) : prob E p P ≤ 1 := by
  classical
  rw [prob_eq_expect]
  calc
    _ ≤ expect E p (fun _ => 1) := by
      apply expect_mono E p hp0 hp1
      intro T hT
      split_ifs <;> norm_num
    _ = 1 := expect_const E p 1

lemma prob_markov (E : Finset α) (p : α → ℝ)
    (hp0 : ∀ e ∈ E, 0 ≤ p e) (hp1 : ∀ e ∈ E, p e ≤ 1)
    (f : Finset α → ℝ) (hf : ∀ T ⊆ E, 0 ≤ f T) (b : ℝ) :
    prob E p (fun T => b ≤ f T) * b ≤ expect E p f := by
  classical
  rw [prob_eq_expect, ← expect_mul_const]
  apply expect_mono E p hp0 hp1
  intro T hT
  by_cases h : b ≤ f T
  · simp only [h, ite_true, one_mul]
  · simpa only [h, ite_false, zero_mul] using hf T hT

lemma prob_exp_bound (E : Finset α) (p : α → ℝ)
    (hp0 : ∀ e ∈ E, 0 ≤ p e) (hp1 : ∀ e ∈ E, p e ≤ 1)
    (f : Finset α → ℝ) (b : ℝ) :
    prob E p (fun T => b ≤ f T) ≤ Real.exp (-b) * expect E p (fun T => Real.exp (f T)) := by
  have hm := prob_markov E p hp0 hp1 (fun T => Real.exp (f T))
    (fun T _ => (Real.exp_pos (f T)).le) (Real.exp b)
  have he : (fun T => Real.exp b ≤ Real.exp (f T)) = (fun T => b ≤ f T) := by
    funext T
    exact propext Real.exp_le_exp
  rw [he] at hm
  have h := mul_le_mul_of_nonneg_right hm (Real.exp_pos (-b)).le
  simpa only [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one,
    mul_comm (expect E p (fun T => Real.exp (f T)))] using h

lemma prob_union (E : Finset α) (p : α → ℝ)
    (hp0 : ∀ e ∈ E, 0 ≤ p e) (hp1 : ∀ e ∈ E, p e ≤ 1)
    (P Q : Finset α → Prop) :
    prob E p (fun T => P T ∨ Q T) ≤ prob E p P + prob E p Q := by
  classical
  rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
  apply expect_mono E p hp0 hp1
  intro T hT
  by_cases hP : P T <;> by_cases hQ : Q T <;> simp [hP, hQ]

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
open Matrix

namespace SpectralSparsify.Sampling.SSFresh

lemma sqrt_pow_even {U : ℝ} (hU : 0 ≤ U) {k : ℕ} (hk : Even k) :
    Real.sqrt U ^ k = U ^ (k / 2) := by
  obtain ⟨m, hm⟩ := hk
  have hkm : k = 2 * m := by omega
  rw [hkm, pow_mul, Real.sq_sqrt hU]
  simp

lemma trace_threshold_power {U : ℝ} (hU : 0 < U) {k : ℕ} (hk : Even k) :
    (4 * (k : ℝ) / Real.sqrt U) ^ k =
      (4 : ℝ) ^ k * (k : ℝ) ^ k * (1 / U) ^ (k / 2) := by
  rw [div_pow, mul_pow, sqrt_pow_even hU.le hk]
  simp only [div_eq_mul_inv, one_mul, inv_pow]

lemma trace_markov_probability {E V : Type*} [DecidableEq E] [Fintype V] [DecidableEq V]
    (F : Finset E) (q : E → ℝ) (hq0 : ∀ e ∈ F, 0 ≤ q e) (hq1 : ∀ e ∈ F, q e ≤ 1)
    (A : Finset E → Matrix V V ℝ) (hA : ∀ T ⊆ F, (A T).IsHermitian)
    (n : ℝ) {U : ℝ} (hU : 0 < U) {k : ℕ} (hk : Even k) (hk0 : 0 < k)
    (hmoment : expect F q (fun T => Matrix.trace (A T ^ k)) ≤
      n * (k : ℝ) ^ k * (1 / U) ^ (k / 2)) :
    prob F q (fun T => NormGE (A T) (4 * (k : ℝ) / Real.sqrt U)) ≤ n / (4 : ℝ) ^ k := by
  let t := 4 * (k : ℝ) / Real.sqrt U
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hsub := prob_mono F q hq0 hq1
    (P := fun T => NormGE (A T) t) (Q := fun T => t ^ k ≤ Matrix.trace (A T ^ k))
    (fun T hT h => normGE_implies_trace (A T) (hA T hT) hk ht h)
  have hm := prob_markov F q hq0 hq1 (fun T => Matrix.trace (A T ^ k))
    (fun T hT => trace_pow_nonneg (A T) (hA T hT) hk) (t ^ k)
  have hh := (mul_le_mul_of_nonneg_right hsub (pow_nonneg ht k)).trans (hm.trans hmoment)
  dsimp [t] at hh
  rw [trace_threshold_power hU hk] at hh
  have hc : 0 < (k : ℝ) ^ k * (1 / U) ^ (k / 2) := by positivity
  have hh' : (prob F q (fun T => NormGE (A T) (4 * (k : ℝ) / Real.sqrt U)) * 4 ^ k) *
      ((k : ℝ) ^ k * (1 / U) ^ (k / 2)) ≤ n * ((k : ℝ) ^ k * (1 / U) ^ (k / 2)) := by
    simpa only [mul_assoc] using hh
  have hh'' := (mul_le_mul_iff_left₀ hc).mp hh'
  exact (le_div_iff₀ (by positivity : 0 < (4 : ℝ) ^ k)).mpr hh''

end SpectralSparsify.Sampling.SSFresh
end

section
namespace SpectralSparsify.Sampling.SSFresh

lemma log_size_pow (s k : ℕ) (h : Real.logb 2 (s:ℝ) ≤ (k:ℝ)) :
    (s:ℝ) ≤ (2:ℝ)^k := by
  by_cases hs : s=0
  · subst s
    simpa only [Nat.cast_zero] using (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k)
  have hs0 : (0:ℝ) < s := by exact_mod_cast (Nat.pos_of_ne_zero hs)
  have hh := (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hs0).mp h
  simpa only [Real.rpow_natCast] using hh

lemma log_failure_pow (p : ℝ) (hp : 0 < p) (k : ℕ)
    (h : Real.logb 2 (3/p) ≤ (k:ℝ)) : 3/p ≤ (2:ℝ)^k := by
  have hh := (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2)
    (show 0 < 3/p by positivity)).mp h
  simpa only [Real.rpow_natCast] using hh

lemma sampling_k_ge_four (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : ℕ) (heven : Even k) (hk : Real.logb 2 (3/p) ≤ (k:ℝ)) : 4 ≤ k := by
  have hh := log_failure_pow p hp k hk
  have hlt : (4:ℝ) < 3/p := (lt_div_iff₀ hp).2 (by linarith)
  have hk3 : 3 ≤ k := by
    by_contra hn
    have hkle : k ≤ 2 := by omega
    have hpow : (2:ℝ)^k ≤ (2:ℝ)^2 := pow_le_pow_right₀ (by norm_num) hkle
    norm_num at hpow
    linarith
  rcases heven with ⟨j,hj⟩
  omega

lemma inverse_power_budget (p : ℝ) (hp : 0 < p) (k : ℕ)
    (hk : Real.logb 2 (3/p) ≤ (k:ℝ)) : 1/(2:ℝ)^k ≤ p/3 := by
  have hh := (div_le_iff₀ hp).mp (log_failure_pow p hp k hk)
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<2^k) (by norm_num : (0:ℝ)<3)).2
  nlinarith

lemma trace_probability_budget (s k : ℕ) (p : ℝ) (hp : 0 < p)
    (hk1 : Real.logb 2 (3/p) ≤ (k:ℝ)) (hk2 : Real.logb 2 (s:ℝ) ≤ (k:ℝ)) :
    (s:ℝ)/(4:ℝ)^k ≤ p/3 := by
  have hsize := log_size_pow s k hk2
  have hfour : (4:ℝ)^k = (2:ℝ)^k*(2:ℝ)^k := by
    rw [show (4:ℝ)=2*2 by norm_num,mul_pow]
  calc
    _ ≤ (2:ℝ)^k/(4:ℝ)^k := div_le_div_of_nonneg_right hsize (by positivity)
    _ = 1/(2:ℝ)^k := by rw [hfour]; field_simp
    _ ≤ _ := inverse_power_budget p hp k hk1

lemma sampleUpsilon_lower (k : ℕ) (ε lam : ℝ)
    (he0 : 0 < ε) (he1 : ε < 1/2) (hl0 : 0 < lam) (hl2 : lam ≤ 2) :
    144*(k:ℝ)^2 ≤ sampleUpsilon k ε lam := by
  have hd : 0 < ε*lam := mul_pos he0 hl0
  have hd1 : ε*lam < 1 := by
    have hh := mul_le_mul_of_nonneg_left hl2 he0.le
    nlinarith
  have hn : 0 ≤ 12*(k:ℝ) := by positivity
  have hratio : 12*(k:ℝ) ≤ 12*(k:ℝ)/(ε*lam) := by
    apply (le_div_iff₀ hd).2
    nlinarith [mul_nonneg hn (show 0 ≤ 1-ε*lam by linarith)]
  unfold sampleUpsilon
  nlinarith [sq_nonneg (12*(k:ℝ)/(ε*lam)-12*(k:ℝ))]

lemma quadratic_exponential_budget (k : ℕ) (hk : 1 ≤ k) :
    2*(2:ℝ)^k*Real.exp (-4*(k:ℝ)^2) ≤ 1/(2:ℝ)^k := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hl := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
  have hex : (2:ℝ)*(2:ℝ)^k*(2:ℝ)^k ≤ Real.exp (4*(k:ℝ)^2) := by
    calc
      _ = (2:ℝ)^(2*k+1) := by rw [pow_succ, show 2*k=k+k by omega, pow_add]; ring
      _ = Real.exp (((2*k+1:ℕ):ℝ)*Real.log 2) := by
        rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        push_cast
        have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*(k:ℝ)+1 by positivity)
        nlinarith
  have hm := mul_le_mul_of_nonneg_right hex (Real.exp_pos (-4*(k:ℝ)^2)).le
  have he : Real.exp (4*(k:ℝ)^2)*Real.exp (-4*(k:ℝ)^2)=1 := by
    rw [← Real.exp_add]
    simp
  rw [he] at hm
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2^k)).2
  nlinarith

lemma degree_probability_budget (s k : ℕ) (p : ℝ) (hp : 0 < p) (hk : 1 ≤ k)
    (hk1 : Real.logb 2 (3/p) ≤ (k:ℝ)) (hk2 : Real.logb 2 (s:ℝ) ≤ (k:ℝ)) :
    2*(s:ℝ)*Real.exp (-4*(k:ℝ)^2) ≤ p/3 := by
  calc
    _ ≤ 2*(2:ℝ)^k*Real.exp (-4*(k:ℝ)^2) := by
      gcongr
      exact log_size_pow s k hk2
    _ ≤ 1/(2:ℝ)^k := quadratic_exponential_budget k hk
    _ ≤ _ := inverse_power_budget p hp k hk1

lemma edge_count_probability_budget (s k : ℕ) (p U : ℝ) (hp : 0 < p)
    (hs : 1 ≤ s) (hk : 1 ≤ k) (hU : 144*(k:ℝ)^2 ≤ U)
    (hk1 : Real.logb 2 (3/p) ≤ (k:ℝ)) :
    Real.exp (-U*(s:ℝ)/4) ≤ p/3 := by
  have hsR : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hU0 : 0 ≤ U := by nlinarith
  have hUs : U ≤ U*(s:ℝ) := by nlinarith [mul_nonneg hU0 (show 0 ≤ (s:ℝ)-1 by linarith)]
  have hl := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
  have hkl := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg k : (0:ℝ) ≤ k)
  calc
    _ ≤ Real.exp (-((k:ℝ)*Real.log 2)) := Real.exp_le_exp.mpr (by nlinarith)
    _ = 1/(2:ℝ)^k := by rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num),one_div]
    _ ≤ _ := inverse_power_budget p hp k hk1

lemma spectral_approx_scalar (ε a b : ℝ) (he0 : 0 < ε) (he1 : ε < 1/2)
    (ha : 0 ≤ a) (hlo : (1-2*ε/3)*a ≤ b) (hhi : b ≤ (1+2*ε/3)*a) :
    (1/(1+ε))*b ≤ a ∧ a ≤ (1+ε)*b := by
  have hs : 0 < 1+ε := by linarith
  constructor
  · have hh : b ≤ a*(1+ε) := by nlinarith
    have hdiv := (div_le_iff₀ hs).2 hh
    simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using hdiv
  · have hmult := mul_le_mul_of_nonneg_left hlo hs.le
    have hcoef : 0 ≤ ε*(1-2*ε) := mul_nonneg he0.le (by linarith)
    have hpos := mul_nonneg hcoef ha
    nlinarith

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
open Matrix

namespace SpectralSparsify.Sampling.SSFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma quad_lapMat (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i) (x : V → ℝ) :
    quad (lapMat w) x = lapForm w x := by
  have hflip : (∑ i, ∑ j, w i j * x j ^ 2) = ∑ i, ∑ j, w i j * x i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hw j i]
  have hq : quad (lapMat w) x =
      (∑ i, ∑ j, w i j * x i ^ 2) - ∑ i, ∑ j, w i j * x i * x j := by
    change x ⬝ᵥ ((diagonal (wDegree w) - Matrix.of w) *ᵥ x) = _
    rw [sub_mulVec, dotProduct_sub]
    simp only [dotProduct, mulVec_diagonal]
    simp only [mulVec, of_apply, dotProduct, wDegree, Finset.mul_sum, Finset.sum_mul]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
      apply Finset.sum_congr rfl <;> intro j _ <;> ring
  have hl : lapForm w x = (1 / 2 : ℝ) *
      ((∑ i, ∑ j, w i j * x i ^ 2) -
        2 * (∑ i, ∑ j, w i j * x i * x j) + ∑ i, ∑ j, w i j * x j ^ 2) := by
    unfold lapForm
    congr 1
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hq, hl, hflip]
  ring

lemma lapMat_isHermitian (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i) :
    (lapMat w).IsHermitian := by
  apply IsHermitian.sub
  · exact isHermitian_diagonal_of_self_adjoint _ (IsSelfAdjoint.all _)
  · change (Matrix.of w).conjTranspose = Matrix.of w
    ext i j
    simpa only [conjTranspose_apply, star_trivial, of_apply] using hw j i

omit [Fintype V] [DecidableEq V] in
lemma adjWeight_symmetric (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ i j, adjWeight G i j = adjWeight G j i := by
  intro i j
  simp only [adjWeight, G.adj_comm]

lemma adjWeight_lapMat (G : SimpleGraph V) [DecidableRel G.Adj] :
    lapMat (adjWeight G) = G.lapMatrix ℝ := by
  have hd : wDegree (adjWeight G) = fun i => (G.degree i : ℝ) := by
    funext i
    simp only [wDegree, adjWeight, SimpleGraph.degree_eq_sum_if_adj]
  unfold lapMat degMat
  rw [hd]
  rfl

lemma quad_normalize (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Matrix V V ℝ) (x : V → ℝ) :
    quad (normalize G A) x = quad A (degInvSqrt G *ᵥ x) := by
  simpa only [normalize, degInvSqrt, diagonal_transpose] using
    quad_conjugate (degInvSqrt G) A x

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
open Matrix

namespace SpectralSparsify.Sampling.SSFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma normalize_isHermitian (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Matrix V V ℝ) (hA : A.IsHermitian) : (normalize G A).IsHermitian := by
  have hd : (degInvSqrt G).conjTranspose = degInvSqrt G := by
    exact isHermitian_diagonal_of_self_adjoint _ (IsSelfAdjoint.all _)
  change (degInvSqrt G * A * degInvSqrt G).conjTranspose = _
  rw [conjTranspose_mul, conjTranspose_mul, hd, hA]
  exact (mul_assoc (degInvSqrt G) A (degInvSqrt G)).symm

lemma normLap_isHermitian (G : SimpleGraph V) [DecidableRel G.Adj] :
    (normLap G).IsHermitian :=
  normalize_isHermitian G _ (G.posSemidef_lapMatrix ℝ).isHermitian

lemma normalize_kernel_forward (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ i, 0 < G.degree i) (A : Matrix V V ℝ) (x : V → ℝ)
    (hx : normalize G A *ᵥ x = 0) : A *ᵥ (degInvSqrt G *ᵥ x) = 0 := by
  have hh : degInvSqrt G *ᵥ (A *ᵥ (degInvSqrt G *ᵥ x)) = 0 := by
    simpa only [normalize, ← mulVec_mulVec] using hx
  funext i
  have hi := congrFun hh i
  have hs : Real.sqrt (G.degree i : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.2 (hdeg i)))
  simpa only [degInvSqrt, mulVec_diagonal, Pi.zero_apply, one_div,
    mul_eq_zero, inv_eq_zero, hs, false_or] using hi

lemma normalize_kernel_backward (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Matrix V V ℝ) (x : V → ℝ) (hx : A *ᵥ (degInvSqrt G *ᵥ x) = 0) :
    normalize G A *ᵥ x = 0 := by
  simp only [normalize, ← mulVec_mulVec, hx, mulVec_zero]

lemma lapMat_mulVec_apply (w : V → V → ℝ) (x : V → ℝ) (i : V) :
    (lapMat w *ᵥ x) i = ∑ j, w i j * (x i - x j) := by
  change ((diagonal (wDegree w) - Matrix.of w) *ᵥ x) i = _
  rw [sub_mulVec]
  simp only [Pi.sub_apply, mulVec_diagonal]
  simp only [wDegree, mulVec, of_apply, dotProduct, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma lapMat_kernel_of_edgeconstant (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → V → ℝ) (hsupp : ∀ i j, ¬G.Adj i j → w i j = 0)
    (x : V → ℝ) (hx : ∀ i j, G.Adj i j → x i = x j) : lapMat w *ᵥ x = 0 := by
  funext i
  rw [lapMat_mulVec_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : G.Adj i j
  · rw [hx i j h, sub_self, mul_zero]
  · rw [hsupp i j h, zero_mul]

lemma normalized_kernel_inclusion (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ i, 0 < G.degree i) (w : V → V → ℝ)
    (hsupp : ∀ i j, ¬G.Adj i j → w i j = 0) (x : V → ℝ)
    (hx : normLap G *ᵥ x = 0) : normalize G (lapMat w) *ᵥ x = 0 := by
  apply normalize_kernel_backward
  apply lapMat_kernel_of_edgeconstant G w hsupp
  apply G.lapMatrix_mulVec_eq_zero_iff_forall_adj.mp
  exact normalize_kernel_forward G hdeg _ x hx

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
open Matrix

namespace SpectralSparsify.Sampling.SSFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma sparsifier_symmetric (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : Sym2 V → ℝ) (T : Finset (Sym2 V)) :
    ∀ i j, sparsifierWeight G S q T i j = sparsifierWeight G S q T j i := by
  intro i j
  simp only [sparsifierWeight, Sym2.eq_swap]

lemma sparsifier_support (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : Sym2 V → ℝ) (T : Finset (Sym2 V))
    (hT : T ⊆ inducedEdges G S) :
    ∀ i j, ¬G.Adj i j → sparsifierWeight G S q T i j = 0 := by
  intro i j hij
  have he : s(i, j) ∉ G.edgeFinset := by simpa using hij
  have ht : s(i, j) ∉ T := fun h => he (Finset.mem_inter.mp (hT h)).1
  have hr : s(i, j) ∉ restEdges G S := fun h => he (Finset.mem_sdiff.mp h).1
  simp only [sparsifierWeight, ht, hr, ite_false]

lemma sparsifier_normalized_kernel (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ i, 0 < G.degree i) (S : Finset V) (q : Sym2 V → ℝ)
    (T : Finset (Sym2 V)) (hT : T ⊆ inducedEdges G S) (x : V → ℝ)
    (hx : normLap G *ᵥ x = 0) :
    normalize G (lapMat (sparsifierWeight G S q T)) *ᵥ x = 0 :=
  normalized_kernel_inclusion G hdeg _ (sparsifier_support G S q T hT) x hx

lemma symError_isHermitian (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : Sym2 V → ℝ) (T : Finset (Sym2 V)) :
    (symError G S q T).IsHermitian := by
  change (symError G S q T).conjTranspose = symError G S q T
  ext i j
  simp only [conjTranspose_apply, star_trivial, symError, G.adj_comm, Sym2.eq_swap, mul_comm]

end SpectralSparsify.Sampling.SSFresh
end

section

namespace SpectralSparsify.Sampling.SSFresh

lemma native_adjacency_failure_budget {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v)
    (S : Finset V) (k : ℕ) (eps lam p : ℝ) (hk : 0 < k) (heven : Even k)
    (he : 0 < eps) (he1 : eps < 1/2) (hl : 0 < lam) (hl2 : lam ≤ 2)
    (hp : 0 < p) (hk1 : Real.logb 2 (3/p) ≤ (k : ℝ))
    (hk2 : Real.logb 2 (S.card : ℝ) ≤ (k : ℝ)) :
    prob (inducedEdges G S) (sampleSubgraphProb G S k eps lam)
      (fun T => NormGE (symError G S (sampleSubgraphProb G S k eps lam) T)
        (eps * lam / 3)) ≤ p/3 := by
  classical
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hU : 1 ≤ sampleUpsilon k eps lam := by
    have hh := sampleUpsilon_lower k eps lam he he1 hl hl2
    nlinarith
  have hU0 : 0 < sampleUpsilon k eps lam := by linarith
  have hq (e : Sym2 V) (he : e ∈ inducedEdges G S) :=
    sampleSubgraphProb_valid G S k eps lam hU0 he
  have hm := sample_rowError_trace_moment G hdeg S k eps lam hU
  have hm' : expect (inducedEdges G S) (sampleSubgraphProb G S k eps lam)
      (fun T => Matrix.trace (symError G S (sampleSubgraphProb G S k eps lam) T ^ k)) ≤
      (S.card : ℝ) * (k : ℝ)^k * (1 / sampleUpsilon k eps lam)^(k/2) := by
    simpa only [symError_trace_eq_rowError G hdeg] using hm
  have hb := trace_markov_probability (inducedEdges G S) (sampleSubgraphProb G S k eps lam)
    (fun e he => (hq e he).1.le) (fun e he => (hq e he).2)
    (fun T => symError G S (sampleSubgraphProb G S k eps lam) T)
    (fun T _ => symError_isHermitian G S _ T) (S.card : ℝ) hU0 heven hk hm'
  rw [sample_trace_threshold k hk eps lam he hl] at hb
  exact hb.trans (trace_probability_budget S.card k p hp hk1 hk2)

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh
variable {α : Type*} [DecidableEq α]

lemma outcome_forced_mem (E : Finset α) (q : α → ℝ) (T : Finset α)
    (hpos : outcomeProb E q T ≠ 0) {e : α} (he : e ∈ E) (hq : q e = 1) :
    e ∈ T := by
  classical
  by_contra hT
  have hz : (∏ j ∈ E \ T, (1 - q j)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨he, hT⟩)
    simp [hq]
  apply hpos
  simp [outcomeProb, hz]

lemma prob_mono_on_support (E : Finset α) (q : α → ℝ)
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    {P Q : Finset α → Prop}
    (hPQ : ∀ T ⊆ E, outcomeProb E q T ≠ 0 → P T → Q T) :
    prob E q P ≤ prob E q Q := by
  classical
  unfold prob
  apply Finset.sum_le_sum
  intro T hT
  by_cases hz : outcomeProb E q T = 0
  · simp [hz]
  · by_cases hp : P T
    · simp [hp, hPQ T (Finset.mem_powerset.mp hT) hz hp]
    · simp only [hp, ite_false]
      split_ifs
      · exact outcomeProb_nonneg E q hq0 hq1 (Finset.mem_powerset.mp hT)
      · exact le_rfl

end SpectralSparsify.Sampling.SSFresh
end

section
namespace SpectralSparsify.Sampling.SSFresh

lemma bernoulli_centered_mgf_scalar (q x : ℝ) (hq : 0 ≤ q) (hx : |x| ≤ 1) :
    (1-q)*Real.exp (-q*x)+q*Real.exp ((1-q)*x) ≤ Real.exp (q*x^2) := by
  have hrem : Real.exp x-1-x ≤ x^2 :=
    (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le hx)
  have hmul := mul_le_mul_of_nonneg_left hrem hq
  have hlin : (1-q)+q*Real.exp x ≤ Real.exp (q*x+q*x^2) := by
    have hh := Real.add_one_le_exp (q*x+q*x^2)
    nlinarith
  calc
    _ = Real.exp (-q*x)*((1-q)+q*Real.exp x) := by
      rw [show (1-q)*x=-q*x+x by ring,Real.exp_add]
      ring
    _ ≤ Real.exp (-q*x)*Real.exp (q*x+q*x^2) :=
      mul_le_mul_of_nonneg_left hlin (Real.exp_pos _).le
    _ = Real.exp (q*x^2) := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma bernoulli_weight_mgf_scalar (q θ w β : ℝ) (hq : 0 ≤ q)
    (hw : 0 ≤ w) (hwb : w ≤ β) (ht : |θ| * β ≤ 1) :
    (1-q)*Real.exp (-θ*q*w)+q*Real.exp (θ*(1-q)*w) ≤
      Real.exp (θ^2*β*q*w) := by
  have hx : |θ*w| ≤ 1 := by
    rw [abs_mul,abs_of_nonneg hw]
    exact (mul_le_mul_of_nonneg_left hwb (abs_nonneg θ)).trans ht
  have hb := bernoulli_centered_mgf_scalar q (θ*w) hq hx
  have he1 : -θ*q*w=-q*(θ*w) := by ring
  have he2 : θ*(1-q)*w=(1-q)*(θ*w) := by ring
  rw [he1,he2]
  apply hb.trans (Real.exp_le_exp.mpr _)
  have hw2 := mul_le_mul_of_nonneg_right hwb hw
  have hp := mul_le_mul_of_nonneg_left hw2 (show 0 ≤ θ^2*q by positivity)
  nlinarith

lemma exp_half_le_seven_quarters : Real.exp (1/2:ℝ) ≤ 7/4 := by
  have he : Real.exp (1/2:ℝ)^2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hp := Real.exp_pos (1/2:ℝ)
  have hu := Real.exp_one_lt_three
  nlinarith

lemma bernoulli_count_mgf_scalar (q : ℝ) (hq : 0 ≤ q) :
    (1-q)+q*Real.exp (1/2:ℝ) ≤ Real.exp (3*q/4) := by
  have hh := mul_le_mul_of_nonneg_left exp_half_le_seven_quarters hq
  have he := Real.add_one_le_exp (3*q/4)
  nlinarith

end SpectralSparsify.Sampling.SSFresh
end

section
open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh
variable {α : Type*} [DecidableEq α]

noncomputable def weightedCentered (E : Finset α) (q w : α → ℝ) (T : Finset α) : ℝ :=
  ∑ e ∈ E, if e ∈ T then (1-q e)*w e else -q e*w e

lemma weighted_centered_mgf (E : Finset α) (q w : α → ℝ)
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    (β θ : ℝ) (hw0 : ∀ e ∈ E, 0 ≤ w e) (hwb : ∀ e ∈ E, w e ≤ β)
    (ht : |θ| * β ≤ 1) :
    expect E q (fun T => Real.exp (θ*weightedCentered E q w T)) ≤
      Real.exp (θ^2*β*(∑ e ∈ E, q e*w e)) := by
  have heq : (fun T => Real.exp (θ*weightedCentered E q w T)) =
      (fun T => Real.exp (∑ e ∈ E, if e ∈ T then θ*(1-q e)*w e else -θ*q e*w e)) := by
    funext T
    congr 1
    unfold weightedCentered
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> ring
  rw [heq,expect_exp_sum]
  calc
    _ ≤ ∏ e ∈ E, Real.exp (θ^2*β*q e*w e) := by
      apply Finset.prod_le_prod
      · intro e he
        exact add_nonneg (mul_nonneg (hq0 e he) (Real.exp_pos _).le)
          (mul_nonneg (sub_nonneg.mpr (hq1 e he)) (Real.exp_pos _).le)
      · intro e he
        simpa only [add_comm] using bernoulli_weight_mgf_scalar (q e) θ (w e) β
          (hq0 e he) (hw0 e he) (hwb e he) ht
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring

lemma upper_chernoff_from_mgf (E : Finset α) (q : α → ℝ)
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    (f : Finset α → ℝ) (β δ D : ℝ) (hβ : 0 < β) (hδ : 0 < δ)
    (hmgf : expect E q (fun T => Real.exp ((δ/(2*β))*f T)) ≤
      Real.exp ((δ/(2*β))^2*β*D)) :
    prob E q (fun T => δ*D ≤ f T) ≤ Real.exp (-(δ^2*D)/(4*β)) := by
  have ht : 0 < δ/(2*β) := by positivity
  calc
    _ ≤ prob E q (fun T => (δ/(2*β))*(δ*D) ≤ (δ/(2*β))*f T) := by
      apply prob_mono E q hq0 hq1
      intro T _ hT
      exact mul_le_mul_of_nonneg_left hT ht.le
    _ ≤ Real.exp (-((δ/(2*β))*(δ*D)))*
        expect E q (fun T => Real.exp ((δ/(2*β))*f T)) :=
      prob_exp_bound E q hq0 hq1 _ _
    _ ≤ Real.exp (-((δ/(2*β))*(δ*D)))*Real.exp ((δ/(2*β))^2*β*D) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring

lemma weighted_centered_two_sided (E : Finset α) (q w : α → ℝ)
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    (β δ D : ℝ) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw0 : ∀ e ∈ E, 0 ≤ w e) (hwb : ∀ e ∈ E, w e ≤ β)
    (hmean : (∑ e ∈ E, q e*w e) ≤ D) :
    prob E q (fun T => δ*D ≤ |weightedCentered E q w T|) ≤
      2*Real.exp (-(δ^2*D)/(4*β)) := by
  let θ := δ/(2*β)
  have ht : 0 < θ := by dsimp [θ]; positivity
  have he : θ*β=δ/2 := by dsimp [θ]; field_simp
  have habs : |θ| * β ≤ 1 := by rw [abs_of_pos ht,he]; linarith
  have hmgf (z : ℝ) (hz : |z| * β ≤ 1) :
      expect E q (fun T => Real.exp (z*weightedCentered E q w T)) ≤ Real.exp (z^2*β*D) := by
    apply (weighted_centered_mgf E q w hq0 hq1 β z hw0 hwb hz).trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hmean (by positivity)
  have hup := upper_chernoff_from_mgf E q hq0 hq1 (weightedCentered E q w) β δ D hβ hδ
    (hmgf θ habs)
  have hneg : expect E q (fun T => Real.exp (θ*(-weightedCentered E q w T))) ≤
      Real.exp (θ^2*β*D) := by
    simpa only [neg_mul,mul_neg,neg_sq] using hmgf (-θ) (by simpa only [abs_neg] using habs)
  have hlo := upper_chernoff_from_mgf E q hq0 hq1 (fun T => -weightedCentered E q w T)
    β δ D hβ hδ hneg
  calc
    _ ≤ prob E q (fun T => δ*D ≤ weightedCentered E q w T ∨ δ*D ≤ -weightedCentered E q w T) := by
      apply prob_mono E q hq0 hq1
      intro T _ hT
      exact le_abs.mp hT
    _ ≤ prob E q (fun T => δ*D ≤ weightedCentered E q w T)+
        prob E q (fun T => δ*D ≤ -weightedCentered E q w T) :=
      prob_union E q hq0 hq1 _ _
    _ ≤ Real.exp (-(δ^2*D)/(4*β))+Real.exp (-(δ^2*D)/(4*β)) := add_le_add hup hlo
    _ = _ := by ring

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma incident_edges_image (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {v : V} (hv : v ∈ S) :
    (G.neighborFinset v ∩ S).image (fun u => s(v,u)) =
      (inducedEdges G S).filter (fun e => v ∈ e) := by
  classical
  ext e
  constructor
  · intro h
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨huG, huS⟩ := Finset.mem_inter.mp hu
    apply Finset.mem_filter.mpr
    exact ⟨(mem_inducedEdges_iff G S v u).mpr ⟨by simpa using huG, hv, huS⟩,
      Sym2.mem_mk_left v u⟩
  · intro h
    obtain ⟨he, hvE⟩ := Finset.mem_filter.mp h
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hvE
    obtain ⟨hvu, _, hu⟩ := (mem_inducedEdges_iff G S v u).mp he
    exact Finset.mem_image.mpr ⟨u, Finset.mem_inter.mpr ⟨by simpa using hvu, hu⟩, rfl⟩

lemma incident_edges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {v : V} (hv : v ∈ S) :
    ((inducedEdges G S).filter (fun e => v ∈ e)).card = inducedDegree G S v := by
  classical
  rw [← incident_edges_image G S hv, Finset.card_image_of_injective]
  · rfl
  · intro a b h
    exact Sym2.congr_right.mp h

lemma incident_edges_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {v : V} (hv : v ∈ S) (f : Sym2 V → ℝ) :
    (∑ e ∈ (inducedEdges G S).filter (fun e => v ∈ e), f e) =
      ∑ u ∈ G.neighborFinset v ∩ S, f s(v,u) := by
  classical
  rw [← incident_edges_image G S hv, Finset.sum_image]
  intro a _ b _ h
  exact Sym2.congr_right.mp h

lemma induced_edge_vertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {e : Sym2 V} (he : e ∈ inducedEdges G S) :
    e.toFinset ⊆ S := by
  intro v hv
  exact Finset.mem_sym2_iff.mp (Finset.mem_inter.mp he).2 v
    (Sym2.mem_toFinset.mp hv)

lemma edge_vertex_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (f : V → ℝ) :
    (∑ e ∈ inducedEdges G S, ∑ v ∈ e.toFinset, f v) =
      ∑ v ∈ S, (inducedDegree G S v : ℝ) * f v := by
  classical
  calc
    _ = ∑ e ∈ inducedEdges G S, ∑ v ∈ S, if v ∈ e then f v else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [← Finset.sum_filter]
      congr 1
      ext v
      simp only [Finset.mem_filter, Sym2.mem_toFinset]
      exact ⟨fun h => ⟨induced_edge_vertices G S he (Sym2.mem_toFinset.mpr h), h⟩,
        fun h => h.2⟩
    _ = ∑ v ∈ S, ∑ e ∈ inducedEdges G S, if v ∈ e then f v else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
        incident_edges_card G S hv]

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def noisyIncidentWeight (q : Sym2 V → ℝ) (v : V) (e : Sym2 V) : ℝ :=
  if v ∈ e ∧ q e < 1 then 1 / q e else 0

lemma noisyIncidentWeight_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {U : ℝ} (hU : 0 < U) (v : V) {e : Sym2 V}
    (he : e ∈ inducedEdges G S) :
    0 ≤ noisyIncidentWeight (sampleProb (fun i => (inducedDegree G S i : ℝ)) U) v e := by
  classical
  unfold noisyIncidentWeight
  split_ifs
  · exact (one_div_pos.mpr (induced_sampleProb_valid G S hU he).1).le
  · exact le_rfl

lemma noisyIncidentWeight_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {U : ℝ} (hU : 0 < U) (v : V) {e : Sym2 V}
    (he : e ∈ inducedEdges G S) :
    noisyIncidentWeight (sampleProb (fun i => (inducedDegree G S i : ℝ)) U) v e ≤
      (G.degree v : ℝ) / U := by
  classical
  unfold noisyIncidentWeight
  split_ifs with h
  · obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp h.1
    exact induced_sampleProb_inverse_bound G S hU he h.2
  · positivity

lemma noisyIncidentWeight_mean (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {U : ℝ} (hU : 0 < U) {v : V} (hv : v ∈ S) :
    (∑ e ∈ inducedEdges G S,
      sampleProb (fun i => (inducedDegree G S i : ℝ)) U e *
      noisyIncidentWeight (sampleProb (fun i => (inducedDegree G S i : ℝ)) U) v e)
      ≤ (G.degree v : ℝ) := by
  classical
  let q := sampleProb (fun i => (inducedDegree G S i : ℝ)) U
  change (∑ e ∈ inducedEdges G S, q e * noisyIncidentWeight q v e) ≤ _
  calc
    _ ≤ ∑ e ∈ inducedEdges G S, if v ∈ e then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro e he
      have hq : q e ≠ 0 := ne_of_gt (induced_sampleProb_valid G S hU he).1
      unfold noisyIncidentWeight
      by_cases hve : v ∈ e <;> by_cases hq1 : q e < 1 <;> simp [hve, hq1, hq]
    _ = (inducedDegree G S v : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
        incident_edges_card G S hv]
      simp
    _ ≤ _ := by exact_mod_cast inducedDegree_le_degree G S v

lemma weightedCentered_incidentNoise (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {U : ℝ} (hU : 0 < U) (v : V) (T : Finset (Sym2 V))
    (hpos : outcomeProb (inducedEdges G S)
      (sampleProb (fun i => (inducedDegree G S i : ℝ)) U) T ≠ 0) :
    weightedCentered (inducedEdges G S)
      (sampleProb (fun i => (inducedDegree G S i : ℝ)) U)
      (noisyIncidentWeight (sampleProb (fun i => (inducedDegree G S i : ℝ)) U) v) T =
      ∑ e ∈ (inducedEdges G S).filter (fun e => v ∈ e),
        edgeNoise (sampleProb (fun i => (inducedDegree G S i : ℝ)) U) T e := by
  classical
  let q := sampleProb (fun i => (inducedDegree G S i : ℝ)) U
  change weightedCentered (inducedEdges G S) q (noisyIncidentWeight q v) T = _
  rw [weightedCentered, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  have hq0 : 0 < q e := (induced_sampleProb_valid G S hU he).1
  have hq1 : q e ≤ 1 := (induced_sampleProb_valid G S hU he).2
  change (if e ∈ T then (1-q e)*noisyIncidentWeight q v e else
    -q e*noisyIncidentWeight q v e) = if v ∈ e then edgeNoise q T e else 0
  by_cases hv : v ∈ e
  · by_cases hlt : q e < 1
    · unfold noisyIncidentWeight edgeNoise
      simp only [hv, hlt, and_self, ite_true]
      split_ifs
      · field_simp
      · field_simp
        ring
    · have heq : q e = 1 := le_antisymm hq1 (le_of_not_gt hlt)
      have hmem := outcome_forced_mem (inducedEdges G S) q T hpos he heq
      simp [noisyIncidentWeight, edgeNoise, hv, heq, hmem]
  · simp [noisyIncidentWeight, hv]

lemma incident_noise_tail (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {U : ℝ} (hU : 0 < U) {v : V} (hv : v ∈ S)
    (hd : 0 < G.degree v) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    prob (inducedEdges G S) (sampleProb (fun i => (inducedDegree G S i : ℝ)) U)
      (fun T => δ * (G.degree v : ℝ) ≤
        |∑ e ∈ (inducedEdges G S).filter (fun e => v ∈ e),
          edgeNoise (sampleProb (fun i => (inducedDegree G S i : ℝ)) U) T e|)
      ≤ 2 * Real.exp (-(U * δ^2) / 4) := by
  let E := inducedEdges G S
  let q := sampleProb (fun i => (inducedDegree G S i : ℝ)) U
  have hq0 : ∀ e ∈ E, 0 ≤ q e := fun e he => (induced_sampleProb_valid G S hU he).1.le
  have hq1 : ∀ e ∈ E, q e ≤ 1 := fun e he => (induced_sampleProb_valid G S hU he).2
  have hD : (0 : ℝ) < G.degree v := by exact_mod_cast hd
  have hb : 0 < (G.degree v : ℝ) / U := div_pos hD hU
  calc
    _ ≤ prob E q (fun T => δ * (G.degree v : ℝ) ≤
        |weightedCentered E q (noisyIncidentWeight q v) T|) := by
      apply prob_mono_on_support E q hq0 hq1
      intro T _ hpos ht
      change δ * (G.degree v : ℝ) ≤ |weightedCentered (inducedEdges G S)
        (sampleProb (fun i => (inducedDegree G S i : ℝ)) U)
        (noisyIncidentWeight (sampleProb (fun i => (inducedDegree G S i : ℝ)) U) v) T|
      rw [weightedCentered_incidentNoise G S hU v T hpos]
      exact ht
    _ ≤ 2 * Real.exp (-(δ^2*(G.degree v : ℝ))/(4*((G.degree v : ℝ)/U))) :=
      weighted_centered_two_sided E q (noisyIncidentWeight q v) hq0 hq1 _ δ _ hb hδ hδ1
        (fun _ he => noisyIncidentWeight_nonneg G S hU v he)
        (fun _ he => noisyIncidentWeight_le G S hU v he)
        (noisyIncidentWeight_mean G S hU hv)
    _ = _ := by
      congr 2
      field_simp

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh
variable {α ι : Type*} [DecidableEq α]

lemma prob_exists_finset (E : Finset α) (q : α → ℝ)
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    (I : Finset ι) (P : ι → Finset α → Prop) :
    prob E q (fun T => ∃ i ∈ I, P i T) ≤ ∑ i ∈ I, prob E q (P i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [prob]
  | @insert i I hi ih =>
    have heq : (fun T => ∃ j ∈ insert i I, P j T) =
        (fun T => P i T ∨ ∃ j ∈ I, P j T) := by
      funext T
      simp
    rw [heq, Finset.sum_insert hi]
    exact (prob_union E q hq0 hq1 _ _).trans (add_le_add le_rfl ih)

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma incident_noise_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {U : ℝ} (hU : 0 < U) (hdeg : ∀ v, 0 < G.degree v)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    prob (inducedEdges G S) (sampleProb (fun i => (inducedDegree G S i : ℝ)) U)
      (fun T => ∃ v ∈ S, δ * (G.degree v : ℝ) ≤
        |∑ e ∈ (inducedEdges G S).filter (fun e => v ∈ e),
          edgeNoise (sampleProb (fun i => (inducedDegree G S i : ℝ)) U) T e|)
      ≤ 2 * S.card * Real.exp (-(U * δ^2) / 4) := by
  let E := inducedEdges G S
  let q := sampleProb (fun i => (inducedDegree G S i : ℝ)) U
  have hq0 : ∀ e ∈ E, 0 ≤ q e := fun e he => (induced_sampleProb_valid G S hU he).1.le
  have hq1 : ∀ e ∈ E, q e ≤ 1 := fun e he => (induced_sampleProb_valid G S hU he).2
  apply (prob_exists_finset E q hq0 hq1 S _).trans
  calc
    _ ≤ ∑ _v ∈ S, 2 * Real.exp (-(U * δ^2) / 4) := by
      apply Finset.sum_le_sum
      intro v hv
      exact incident_noise_tail G S hU hv (hdeg v) δ hδ hδ1
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

lemma native_degree_failure_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hdeg : ∀ v, 0 < G.degree v)
    (k : ℕ) (ε lam p : ℝ) (hk : 1 ≤ k) (he0 : 0 < ε) (he1 : ε < 1/2)
    (hl0 : 0 < lam) (hl2 : lam ≤ 2) (hp : 0 < p)
    (hk1 : Real.logb 2 (3/p) ≤ (k:ℝ)) (hk2 : Real.logb 2 S.card ≤ (k:ℝ)) :
    prob (inducedEdges G S) (sampleSubgraphProb G S k ε lam)
      (fun T => ∃ v ∈ S, (ε*lam/3) * (G.degree v : ℝ) ≤
        |∑ e ∈ (inducedEdges G S).filter (fun e => v ∈ e),
          edgeNoise (sampleSubgraphProb G S k ε lam) T e|) ≤ p/3 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hU : 0 < sampleUpsilon k ε lam := by unfold sampleUpsilon; positivity
  have hδ : 0 < ε*lam/3 := by positivity
  have hδ1 : ε*lam/3 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hl2 he0.le
    nlinarith
  have h := incident_noise_union G S hU hdeg (ε*lam/3) hδ hδ1
  have hex : -(sampleUpsilon k ε lam * (ε*lam/3)^2)/4 = -4*(k:ℝ)^2 := by
    unfold sampleUpsilon
    field_simp
    ring
  rw [hex] at h
  exact h.trans (degree_probability_budget S.card k p hp hk hk1 hk2)

end SpectralSparsify.Sampling.SSFresh
end

section
open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh
variable {α : Type*} [DecidableEq α]

noncomputable def keptCount (E T : Finset α) : ℝ :=
  ∑ e ∈ E, if e ∈ T then 1 else 0

lemma keptCount_eq_card (E T : Finset α) (hT : T ⊆ E) : keptCount E T = (T.card:ℝ) := by
  have hf : E.filter (fun e => e ∈ T)=T := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hT h,h⟩⟩
  unfold keptCount
  rw [← Finset.sum_filter,hf]
  simp

lemma count_mgf_le (E : Finset α) (q : α → ℝ)
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    (M : ℝ) (hmean : (∑ e ∈ E, q e) ≤ M) :
    expect E q (fun T => Real.exp ((1/2:ℝ)*keptCount E T)) ≤ Real.exp (3*M/4) := by
  have he : (fun T => Real.exp ((1/2:ℝ)*keptCount E T)) =
      (fun T => Real.exp (∑ e ∈ E, if e ∈ T then (1/2:ℝ) else 0)) := by
    funext T
    congr 1
    unfold keptCount
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> ring
  rw [he,expect_exp_sum]
  calc
    _ ≤ ∏ e ∈ E, Real.exp (3*q e/4) := by
      apply Finset.prod_le_prod
      · intro e he
        exact add_nonneg (mul_nonneg (hq0 e he) (Real.exp_pos _).le)
          (mul_nonneg (sub_nonneg.mpr (hq1 e he)) (Real.exp_pos _).le)
      · intro e he
        simpa only [Real.exp_zero,mul_one,add_comm] using bernoulli_count_mgf_scalar (q e) (hq0 e he)
    _ = Real.exp (3*(∑ e ∈ E, q e)/4) := by
      rw [← Real.exp_sum,← Finset.sum_div,← Finset.mul_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

lemma kept_count_chernoff (E : Finset α) (q : α → ℝ)
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    (M : ℝ) (hmean : (∑ e ∈ E, q e) ≤ M) :
    prob E q (fun T => 2*M < keptCount E T) ≤ Real.exp (-M/4) := by
  calc
    _ ≤ prob E q (fun T => M ≤ (1/2:ℝ)*keptCount E T) := by
      apply prob_mono E q hq0 hq1
      intro T _ hT
      linarith
    _ ≤ Real.exp (-M)*expect E q (fun T => Real.exp ((1/2:ℝ)*keptCount E T)) :=
      prob_exp_bound E q hq0 hq1 _ _
    _ ≤ Real.exp (-M)*Real.exp (3*M/4) :=
      mul_le_mul_of_nonneg_left (count_mgf_le E q hq0 hq1 M hmean) (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma subset_count_chernoff (E : Finset α) (q : α → ℝ)
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    (M : ℝ) (hmean : (∑ e ∈ E, q e) ≤ M) :
    prob E q (fun T => 2*M < (T.card:ℝ)) ≤ Real.exp (-M/4) := by
  apply (prob_mono E q hq0 hq1 (fun T hT h => ?_)).trans
    (kept_count_chernoff E q hq0 hq1 M hmean)
  rwa [keptCount_eq_card E T hT]

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma induced_sampleProb_charge (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {U : ℝ} (hU : 0 ≤ U) {e : Sym2 V}
    (he : e ∈ inducedEdges G S) :
    sampleProb (fun v => (inducedDegree G S v : ℝ)) U e ≤
      U * ∑ v ∈ e.toFinset, 1 / (inducedDegree G S v : ℝ) := by
  induction e using Sym2.ind with
  | _ i j =>
    have hij := ((mem_inducedEdges_iff G S i j).mp he).1
    have hi : (0 : ℝ) < inducedDegree G S i := by
      exact_mod_cast inducedDegree_pos_of_edge G S he
    have hj : (0 : ℝ) < inducedDegree G S j := by
      have he' : s(j,i) ∈ inducedEdges G S := by simpa only [Sym2.eq_swap] using he
      exact_mod_cast inducedDegree_pos_of_edge G S he'
    rw [Sym2.toFinset_mk_eq, Finset.sum_pair hij.ne]
    change min 1 (U / min (inducedDegree G S i : ℝ) (inducedDegree G S j : ℝ)) ≤ _
    apply le_trans (min_le_right _ _)
    rcases le_total (inducedDegree G S i : ℝ) (inducedDegree G S j : ℝ) with h | h
    · rw [min_eq_left h]
      have hn : 0 ≤ U * (1 / (inducedDegree G S j : ℝ)) := mul_nonneg hU (by positivity)
      nlinarith [show U / (inducedDegree G S i : ℝ) = U * (1 / (inducedDegree G S i : ℝ)) by ring]
    · rw [min_eq_right h]
      have hn : 0 ≤ U * (1 / (inducedDegree G S i : ℝ)) := mul_nonneg hU (by positivity)
      nlinarith [show U / (inducedDegree G S j : ℝ) = U * (1 / (inducedDegree G S j : ℝ)) by ring]

lemma induced_sampleProb_sum_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {U : ℝ} (hU : 0 ≤ U) :
    (∑ e ∈ inducedEdges G S, sampleProb (fun v => (inducedDegree G S v : ℝ)) U e)
      ≤ U * S.card := by
  calc
    _ ≤ ∑ e ∈ inducedEdges G S, U * ∑ v ∈ e.toFinset,
        1 / (inducedDegree G S v : ℝ) :=
      Finset.sum_le_sum fun _ he => induced_sampleProb_charge G S hU he
    _ = U * ∑ v ∈ S, (inducedDegree G S v : ℝ) *
        (1 / (inducedDegree G S v : ℝ)) := by
      rw [← Finset.mul_sum, edge_vertex_sum]
    _ ≤ U * ∑ _v ∈ S, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hU
      apply Finset.sum_le_sum
      intro v _
      by_cases h : inducedDegree G S v = 0
      · simp [h]
      · have hn : (inducedDegree G S v : ℝ) ≠ 0 := by exact_mod_cast h
        simp [hn]
    _ = _ := by simp

lemma sampleSubgraphProb_sum_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (k : ℕ) (ε lam : ℝ) :
    (∑ e ∈ inducedEdges G S, sampleSubgraphProb G S k ε lam e) ≤
      sampleUpsilon k ε lam * S.card :=
  induced_sampleProb_sum_le G S (sq_nonneg _)

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma native_count_failure_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (k : ℕ) (ε lam p : ℝ) (hk : 1 ≤ k)
    (he0 : 0 < ε) (he1 : ε < 1/2) (hl0 : 0 < lam) (hl2 : lam ≤ 2)
    (hp : 0 < p) (hk1 : Real.logb 2 (3/p) ≤ (k:ℝ)) :
    prob (inducedEdges G S) (sampleSubgraphProb G S k ε lam)
      (fun T => 288 * (k : ℝ)^2 / (ε*lam)^2 * S.card < (T.card : ℝ)) ≤ p/3 := by
  classical
  by_cases hs : S = ∅
  · subst S
    simp [inducedEdges, prob, outcomeProb]
    positivity
  have hs1 : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hU : 0 < sampleUpsilon k ε lam := by unfold sampleUpsilon; positivity
  have hq0 : ∀ e ∈ inducedEdges G S, 0 ≤ sampleSubgraphProb G S k ε lam e :=
    fun e he => (sampleSubgraphProb_valid G S k ε lam hU he).1.le
  have hq1 : ∀ e ∈ inducedEdges G S, sampleSubgraphProb G S k ε lam e ≤ 1 :=
    fun e he => (sampleSubgraphProb_valid G S k ε lam hU he).2
  have hc : 288 * (k : ℝ)^2 / (ε*lam)^2 * S.card =
      2 * (sampleUpsilon k ε lam * S.card) := by
    unfold sampleUpsilon
    ring
  simp_rw [hc]
  exact (subset_count_chernoff (inducedEdges G S) (sampleSubgraphProb G S k ε lam)
    hq0 hq1 _ (sampleSubgraphProb_sum_le G S k ε lam)).trans
    (by
      simpa only [neg_mul] using
        (edge_count_probability_budget S.card k p (sampleUpsilon k ε lam) hp hs1 hk
          (sampleUpsilon_lower k ε lam he0 he1 hl0 hl2) hk1))

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh
variable {α : Type*} [DecidableEq α]

lemma prob_complement (E : Finset α) (q : α → ℝ) (P : Finset α → Prop) :
    prob E q (fun T => ¬ P T) = 1 - prob E q P := by
  classical
  have h : prob E q (fun T => ¬ P T) + prob E q P = 1 := by
    unfold prob
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ T ∈ E.powerset, outcomeProb E q T := by
        apply Finset.sum_congr rfl
        intro T _
        by_cases hp : P T <;> simp [hp]
      _ = 1 := outcomeProb_sum E q
  linarith

lemma prob_good_from_three_bad (E : Finset α) (q : α → ℝ)
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    (A B C Good : Finset α → Prop) (p : ℝ)
    (hA : prob E q A ≤ p/3) (hB : prob E q B ≤ p/3) (hC : prob E q C ≤ p/3)
    (hgood : ∀ T ⊆ E, outcomeProb E q T ≠ 0 → ¬ A T → ¬ B T → ¬ C T → Good T) :
    1 - p ≤ prob E q Good := by
  have hbad : prob E q (fun T => A T ∨ B T ∨ C T) ≤ p := by
    have hBC := prob_union E q hq0 hq1 B C
    have hABC := prob_union E q hq0 hq1 A (fun T => B T ∨ C T)
    linarith
  calc
    1 - p ≤ 1 - prob E q (fun T => A T ∨ B T ∨ C T) := by linarith
    _ = prob E q (fun T => ¬ (A T ∨ B T ∨ C T)) := (prob_complement E q _).symm
    _ ≤ prob E q Good := by
      apply prob_mono_on_support E q hq0 hq1
      intro T hT hpos hn
      exact hgood T hT hpos (fun h => hn (Or.inl h))
        (fun h => hn (Or.inr (Or.inl h))) (fun h => hn (Or.inr (Or.inr h)))

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
open Matrix

namespace SpectralSparsify.Sampling.SSFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def adjDifference (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : Sym2 V → ℝ) (T : Finset (Sym2 V)) : Matrix V V ℝ :=
  fun i j => sparsifierWeight G S q T i j - adjWeight G i j

noncomputable def degreeDelta (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : Sym2 V → ℝ) (T : Finset (Sym2 V)) (i : V) : ℝ :=
  ∑ j, adjDifference G S q T i j

lemma adjDifference_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : Sym2 V → ℝ) (T : Finset (Sym2 V))
    (hT : T ⊆ inducedEdges G S) (i j : V) :
    adjDifference G S q T i j =
      if s(i,j) ∈ inducedEdges G S then edgeNoise q T s(i,j) else 0 := by
  by_cases he : s(i,j) ∈ inducedEdges G S
  · have hij := ((mem_inducedEdges_iff G S i j).mp he).1
    have hr : s(i,j) ∉ restEdges G S := by simp only [restEdges, Finset.mem_sdiff, he, not_true_eq_false, and_false, not_false_eq_true]
    simp only [adjDifference, sparsifierWeight, adjWeight, he, hij, hr, ite_true, ite_false, edgeNoise]
  · have ht : s(i,j) ∉ T := fun h => he (hT h)
    by_cases hij : G.Adj i j
    · have hr : s(i,j) ∈ restEdges G S := by
        apply Finset.mem_sdiff.mpr
        exact ⟨by simpa using hij, he⟩
      simp only [adjDifference, sparsifierWeight, adjWeight, he, ht, hr, hij, ite_true, ite_false, sub_self]
    · rw [adjDifference, sparsifier_support G S q T hT i j hij]
      simp only [adjWeight, hij, he, ite_false, sub_zero]

lemma adjDifference_outside (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : Sym2 V → ℝ) (T : Finset (Sym2 V))
    (hT : T ⊆ inducedEdges G S) (i j : V) (h : i ∉ S ∨ j ∉ S) :
    adjDifference G S q T i j = 0 := by
  rw [adjDifference_eq G S q T hT]
  apply if_neg
  rw [mem_inducedEdges_iff]
  rcases h with h | h <;> tauto

lemma degreeDelta_outside (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : Sym2 V → ℝ) (T : Finset (Sym2 V))
    (hT : T ⊆ inducedEdges G S) (i : V) (hi : i ∉ S) : degreeDelta G S q T i = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact adjDifference_outside G S q T hT i j (Or.inl hi)

lemma lap_difference (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : Sym2 V → ℝ) (T : Finset (Sym2 V)) :
    lapMat (sparsifierWeight G S q T) - G.lapMatrix ℝ =
      diagonal (degreeDelta G S q T) - adjDifference G S q T := by
  rw [← adjWeight_lapMat G]
  have hd : degreeDelta G S q T =
      wDegree (sparsifierWeight G S q T) - wDegree (adjWeight G) := by
    funext i
    simp only [degreeDelta, adjDifference, wDegree, Pi.sub_apply, Finset.sum_sub_distrib]
  rw [hd]
  unfold lapMat degMat adjMat adjDifference
  ext i j
  change ((if i = j then wDegree (sparsifierWeight G S q T) i else 0) -
      sparsifierWeight G S q T i j) -
      ((if i = j then wDegree (adjWeight G) i else 0) - adjWeight G i j) =
      (if i = j then wDegree (sparsifierWeight G S q T) i - wDegree (adjWeight G) i else 0) -
      (sparsifierWeight G S q T i j - adjWeight G i j)
  split_ifs <;> ring

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators

namespace SpectralSparsify.Sampling.SSFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma degreeDelta_incidentNoise (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : Sym2 V → ℝ) (T : Finset (Sym2 V))
    (hT : T ⊆ inducedEdges G S) {v : V} (hv : v ∈ S) :
    degreeDelta G S q T v =
      ∑ e ∈ (inducedEdges G S).filter (fun e => v ∈ e), edgeNoise q T e := by
  rw [incident_edges_sum G S hv]
  have hf : G.neighborFinset v ∩ S = Finset.univ.filter (fun j => G.Adj v j ∧ j ∈ S) := by
    ext j
    simp
  rw [hf, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  rw [adjDifference_eq G S q T hT]
  simp only [mem_inducedEdges_iff, hv, true_and]

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
open Matrix

namespace SpectralSparsify.Sampling.SSFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma quad_as_double_sum (A : Matrix V V ℝ) (x : V → ℝ) :
    quad A x = ∑ i, ∑ j, x i * A i j * x j := by
  simp only [quad, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

omit [DecidableEq V] in
lemma quad_restrict (A : Matrix V V ℝ) (S : Finset V) (x : V → ℝ)
    (hzero : ∀ i j, i ∉ S ∨ j ∉ S → A i j = 0) :
    quad A x = quad (fun i j : S => A i j) (fun i : S => x i) := by
  rw [quad_as_double_sum A x, quad_as_double_sum (V := S)
    (fun i j => A i.val j.val) (fun i => x i.val)]
  calc
    _ = ∑ i ∈ S, ∑ j, x i * A i j * x j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      apply Finset.sum_eq_zero
      intro j _
      rw [hzero i j (Or.inl hi), mul_zero, zero_mul]
    _ = ∑ i ∈ S, ∑ j ∈ S, x i * A i j * x j := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro j _ hj
      rw [hzero i j (Or.inr hj), mul_zero, zero_mul]
    _ = _ := by
      rw [← Finset.sum_coe_sort S (fun i => ∑ j ∈ S, x i * A i j * x j)]
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.sum_coe_sort S (fun j => x i.val * A i.val j * x j)).symm

omit [DecidableEq V] in

lemma sqNorm_restrict_le (S : Finset V) (x : V → ℝ) :
    sqNorm (fun i : S => x i) ≤ sqNorm x := by
  simp only [sqNorm, dotProduct]
  have hs : (∑ i : S, x i.val * x i.val) = ∑ i ∈ S, x i * x i :=
    Finset.sum_coe_sort S (fun i => x i * x i)
  rw [hs]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun i _ _ => mul_self_nonneg (x i))

omit [DecidableEq V] in
lemma normLE_of_quad_bound (A : Matrix V V ℝ) (t : ℝ)
    (h : ∀ x, |quad A x| ≤ t * sqNorm x) : NormLE A t := by
  intro mu x hx he
  have hn := sqNorm_pos hx
  have hb := h x
  have hq : quad A x = mu * sqNorm x := by
    simp only [quad, he, dotProduct_smul, smul_eq_mul, sqNorm]
  rw [hq, abs_mul, abs_of_pos hn] at hb
  exact (mul_le_mul_iff_left₀ hn).mp hb

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
open Matrix

namespace SpectralSparsify.Sampling.SSFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma normalize_adjDifference_entry (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : Sym2 V → ℝ) (T : Finset (Sym2 V))
    (hT : T ⊆ inducedEdges G S) (i j : S) :
    normalize G (adjDifference G S q T) i j = symError G S q T i j := by
  simp only [normalize, degInvSqrt, diagonal_mul, mul_diagonal]
  rw [adjDifference_eq G S q T hT]
  simp only [mem_inducedEdges_iff, i.property, j.property, and_true, symError]
  split_ifs <;> simp only [div_eq_mul_inv] <;> ring

lemma normalize_adjDifference_outside (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : Sym2 V → ℝ) (T : Finset (Sym2 V))
    (hT : T ⊆ inducedEdges G S) (i j : V) (h : i ∉ S ∨ j ∉ S) :
    normalize G (adjDifference G S q T) i j = 0 := by
  simp only [normalize, degInvSqrt, diagonal_mul, mul_diagonal,
    adjDifference_outside G S q T hT i j h, mul_zero, zero_mul]

lemma adjacency_error_quad_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : Sym2 V → ℝ) (T : Finset (Sym2 V))
    (hT : T ⊆ inducedEdges G S) {delta : ℝ} (hd : 0 ≤ delta)
    (hA : NormLE (symError G S q T) delta) (x : V → ℝ) :
    |quad (normalize G (adjDifference G S q T)) x| ≤ delta * sqNorm x := by
  rw [quad_restrict _ S x (normalize_adjDifference_outside G S q T hT)]
  have he : (fun i j : S => normalize G (adjDifference G S q T) i j) =
      symError G S q T := by
    ext i j
    exact normalize_adjDifference_entry G S q T hT i j
  rw [he]
  exact (abs_quad_le_of_normLE _ (symError_isHermitian G S q T) hA _).trans
    (mul_le_mul_of_nonneg_left (sqNorm_restrict_le S x) hd)

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
open Matrix

namespace SpectralSparsify.Sampling.SSFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma sum_adj_first_sq (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
    (∑ i, ∑ j, if G.Adj i j then x i ^ 2 else 0) =
      ∑ i, (G.degree i : ℝ) * x i ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [SimpleGraph.degree_eq_sum_if_adj, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

lemma quad_lapMatrix_le (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
    quad (G.lapMatrix ℝ) x ≤ 2 * ∑ i, (G.degree i : ℝ) * x i ^ 2 := by
  have hform : quad (G.lapMatrix ℝ) x =
      (∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 := by
    simpa only [Matrix.toLinearMap₂'_apply', quad] using G.lapMatrix_toLinearMap₂' ℝ x
  have hflip : (∑ i, ∑ j, if G.Adj i j then x j ^ 2 else 0) =
      ∑ i, ∑ j, if G.Adj i j then x i ^ 2 else 0 := by
    rw [Finset.sum_comm]
    simp only [G.adj_comm]
  have hb : (∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0) ≤
      2 * (∑ i, ∑ j, if G.Adj i j then x i ^ 2 else 0) +
      2 * (∑ i, ∑ j, if G.Adj i j then x j ^ 2 else 0) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    split_ifs <;> nlinarith [sq_nonneg (x i + x j)]
  rw [hflip, sum_adj_first_sq] at hb
  rw [hform]
  linarith

lemma weighted_norm_rescale (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ i, 0 < G.degree i) (x : V → ℝ) :
    (∑ i, (G.degree i : ℝ) * (degInvSqrt G *ᵥ x) i ^ 2) = sqNorm x := by
  unfold sqNorm dotProduct
  apply Finset.sum_congr rfl
  intro i _
  have hd : 0 < (G.degree i : ℝ) := Nat.cast_pos.2 (hdeg i)
  have hs := Real.sq_sqrt hd.le
  have hn := ne_of_gt (Real.sqrt_pos.2 hd)
  simp only [degInvSqrt, mulVec_diagonal]
  field_simp
  nlinarith

lemma normLap_quad_le_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ i, 0 < G.degree i) (x : V → ℝ) :
    quad (normLap G) x ≤ 2 * sqNorm x := by
  rw [normLap, quad_normalize]
  simpa only [weighted_norm_rescale G hdeg] using
    quad_lapMatrix_le G (degInvSqrt G *ᵥ x)

lemma normLap_diagonal (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ i, 0 < G.degree i) (i : V) : normLap G i i = 1 := by
  have hd : 0 < (G.degree i : ℝ) := Nat.cast_pos.2 (hdeg i)
  have hs := Real.sq_sqrt hd.le
  have hn := ne_of_gt (Real.sqrt_pos.2 hd)
  simp only [normLap, normalize, degInvSqrt, diagonal_mul, mul_diagonal,
    SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply, diagonal_apply_eq,
    SimpleGraph.adjMatrix_apply]
  rw [if_neg G.irrefl, sub_zero]
  field_simp
  nlinarith

lemma native_gap_le_two (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hdeg : ∀ i, 0 < G.degree i) {lam : ℝ} (hgap : NonzeroEigGE (normLap G) lam) :
    lam ≤ 2 := by
  have hne : normLap G ≠ 0 := by
    intro h
    obtain ⟨i⟩ := ‹Nonempty V›
    have hh := normLap_diagonal G hdeg i
    rw [h] at hh
    norm_num at hh
  obtain ⟨x, mu, hm, hx, he⟩ := (normLap_isHermitian G).exists_eigenvector_of_ne_zero hne
  have hmu := hgap mu x hx he hm
  have hb := normLap_quad_le_two G hdeg x
  have hq : quad (normLap G) x = mu * sqNorm x := by
    simp only [quad, he, dotProduct_smul, smul_eq_mul, sqNorm]
  rw [hq] at hb
  exact hmu.trans ((mul_le_mul_iff_left₀ (sqNorm_pos hx)).mp hb)

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
open Matrix Unitary WithLp

namespace SpectralSparsify.Sampling.SSFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma unitary_transpose_mulVec (U : Matrix.unitaryGroup V ℝ) (x : V → ℝ) :
    (U : Matrix V V ℝ)ᵀ *ᵥ ((U : Matrix V V ℝ) *ᵥ x) = x := by
  rw [mulVec_mulVec]
  have h : (U : Matrix V V ℝ)ᵀ * (U : Matrix V V ℝ) = 1 := by
    simpa only [coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      coe_star_mul_self U
  rw [h, one_mulVec]

lemma sqNorm_unitary_mulVec (U : Matrix.unitaryGroup V ℝ) (x : V → ℝ) :
    sqNorm ((U : Matrix V V ℝ) *ᵥ x) = sqNorm x := by
  have h := sqNorm_unitary_coords U ((U : Matrix V V ℝ) *ᵥ x)
  rw [unitary_transpose_mulVec] at h
  exact h.symm

noncomputable def spectralKeep (A : Matrix V V ℝ) (hA : A.IsHermitian) (x : V → ℝ) : V → ℝ :=
  fun i => if hA.eigenvalues i = 0 then 0 else
    ((hA.eigenvectorUnitary : Matrix V V ℝ)ᵀ *ᵥ x) i

noncomputable def spectralProjection (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (x : V → ℝ) : V → ℝ :=
  (hA.eigenvectorUnitary : Matrix V V ℝ) *ᵥ spectralKeep A hA x

lemma mulVec_eigen_coordinates (A : Matrix V V ℝ) (hA : A.IsHermitian) (x : V → ℝ) :
    A *ᵥ x = (hA.eigenvectorUnitary : Matrix V V ℝ) *ᵥ
      (fun i => hA.eigenvalues i * ((hA.eigenvectorUnitary : Matrix V V ℝ)ᵀ *ᵥ x) i) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [conjStarAlgAut_apply]
  simp only [RCLike.ofReal_real_eq_id, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial, ← mulVec_mulVec]
  congr 1
  funext i
  simp only [mulVec_diagonal, Function.comp_apply, id_eq]

lemma spectralProjection_same_image (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (x : V → ℝ) : A *ᵥ spectralProjection A hA x = A *ᵥ x := by
  rw [mulVec_eigen_coordinates A hA, mulVec_eigen_coordinates A hA]
  unfold spectralProjection
  rw [unitary_transpose_mulVec]
  congr 1
  funext i
  unfold spectralKeep
  split_ifs with hi
  · simp [hi]
  · rfl

lemma spectralProjection_gap (A : Matrix V V ℝ) (hA : A.IsHermitian)
    {lam : ℝ} (hgap : NonzeroEigGE A lam) (x : V → ℝ) :
    lam * sqNorm (spectralProjection A hA x) ≤ quad A x := by
  rw [spectralProjection, sqNorm_unitary_mulVec, quad_eigenvalues A hA]
  simp only [sqNorm, dotProduct, spectralKeep, ← pow_two]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · simp [hi]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact hgap _ _ ((ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero i))
      (hA.mulVec_eigenvectorBasis i) hi

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
open Matrix

namespace SpectralSparsify.Sampling.SSFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma quad_eq_of_same_image (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (x y : V → ℝ) (h : A *ᵥ x = A *ᵥ y) : quad A x = quad A y := by
  have ht : Aᵀ = A := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hA
  unfold quad
  calc
    x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ y) := congrArg (fun z => x ⬝ᵥ z) h
    _ = y ⬝ᵥ (A *ᵥ x) := by simpa only [ht] using dotProduct_transpose_mulVec A x y
    _ = y ⬝ᵥ (A *ᵥ y) := congrArg (fun z => y ⬝ᵥ z) h

lemma relative_quad_error (A B : Matrix V V ℝ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) {lam eta : ℝ} (heta : 0 ≤ eta)
    (hgap : NonzeroEigGE A lam)
    (hker : ∀ x : V → ℝ, A *ᵥ x = 0 → B *ᵥ x = 0)
    (herr : NormLE (B - A) (eta * lam)) (x : V → ℝ) :
    |quad B x - quad A x| ≤ eta * quad A x := by
  let z := spectralProjection A hA x
  have ha : A *ᵥ z = A *ᵥ x := spectralProjection_same_image A hA x
  have hak : A *ᵥ (x - z) = 0 := by rw [mulVec_sub, ha, sub_self]
  have hb : B *ᵥ x = B *ᵥ z := by
    have h := hker (x - z) hak
    rwa [mulVec_sub, sub_eq_zero] at h
  have hqa : quad A x = quad A z := quad_eq_of_same_image A hA x z ha.symm
  have hqb : quad B x = quad B z := quad_eq_of_same_image B hB x z hb
  have hbound := abs_quad_le_of_normLE (B - A) (hB.sub hA) herr z
  have hsub : quad (B - A) z = quad B z - quad A z := by
    simp only [quad, sub_mulVec, dotProduct_sub]
  rw [hsub] at hbound
  calc
    |quad B x - quad A x| = |quad B z - quad A z| := by rw [hqa, hqb]
    _ ≤ eta * lam * sqNorm z := hbound
    _ = eta * (lam * sqNorm z) := mul_assoc _ _ _
    _ ≤ eta * quad A x := mul_le_mul_of_nonneg_left (spectralProjection_gap A hA hgap x) heta

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
open Matrix

namespace SpectralSparsify.Sampling.SSFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma diagonal_error_quad_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ i, 0 < G.degree i) (a : V → ℝ) {delta : ℝ}
    (ha : ∀ i, |a i| ≤ delta * (G.degree i : ℝ)) (x : V → ℝ) :
    |quad (normalize G (diagonal a)) x| ≤ delta * sqNorm x := by
  rw [quad_normalize, quad_diagonal]
  calc
    _ ≤ ∑ i, |a i * (degInvSqrt G *ᵥ x) i ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, delta * (G.degree i : ℝ) * (degInvSqrt G *ᵥ x) i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_pow, sq_abs]
      exact mul_le_mul_of_nonneg_right (ha i) (sq_nonneg _)
    _ = delta * sqNorm x := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, weighted_norm_rescale G hdeg]

lemma normalize_sub (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Matrix V V ℝ) : normalize G (A - B) = normalize G A - normalize G B := by
  simp only [normalize, mul_sub, sub_mul]

lemma sparsifier_normalized_error (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ i, 0 < G.degree i) (S : Finset V) (q : Sym2 V → ℝ)
    (T : Finset (Sym2 V)) (hT : T ⊆ inducedEdges G S) {delta : ℝ}
    (hd : 0 ≤ delta) (hA : NormLE (symError G S q T) delta)
    (hD : ∀ i ∈ S, |degreeDelta G S q T i| ≤ delta * (G.degree i : ℝ)) :
    NormLE (normalize G (lapMat (sparsifierWeight G S q T)) - normLap G) (2 * delta) := by
  apply normLE_of_quad_bound
  intro x
  have hall (i : V) : |degreeDelta G S q T i| ≤ delta * (G.degree i : ℝ) := by
    by_cases hi : i ∈ S
    · exact hD i hi
    · rw [degreeDelta_outside G S q T hT i hi, abs_zero]
      positivity
  have hdq := diagonal_error_quad_bound G hdeg _ hall x
  have haq := adjacency_error_quad_bound G S q T hT hd hA x
  have heq : normalize G (lapMat (sparsifierWeight G S q T)) - normLap G =
      normalize G (diagonal (degreeDelta G S q T)) - normalize G (adjDifference G S q T) := by
    rw [normLap, ← normalize_sub, lap_difference, normalize_sub]
  rw [heq]
  have hquad (A B : Matrix V V ℝ) : quad (A - B) x = quad A x - quad B x := by
    simp only [quad, sub_mulVec, dotProduct_sub]
  rw [hquad]
  exact (abs_sub _ _).trans (by linarith)

lemma deterministic_spectral_approx (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ i, 0 < G.degree i) (S : Finset V) (q : Sym2 V → ℝ)
    (T : Finset (Sym2 V)) (hT : T ⊆ inducedEdges G S)
    {eps lam : ℝ} (heps : 0 < eps) (heps1 : eps < 1 / 2) (hlam : 0 < lam)
    (hgap : NonzeroEigGE (normLap G) lam)
    (hA : NormLE (symError G S q T) (eps * lam / 3))
    (hD : ∀ i ∈ S, |degreeDelta G S q T i| ≤ (eps * lam / 3) * (G.degree i : ℝ)) :
    IsApprox (1 + eps) (sparsifierWeight G S q T) (adjWeight G) := by
  have herr := sparsifier_normalized_error G hdeg S q T hT (by positivity) hA hD
  have hs := normalize_isHermitian G _
    (lapMat_isHermitian _ (sparsifier_symmetric G S q T))
  have hr (y : V → ℝ) := relative_quad_error (normLap G)
    (normalize G (lapMat (sparsifierWeight G S q T))) (normLap_isHermitian G) hs
    (eta := 2 * eps / 3) (by positivity) hgap
    (sparsifier_normalized_kernel G hdeg S q T hT)
    (by convert herr using 1; ring) y
  intro x
  let y : V → ℝ := fun i => Real.sqrt (G.degree i) * x i
  have hy : degInvSqrt G *ᵥ y = x := by
    funext i
    have hn : Real.sqrt (G.degree i : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.2 (hdeg i)))
    simp only [degInvSqrt, mulVec_diagonal, y]
    field_simp
  have hb := hr y
  rw [normLap, quad_normalize, quad_normalize, hy,
    quad_lapMat _ (sparsifier_symmetric G S q T), ← adjWeight_lapMat G,
    quad_lapMat _ (adjWeight_symmetric G)] at hb
  have ha : 0 ≤ lapForm (adjWeight G) x := by
    rw [← quad_lapMat _ (adjWeight_symmetric G), adjWeight_lapMat G]
    simpa only [quad, star_trivial] using (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg x
  obtain ⟨hlo, hhi⟩ := abs_le.mp hb
  apply spectral_approx_scalar eps _ _ heps heps1 ha <;> nlinarith

end SpectralSparsify.Sampling.SSFresh
end

section

open scoped BigOperators
namespace SpectralSparsify.Sampling.SSFresh

lemma sampling_nonempty {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v)
    (eps p lam : ℝ) (he : 0 < eps) (he1 : eps < 1/2) (hp : 0 < p) (hp1 : p < 1/2)
    (hl : 0 < lam) (hgap : NonzeroEigGE (normLap G) lam)
    (S : Finset V) (k : ℕ) (heven : Even k)
    (hk1 : Real.logb 2 (3/p) ≤ (k : ℝ)) (hk2 : Real.logb 2 S.card ≤ (k : ℝ)) :
    1-p ≤ prob (inducedEdges G S) (sampleSubgraphProb G S k eps lam)
      (fun T => IsApprox (1+eps) (sparsifierWeight G S (sampleSubgraphProb G S k eps lam) T)
        (adjWeight G) ∧ (T.card : ℝ) ≤ 288*(k : ℝ)^2/(eps*lam)^2*S.card) := by
  classical
  have hl2 := native_gap_le_two G hdeg hgap
  have hk4 := sampling_k_ge_four p hp hp1 k heven hk1
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hU : 0 < sampleUpsilon k eps lam := by unfold sampleUpsilon; positivity
  let q := sampleSubgraphProb G S k eps lam
  let A := fun T => NormGE (symError G S q T) (eps*lam/3)
  let B := fun T => ∃ v ∈ S, (eps*lam/3)*(G.degree v : ℝ) ≤
    |∑ e ∈ (inducedEdges G S).filter (fun e => v ∈ e), edgeNoise q T e|
  let C := fun T : Finset (Sym2 V) => 288*(k : ℝ)^2/(eps*lam)^2*S.card < (T.card : ℝ)
  apply prob_good_from_three_bad (inducedEdges G S) q
    (fun e he => (sampleSubgraphProb_valid G S k eps lam hU he).1.le)
    (fun e he => (sampleSubgraphProb_valid G S k eps lam hU he).2) A B C _ p
  · exact native_adjacency_failure_budget G hdeg S k eps lam p hk0 heven he he1 hl hl2 hp hk1 hk2
  · exact native_degree_failure_budget G S hdeg k eps lam p (by omega) he he1 hl hl2 hp hk1 hk2
  · exact native_count_failure_budget G S k eps lam p (by omega) he he1 hl hl2 hp hk1
  · intro T hT _ hA hB hC
    constructor
    · apply deterministic_spectral_approx G hdeg S q T hT he he1 hl hgap
      · intro mu f hf heig
        exact (lt_of_not_ge (fun h => hA ⟨mu, f, hf, heig, h⟩)).le
      · intro v hv
        rw [degreeDelta_incidentNoise G S q T hT hv]
        exact (lt_of_not_ge (fun h => hB ⟨v, hv, h⟩)).le
    · exact le_of_not_gt hC

end SpectralSparsify.Sampling.SSFresh
end

section

namespace SpectralSparsify.Sampling.SSFresh
variable {V : Type*} [Fintype V] [DecidableEq V] [IsEmpty V]

lemma native_empty_case (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (k : ℕ) (ε lam p : ℝ) (hp : 0 ≤ p) :
    1 - p ≤ prob (inducedEdges G S) (sampleSubgraphProb G S k ε lam)
      (fun T =>
        IsApprox (1 + ε) (sparsifierWeight G S (sampleSubgraphProb G S k ε lam) T)
            (adjWeight G) ∧
          (T.card : ℝ) ≤ 288 * (k : ℝ)^2 / (ε * lam)^2 * S.card) := by
  classical
  have hS : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun v _ => isEmptyElim v)
  have hE : inducedEdges G S = ∅ := by simp [inducedEdges, hS]
  have ha (T : Finset (Sym2 V)) :
      IsApprox (1 + ε) (sparsifierWeight G S (sampleSubgraphProb G S k ε lam) T)
        (adjWeight G) := by
    intro x
    simp [lapForm]
  unfold prob
  rw [hE]
  simp only [Finset.powerset_empty, Finset.sum_singleton, ha, true_and]
  simp [hS, outcomeProb]
  exact hp

end SpectralSparsify.Sampling.SSFresh
end

section

namespace SpectralSparsify.Sampling

/-- Theorem 6.1 (Sampling High-Conductance Graphs; Spielman–Teng, arXiv:0808.4134v3, p. 8). Let
`ε, p ∈ (0, 1/2)` and let `G = (V, E)` be an unweighted graph with no isolated vertex whose smallest
nonzero normalized Laplacian eigenvalue is at least `λ > 0`. Let `S ⊆ V`, let `F` be the edges of
`G(S)` and `H = E - F`. Run `Sample((S, F), ε, p, λ)` with an even integer `k ≥ log₂(3/p)`,
`k ≥ log₂ |S|`: each edge `{i, j} ∈ F` is kept independently with probability
`p_{i,j} = min(1, Υ / min(d_i, d_j))`, `Υ = (12k/(ελ))²`, `d_i` the degree in `G(S)`, and gets weight
`1/p_{i,j}`; `G̃ = (V, F̃ ∪ H)` with weight `1` on `H`. Then with probability at least `1 - p`,
(S.1) `G̃` is a `(1+ε)`-approximation of `G`, and (S.2) `|F̃| ≤ 288 k² / (ελ)² · |S|`.
The paper sets `k = max(log₂(3/p), log₂ n)`; its proof needs `k` to be an even integer, so `k` is a
parameter here (the printed statement is the case where that maximum is an even integer). -/
theorem SSFresh.sampling_theorem_6_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v)
    (ε p lam : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hp0 : 0 < p) (hp1 : p < 1 / 2)
    (hlam : 0 < lam) (hspec : NonzeroEigGE (normLap G) lam)
    (S : Finset V) (k : ℕ) (hk : Even k)
    (hk1 : Real.logb 2 (3 / p) ≤ k) (hk2 : Real.logb 2 S.card ≤ k) :
    1 - p ≤ prob (inducedEdges G S) (sampleSubgraphProb G S k ε lam)
      (fun T =>
        IsApprox (1 + ε) (sparsifierWeight G S (sampleSubgraphProb G S k ε lam) T)
            (adjWeight G) ∧
          (T.card : ℝ) ≤ 288 * (k : ℝ) ^ 2 / (ε * lam) ^ 2 * S.card) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    let := h
    exact SSFresh.native_empty_case G S k ε lam p hp0.le
  | inr h =>
    let := h
    exact SSFresh.sampling_nonempty G hdeg ε p lam hε0 hε1 hp0 hp1 hlam hspec S k hk hk1 hk2

end SpectralSparsify.Sampling
end

open SpectralSparsify.Sampling

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v)
    (ε p lam : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hp0 : 0 < p) (hp1 : p < 1 / 2)
    (hlam : 0 < lam) (hspec : NonzeroEigGE (normLap G) lam)
    (S : Finset V) (k : ℕ) (hk : Even k)
    (hk1 : Real.logb 2 (3 / p) ≤ k) (hk2 : Real.logb 2 S.card ≤ k) :
    1 - p ≤ prob (inducedEdges G S) (sampleSubgraphProb G S k ε lam)
      (fun T =>
        IsApprox (1 + ε) (sparsifierWeight G S (sampleSubgraphProb G S k ε lam) T)
            (adjWeight G) ∧
          (T.card : ℝ) ≤ 288 * (k : ℝ) ^ 2 / (ε * lam) ^ 2 * S.card) := by
  exact SSFresh.sampling_theorem_6_1 G hdeg ε p lam hε0 hε1 hp0 hp1 hlam hspec S k hk hk1 hk2
