-- Prove2me | solution 1 for SendSplit.Existence.flow_le_sum_pos_demand
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:27:27.953585+00:00
-- url     : https://prove2.me/submissions/ac52beef-d593-4662-a803-1b3d4b074a9e

import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Definitions.Def_SendSplit_Existence_ReducedCost
import Definitions.Def_SendSplit_Existence_AugmentedGraph



namespace SendSplit.Existence
variable {n : ℕ}

lemma sum_in_eq (G : ArcGraph n) (g : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => (j, i) ∈ G.A), g j i = ∑ p ∈ G.A, g p.1 p.2 := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  rw [← Finset.sum_product' (f := fun j i => if (j, i) ∈ G.A then g j i else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext p; simp

lemma sum_out_eq (G : ArcGraph n) (g : Fin n → Fin n → ℝ) :
    ∑ i, ∑ k ∈ Finset.univ.filter (fun k => (i, k) ∈ G.A), g i k = ∑ p ∈ G.A, g p.1 p.2 := by
  classical
  simp only [Finset.sum_filter]
  rw [← Finset.sum_product' (f := fun j i => if (j, i) ∈ G.A then g j i else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext p; simp

lemma concave_subadd {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ici 0) f) (h0 : f 0 = 0) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : f (a + b) ≤ f a + f b := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with h | h
  · have ha' : a = 0 := by linarith
    have hb' : b = 0 := by linarith
    subst ha' hb'; simp [h0]
  · have s1 := hf.2 (Set.mem_Ici.2 (add_nonneg ha hb)) (Set.mem_Ici.2 le_rfl : (0:ℝ) ∈ Set.Ici 0)
      (div_nonneg ha h.le) (sub_nonneg.2 ((div_le_one h).2 (by linarith)) : (0:ℝ) ≤ 1 - a / (a+b))
      (by ring)
    have s2 := hf.2 (Set.mem_Ici.2 (add_nonneg ha hb)) (Set.mem_Ici.2 le_rfl : (0:ℝ) ∈ Set.Ici 0)
      (div_nonneg hb h.le) (sub_nonneg.2 ((div_le_one h).2 (by linarith)) : (0:ℝ) ≤ 1 - b / (a+b))
      (by ring)
    simp only [smul_eq_mul, h0, mul_zero, add_zero] at s1 s2
    have e1 : a / (a + b) * (a + b) = a := by field_simp
    have e2 : b / (a + b) * (a + b) = b := by field_simp
    rw [e1] at s1; rw [e2] at s2
    have e3 : a / (a+b) + b / (a+b) = 1 := by field_simp
    have s3 : (a / (a+b) + b / (a+b)) * f (a+b) ≤ f a + f b := by rw [add_mul]; linarith
    rwa [e3, one_mul] at s3

theorem reducedFlowCost_core (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (π : Fin n → ℝ) (r : Fin n → ℝ) (x : Fin n → Fin n → ℝ) (hx : IsFlow G r x) :
    reducedFlowCost G c π x = flowCost G c x + ∑ i, π i * r i := by
  have h1 : ∑ i, π i * r i = ∑ i, π i * ((∑ j ∈ Finset.univ.filter (fun j => (j, i) ∈ G.A), x j i)
        - (∑ k ∈ Finset.univ.filter (fun k => (i, k) ∈ G.A), x i k)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx.2 i]
  rw [h1]
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  have a := sum_in_eq G (fun j i => π i * x j i)
  have b := sum_out_eq G (fun i k => π i * x i k)
  rw [a, b]
  unfold reducedFlowCost flowCost reducedArcCost
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem concave_sandwich_core (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) (x y : Fin n → Fin n → ℝ) (hx : IsPreflow G x)
    (hy : IsPreflow G y) (θ : ℝ) (hθ : 0 ≤ θ) :
    (1 / 2 : ℝ) * flowCost G c (fun i j => 2 * x i j)
        + (1 / 2 : ℝ) * flowCost G c (fun i j => 2 * (θ * y i j))
        ≤ flowCost G c (fun i j => x i j + θ * y i j) ∧
      flowCost G c (fun i j => x i j + θ * y i j)
        ≤ flowCost G c x + flowCost G c (fun i j => θ * y i j) := by
  have hxy : ∀ p ∈ G.A, 0 ≤ x p.1 p.2 := fun p _ => hx.1 _ _
  have hyy : ∀ p ∈ G.A, 0 ≤ θ * y p.1 p.2 := fun p _ => mul_nonneg hθ (hy.1 _ _)
  constructor
  · unfold flowCost
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hcc, h0⟩ := hc p hp
    have := hcc.2 (by simpa using mul_nonneg zero_le_two (hxy p hp) : 2 * x p.1 p.2 ∈ Set.Ici (0:ℝ))
      (by simpa using mul_nonneg zero_le_two (hyy p hp) : 2 * (θ * y p.1 p.2) ∈ Set.Ici (0:ℝ))
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    simp only [smul_eq_mul] at this
    have e : 1 / 2 * (2 * x p.1 p.2) + 1 / 2 * (2 * (θ * y p.1 p.2)) = x p.1 p.2 + θ * y p.1 p.2 := by ring
    rw [e] at this
    exact this
  · unfold flowCost
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hcc, h0⟩ := hc p hp
    -- subadditivity of concave function with c 0 = 0
    have ha0 : 0 ≤ x p.1 p.2 := hxy p hp
    have hb0 : 0 ≤ θ * y p.1 p.2 := hyy p hp
    exact concave_subadd (hcc) h0 ha0 hb0

theorem flow_le_core (G : ArcGraph n) (r : Fin n → ℝ)
    (x : Fin n → Fin n → ℝ) (hx : IsFlow G r x) (p : Fin n × Fin n) (hp : p ∈ G.A)
    (hpC : ¬ SameComponent G p.1 p.2) :
    x p.1 p.2 ≤ ∑ i, max (r i) 0 := by
  classical
  obtain ⟨⟨hnn, hzero⟩, hcons⟩ := hx
  set Q : Finset (Fin n) := Finset.univ.filter (fun i => Reach G p.2 i) with hQ
  have hmem : ∀ i, i ∈ Q ↔ Reach G p.2 i := by intro i; simp [hQ]
  have hclosed : ∀ q ∈ G.A, q.1 ∈ Q → q.2 ∈ Q := by
    intro q hq h1
    rw [hmem] at h1 ⊢
    exact Relation.ReflTransGen.tail h1 hq
  have hpa : p.1 ∉ Q := by
    intro h
    rw [hmem] at h
    exact hpC ⟨Relation.ReflTransGen.single hp, h⟩
  have hb : p.2 ∈ Q := by rw [hmem]; exact Relation.ReflTransGen.refl
  have h1 : ∑ i ∈ Q, r i = ∑ q ∈ G.A, ((if q.2 ∈ Q then x q.1 q.2 else 0) - (if q.1 ∈ Q then x q.1 q.2 else 0)) := by
    have e1 := sum_in_eq G (fun j i => if i ∈ Q then x j i else 0)
    have e2 := sum_out_eq G (fun i k => if i ∈ Q then x i k else 0)
    rw [Finset.sum_sub_distrib, ← e1, ← e2, ← Finset.sum_sub_distrib]
    have : ∑ i ∈ Q, r i = ∑ i, if i ∈ Q then r i else 0 := by
      rw [hQ, Finset.sum_filter]; simp [hQ]
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i ∈ Q
    · simp only [h, if_true, ← hcons i]
    · simp [h]
  have h2 : x p.1 p.2 ≤ ∑ q ∈ G.A, ((if q.2 ∈ Q then x q.1 q.2 else 0) - (if q.1 ∈ Q then x q.1 q.2 else 0)) := by
    rw [← Finset.add_sum_erase _ _ hp]
    have : (if p.2 ∈ Q then x p.1 p.2 else 0) - (if p.1 ∈ Q then x p.1 p.2 else 0) = x p.1 p.2 := by
      simp [hb, hpa]
    rw [this]
    have : 0 ≤ ∑ q ∈ G.A.erase p, ((if q.2 ∈ Q then x q.1 q.2 else 0) - (if q.1 ∈ Q then x q.1 q.2 else 0)) := by
      refine Finset.sum_nonneg fun q hq => ?_
      have hqA := Finset.mem_of_mem_erase hq
      by_cases h : q.1 ∈ Q
      · simp [h, hclosed q hqA h]
      · by_cases h' : q.2 ∈ Q <;> simp [h, h', hnn]
    linarith
  have h3 : ∑ i ∈ Q, r i ≤ ∑ i, max (r i) 0 := by
    calc ∑ i ∈ Q, r i ≤ ∑ i ∈ Q, max (r i) 0 := Finset.sum_le_sum fun i _ => le_max_left _ _
      _ ≤ ∑ i, max (r i) 0 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => le_max_right _ _
  linarith

end SendSplit.Existence

open SendSplit.Existence


theorem solution {n : ℕ} (G : ArcGraph n) (r : Fin n → ℝ)
    (x : Fin n → Fin n → ℝ) (hx : IsFlow G r x) (p : Fin n × Fin n) (hp : p ∈ G.A)
    (hpC : ¬ SameComponent G p.1 p.2) :
    x p.1 p.2 ≤ ∑ i, max (r i) 0 := by
  exact flow_le_core G r x hx p hp hpC
