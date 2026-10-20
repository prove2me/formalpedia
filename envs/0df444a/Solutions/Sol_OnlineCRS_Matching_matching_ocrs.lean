-- Prove2me | solution 1 for OnlineCRS.Matching.matching_ocrs
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T05:01:30.914573+00:00
-- url     : https://prove2.me/submissions/728b439d-d65f-49a6-8221-a57189bf41a6

/-
SPDX-License-Identifier: Apache-2.0
Original Lean formalization of the randomized matching OCRS theorem.
Mathematical source: Feldman, Svensson, and Zenklusen,
Online Contention Resolution Schemes, arXiv:1508.00142v2, Theorem 2.7.
Native Prove2Me definitions are imported unchanged. No accepted proof source is copied.
-/
import Mathlib
import Definitions.Def_OnlineCRS_Matching_Model

-- BEGIN FiniteWeights
noncomputable section
namespace OCRSMatchingProof
open OnlineCRS.Matroid
open scoped Classical

variable {α : Type} [Fintype α] [DecidableEq α]

def finsetBoolEquiv : Finset α ≃ (α → Bool) where
  toFun A i := decide (i ∈ A)
  invFun f := Finset.univ.filter (fun i => f i = true)
  left_inv A := by ext i; simp
  right_inv f := by funext i; simp

lemma sum_finset_prod (f : α → Bool → ℝ) :
    (∑ A : Finset α, ∏ i, f i (decide (i ∈ A))) = ∏ i, (f i true + f i false) := by
  calc
    _ = ∑ c : α → Bool, ∏ i, f i (c i) :=
      Fintype.sum_equiv finsetBoolEquiv _ _ (fun _ => rfl)
    _ = ∏ i, ∑ b : Bool, f i b := (Fintype.prod_sum f).symm
    _ = _ := by simp only [Fintype.sum_bool]

lemma sum_finset_finset_prod (f : α → Bool → Bool → ℝ) :
    (∑ K : Finset α, ∑ A : Finset α,
      ∏ i, f i (decide (i ∈ K)) (decide (i ∈ A))) =
    ∏ i, (f i true true + f i true false + (f i false true + f i false false)) := by
  simp_rw [sum_finset_prod]
  exact sum_finset_prod (fun i b => f i b true + f i b false)

lemma activeProb_nonneg (p : α → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (A : Finset α) :
    0 ≤ activeProb p A := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact (hp i).1
  · exact sub_nonneg.mpr (hp i).2

lemma sum_activeProb (p : α → ℝ) : (∑ A : Finset α, activeProb p A) = 1 := by
  have h := sum_finset_prod (fun i b => if b then p i else 1-p i)
  simpa [activeProb] using h

end OCRSMatchingProof
end
-- END FiniteWeights

-- BEGIN FiniteWeightsEvent
noncomputable section
namespace OCRSMatchingProof
open OnlineCRS.Matroid
open scoped Classical

variable {α : Type} [Fintype α] [DecidableEq α]

def edgeLocalWeight (q p : α → ℝ) (e : α) (D : Finset α) (i : α) (k a : Bool) : ℝ :=
  (if k then q i else 1-q i) * (if a then p i else 1-p i) *
    if (i = e → k = true) ∧ (i ∈ D → ¬(k = true ∧ a = true)) then 1 else 0

omit [Fintype α] in
lemma edgeLocalWeight_sum (q p : α → ℝ) (e : α) (D : Finset α) (he : e ∉ D) (i : α) :
    edgeLocalWeight q p e D i true true + edgeLocalWeight q p e D i true false +
    (edgeLocalWeight q p e D i false true + edgeLocalWeight q p e D i false false) =
    (if i=e then q e else 1) * (if i∈D then 1-q i*p i else 1) := by
  by_cases hi : i=e
  · subst i
    simp [edgeLocalWeight,he]
    ring
  · by_cases hd : i∈D <;> simp [edgeLocalWeight,hi,hd] <;> ring

lemma successful_event_prod (q p : α → ℝ) (e : α) (D K A : Finset α) :
    activeProb q K * activeProb p A *
      (if e ∈ K ∧ ∀ i ∈ D, ¬(i ∈ K ∧ i ∈ A) then (1 : ℝ) else 0) =
    ∏ i, edgeLocalWeight q p e D i (decide (i∈K)) (decide (i∈A)) := by
  have he : (∀ i : α, (i=e → i∈K) ∧ (i∈D → ¬(i∈K ∧ i∈A))) ↔
      e∈K ∧ ∀ i∈D, ¬(i∈K ∧ i∈A) := by
    constructor
    · intro h
      exact ⟨(h e).1 rfl, fun i hi => (h i).2 hi⟩
    · rintro ⟨hk,hd⟩ i
      exact ⟨fun h => h ▸ hk, fun h => hd i h⟩
  simp only [edgeLocalWeight, decide_eq_true_eq]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Fintype.prod_ite_zero]
  simp only [he]
  split_ifs
  · simp_rw [← mul_ite]
    rw [Finset.prod_mul_distrib]
    rfl
  · rfl

lemma successful_event_mass (q p : α → ℝ) (e : α) (D : Finset α) (he : e ∉ D) :
    (∑ K : Finset α, ∑ A : Finset α,
      activeProb q K * activeProb p A *
        (if e ∈ K ∧ ∀ i ∈ D, ¬(i ∈ K ∧ i ∈ A) then (1 : ℝ) else 0)) =
    q e * ∏ i ∈ D, (1-q i*p i) := by
  simp_rw [successful_event_prod]
  rw [sum_finset_finset_prod]
  simp_rw [edgeLocalWeight_sum q p e D he]
  rw [Finset.prod_mul_distrib]
  simp

end OCRSMatchingProof
end
-- END FiniteWeightsEvent

-- BEGIN Inclusion
noncomputable section
namespace OCRSMatchingProof
open OnlineCRS.Matching

lemma incl_bounds {E : Type} (x : E → ℝ) (e : E) : 0 ≤ incl x e ∧ incl x e ≤ 1 := by
  unfold incl
  split_ifs with hx hz
  · norm_num
  · have ht : 0 < x e := lt_of_le_of_ne hx (Ne.symm hz)
    have he : Real.exp (-x e) ≤ 1 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    have hl := Real.add_one_le_exp (-x e)
    constructor
    · exact div_nonneg (by linarith) ht.le
    · exact (div_le_one ht).mpr (by linarith)
  · norm_num

lemma incl_mul {E : Type} (x : E → ℝ) (e : E) (hx : 0 ≤ x e) :
    incl x e * x e = 1 - Real.exp (-x e) := by
  unfold incl
  rw [if_pos hx]
  split_ifs with hz
  · simp [hz]
  · exact div_mul_cancel₀ _ hz

lemma exp_neg_le_incl {E : Type} (x : E → ℝ) (e : E) (hx : 0 ≤ x e) :
    Real.exp (-x e) ≤ incl x e := by
  by_cases hz : x e = 0
  · simp [incl,hz]
  have ht : 0 < x e := lt_of_le_of_ne hx (Ne.symm hz)
  rw [incl,if_pos hx,if_neg hz,le_div_iff₀ ht]
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (x e)) (Real.exp_pos (-x e)).le
  have he : Real.exp (x e) * Real.exp (-x e) = 1 := by rw [← Real.exp_add]; simp
  rw [he] at h
  nlinarith

end OCRSMatchingProof
end
-- END Inclusion

-- BEGIN GraphFamilies
noncomputable section
namespace OCRSMatchingProof
open OnlineCRS.Matching OnlineCRS.Matroid EdmondsMatching65.Polyhedron
open scoped Classical

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
lemma mem_famK (G : EdmondsMatching65.Polyhedron.Graph V E) (K I : Finset E) :
    I ∈ famK G K ↔ I ⊆ K ∧ IsMatching G I := by
  simp [famK]

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma matching_empty (G : EdmondsMatching65.Polyhedron.Graph V E) : IsMatching G ∅ := by simp [IsMatching]

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma matching_mono (G : EdmondsMatching65.Polyhedron.Graph V E) {I J : Finset E} (h : IsMatching G I) (hJI : J ⊆ I) :
    IsMatching G J := by
  intro e he f hf hne v hv
  exact h e (hJI he) f (hJI hf) hne v hv

omit [Fintype V] [DecidableEq V] in
lemma famK_greedy (G : EdmondsMatching65.Polyhedron.Graph V E) (K : Finset E) : IsGreedyFamily (IsMatching G) (famK G K) := by
  refine ⟨(mem_famK G K ∅).mpr ⟨Finset.empty_subset _,matching_empty G⟩,?_,?_⟩
  · intro I hI J hJI
    have h := (mem_famK G K I).mp hI
    exact (mem_famK G K J).mpr ⟨hJI.trans h.1,matching_mono G h.2 hJI⟩
  · intro I hI
    exact ((mem_famK G K I).mp hI).2

omit [Fintype V] [DecidableEq V] in
lemma mem_edgeStar (G : EdmondsMatching65.Polyhedron.Graph V E) (u : V) (e : E) : e ∈ edgeStar G u ↔ u ∈ G.ends e := by
  simp [edgeStar]

omit [Fintype V] [DecidableEq V] in
lemma edge_not_otherIncident (G : EdmondsMatching65.Polyhedron.Graph V E) (u v : V) (e : E) :
    e ∉ otherIncident G u v e := by simp [otherIncident]

omit [Fintype V] [DecidableEq V] in
lemma mem_otherIncident (G : EdmondsMatching65.Polyhedron.Graph V E) (u v : V) (e f : E) :
    f ∈ otherIncident G u v e ↔ (u ∈ G.ends f ∨ v ∈ G.ends f) ∧ f ≠ e := by
  simp [otherIncident,edgeStar]

omit [Fintype V] [DecidableEq V] in
lemma successful_selectable (G : EdmondsMatching65.Polyhedron.Graph V E) (A K : Finset E) (e : E) (u v : V)
    (he : G.ends e = s(u,v)) (heK : e ∈ K)
    (havoid : ∀ f ∈ otherIncident G u v e, ¬(f ∈ K ∧ f ∈ A)) :
    Selectable (famK G K) A e := by
  intro I hIA hI
  have hIK := ((mem_famK G K I).mp hI).1
  have hmatch := ((mem_famK G K I).mp hI).2
  have hconf : ∀ f ∈ I, f ≠ e → ∀ w : V, w ∈ G.ends e → w ∉ G.ends f := by
    intro f hf hfe w hwe hwf
    have hw : w = u ∨ w = v := by simpa [he] using hwe
    have hN : f ∈ otherIncident G u v e := by
      apply (mem_otherIncident G u v e f).mpr
      refine ⟨?_,hfe⟩
      rcases hw with rfl | rfl
      · exact Or.inl hwf
      · exact Or.inr hwf
    exact havoid f hN ⟨hIK hf,hIA hf⟩
  apply (mem_famK G K (insert e I)).mpr
  refine ⟨Finset.insert_subset heK hIK,?_⟩
  intro f hfIns g hgIns hfg w hwf
  rcases Finset.mem_insert.mp hfIns with rfl | hf
  · rcases Finset.mem_insert.mp hgIns with rfl | hg
    · exact (hfg rfl).elim
    · exact hconf g hg (Ne.symm hfg) w hwf
  · rcases Finset.mem_insert.mp hgIns with rfl | hg
    · exact fun hwe => hconf f hf hfg w hwe hwf
    · exact hmatch f hf g hg hfg w hwf

end OCRSMatchingProof
end
-- END GraphFamilies

-- BEGIN Pushforward
noncomputable section
namespace OCRSMatchingProof
open OnlineCRS.Matching OnlineCRS.Matroid EdmondsMatching65.Polyhedron
open scoped Classical
variable {V E : Type} [Fintype E] [DecidableEq E]

lemma weight_nonneg (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ)
    (Fam : Finset (Finset E)) : 0 ≤ ocrsWeight G x Fam := by
  apply Finset.sum_nonneg
  intro K _
  exact mul_nonneg (activeProb_nonneg _ (incl_bounds x) K) (by split_ifs <;> norm_num)

lemma weight_expectation (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ)
    (f : Finset (Finset E) → ℝ) :
    ∑ Fam, ocrsWeight G x Fam * f Fam = ∑ K, activeProb (incl x) K * f (famK G K) := by
  simp only [ocrsWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro K _
  simp [ite_mul]

lemma weight_sum (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ) :
    ∑ Fam, ocrsWeight G x Fam = 1 := by
  simpa using (weight_expectation G x (fun _ => 1)).trans (by simpa using sum_activeProb (incl x))

lemma weight_support (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ)
    (Fam : Finset (Finset E)) (h : ocrsWeight G x Fam ≠ 0) :
    IsGreedyFamily (IsMatching G) Fam := by
  by_contra hn
  apply h
  unfold ocrsWeight
  apply Finset.sum_eq_zero
  intro K _
  have he : famK G K ≠ Fam := by
    intro he
    exact hn (he ▸ famK_greedy G K)
  simp [he]

lemma weight_randGreedy (G : EdmondsMatching65.Polyhedron.Graph V E) :
    IsRandGreedyOCRS (IsMatching G) (ocrsWeight G) := by
  intro x
  exact ⟨weight_nonneg G x, weight_sum G x, weight_support G x⟩

end OCRSMatchingProof
end
-- END Pushforward

-- BEGIN SelectionBound
noncomputable section
namespace OCRSMatchingProof
open OnlineCRS.Matching OnlineCRS.Matroid EdmondsMatching65.Polyhedron
open scoped Classical
variable {V E : Type} [Fintype E] [DecidableEq E]

lemma success_le_selection (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ)
    (hx : ∀ f, 0 ≤ x f ∧ x f ≤ 1) (e : E) (u v : V) (he : G.ends e = s(u,v)) :
    incl x e * ∏ f ∈ otherIncident G u v e, (1 - incl x f * x f) ≤
      ∑ Fam, ocrsWeight G x Fam * selProb x Fam e := by
  rw [weight_expectation]
  rw [← successful_event_mass (incl x) x e (otherIncident G u v e) (edge_not_otherIncident G u v e)]
  apply Finset.sum_le_sum
  intro K _
  rw [selProb, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  have hK := activeProb_nonneg (incl x) (incl_bounds x) K
  have hA := activeProb_nonneg x hx A
  by_cases hs : e ∈ K ∧ ∀ f ∈ otherIncident G u v e, ¬(f ∈ K ∧ f ∈ A)
  · have ht := successful_selectable G A K e u v he hs.1 hs.2
    rw [if_pos hs, if_pos ht, mul_one]
  · simp only [if_neg hs, mul_zero]
    exact mul_nonneg hK (by split_ifs <;> positivity)

lemma inclusion_product_bound {E : Type} [Fintype E] [DecidableEq E] (x : E → ℝ)
    (hx : ∀ f, 0 ≤ x f) (e : E) (D : Finset E) :
    Real.exp (-(x e + ∑ f ∈ D, x f)) ≤ incl x e * ∏ f ∈ D, (1 - incl x f * x f) := by
  have hp : (∏ f ∈ D, (1 - incl x f * x f)) = Real.exp (-(∑ f ∈ D, x f)) := by
    simp_rw [incl_mul x _ (hx _), sub_sub_cancel]
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [hp, neg_add, Real.exp_add]
  exact mul_le_mul_of_nonneg_right (exp_neg_le_incl x e (hx e)) (Real.exp_pos _).le

end OCRSMatchingProof
end
-- END SelectionBound

-- BEGIN DegreeBounds
noncomputable section
namespace OCRSMatchingProof
open OnlineCRS.Matching EdmondsMatching65.Polyhedron
open scoped Classical Pointwise
variable {V E : Type} [Fintype E] [DecidableEq E]

lemma scaled_degree_bounds (G : EdmondsMatching65.Polyhedron.Graph V E) (b : ℝ)
    (hb : 0 ≤ b) (x : E → ℝ) (hx : x ∈ b • matchingRelax G) :
    (∀ e, 0 ≤ x e) ∧ (∀ u, ∑ e ∈ edgeStar G u, x e ≤ b) := by
  rcases hx with ⟨y, hy, rfl⟩
  refine ⟨fun e => mul_nonneg hb (hy.1 e), ?_⟩
  intro u
  change ∑ e ∈ edgeStar G u, b * y e ≤ b
  rw [← Finset.mul_sum]
  simpa using mul_le_mul_of_nonneg_left (hy.2 u) hb

lemma coordinate_le_degree (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ)
    (hx : ∀ e, 0 ≤ x e) (e : E) (u : V) (hu : u ∈ G.ends e) :
    x e ≤ ∑ f ∈ edgeStar G u, x f := by
  exact Finset.single_le_sum (fun f _ => hx f) ((mem_edgeStar G u e).mpr hu)

lemma scaled_coordinate_bounds (G : EdmondsMatching65.Polyhedron.Graph V E) (b : ℝ)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (x : E → ℝ) (hx : x ∈ b • matchingRelax G) :
    ∀ e, 0 ≤ x e ∧ x e ≤ 1 := by
  obtain ⟨hn, hd⟩ := scaled_degree_bounds G b hb x hx
  intro e
  obtain ⟨⟨u, v⟩, he⟩ := Sym2.mk_surjective (G.ends e)
  refine ⟨hn e, (coordinate_le_degree G x hn e u ?_).trans ((hd u).trans hb1)⟩
  simp [← he]

lemma neighborhood_degree_bound (G : EdmondsMatching65.Polyhedron.Graph V E) (b : ℝ)
    (x : E → ℝ) (hn : ∀ e, 0 ≤ x e)
    (hd : ∀ u, ∑ e ∈ edgeStar G u, x e ≤ b)
    (e : E) (u v : V) (he : G.ends e = s(u,v)) :
    x e + ∑ f ∈ otherIncident G u v e, x f ≤ 2 * b := by
  have hsub : insert e (otherIncident G u v e) ⊆ edgeStar G u ∪ edgeStar G v := by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · apply Finset.mem_union_left
      exact (mem_edgeStar G u f).mpr (by simp [he])
    · exact (Finset.mem_sdiff.mp hf).1
  calc
    x e + ∑ f ∈ otherIncident G u v e, x f =
        ∑ f ∈ insert e (otherIncident G u v e), x f := by
      rw [Finset.sum_insert (edge_not_otherIncident G u v e)]
    _ ≤ ∑ f ∈ edgeStar G u ∪ edgeStar G v, x f :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f _ _ => hn f)
    _ ≤ (∑ f ∈ edgeStar G u, x f) + ∑ f ∈ edgeStar G v, x f :=
      by
        have hi : 0 ≤ ∑ f ∈ edgeStar G u ∩ edgeStar G v, x f :=
          Finset.sum_nonneg (fun f _ => hn f)
        have hu := Finset.sum_union_inter (f := x) (s₁ := edgeStar G u) (s₂ := edgeStar G v)
        linarith
    _ ≤ 2 * b := by linarith [hd u, hd v]

end OCRSMatchingProof
end
-- END DegreeBounds

-- BEGIN NativeRoot
namespace OnlineCRS.Matching

/-- Theorem 2.7, p. 13: the degree relaxation of matching admits a randomized greedy OCRS. -/
theorem matching_ocrs {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∃ w : (E → ℝ) → Finset (Finset E) → ℝ,
      OnlineCRS.Matroid.IsSelectableRand (EdmondsMatching65.Polyhedron.IsMatching G) (matchingRelax G) b
        (Real.exp (-2 * b)) w := by
  refine ⟨ocrsWeight G, OCRSMatchingProof.weight_randGreedy G, ?_⟩
  intro x hx e
  obtain ⟨hn, hd⟩ := OCRSMatchingProof.scaled_degree_bounds G b hb0 x hx
  have h01 := OCRSMatchingProof.scaled_coordinate_bounds G b hb0 hb1 x hx
  have hre : ∃ u v, G.ends e = s(u,v) :=
    Sym2.inductionOn (G.ends e) (fun u v => ⟨u,v,rfl⟩)
  obtain ⟨u,v,he⟩ := hre
  calc
    Real.exp (-2 * b) ≤ Real.exp (-(x e + ∑ f ∈ otherIncident G u v e, x f)) := by
      apply Real.exp_le_exp.mpr
      linarith [OCRSMatchingProof.neighborhood_degree_bound G b x hn hd e u v he]
    _ ≤ incl x e * ∏ f ∈ otherIncident G u v e, (1 - incl x f * x f) :=
      OCRSMatchingProof.inclusion_product_bound x hn e _
    _ ≤ _ := OCRSMatchingProof.success_le_selection G x h01 e u v he

end OnlineCRS.Matching
-- END NativeRoot

theorem solution {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∃ w : (E → ℝ) → Finset (Finset E) → ℝ,
      OnlineCRS.Matroid.IsSelectableRand (EdmondsMatching65.Polyhedron.IsMatching G)
        (OnlineCRS.Matching.matchingRelax G) b (Real.exp (-2 * b)) w :=
  OnlineCRS.Matching.matching_ocrs G b hb0 hb1
