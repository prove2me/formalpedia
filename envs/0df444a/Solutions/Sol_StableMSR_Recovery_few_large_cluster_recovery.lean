-- Prove2me | solution 1 for StableMSR.Recovery.few_large_cluster_recovery
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T15:12:16.887196+00:00
-- url     : https://prove2.me/submissions/30346cc7-9b65-4fe3-a85a-c6c32da83675

import Definitions.Def_StableMSR_Recovery_FewBranch
import Theorems.Thm_StableMSR_Recovery_center_separation
import Theorems.Thm_StableMSR_Recovery_small_cluster_components
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto


set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery
namespace CandidateAux



/- Equation (1): input-distance ball representations passing every source test. -/


theorem representation_card {n : ℕ} (d : Point n → Point n → ℝ) (γ R : ℝ) :
    (representations d γ R).card ≤ n ^ 2 := by
  have h := Finset.card_le_card (Finset.filter_subset
    (fun q : Point n × Point n =>
      (γ - 1) * R / 4 ≤ d q.1 q.2 ∧ d q.1 q.2 ≤ R ∧
      (γ - 1) * R / 4 ≤ radius d (represented d q) ∧
      radius d (represented d q) ≤ R ∧
      represented d q = ball d q.1 (γ * d q.1 q.2)) Finset.univ)
  simpa [representations, Point, pow_two] using h

lemma exists_center {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (hC : C.Nonempty) : ∃ c, OptimalCenter d C c := by
  obtain ⟨c, hc, he⟩ := Finset.exists_mem_eq_inf' hC (eccentricity d C)
  exact ⟨c, hc, by simpa [radius, hC] using he.symm⟩

lemma radius_attained {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} {c : Point n} (hc : OptimalCenter d C c) :
    ∃ x ∈ C, d c x = radius d C := by
  have hC : C.Nonempty := ⟨c, hc.1⟩
  obtain ⟨x, hx, he⟩ := Finset.exists_mem_eq_sup' hC (d c)
  refine ⟨x, hx, he.symm.trans ?_⟩
  simpa [eccentricity, hC] using hc.2

lemma radius_le_largest {n : ℕ} (d : Point n → Point n → ℝ)
    {O : Partition n} {C : Cluster n} (hC : C ∈ O) :
    radius d C ≤ largestRadius d O := by
  rw [largestRadius, dif_pos ⟨C, hC⟩]
  exact Finset.le_sup' (radius d) hC

/- Every true large cluster occurs among the at most n² representations. -/
theorem large_cluster_represented {n : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n)
    (γ : ℝ) (hγ : 1 < γ) (O : Partition n) (hO : Stable d k γ O)
    (C : Cluster n) (hC : C ∈ largeClusters d O (γ - 1)) :
    ∃ q ∈ representations d γ (largestRadius d O), represented d q = C := by
  obtain ⟨hCO, hlarge⟩ := Finset.mem_filter.mp hC
  obtain ⟨c, hc⟩ := exists_center d (hO.1.2.1 C hCO)
  obtain ⟨x, hx, hcx⟩ := radius_attained d hc
  have hsep := center_separation d hd k hk γ hγ O hO C hCO c hc
  have hrep : represented d (c, x) = C := by
    simpa only [represented, hcx] using hsep.2.2.1.symm
  refine ⟨(c, x), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hrep⟩
  change (γ - 1) * largestRadius d O / 4 ≤ radius d C at hlarge
  simp only [Prod.fst, Prod.snd, hcx, hrep]
  exact ⟨hlarge, radius_le_largest d hCO, hlarge,
    radius_le_largest d hCO, hsep.2.2.2⟩

/- Choosing one representation per distinct set preserves the family size. -/
theorem lift_family {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (T : Finset B) (f : A → B)
    (h : ∀ b ∈ T, ∃ a ∈ S, f a = b) :
    ∃ Q ⊆ S, Q.card = T.card ∧ Q.image f = T := by
  choose g hg using (fun b : {b // b ∈ T} => h b.val b.property)
  have hinj : Function.Injective g := by
    intro b c hbc
    apply Subtype.ext
    exact (hg b).2.symm.trans ((congrArg f hbc).trans (hg c).2)
  let Q := T.attach.image g
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact (hg b).1
  · change (T.attach.image g).card = T.card
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  · have hf : (fun b : {b // b ∈ T} => f (g b)) = Subtype.val :=
      funext (fun b => (hg b).2)
    change (T.attach.image g).image f = T
    rw [Finset.image_image]
    change T.attach.image (fun b => f (g b)) = T
    rw [hf, Finset.attach_image_val]

/- The true large-cluster family has a size-preserving candidate representation. -/
theorem large_family_represented {n : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n)
    (γ : ℝ) (hγ : 1 < γ) (O : Partition n) (hO : Stable d k γ O) :
    ∃ Q ⊆ representations d γ (largestRadius d O),
      Q.card = (largeClusters d O (γ - 1)).card ∧
      Q.image (represented d) = largeClusters d O (γ - 1) := by
  exact lift_family _ _ _ (large_cluster_represented d hd k hk γ hγ O hO)



/- Bounded disjoint-family enumeration includes the true large-cluster family. -/
theorem bounded_enumeration_complete {n : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n)
    (γ : ℝ) (hγ : 1 < γ) (O : Partition n) (hO : Stable d k γ O)
    (budget : ℕ) (hbudget : (largeClusters d O (γ - 1)).card ≤ budget) :
    ∃ Q ∈ families d γ (largestRadius d O) budget,
      Q.image (represented d) = largeClusters d O (γ - 1) := by
  obtain ⟨Q, hQ, hcard, himage⟩ := large_family_represented d hd k hk γ hγ O hO
  have hinj : Set.InjOn (represented d) (Q : Set (Point n × Point n)) := by
    apply Finset.injOn_of_card_image_eq
    rw [himage, hcard]
  refine ⟨Q, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hQ, ?_⟩, himage⟩
  refine ⟨hcard ▸ hbudget, ?_⟩
  intro p hp q hq hpq
  have hpT : represented d p ∈ largeClusters d O (γ - 1) := by
    rw [← himage]
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hqT : represented d q ∈ largeClusters d O (γ - 1) := by
    rw [← himage]
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  exact hO.1.2.2.1 (Finset.mem_filter.mp hpT).1 (Finset.mem_filter.mp hqT).1
    (fun h => hpq (hinj hp hq h))

lemma large_small_union {n : ℕ} (d : Point n → Point n → ℝ)
    (O : Partition n) (ε : ℝ) :
    largeClusters d O ε ∪ smallClusters d O ε = O := by
  ext C
  simp only [largeClusters, smallClusters, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hC
    rcases le_or_gt (smallThreshold d O ε) (radius d C) with h | h
    · exact Or.inl ⟨hC, h⟩
    · exact Or.inr ⟨hC, h⟩

lemma component_nonempty {n : ℕ} (d : Point n → Point n → ℝ)
    (s : ℝ) (W : Cluster n) {K : Cluster n} (hK : K ∈ components d s W) :
    K.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hK
  exact ⟨x, Finset.mem_filter.mpr ⟨hx, SimpleGraph.Reachable.refl x⟩⟩

/- Removing the true large clusters leaves precisely the globally identified small components. -/
theorem small_clusters_from_global_components {n : ℕ}
    (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n)
    (O : Partition n) (hO : Stable d k γ O) :
    (components d (2 * smallThreshold d O (γ - 1)) Finset.univ).filter
      (fun K => Disjoint K ((largeClusters d O (γ - 1)).biUnion id)) =
      smallClusters d O (γ - 1) := by
  obtain ⟨hsmall, hrest⟩ := small_cluster_components d hd k hk γ hγ hkn O hO
  ext K
  constructor
  · intro hK
    obtain ⟨hcomp, hdis⟩ := Finset.mem_filter.mp hK
    by_contra hn
    have hsub := hrest K hcomp hn
    obtain ⟨x, hx⟩ := component_nonempty d _ _ hcomp
    exact Finset.disjoint_left.mp hdis hx (hsub hx)
  · intro hK
    refine Finset.mem_filter.mpr ⟨hsmall K hK, ?_⟩
    apply Finset.disjoint_left.mpr
    intro x hx hU
    obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hU
    obtain ⟨hKO, hKr⟩ := Finset.mem_filter.mp hK
    obtain ⟨hCO, hCr⟩ := Finset.mem_filter.mp hC
    have hKC : K ≠ C := by intro heq; subst C; linarith
    exact Finset.disjoint_left.mp (hO.1.2.2.1 hKO hCO hKC) hx hxC

/- A feasibility-checked completion using global components; at the true large
family it is the same completion as recomputing residual threshold components. -/


/- If the bounded enumeration can hold all true large clusters, one enumerated
family completes exactly to the unique optimal partition. -/
theorem few_branch_complete {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n)
    (O : Partition n) (hO : Stable d k γ O) (budget : ℕ)
    (hbudget : (largeClusters d O (γ - 1)).card ≤ budget) :
    ∃ Q ∈ families d γ (largestRadius d O) budget,
      completeFamily d γ (largestRadius d O) Q = O := by
  obtain ⟨Q, hQ, himage⟩ := bounded_enumeration_complete d hd k hk γ hγ.1 O hO budget hbudget
  refine ⟨Q, hQ, ?_⟩
  unfold completeFamily
  rw [himage]
  change largeClusters d O (γ - 1) ∪
    (components d (2 * smallThreshold d O (γ - 1)) Finset.univ).filter
      (fun K => Disjoint K ((largeClusters d O (γ - 1)).biUnion id)) = O
  rw [small_clusters_from_global_components d hd k hk γ hγ hkn O hO,
    large_small_union]

end CandidateAux
end StableMSR.Recovery


set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.CandidateAux

/- Retain a candidate only after validating the partition and a strict cost improvement. -/


theorem improve_feasible {n : ℕ} (d : Point n → Point n → ℝ) (k : ℕ)
    (A B : Partition n) (hA : Feasible Finset.univ k A) :
    Feasible Finset.univ k (improve d k A B) := by
  unfold improve
  split_ifs with h
  · exact h.1
  · exact hA

theorem improve_le_left {n : ℕ} (d : Point n → Point n → ℝ) (k : ℕ)
    (A B : Partition n) : cost d (improve d k A B) ≤ cost d A := by
  unfold improve
  split_ifs with h
  · exact h.2.le
  · exact le_rfl

theorem improve_le_right {n : ℕ} (d : Point n → Point n → ℝ) (k : ℕ)
    (A B : Partition n) (hB : Feasible Finset.univ k B) :
    cost d (improve d k A B) ≤ cost d B := by
  unfold improve
  split_ifs with h
  · exact le_rfl
  · exact le_of_not_gt (fun hlt => h ⟨hB, hlt⟩)

/- Sequential, feasibility-checked minimum selection; the initial answer handles an empty list. -/


theorem select_feasible {n : ℕ} (d : Point n → Point n → ℝ) (k : ℕ)
    (candidates : List (Partition n)) (initial : Partition n)
    (h : Feasible Finset.univ k initial) :
    Feasible Finset.univ k (select d k initial candidates) := by
  induction candidates generalizing initial with
  | nil => exact h
  | cons B bs ih => exact ih _ (improve_feasible d k initial B h)

theorem select_le_initial {n : ℕ} (d : Point n → Point n → ℝ) (k : ℕ)
    (candidates : List (Partition n)) (initial : Partition n) :
    cost d (select d k initial candidates) ≤ cost d initial := by
  induction candidates generalizing initial with
  | nil => exact le_rfl
  | cons B bs ih => exact (ih _).trans (improve_le_left d k initial B)

theorem select_le_member {n : ℕ} (d : Point n → Point n → ℝ) (k : ℕ)
    (candidates : List (Partition n)) (initial B : Partition n)
    (hB : B ∈ candidates) (hf : Feasible Finset.univ k B) :
    cost d (select d k initial candidates) ≤ cost d B := by
  induction candidates generalizing initial with
  | nil => simp at hB
  | cons A as ih =>
    rcases List.mem_cons.mp hB with rfl | hB
    · exact (select_le_initial d k as _).trans (improve_le_right d k initial B hf)
    · exact ih _ hB

theorem select_unique_optimum {n : ℕ} (d : Point n → Point n → ℝ) (k : ℕ)
    (candidates : List (Partition n)) (initial O : Partition n)
    (hi : Feasible Finset.univ k initial) (hO : UniqueOptimal d Finset.univ k O)
    (hmem : O ∈ candidates) : select d k initial candidates = O := by
  apply hO.2
  refine ⟨select_feasible d k candidates initial hi, ?_⟩
  intro Q hQ
  exact (select_le_member d k candidates initial O hmem hO.1.1).trans (hO.1.2 Q hQ)

theorem stable_unique {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (γ : ℝ) (hγ : 1 ≤ γ) (O : Partition n) (hO : Stable d k γ O) :
    UniqueOptimal d Finset.univ k O := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  apply hO.2 d
  constructor
  · intro x y
    rw [← hm x y, ← hm y x]
    exact dist_comm x y
  · intro x y
    refine ⟨le_rfl, ?_⟩
    have hn : 0 ≤ d x y := by rw [← hm x y]; exact dist_nonneg
    nlinarith

/- The true largest radius is one of the input distances enumerated by Algorithm 1. -/
theorem largest_radius_is_input_distance {n k : ℕ} (d : Point n → Point n → ℝ)
    (O : Partition n) (hO : Feasible Finset.univ k O) (hk : 1 ≤ k) :
    ∃ c x : Point n, d c x = largestRadius d O := by
  have hn : O.Nonempty := Finset.card_pos.mp (by rw [hO.1]; omega)
  obtain ⟨C, hC, he⟩ := Finset.exists_mem_eq_sup' hn (radius d)
  obtain ⟨c, hc⟩ := exists_center d (hO.2.1 C hC)
  obtain ⟨x, hx, hcx⟩ := radius_attained d hc
  refine ⟨c, x, hcx.trans ?_⟩
  simpa [largestRadius, hn] using he.symm

/- The finite outputs of Branch A, including every guessed input-distance scale. -/


theorem optimum_in_fewOutputs {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n)
    (O : Partition n) (hO : Stable d k γ O) (budget : ℕ)
    (hbudget : (largeClusters d O (γ - 1)).card ≤ budget) :
    O ∈ fewOutputs d γ budget := by
  obtain ⟨c, x, hr⟩ := largest_radius_is_input_distance d O hO.1 hk.1
  obtain ⟨Q, hQ, he⟩ := few_branch_complete d hd k hk γ hγ hkn O hO budget hbudget
  apply Finset.mem_biUnion.mpr
  refine ⟨(c, x), Finset.mem_univ _, ?_⟩
  simpa only [hr] using Finset.mem_image.mpr ⟨Q, hQ, he⟩

/- Branch A recovers the unique optimum whenever its bound holds. This is a finite
algorithm specification, not yet an assertion about the canonical machine interpreter. -/
theorem few_branch_recovers {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n)
    (O : Partition n) (hO : Stable d k γ O) (budget : ℕ)
    (hbudget : (largeClusters d O (γ - 1)).card ≤ budget)
    (initial : Partition n) (hi : Feasible Finset.univ k initial) :
    select d k initial (fewOutputs d γ budget).toList = O := by
  apply select_unique_optimum d k _ initial O hi (stable_unique d hd k γ hγ.1.le O hO)
  exact Finset.mem_toList.mpr (optimum_in_fewOutputs d hd k hk γ hγ hkn O hO budget hbudget)

end StableMSR.Recovery.CandidateAux


set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Enumeration

/- Explicit bounded enumeration: extend every length-B option tuple by every
alphabet symbol or a blank. No powerset of the alphabet is constructed. -/
def seeds {α : Type*} (alphabet : List α) : ℕ → List (List (Option α))
  | 0 => [[]]
  | B+1 => (none :: alphabet.map some).flatMap
      (fun x => (seeds alphabet B).map (fun xs => x :: xs))

lemma mem_seeds_cons {α : Type*} (alphabet : List α) (B : ℕ)
    (x : Option α) (xs : List (Option α)) :
    x::xs ∈ seeds alphabet (B+1) ↔
      x ∈ none :: alphabet.map some ∧ xs ∈ seeds alphabet B := by
  simp only [seeds, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, ys, hys, he⟩
    cases he
    exact ⟨ha, hys⟩
  · rintro ⟨hx, hxs⟩
    exact ⟨x, hx, xs, hxs, rfl⟩

lemma mem_seeds {α : Type*} (alphabet : List α) (B : ℕ) (xs : List (Option α)) :
    xs ∈ seeds alphabet B ↔ xs.length = B ∧
      ∀ x ∈ xs, x ∈ none :: alphabet.map some := by
  induction B generalizing xs with
  | zero => cases xs <;> simp [seeds]
  | succ B ih =>
      cases xs with
      | nil => simp [seeds]
      | cons x xs =>
          rw [mem_seeds_cons, ih]
          simp only [List.length_cons, List.forall_mem_cons, Nat.add_right_cancel_iff]
          tauto

lemma seeds_length {α : Type*} (alphabet : List α) (B : ℕ) :
    (seeds alphabet B).length = (alphabet.length+1)^B := by
  induction B with
  | zero => simp [seeds]
  | succ B ih =>
      simp [seeds, List.length_flatMap, ih, List.map_map, pow_succ,
        Nat.mul_comm, Nat.add_comm, Function.comp_def, Nat.add_mul]

/- Decode a bounded option tuple, ignoring blanks and repeated representations. -/
def decode {α : Type*} [DecidableEq α] (xs : List (Option α)) : Finset α :=
  (xs.filterMap id).toFinset

@[simp] lemma mem_decode {α : Type*} [DecidableEq α] (a : α) (xs : List (Option α)) :
    a ∈ decode xs ↔ some a ∈ xs := by simp [decode]

lemma decode_card_le {α : Type*} [DecidableEq α] (xs : List (Option α)) :
    (decode xs).card ≤ xs.length := by
  exact (List.toFinset_card_le (l := xs.filterMap id)).trans (List.length_filterMap_le id xs)

/- All subsets with at most B elements, generated by bounded tuples. -/
noncomputable def boundedSubsets {α : Type*} [DecidableEq α] (S : Finset α) (B : ℕ) :
    Finset (Finset α) := ((seeds S.toList B).map decode).toFinset

lemma mem_boundedSubsets {α : Type*} [DecidableEq α] (S Q : Finset α) (B : ℕ) :
    Q ∈ boundedSubsets S B ↔ Q ⊆ S ∧ Q.card ≤ B := by
  constructor
  · intro hQ
    obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hQ)
    obtain ⟨hlen, hall⟩ := (mem_seeds S.toList B xs).mp hxs
    constructor
    · intro a ha
      have hh := hall (some a) ((mem_decode a xs).mp ha)
      simpa using hh
    · exact (decode_card_le xs).trans_eq hlen
  · rintro ⟨hQS, hQB⟩
    let xs : List (Option α) := Q.toList.map some ++ List.replicate (B-Q.card) none
    have hlen : xs.length = B := by simp only [xs, List.length_append, List.length_map,
      Finset.length_toList, List.length_replicate]; omega
    have hall : ∀ x ∈ xs, x ∈ none :: S.toList.map some := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
        simp only [List.mem_cons, Option.some_ne_none, List.mem_map, Option.some.injEq,
          exists_eq_right, false_or, Finset.mem_toList]
        exact hQS (Finset.mem_toList.mp ha)
      · have hxnone : x = none := (List.mem_replicate.mp h).2
        simp [hxnone]
    have hdecode : decode xs = Q := by
      ext a
      simp [xs]
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨xs, (mem_seeds S.toList B xs).mpr ⟨hlen, hall⟩, hdecode⟩

lemma boundedSubsets_card {α : Type*} [DecidableEq α] (S : Finset α) (B : ℕ) :
    (boundedSubsets S B).card ≤ (S.card+1)^B := by
  have h := List.toFinset_card_le (l := (seeds S.toList B).map decode)
  simpa [boundedSubsets, seeds_length] using h

/- The number of tuple-entry visits plus all ordered pair/point inspections.
This is a semantic scan count, not a claim about compiled RAM execution. -/
def inspectionWork {α : Type*} (points : ℕ) (xs : List (Option α)) : ℕ :=
  xs.length + points * xs.length^2

lemma inspection_work_sum {α : Type*} (alphabet : List α) (B points : ℕ) :
    ((seeds alphabet B).map (inspectionWork points)).sum =
      (B + points*B^2) * (alphabet.length+1)^B := by
  have hmap : (seeds alphabet B).map (inspectionWork points) =
      (seeds alphabet B).map (fun _ => B+points*B^2) := by
    apply List.map_congr_left
    intro xs hxs
    simp only [inspectionWork, ((mem_seeds alphabet B xs).mp hxs).1]
  rw [hmap]
  simp [seeds_length, Nat.mul_comm]

lemma seed_count_polynomial (n B : ℕ) (hn : 2 ≤ n) :
    (n^2+1)^B ≤ n^(3*B) := by
  have hbase : n^2+1 ≤ n^3 := by
    have hsq : 1 ≤ n^2 := by nlinarith
    nlinarith [Nat.mul_le_mul_right (n^2) hn]
  simpa only [pow_mul] using Nat.pow_le_pow_left hbase B

lemma inspection_work_polynomial (n B : ℕ) (hn : 2 ≤ n) :
    (B+n*B^2)*(n^2+1)^B ≤ n^(5*B+1) := by
  have hB : B+B^2 ≤ 2^(2*B) := by
    have h := Nat.two_mul_sq_add_one_le_two_pow_two_mul B
    nlinarith [sq_nonneg ((B:ℤ)-1)]
  have hf : B+n*B^2 ≤ n * n^(2*B) := by
    have h₁ : B+n*B^2 ≤ n*(B+B^2) := by nlinarith
    exact h₁.trans (Nat.mul_le_mul_left n (hB.trans (Nat.pow_le_pow_left hn _)))
  calc
    (B+n*B^2)*(n^2+1)^B ≤ (n*n^(2*B))*n^(3*B) :=
      Nat.mul_le_mul hf (seed_count_polynomial n B hn)
    _ = n^(5*B+1) := by
      rw [← pow_succ', ← pow_add]
      congr 1
      omega

end StableMSR.Recovery.Enumeration


set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.CandidateAux

/- Enumerate bounded option tuples, decode their sets, and retain disjoint families.
The full powerset of the candidate representation set is never needed. -/
noncomputable def efficientFamilies {n : ℕ} (d : Point n → Point n → ℝ)
    (γ R : ℝ) (budget : ℕ) : Finset (Finset (Point n × Point n)) :=
  (Enumeration.boundedSubsets (representations d γ R) budget).filter (fun Q =>
    (Q : Set (Point n × Point n)).Pairwise (fun p q => Disjoint (represented d p) (represented d q)))

/- The bounded tuple enumeration is extensionally identical to the original specification. -/
theorem efficientFamilies_eq {n : ℕ} (d : Point n → Point n → ℝ)
    (γ R : ℝ) (budget : ℕ) : efficientFamilies d γ R budget = families d γ R budget := by
  ext Q
  simp only [efficientFamilies, families, Finset.mem_filter, Enumeration.mem_boundedSubsets,
    Finset.mem_powerset, and_assoc]

/- At most (n²+1)^B tuples suffice to enumerate all disjoint B-bounded families. -/
theorem families_card {n : ℕ} (d : Point n → Point n → ℝ) (γ R : ℝ) (budget : ℕ) :
    (families d γ R budget).card ≤ (n^2+1)^budget := by
  rw [← efficientFamilies_eq]
  exact (Finset.card_filter_le _ _).trans
    ((Enumeration.boundedSubsets_card _ _).trans
      (Nat.pow_le_pow_left (Nat.add_le_add_right (representation_card d γ R) 1) budget))

/- Every input-distance guess together contributes at most n²(n²+1)^B outputs. -/
theorem fewOutputs_card {n : ℕ} (d : Point n → Point n → ℝ) (γ : ℝ) (budget : ℕ) :
    (fewOutputs d γ budget).card ≤ n^2*(n^2+1)^budget := by
  unfold fewOutputs
  calc
    _ ≤ ∑ p : Point n × Point n,
        ((families d γ (d p.1 p.2) budget).image (completeFamily d γ (d p.1 p.2))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p : Point n × Point n, (n^2+1)^budget := by
      exact Finset.sum_le_sum (fun p _ => Finset.card_image_le.trans (families_card d γ _ budget))
    _ = n^2*(n^2+1)^budget := by simp [Point, pow_two]

/- For n≥2 the finite-family count is bounded by a power with a uniform linear exponent. -/
theorem fewOutputs_card_polynomial {n : ℕ} (d : Point n → Point n → ℝ)
    (γ : ℝ) (budget : ℕ) (hn : 2 ≤ n) :
    (fewOutputs d γ budget).card ≤ n^(3*budget+2) := by
  calc
    _ ≤ n^2*(n^2+1)^budget := fewOutputs_card d γ budget
    _ ≤ n^2*n^(3*budget) := Nat.mul_le_mul_left _ (Enumeration.seed_count_polynomial n budget hn)
    _ = _ := by rw [← pow_add]; congr 1; omega

/- Explicit aggregate scan count for all radius guesses, including tuple-entry
visits and an ordered representation-pair/point inspection for disjointness.
This counts semantic inspections; it does not claim a compiled RAM runtime. -/
theorem all_scale_inspection_bound (n budget : ℕ) (hn : 2 ≤ n) :
    n^2 * ((budget+n*budget^2)*(n^2+1)^budget) ≤ n^(5*budget+3) := by
  calc
    _ ≤ n^2*n^(5*budget+1) :=
      Nat.mul_le_mul_left _ (Enumeration.inspection_work_polynomial n budget hn)
    _ = _ := by rw [← pow_add]; congr 1; omega

/- A small finite family of feasible partitions is selected before the unknown
optimum. It contains every stable optimum with at most B large clusters. -/
theorem bounded_few_candidate_family {n : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n)
    (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n) (budget : ℕ) :
    ∃ F : Finset (Partition n), F.card ≤ n^2*(n^2+1)^budget ∧
      (∀ Q ∈ F, Feasible Finset.univ k Q) ∧
      ∀ O : Partition n, Stable d k γ O →
        (largeClusters d O (γ-1)).card ≤ budget → O ∈ F := by
  let F := (fewOutputs d γ budget).filter (Feasible Finset.univ k)
  refine ⟨F, (Finset.card_filter_le _ _).trans (fewOutputs_card d γ budget), ?_, ?_⟩
  · intro Q hQ
    exact (Finset.mem_filter.mp hQ).2
  · intro O hO hb
    exact Finset.mem_filter.mpr
      ⟨optimum_in_fewOutputs d hd k hk γ hγ hkn O hO budget hb, hO.1⟩

end StableMSR.Recovery.CandidateAux

open StableMSR.Recovery

theorem solution {n : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n)
    (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n) (budget : ℕ)
    (initial : Partition n) (hi : Feasible Finset.univ k initial) :
    (CandidateAux.fewOutputs d γ budget).card ≤ n ^ 2 * (n ^ 2 + 1) ^ budget ∧
      Feasible Finset.univ k
        (CandidateAux.select d k initial (CandidateAux.fewOutputs d γ budget).toList) ∧
      ∀ O : Partition n, Stable d k γ O →
        (largeClusters d O (γ - 1)).card ≤ budget →
        CandidateAux.select d k initial (CandidateAux.fewOutputs d γ budget).toList = O := by
  refine ⟨CandidateAux.fewOutputs_card d γ budget,
    CandidateAux.select_feasible d k _ initial hi, ?_⟩
  intro O hO hbudget
  exact CandidateAux.few_branch_recovers d hd k hk γ hγ hkn O hO budget hbudget initial hi
