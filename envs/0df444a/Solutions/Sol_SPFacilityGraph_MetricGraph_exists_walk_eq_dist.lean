-- Prove2me | solution 1 for SPFacilityGraph.MetricGraph.exists_walk_eq_dist
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:13:31.001249+00:00
-- url     : https://prove2.me/submissions/967c178c-cbe3-4adc-b965-71ae17505a08

import Mathlib
import Definitions.Def_SPFacilityGraph_MetricGraph_dist

set_option autoImplicit false

namespace SPFacilityGraph
namespace MetricGraph

variable {k : ℕ} (G : MetricGraph k)

/-- walk-length set with functions `ℕ → E`. -/
def fnSet (x y : EuclideanSpace ℝ (Fin k)) : Set ℝ :=
  {L | ∃ (m : ℕ) (p : ℕ → EuclideanSpace ℝ (Fin k)), p 0 = x ∧ p m = y ∧
    (∀ j < m, ∃ e ∈ G.edges, p j ∈ segment ℝ e.1 e.2 ∧ p (j+1) ∈ segment ℝ e.1 e.2) ∧
    L = ∑ j ∈ Finset.range m, ‖p (j+1) - p j‖}

lemma zip_tail_sum_aux {α : Type*} (f : α × α → ℝ) (a : α) (L : List α) :
    (((a :: L).zip (a :: L).tail).map f).sum =
      (match L with | [] => 0 | b :: _ => f (a, b)) + ((L.zip L.tail).map f).sum := by
  cases L with
  | nil => simp
  | cons b L => simp

lemma range_map_sum (m : ℕ) (p : ℕ → EuclideanSpace ℝ (Fin k)) :
    ((((List.range (m+1)).map p).zip ((List.range (m+1)).map p).tail).map
        (fun q => ‖q.2 - q.1‖)).sum = ∑ j ∈ Finset.range m, ‖p (j+1) - p j‖ := by
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
    have h1 : (List.range (m+1+1)).map p = p 0 :: (List.range (m+1)).map (fun j => p (j+1)) := by
      rw [List.range_succ_eq_map]; simp [Function.comp_def]
    rw [h1, zip_tail_sum_aux, ih (fun j => p (j+1)), Finset.sum_range_succ']
    have h2 : (List.range (m+1)).map (fun j => p (j+1)) =
        p 1 :: (List.range m).map (fun j => p (j+1+1)) := by
      rw [List.range_succ_eq_map]; simp [Function.comp_def]
    rw [h2]; simp only; ring

lemma dist_eq_sInf_fnSet (x y : G.Pt) : G.dist x y = sInf (G.fnSet x y) := by
  unfold MetricGraph.dist
  congr 1
  ext L
  constructor
  · rintro ⟨l, hh, hl, hc, rfl⟩
    have hne : l ≠ [] := by rintro rfl; simp at hh
    set m := l.length - 1 with hm
    have hlen : l.length = m + 1 := by
      have := List.length_pos_iff.2 hne; omega
    set p : ℕ → EuclideanSpace ℝ (Fin k) := fun j => l.getD j (x : EuclideanSpace ℝ (Fin k)) with hp
    have hlp : l = (List.range (m+1)).map p := by
      apply List.ext_getElem
      · simp [hlen]
      · intro n h1 h2
        simp [hp, List.getElem?_eq_getElem h1]
    refine ⟨m, p, ?_, ?_, ?_, ?_⟩
    · rw [hlp, List.range_succ_eq_map] at hh; simpa using hh
    · rw [hlp] at hl
      rw [List.getLast?_eq_some_getLast (by simp)] at hl
      simpa [List.getLast_map, List.getLast_range] using hl
    · rw [hlp, List.isChain_map, List.isChain_range_succ] at hc
      intro j hj; exact hc j hj
    · rw [hlp]; exact range_map_sum m p
  · rintro ⟨m, p, h0, hm, hc, rfl⟩
    refine ⟨(List.range (m+1)).map p, ?_, ?_, ?_, ?_⟩
    · rw [List.range_succ_eq_map]; simp [h0]
    · rw [List.getLast?_eq_some_getLast (by simp)]
      simp [List.getLast_map, List.getLast_range, hm]
    · rw [List.isChain_map, List.isChain_range_succ]
      intro j hj; exact hc j hj
    · exact (range_map_sum m p).symm

/-- walk predicate -/
def IsW (m : ℕ) (p : ℕ → EuclideanSpace ℝ (Fin k)) : Prop :=
  ∀ j < m, ∃ e ∈ G.edges, p j ∈ segment ℝ e.1 e.2 ∧ p (j+1) ∈ segment ℝ e.1 e.2

/-- concatenation of walks -/
def wcat (m : ℕ) (p q : ℕ → EuclideanSpace ℝ (Fin k)) : ℕ → EuclideanSpace ℝ (Fin k) :=
  fun j => if j ≤ m then p j else q (j - m)

lemma wcat_isW {m n : ℕ} {p q : ℕ → EuclideanSpace ℝ (Fin k)} (hpq : p m = q 0)
    (hp : G.IsW m p) (hq : G.IsW n q) : G.IsW (m + n) (wcat m p q) := by
  intro j hj
  by_cases h : j + 1 ≤ m
  · have := hp j (by omega)
    simpa [wcat, h, show j ≤ m by omega] using this
  · by_cases h' : j = m
    · have := hq 0 (by omega)
      simpa [wcat, h', hpq, show j + 1 - j = 1 by omega] using this
    · have := hq (j - m) (by omega)
      simpa [wcat, show ¬ j ≤ m by omega, h, show j + 1 - m = j - m + 1 by omega] using this

lemma wcat_sum (m n : ℕ) (p q : ℕ → EuclideanSpace ℝ (Fin k)) (hpq : p m = q 0) :
    ∑ j ∈ Finset.range (m + n), ‖wcat m p q (j+1) - wcat m p q j‖ =
      ∑ j ∈ Finset.range m, ‖p (j+1) - p j‖ + ∑ j ∈ Finset.range n, ‖q (j+1) - q j‖ := by
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    simp [wcat, show j ≤ m by omega, show j + 1 ≤ m by omega]
  · apply Finset.sum_congr rfl
    intro j _
    by_cases h : j = 0
    · subst h; simp [wcat, hpq]
    · simp [wcat, show ¬ m + j ≤ m by omega, show ¬ m + j + 1 ≤ m by omega,
        show m + j + 1 - m = j + 1 by omega]

lemma wcat_zero (m : ℕ) (p q : ℕ → EuclideanSpace ℝ (Fin k)) : wcat m p q 0 = p 0 := by
  simp [wcat]

lemma wcat_end (m n : ℕ) (p q : ℕ → EuclideanSpace ℝ (Fin k)) (hpq : p m = q 0) :
    wcat m p q (m + n) = q n := by
  by_cases h : n = 0
  · subst h; simp [wcat, hpq]
  · simp [wcat, show ¬ m + n ≤ m by omega]

lemma mem_carrier_of_adj {a b : EuclideanSpace ℝ (Fin k)}
    (h : ∃ e ∈ G.edges, a ∈ segment ℝ e.1 e.2 ∧ b ∈ segment ℝ e.1 e.2) :
    a ∈ G.carrier ∧ b ∈ G.carrier := by
  obtain ⟨e, he, ha, hb⟩ := h
  exact ⟨Set.mem_biUnion he ha, Set.mem_biUnion he hb⟩

lemma isCompact_seg (a b : EuclideanSpace ℝ (Fin k)) : IsCompact (segment ℝ a b) := by
  rw [← convexHull_pair]; exact (Set.toFinite ({a, b} : Set (EuclideanSpace ℝ (Fin k)))).isCompact_convexHull ℝ

lemma isCompact_carrier : IsCompact G.carrier :=
  G.edges.finite_toSet.isCompact_biUnion (fun e _ => isCompact_seg e.1 e.2)

/-- every two points of the carrier are joined by a walk -/
lemma fnSet_nonempty (x y : G.Pt) : (G.fnSet x y).Nonempty := by
  classical
  let R : Set (EuclideanSpace ℝ (Fin k)) := {q | ∃ m p, p 0 = (x : EuclideanSpace ℝ (Fin k)) ∧ p m = q ∧ G.IsW m p}
  have hext : ∀ r ∈ R, ∀ q, (∃ e ∈ G.edges, r ∈ segment ℝ e.1 e.2 ∧ q ∈ segment ℝ e.1 e.2) → q ∈ R := by
    rintro r ⟨m, p, h0, hm, hw⟩ q hrq
    refine ⟨m + 1, wcat m p (fun j => if j = 0 then r else q), ?_, ?_, ?_⟩
    · rw [wcat_zero]; exact h0
    · rw [wcat_end _ _ _ _ (by simp [hm])]; simp
    · apply G.wcat_isW (by simp [hm]) hw
      intro j hj
      have : j = 0 := by omega
      subst this; simpa using hrq
  have hxR : (x : EuclideanSpace ℝ (Fin k)) ∈ R := ⟨0, fun _ => x, rfl, rfl, fun j hj => absurd hj (by omega)⟩
  have hyR : (y : EuclideanSpace ℝ (Fin k)) ∈ R := by
    by_contra hy
    let A := ⋃ e ∈ G.edges.filter (fun e => (segment ℝ e.1 e.2 ∩ R).Nonempty), segment ℝ e.1 e.2
    let B := ⋃ e ∈ G.edges.filter (fun e => ¬ (segment ℝ e.1 e.2 ∩ R).Nonempty), segment ℝ e.1 e.2
    have hA : IsClosed A := Set.Finite.isClosed_biUnion (Finset.finite_toSet _)
      (fun e _ => (isCompact_seg e.1 e.2).isClosed)
    have hB : IsClosed B := Set.Finite.isClosed_biUnion (Finset.finite_toSet _)
      (fun e _ => (isCompact_seg e.1 e.2).isClosed)
    have hsub : G.carrier ⊆ A ∪ B := by
      intro q hq
      obtain ⟨e, he, hqe⟩ := Set.mem_iUnion₂.1 hq
      by_cases h : (segment ℝ e.1 e.2 ∩ R).Nonempty
      · left; exact Set.mem_biUnion (Finset.mem_filter.2 ⟨he, h⟩) hqe
      · right; exact Set.mem_biUnion (Finset.mem_filter.2 ⟨he, h⟩) hqe
    have hcA : (G.carrier ∩ A).Nonempty := by
      obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.1 x.2
      exact ⟨x, x.2, Set.mem_biUnion (Finset.mem_filter.2 ⟨he, ⟨x, hxe, hxR⟩⟩) hxe⟩
    have hcB : (G.carrier ∩ B).Nonempty := by
      obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.1 y.2
      refine ⟨y, y.2, Set.mem_biUnion (Finset.mem_filter.2 ⟨he, ?_⟩) hye⟩
      rintro ⟨r, hr, hrR⟩
      exact hy (hext r hrR y ⟨e, he, hr, hye⟩)
    obtain ⟨q, -, hqA, hqB⟩ :=
      (isPreconnected_closed_iff.1 G.connected.isPreconnected) A B hA hB hsub hcA hcB
    obtain ⟨e, he, hqe⟩ := Set.mem_iUnion₂.1 hqA
    obtain ⟨e', he', hqe'⟩ := Set.mem_iUnion₂.1 hqB
    obtain ⟨-, r, hr, hrR⟩ := Finset.mem_filter.1 he
    exact (Finset.mem_filter.1 he').2 ⟨q, hqe', hext r hrR q ⟨e, (Finset.mem_filter.1 he).1, hr, hqe⟩⟩
  obtain ⟨m, p, h0, hm, hw⟩ := hyR
  exact ⟨_, m, p, h0, hm, hw, rfl⟩

lemma fnSet_bdd (x y : EuclideanSpace ℝ (Fin k)) : BddBelow (G.fnSet x y) :=
  ⟨0, by rintro L ⟨m, p, -, -, -, rfl⟩; exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)⟩

lemma norm_sub_le_sum (a n : ℕ) (p : ℕ → EuclideanSpace ℝ (Fin k)) :
    ‖p (a + n) - p a‖ ≤ ∑ i ∈ Finset.range n, ‖p (a + i + 1) - p (a + i)‖ := by
  have h := Finset.sum_range_sub (fun i => p (a + i)) n
  simp only [add_zero] at h
  rw [← h]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl; intro i _; rw [add_assoc]

/-- one shortcut step -/
lemma shortcut_step (m : ℕ) (p : ℕ → EuclideanSpace ℝ (Fin k)) (hw : G.IsW m p)
    (hm : G.edges.card < m) :
    ∃ (m' : ℕ) (p' : ℕ → EuclideanSpace ℝ (Fin k)), m' < m ∧ p' 0 = p 0 ∧ p' m' = p m ∧
      G.IsW m' p' ∧ ∑ i ∈ Finset.range m', ‖p' (i+1) - p' i‖ ≤
        ∑ i ∈ Finset.range m, ‖p (i+1) - p i‖ := by
  classical
  choose c hc using hw
  let c' : ℕ → EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) :=
    fun j => if h : j < m then c j h else 0
  have hmaps : ∀ j ∈ Finset.range m, c' j ∈ G.edges := by
    intro j hj; rw [Finset.mem_range] at hj; simp only [c', dif_pos hj]; exact (hc j hj).1
  obtain ⟨j, hj, j', hj', hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simpa using hm) hmaps
  rw [Finset.mem_range] at hj hj'
  -- wlog j < j'
  obtain ⟨a, b, hab, hb, e, he, hae, hbe⟩ : ∃ a b, a + 2 ≤ b ∧ b ≤ m ∧
      ∃ e ∈ G.edges, p a ∈ segment ℝ e.1 e.2 ∧ p b ∈ segment ℝ e.1 e.2 := by
    rcases lt_or_gt_of_ne hne with h | h
    · refine ⟨j, j' + 1, by omega, by omega, c' j, hmaps j (Finset.mem_range.2 hj), ?_, ?_⟩
      · simp only [c', dif_pos hj]; exact (hc j hj).2.1
      · rw [heq]; simp only [c', dif_pos hj']; exact (hc j' hj').2.2
    · refine ⟨j', j + 1, by omega, by omega, c' j', hmaps j' (Finset.mem_range.2 hj'), ?_, ?_⟩
      · simp only [c', dif_pos hj']; exact (hc j' hj').2.1
      · rw [← heq]; simp only [c', dif_pos hj]; exact (hc j hj).2.2
  set d := b - a - 1 with hd
  refine ⟨m - d, fun i => if i ≤ a then p i else p (i + d), by omega, by simp, ?_, ?_, ?_⟩
  · simp only [show ¬ m - d ≤ a by omega, if_false]; congr 1; omega
  · intro i hi
    by_cases h1 : i + 1 ≤ a
    · simp only [show i ≤ a by omega, h1, if_true]; exact ⟨_, hc i (by omega)⟩
    · by_cases h2 : i = a
      · subst h2
        simp only [le_refl, if_true, show ¬ i + 1 ≤ i by omega, if_false]
        rw [show i + 1 + d = b by omega]; exact ⟨e, he, hae, hbe⟩
      · simp only [show ¬ i ≤ a by omega, h1, if_false]
        rw [show i + 1 + d = i + d + 1 by omega]; exact ⟨_, hc (i + d) (by omega)⟩
  · set f : ℕ → ℝ := fun i => ‖p (i+1) - p i‖ with hf
    set p' : ℕ → EuclideanSpace ℝ (Fin k) := fun i => if i ≤ a then p i else p (i + d) with hp'
    have hL : ∑ i ∈ Finset.range (m - d), ‖p' (i+1) - p' i‖ =
        ∑ i ∈ Finset.range a, f i + ‖p b - p a‖ + ∑ i ∈ Finset.range (m - b), f (b + i) := by
      rw [show m - d = a + 1 + (m - b) by omega, Finset.sum_range_add, Finset.sum_range_succ]
      congr 1; congr 1
      · apply Finset.sum_congr rfl; intro i hi
        rw [Finset.mem_range] at hi
        simp [hp', hf, show i ≤ a by omega, show i + 1 ≤ a by omega]
      · simp only [hp', le_refl, if_true, show ¬ a + 1 ≤ a by omega, if_false]
        rw [show a + 1 + d = b by omega]
      · apply Finset.sum_congr rfl; intro i _
        simp only [hp', hf, show ¬ a + 1 + i ≤ a by omega, show ¬ a + 1 + i + 1 ≤ a by omega,
          if_false]
        congr 2 <;> congr 1 <;> omega
    have hR : ∑ i ∈ Finset.range m, ‖p (i+1) - p i‖ =
        ∑ i ∈ Finset.range a, f i + ∑ i ∈ Finset.range (b - a), f (a + i) +
          ∑ i ∈ Finset.range (m - b), f (b + i) := by
      conv_lhs => rw [show m = a + (b - a) + (m - b) by omega, Finset.sum_range_add,
        Finset.sum_range_add]
      congr 1
      apply Finset.sum_congr rfl; intro i _; simp only [hf]; congr 3 <;> omega
    rw [hL, hR]
    have := norm_sub_le_sum a (b - a) p
    rw [show a + (b - a) = b by omega] at this
    have h3 : ∑ i ∈ Finset.range (b - a), ‖p (a + i + 1) - p (a + i)‖ =
        ∑ i ∈ Finset.range (b - a), f (a + i) := rfl
    linarith

lemma shortcut (m : ℕ) (p : ℕ → EuclideanSpace ℝ (Fin k)) (hw : G.IsW m p) :
    ∃ (m' : ℕ) (p' : ℕ → EuclideanSpace ℝ (Fin k)), m' ≤ G.edges.card ∧ p' 0 = p 0 ∧
      p' m' = p m ∧ G.IsW m' p' ∧ ∑ i ∈ Finset.range m', ‖p' (i+1) - p' i‖ ≤
        ∑ i ∈ Finset.range m, ‖p (i+1) - p i‖ := by
  induction m using Nat.strong_induction_on generalizing p with
  | _ m ih =>
    by_cases hm : m ≤ G.edges.card
    · exact ⟨m, p, hm, rfl, rfl, hw, le_rfl⟩
    · obtain ⟨m1, p1, hlt, h0, hend, hw1, hle⟩ := G.shortcut_step m p hw (by omega)
      obtain ⟨m2, p2, hm2, h0', hend', hw2, hle'⟩ := ih m1 hlt p1 hw1
      exact ⟨m2, p2, hm2, h0'.trans h0, hend'.trans hend, hw2, hle'.trans hle⟩

lemma isClosed_isW (m : ℕ) : IsClosed {p : ℕ → EuclideanSpace ℝ (Fin k) | G.IsW m p} := by
  have : {p : ℕ → EuclideanSpace ℝ (Fin k) | G.IsW m p} = ⋂ j ∈ Finset.range m, ⋃ e ∈ G.edges,
      ((fun p : ℕ → EuclideanSpace ℝ (Fin k) => p j) ⁻¹' segment ℝ e.1 e.2 ∩
        (fun p : ℕ → EuclideanSpace ℝ (Fin k) => p (j+1)) ⁻¹' segment ℝ e.1 e.2) := by
    ext p; simp only [IsW, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage, Finset.mem_range, exists_prop]
  rw [this]
  refine isClosed_biInter (fun j _ => Set.Finite.isClosed_biUnion (Finset.finite_toSet _)
    (fun e _ => IsClosed.inter ?_ ?_))
  · exact (isCompact_seg e.1 e.2).isClosed.preimage (continuous_apply j)
  · exact (isCompact_seg e.1 e.2).isClosed.preimage (continuous_apply (j+1))

lemma exists_min_walk (x y : G.Pt) : ∃ (m : ℕ) (p : ℕ → EuclideanSpace ℝ (Fin k)),
    p 0 = x ∧ p m = y ∧ G.IsW m p ∧
      ∑ i ∈ Finset.range m, ‖p (i+1) - p i‖ = sInf (G.fnSet x y) := by
  classical
  set X : EuclideanSpace ℝ (Fin k) := (x : EuclideanSpace ℝ (Fin k)) with hX
  set Y : EuclideanSpace ℝ (Fin k) := (y : EuclideanSpace ℝ (Fin k)) with hY
  let S : ℕ → Set (ℕ → EuclideanSpace ℝ (Fin k)) := fun m =>
    {p | p 0 = X} ∩ {p | p m = Y} ∩ {p | G.IsW m p} ∩ Set.pi Set.univ (fun _ => G.carrier)
  let Lf : ℕ → (ℕ → EuclideanSpace ℝ (Fin k)) → ℝ := fun m p => ∑ i ∈ Finset.range m, ‖p (i+1) - p i‖
  let A : Set ℝ := ⋃ m ∈ Finset.range (G.edges.card + 1), Lf m '' S m
  have hScpt : ∀ m, IsCompact (S m) := by
    intro m
    refine IsCompact.inter_left (isCompact_univ_pi (fun _ => G.isCompact_carrier)) ?_
    refine IsClosed.inter (IsClosed.inter ?_ ?_) (G.isClosed_isW m)
    · exact isClosed_eq (continuous_apply 0) continuous_const
    · exact isClosed_eq (continuous_apply m) continuous_const
  have hLc : ∀ m, Continuous (Lf m) := fun m =>
    continuous_finsetSum _ (fun i _ => ((continuous_apply (i+1)).sub (continuous_apply i)).norm)
  have hAc : IsCompact A := (Finset.range _).isCompact_biUnion
    (fun m _ => (hScpt m).image (hLc m))
  have hAsub : A ⊆ G.fnSet x y := by
    intro L hL
    obtain ⟨m, -, p, ⟨⟨⟨h0, hm⟩, hw⟩, -⟩, rfl⟩ := by simpa [A] using hL
    exact ⟨m, p, h0, hm, hw, rfl⟩
  -- every walk is dominated by an element of `A`
  have hdom : ∀ L ∈ G.fnSet x y, ∃ L' ∈ A, L' ≤ L := by
    rintro L ⟨m, p, h0, hm, hw, rfl⟩
    obtain ⟨m', p', hm', h0', hend', hw', hle⟩ := G.shortcut m p hw
    let q : ℕ → EuclideanSpace ℝ (Fin k) := fun i => if i ≤ m' then p' i else Y
    have hqeq : Lf m' q = Lf m' p' := by
      apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
      simp [q, show i ≤ m' by omega, show i + 1 ≤ m' by omega]
    refine ⟨Lf m' q, Set.mem_biUnion (Finset.mem_range.2 (by omega)) ⟨q, ?_, rfl⟩, ?_⟩
    · refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · show q 0 = X; simp [q, h0', h0, hX]
      · show q m' = Y; simp [q, hend', hm, hY]
      · intro i hi
        simpa [q, show i ≤ m' by omega, show i + 1 ≤ m' by omega] using hw' i hi
      · intro i _
        by_cases hi : i ≤ m'
        · simp only [q, hi, if_true]
          rcases Nat.eq_zero_or_pos m' with h | h
          · have : i = 0 := by omega
            subst this; rw [h0', h0]; exact x.2
          · rcases Nat.lt_or_ge i m' with h2 | h2
            · exact (G.mem_carrier_of_adj (hw' i h2)).1
            · have := (G.mem_carrier_of_adj (hw' (i - 1) (by omega))).2
              rwa [show i - 1 + 1 = i by omega] at this
        · simp only [q, hi, if_false]; exact y.2
    · rw [hqeq]; exact hle
  have hAne : A.Nonempty := by
    obtain ⟨L, hL⟩ := G.fnSet_nonempty x y
    obtain ⟨L', hL', -⟩ := hdom L hL
    exact ⟨L', hL'⟩
  have hmem := hAc.sInf_mem hAne
  have heq : sInf A = sInf (G.fnSet x y) := by
    apply le_antisymm
    · apply le_csInf (G.fnSet_nonempty x y)
      intro L hL
      obtain ⟨L', hL', hle⟩ := hdom L hL
      exact (csInf_le hAc.bddBelow hL').trans hle
    · exact csInf_le (G.fnSet_bdd _ _) (hAsub hmem)
  obtain ⟨m, p, h0, hm, hw, hL⟩ := hAsub hmem
  exact ⟨m, p, h0, hm, hw, hL.symm.trans heq⟩

end MetricGraph
end SPFacilityGraph

open SPFacilityGraph in
theorem solution {k : ℕ} (G : MetricGraph k) (x y : G.Pt) :
    ∃ (m : ℕ) (p : ℕ → EuclideanSpace ℝ (Fin k)), p 0 = x ∧ p m = y ∧
      (∀ j < m, ∃ e ∈ G.edges, p j ∈ segment ℝ e.1 e.2 ∧ p (j + 1) ∈ segment ℝ e.1 e.2) ∧
      ∑ j ∈ Finset.range m, ‖p (j + 1) - p j‖ = G.dist x y := by
  rw [G.dist_eq_sInf_fnSet]
  exact G.exists_min_walk x y
