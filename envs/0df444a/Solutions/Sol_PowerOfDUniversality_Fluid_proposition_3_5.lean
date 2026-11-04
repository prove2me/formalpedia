-- Prove2me | solution 1 for PowerOfDUniversality.Fluid.proposition_3_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T01:48:32.479936+00:00
-- url     : https://prove2.me/submissions/febf760a-1f0f-42cc-82cb-1f4f26b0844f

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid.Prop35Aux

open PowerOfDUniversality.Fluid

lemma le_level_iff (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (Q : ℕ →₀ ℕ) (hQ : IsOccupancy N b Q)
    (c : ℕ) (hc1 : 1 ≤ c) (hcN : c ≤ N) (i : ℕ) :
    i ≤ level N Q c ↔ N + 1 ≤ Q i + c := by
  obtain ⟨h0, hanti, _⟩ := hQ
  constructor
  · intro hi
    have hne : (Q.support.filter (fun i => N + 1 ≤ Q i + c)).Nonempty := by
      refine ⟨0, ?_⟩
      rw [Finset.mem_filter, Finsupp.mem_support_iff, h0]
      omega
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup _ hne id
    rw [Finset.mem_filter] at hj
    have hl : level N Q c = j := hjeq
    have := hanti (show i ≤ j by omega)
    omega
  · intro hi
    apply Finset.le_sup (f := id)
    rw [Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨by omega, hi⟩

lemma level_le_b (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (Q : ℕ →₀ ℕ) (hQ : IsOccupancy N b Q)
    (c : ℕ) (hc1 : 1 ≤ c) (hcN : c ≤ N) : ((level N Q c : ℕ) : ℕ∞) ≤ b := by
  by_contra h
  push Not at h
  have h1 := (le_level_iff N hN b Q hQ c hc1 hcN (level N Q c)).mp le_rfl
  have h2 := hQ.2.2 _ h
  omega

lemma add_apply (N : ℕ) (b : ℕ∞) (c : ℕ) (x : Ensemble) (i : ℕ) :
    (addItem N b c x).Q i = x.Q i +
      (if ((level N x.Q c : ℕ) : ℕ∞) < b ∧ i = level N x.Q c + 1 then 1 else 0) := by
  unfold addItem
  by_cases h : ((level N x.Q c : ℕ) : ℕ∞) < b
  · rw [if_pos h]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    by_cases hi : i = level N x.Q c + 1
    · rw [if_pos hi.symm, if_pos ⟨h, hi⟩]
    · rw [if_neg (fun e => hi e.symm), if_neg (fun e => hi e.2)]
  · rw [if_neg h, if_neg (fun e => h e.1)]
    simp

lemma remove_apply (N : ℕ) (k : ℕ) (x : Ensemble) (i : ℕ) :
    (removeItem N k x).Q i = x.Q i -
      (if 1 ≤ level N x.Q k ∧ i = level N x.Q k then 1 else 0) := by
  unfold removeItem
  by_cases h : 1 ≤ level N x.Q k
  · rw [if_pos h]
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
    by_cases hi : i = level N x.Q k
    · rw [if_pos hi.symm, if_pos ⟨h, hi⟩]
    · rw [if_neg (fun e => hi e.symm), if_neg (fun e => hi e.2)]
  · rw [if_neg h, if_neg (fun e => h e.1)]
    simp

lemma occ_add (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (x : Ensemble) (hx : IsOccupancy N b x.Q)
    (c : ℕ) (hc1 : 1 ≤ c) (hcN : c ≤ N) : IsOccupancy N b (addItem N b c x).Q := by
  obtain ⟨I, hI⟩ : ∃ I, level N x.Q c = I := ⟨_, rfl⟩
  have hl := le_level_iff N hN b x.Q hx c hc1 hcN
  have f1 := (hl I).mp (le_of_eq hI.symm)
  have f2 : ¬ N + 1 ≤ x.Q (I + 1) + c := fun h => by have := (hl (I + 1)).mpr h; omega
  obtain ⟨h0, hanti, hzero⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · rw [add_apply, hI, h0]; simp
  · intro i j hij
    show (addItem N b c x).Q j ≤ (addItem N b c x).Q i
    rw [add_apply, add_apply, hI]
    have := hanti hij
    by_cases hj : j = I + 1
    · subst hj
      by_cases hi : i = I + 1
      · subst hi; exact le_rfl
      · have : x.Q I ≤ x.Q i := hanti (by omega)
        split_ifs <;> omega
    · by_cases hi : i = I + 1
      · split_ifs <;> omega
      · split_ifs <;> omega
  · intro i hi
    rw [add_apply, hI, hzero i hi]
    rw [if_neg]
    rintro ⟨h1, rfl⟩
    have : ((I : ℕ∞) + 1) ≤ b := Order.add_one_le_of_lt h1
    push_cast at hi
    exact absurd (lt_of_le_of_lt this hi) (lt_irrefl _)

lemma occ_remove (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (x : Ensemble) (hx : IsOccupancy N b x.Q)
    (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) : IsOccupancy N b (removeItem N k x).Q := by
  obtain ⟨I, hI⟩ : ∃ I, level N x.Q k = I := ⟨_, rfl⟩
  have hl := le_level_iff N hN b x.Q hx k hk1 hkN
  have f1 := (hl I).mp (le_of_eq hI.symm)
  have f2 : ¬ N + 1 ≤ x.Q (I + 1) + k := fun h => by have := (hl (I + 1)).mpr h; omega
  obtain ⟨h0, hanti, hzero⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · rw [remove_apply, hI, h0]; split_ifs <;> omega
  · intro i j hij
    show (removeItem N k x).Q j ≤ (removeItem N k x).Q i
    rw [remove_apply, remove_apply, hI]
    have := hanti hij
    by_cases hi : i = I
    · subst hi
      by_cases hj : j = i
      · subst hj; exact le_rfl
      · have : x.Q j ≤ x.Q (i + 1) := hanti (by omega)
        split_ifs <;> omega
    · split_ifs <;> omega
  · intro i hi
    rw [remove_apply, hzero i hi]
    simp

/-! ### The ℓ¹ distance as a sum over a fixed range -/

lemma occDist_eq_sum (Q Q' : ℕ →₀ ℕ) (M : ℕ) (hM : ∀ i, M < i → Q i = 0 ∧ Q' i = 0) :
    occDist Q Q' = ∑ i ∈ Finset.Icc 1 M, (Q i - Q' i + (Q' i - Q i)) := by
  unfold occDist
  rw [Finset.sum_subset (s₂ := Finset.Icc 1 M)]
  · apply Finset.sum_congr rfl
    intro i _
    omega
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_union, Finsupp.mem_support_iff,
      Finsupp.mem_support_iff] at hi
    rw [Finset.mem_Icc]
    refine ⟨hi.2, ?_⟩
    by_contra h
    have := hM i (by omega)
    rcases hi.1 with h' | h' <;> simp_all
  · intro i hi1 hi
    rw [Finset.mem_Icc] at hi1
    rw [Finset.mem_filter, Finset.mem_union, Finsupp.mem_support_iff,
      Finsupp.mem_support_iff] at hi
    have hQ : Q i = 0 := by by_contra h; exact hi ⟨Or.inl h, hi1.1⟩
    have hQ' : Q' i = 0 := by by_contra h; exact hi ⟨Or.inr h, hi1.1⟩
    rw [hQ, hQ']; rfl


/-- `g Q Q' i = |Q_i − Q'_i|` in `ℕ`. -/
def g (Q Q' : ℕ →₀ ℕ) (i : ℕ) : ℕ := Q i - Q' i + (Q' i - Q i)

/-- A common index bound beyond which four finsupps vanish. -/
def bound (Q1 Q2 R1 R2 : ℕ →₀ ℕ) : ℕ :=
  (Q1.support ∪ Q2.support ∪ R1.support ∪ R2.support).sup id

lemma bound_spec (Q1 Q2 R1 R2 : ℕ →₀ ℕ) (M : ℕ) (hM : bound Q1 Q2 R1 R2 ≤ M) (i : ℕ)
    (hi : M < i) : (Q1 i = 0 ∧ Q2 i = 0) ∧ (R1 i = 0 ∧ R2 i = 0) := by
  have key : ∀ (F : ℕ →₀ ℕ), F.support ⊆ (Q1.support ∪ Q2.support ∪ R1.support ∪ R2.support) →
      F i = 0 := by
    intro F hF
    by_contra h
    have hmem : i ∈ (Q1.support ∪ Q2.support ∪ R1.support ∪ R2.support) :=
      hF (Finsupp.mem_support_iff.mpr h)
    have := Finset.le_sup (f := id) hmem
    simp only [id] at this
    unfold bound at hM
    omega
  refine ⟨⟨key Q1 ?_, key Q2 ?_⟩, ⟨key R1 ?_, key R2 ?_⟩⟩ <;>
    intro x hx <;> simp only [Finset.mem_union] <;> tauto

lemma dist_same (Q1 Q2 R1 R2 : ℕ →₀ ℕ) (a a' : ℕ) (ha' : 1 ≤ a')
    (h : ∀ i, g R1 R2 i + (if i = a' then 1 else 0) ≤ g Q1 Q2 i + (if i = a then 1 else 0)) :
    occDist R1 R2 ≤ occDist Q1 Q2 := by
  set M := bound Q1 Q2 R1 R2 + a'
  have hM : bound Q1 Q2 R1 R2 ≤ M := by omega
  rw [occDist_eq_sum Q1 Q2 M (fun i hi => (bound_spec Q1 Q2 R1 R2 M hM i hi).1),
    occDist_eq_sum R1 R2 M (fun i hi => (bound_spec Q1 Q2 R1 R2 M hM i hi).2)]
  have hs := Finset.sum_le_sum (s := Finset.Icc 1 M) (fun i _ => h i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq'] at hs
  have hmem : a' ∈ Finset.Icc 1 M := by rw [Finset.mem_Icc]; omega
  rw [if_pos hmem] at hs
  unfold g at hs
  split_ifs at hs <;> omega

lemma dist_diff (Q1 Q2 R1 R2 : ℕ →₀ ℕ) (a a' : ℕ)
    (h : ∀ i, g R1 R2 i ≤ g Q1 Q2 i + (if i = a then 1 else 0) + (if i = a' then 1 else 0)) :
    occDist R1 R2 ≤ occDist Q1 Q2 + 2 := by
  set M := bound Q1 Q2 R1 R2
  have hM : bound Q1 Q2 R1 R2 ≤ M := le_rfl
  rw [occDist_eq_sum Q1 Q2 M (fun i hi => (bound_spec Q1 Q2 R1 R2 M hM i hi).1),
    occDist_eq_sum R1 R2 M (fun i hi => (bound_spec Q1 Q2 R1 R2 M hM i hi).2)]
  have hs := Finset.sum_le_sum (s := Finset.Icc 1 M) (fun i _ => h i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq'] at hs
  unfold g at hs
  split_ifs at hs <;> omega

lemma remove_same (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (x y : Ensemble) (hx : IsOccupancy N b x.Q)
    (hy : IsOccupancy N b y.Q) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    occDist (removeItem N k x).Q (removeItem N k y).Q ≤ occDist x.Q y.Q := by
  have hlx := le_level_iff N hN b x.Q hx k hk1 hkN
  have hly := le_level_iff N hN b y.Q hy k hk1 hkN
  have rx := remove_apply N k x
  have ry := remove_apply N k y
  obtain ⟨a, ha⟩ : ∃ a, level N x.Q k = a := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a', level N y.Q k = a' := ⟨_, rfl⟩
  rw [ha] at rx hlx
  rw [ha'] at ry hly
  have fx := (hlx a).mp le_rfl
  have fy := (hly a').mp le_rfl
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · have c1 : ¬ N + 1 ≤ x.Q a' + k := fun h => by have := (hlx a').mpr h; omega
    apply dist_same _ _ _ _ a a' (by omega)
    intro i
    unfold g
    rw [rx, ry]
    by_cases hi : i = a'
    · subst hi; split_ifs <;> omega
    · split_ifs <;> omega
  · subst heq
    apply dist_same _ _ _ _ 1 1 le_rfl
    intro i
    unfold g
    rw [rx, ry]
    split_ifs <;> omega
  · have c1 : ¬ N + 1 ≤ y.Q a + k := fun h => by have := (hly a).mpr h; omega
    apply dist_same _ _ _ _ a' a (by omega)
    intro i
    unfold g
    rw [rx, ry]
    by_cases hi : i = a
    · subst hi; split_ifs <;> omega
    · split_ifs <;> omega

lemma add_same (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (x y : Ensemble) (hx : IsOccupancy N b x.Q)
    (hy : IsOccupancy N b y.Q) (c : ℕ) (hc1 : 1 ≤ c) (hcN : c ≤ N) :
    occDist (addItem N b c x).Q (addItem N b c y).Q ≤ occDist x.Q y.Q := by
  have hlx := le_level_iff N hN b x.Q hx c hc1 hcN
  have hly := le_level_iff N hN b y.Q hy c hc1 hcN
  have bx := level_le_b N hN b x.Q hx c hc1 hcN
  have bY := level_le_b N hN b y.Q hy c hc1 hcN
  have rx := add_apply N b c x
  have ry := add_apply N b c y
  obtain ⟨a, ha⟩ : ∃ a, level N x.Q c = a := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a', level N y.Q c = a' := ⟨_, rfl⟩
  rw [ha] at rx hlx bx
  rw [ha'] at ry hly bY
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · have c1 : ¬ N + 1 ≤ x.Q (a + 1) + c := fun h => by have := (hlx (a + 1)).mpr h; omega
    have c2 := (hly (a + 1)).mp (by omega)
    have hab : ((a : ℕ) : ℕ∞) < b :=
      lt_of_lt_of_le (by exact_mod_cast hlt) bY
    apply dist_same _ _ _ _ (a' + 1) (a + 1) (by omega)
    intro i
    unfold g
    rw [rx, ry]
    by_cases hi : i = a + 1
    · subst hi; simp only [hab, true_and, if_true]; split_ifs <;> omega
    · split_ifs <;> omega
  · subst heq
    apply dist_same _ _ _ _ 1 1 le_rfl
    intro i
    unfold g
    rw [rx, ry]
    split_ifs <;> omega
  · have c1 : ¬ N + 1 ≤ y.Q (a' + 1) + c := fun h => by have := (hly (a' + 1)).mpr h; omega
    have c2 := (hlx (a' + 1)).mp (by omega)
    have hab : ((a' : ℕ) : ℕ∞) < b :=
      lt_of_lt_of_le (by exact_mod_cast hgt) bx
    apply dist_same _ _ _ _ (a + 1) (a' + 1) (by omega)
    intro i
    unfold g
    rw [rx, ry]
    by_cases hi : i = a' + 1
    · subst hi; simp only [hab, true_and, if_true]; split_ifs <;> omega
    · split_ifs <;> omega

lemma add_diff (N : ℕ) (b : ℕ∞) (x y : Ensemble) (c c' : ℕ) :
    occDist (addItem N b c x).Q (addItem N b c' y).Q ≤ occDist x.Q y.Q + 2 := by
  apply dist_diff _ _ _ _ (level N x.Q c + 1) (level N y.Q c' + 1)
  intro i
  unfold g
  rw [add_apply, add_apply]
  split_ifs <;> omega


lemma uniformPos_bounds (N : ℕ) (hN : 1 ≤ N) (x : ℝ) : 1 ≤ uniformPos N x ∧ uniformPos N x ≤ N := by
  unfold uniformPos
  exact ⟨le_min (by omega) hN, min_le_right _ _⟩

open Classical in
lemma main_ineq (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (lam : ℝ) (pol₁ pol₂ : Scheme)
    (h₁ : IsScheme N pol₁) (h₂ : IsScheme N pol₂) (Q0 : ℕ →₀ ℕ) (hQ0 : IsOccupancy N b Q0)
    (ξ : ℕ → ℕ → ℝ) (n : ℕ) :
    IsOccupancy N b (eventState N b lam pol₁ Q0 ξ n).Q ∧
    IsOccupancy N b (eventState N b lam pol₂ Q0 ξ n).Q ∧
    occDist (eventState N b lam pol₁ Q0 ξ n).Q (eventState N b lam pol₂ Q0 ξ n).Q ≤
      2 * ((Finset.range n).filter (fun k => IsArrival N lam (ξ (k + 1)) ∧
        pol₁ (k + 1) (eventState N b lam pol₁ Q0 ξ k).Q (ξ (k + 1)) ≠
        pol₂ (k + 1) (eventState N b lam pol₂ Q0 ξ k).Q (ξ (k + 1)))).card := by
  induction n with
  | zero =>
    refine ⟨hQ0, hQ0, ?_⟩
    simp only [eventState]
    have : occDist Q0 Q0 = 0 := by
      unfold occDist
      apply Finset.sum_eq_zero
      intro i _
      simp
    omega
  | succ n ih =>
    obtain ⟨o1, o2, hd⟩ := ih
    set x := eventState N b lam pol₁ Q0 ξ n with hx
    set y := eventState N b lam pol₂ Q0 ξ n with hy
    have e1 : eventState N b lam pol₁ Q0 ξ (n + 1) =
        if IsArrival N lam (ξ (n + 1)) then addItem N b (pol₁ (n + 1) x.Q (ξ (n + 1))) x
        else removeItem N (uniformPos N (ξ (n + 1) 2)) x := by
      simp only [eventState, step, hx]
    have e2 : eventState N b lam pol₂ Q0 ξ (n + 1) =
        if IsArrival N lam (ξ (n + 1)) then addItem N b (pol₂ (n + 1) y.Q (ξ (n + 1))) y
        else removeItem N (uniformPos N (ξ (n + 1) 2)) y := by
      simp only [eventState, step, hy]
    rw [e1, e2, Finset.range_add_one, Finset.filter_insert]
    have hnot : n ∉ Finset.filter (fun k => IsArrival N lam (ξ (k + 1)) ∧
        pol₁ (k + 1) (eventState N b lam pol₁ Q0 ξ k).Q (ξ (k + 1)) ≠
        pol₂ (k + 1) (eventState N b lam pol₂ Q0 ξ k).Q (ξ (k + 1))) (Finset.range n) := by
      simp
    obtain ⟨u1, u2⟩ := uniformPos_bounds N hN (ξ (n + 1) 2)
    by_cases harr : IsArrival N lam (ξ (n + 1))
    · simp only [harr, if_true, true_and]
      obtain ⟨p1, p1'⟩ := h₁ (n + 1) x.Q (ξ (n + 1))
      obtain ⟨p2, p2'⟩ := h₂ (n + 1) y.Q (ξ (n + 1))
      refine ⟨occ_add N hN b x o1 _ p1 p1', occ_add N hN b y o2 _ p2 p2', ?_⟩
      by_cases hc : pol₁ (n + 1) x.Q (ξ (n + 1)) = pol₂ (n + 1) y.Q (ξ (n + 1))
      · rw [if_neg (fun h => h hc)]
        rw [hc]
        have := add_same N hN b x y o1 o2 _ p2 p2'
        omega
      · rw [if_pos hc, Finset.card_insert_of_notMem hnot]
        have := add_diff N b x y (pol₁ (n + 1) x.Q (ξ (n + 1))) (pol₂ (n + 1) y.Q (ξ (n + 1)))
        omega
    · simp only [harr, if_false, false_and]
      refine ⟨occ_remove N hN b x o1 _ u1 u2, occ_remove N hN b y o2 _ u1 u2, ?_⟩
      have := remove_same N hN b x y o1 o2 _ u1 u2
      omega

end PowerOfDUniversality.Fluid.Prop35Aux

open PowerOfDUniversality.Fluid PowerOfDUniversality.Fluid.Prop35Aux

theorem solution (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (hlam : 0 ≤ lam)
    (pol₁ pol₂ : Scheme) (h₁ : IsScheme N pol₁) (h₂ : IsScheme N pol₂)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (sys₁ sys₂ : System P N b lam) (hξ : sys₁.ξ = sys₂.ξ) (hQ0 : ∀ ω, sys₁.Q0 ω = sys₂.Q0 ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      occDist (sys₁.occ pol₁ ω t) (sys₂.occ pol₂ ω t)
        ≤ 2 * sys₁.diffDecisions sys₂ pol₁ pol₂ ω t := by
  refine Filter.Eventually.of_forall (fun ω t _ => ?_)
  have hm : sys₂.marks ω = sys₁.marks ω := by
    funext j r; simp [System.marks, hξ]
  have hc : sys₂.count ω t = sys₁.count ω t := by
    simp only [System.count, hm]
  have h2 : ∀ n, sys₂.stateSeq pol₂ ω n =
      eventState N b lam pol₂ (sys₁.Q0 ω) (sys₁.marks ω) n := by
    intro n; simp only [System.stateSeq, hm, hQ0]
  have h1 : ∀ n, sys₁.stateSeq pol₁ ω n =
      eventState N b lam pol₁ (sys₁.Q0 ω) (sys₁.marks ω) n := fun n => rfl
  have key := (main_ineq N hN b lam pol₁ pol₂ h₁ h₂ (sys₁.Q0 ω) (sys₁.isOccupancy_Q0 ω)
    (sys₁.marks ω) (sys₁.count ω t)).2.2
  unfold System.occ System.diffDecisions
  rw [hc, h2, h1]
  convert key using 3
  ext k
  simp only [Finset.mem_filter, h1, h2]
