-- Prove2me | solution 1 for OpenMath.WOWII96.key
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:37:45.02825+00:00
-- url     : https://prove2.me/submissions/dde28ee6-8ba6-4af8-a284-6c5ffae0e3a0

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_OpenMath_WOWII96
public import Theorems.Thm_OpenMath_card_le_indepNeighborsCard
public import Theorems.Thm_OpenMath_exists_parent


set_option autoImplicit true
@[expose] public section
public section
open OpenMath OpenMath.WOWII96
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace OpenMath.WOWII96
theorem _root_.solution (G : SimpleGraph α) (h : G.Connected) (v : α) (L : ℕ) (hL2 : 2 ≤ L)
    (hL : ∀ u, indepNeighborsCard G u ≤ L) :
    G.indepNum + distEven G v ≤ 1 + distEven G v * L := by
  classical
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  have hind : (I : Set α).Pairwise fun x y => ¬ G.Adj x y := hI.isIndepSet
  rw [← hI.card_eq]
  -- the even layer, and the two halves of `I`
  set E : Finset α := univ.filter fun w => Even (G.dist v w) with hE
  set IE : Finset α := I.filter fun w => Even (G.dist v w) with hIE
  set IO : Finset α := I.filter fun w => ¬ Even (G.dist v w) with hIO
  have hsplit : IE.card + IO.card = I.card := card_filter_add_card_filter_not _
  -- parents
  have hpar : ∀ w : α, ∃ p, w ≠ v → G.Adj p w ∧ G.dist v p + 1 = G.dist v w := by
    intro w
    by_cases hw : w = v
    · exact ⟨v, fun h' => absurd hw h'⟩
    · obtain ⟨p, hp⟩ := exists_parent h hw
      exact ⟨p, fun _ => hp⟩
  choose par hpar using hpar
  have hIO_ne : ∀ w ∈ IO, w ≠ v := by
    intro w hw hwv
    subst hwv
    simp [hIO] at hw
  set P : Finset α := IO.image par with hP
  -- parents are in the even layer and outside `I`
  have hP_E : ∀ u ∈ P, u ∈ E := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hu
    have hwodd : ¬ Even (G.dist v w) := (mem_filter.mp hw).2
    have := (hpar w (hIO_ne w hw)).2
    simp only [hE, mem_filter, mem_univ, true_and]
    by_contra hcon
    apply hwodd
    rw [← this]
    exact (Nat.not_even_iff_odd.mp hcon).add_one
  have hP_I : ∀ u ∈ P, u ∉ I := by
    intro u hu huI
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hu
    have hwI : w ∈ I := (mem_filter.mp hw).1
    have hadj := (hpar w (hIO_ne w hw)).1
    exact hind huI hwI hadj.ne hadj
  -- (1) |I ∩ even| + |P| ≤ |E|
  have h1 : IE.card + P.card ≤ E.card := by
    rw [← card_union_of_disjoint]
    · apply card_le_card
      intro x hx
      rcases mem_union.mp hx with hx | hx
      · simp only [hE, mem_filter, mem_univ, true_and]
        exact (mem_filter.mp hx).2
      · exact hP_E x hx
    · rw [Finset.disjoint_left]
      intro x hx hxP
      exact hP_I x hxP (mem_filter.mp hx).1
  -- (2) fibre bound: each parent `u` has at most `L - 1` children, `v` at most `L`
  have hfib : ∀ u ∈ P, (IO.filter fun w => par w = u).card + 1 ≤ L + (if u = v then 1 else 0) := by
    intro u hu
    set F := IO.filter fun w => par w = u with hF
    have hFadj : ∀ w ∈ F, G.Adj u w := by
      intro w hw
      obtain ⟨hwIO, hpw⟩ := mem_filter.mp hw
      rw [← hpw]
      exact (hpar w (hIO_ne w hwIO)).1
    have hFind : (F : Set α).Pairwise fun x y => ¬ G.Adj x y := by
      intro x hx y hy hxy
      exact hind (mem_filter.mp (mem_filter.mp hx).1).1 (mem_filter.mp (mem_filter.mp hy).1).1 hxy
    by_cases huv : u = v
    · simp only [huv, ite_true]
      have := card_le_indepNeighborsCard (u := u) hFadj hFind
      have := hL u
      omega
    · simp only [huv, ite_false, add_zero]
      obtain ⟨x, hxu, hxd⟩ := exists_parent h huv
      -- every child `w` of `u` is at distance `dist v u + 1`
      have hFd : ∀ w ∈ F, G.dist v w = G.dist v u + 1 := by
        intro w hw
        obtain ⟨hwIO, hpw⟩ := mem_filter.mp hw
        have := (hpar w (hIO_ne w hwIO)).2
        rw [hpw] at this
        omega
      have hxF : x ∉ F := by
        intro hx
        have := hFd x hx
        omega
      have hcard := card_le_indepNeighborsCard (u := u) (S := insert x F)
        (by
          intro t ht
          rcases mem_insert.mp ht with rfl | ht
          · exact hxu.symm
          · exact hFadj t ht)
        (by
          rw [coe_insert, Set.pairwise_insert]
          refine ⟨hFind, fun w hw _ => ⟨fun hadj => ?_, fun hadj => ?_⟩⟩
          · have hdw := hFd w hw
            rcases hadj.diff_dist_adj (u := v) with h' | h' | h' <;> omega
          · have hdw := hFd w hw
            rcases hadj.symm.diff_dist_adj (u := v) with h' | h' | h' <;> omega)
      rw [card_insert_of_notMem hxF] at hcard
      have := hL u
      omega
  -- (3) sum the fibres:  |I ∩ odd| + |P| ≤ L·|P| + 1
  have h2 : IO.card + P.card ≤ L * P.card + 1 := by
    have hsum : IO.card = ∑ u ∈ P, (IO.filter fun w => par w = u).card :=
      card_eq_sum_card_fiberwise (fun w hw => mem_image_of_mem par hw)
    have hb : ∑ u ∈ P, ((IO.filter fun w => par w = u).card + 1)
        ≤ ∑ u ∈ P, (L + if u = v then 1 else 0) := sum_le_sum hfib
    rw [sum_add_distrib, sum_add_distrib, sum_const, sum_const, smul_eq_mul, smul_eq_mul,
      mul_one, ← hsum, sum_ite_eq' P v (fun _ => 1)] at hb
    have : (if v ∈ P then 1 else 0) ≤ 1 := by split_ifs <;> omega
    rw [mul_comm]
    omega
  -- (4) combine, using `|P| ≤ |E|` and `L ≥ 2`
  have hD : distEven G v = E.card := rfl
  rw [hD]
  have hPE : P.card ≤ E.card := by omega
  obtain ⟨M, rfl⟩ : ∃ M, L = M + 2 := ⟨L - 2, by omega⟩
  have : M * P.card ≤ M * E.card := Nat.mul_le_mul_left M hPE
  nlinarith
end OpenMath.WOWII96
