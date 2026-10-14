-- Prove2me | solution 1 for OneTwoThree.Weighting.lemma_4_mincut
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-14T10:33:35.866114+00:00
-- url     : https://prove2.me/submissions/2599de7a-6aeb-4f72-a7ed-16ad517e73db

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_STFlow
import Definitions.Def_OneTwoThree_Weighting_AuxNetwork

set_option autoImplicit false

open Finset SimpleGraph
open scoped symmDiff
open OneTwoThree.Weighting

/-- Reindexing a sum over `V × V` by `Prod.swap`. -/
theorem mincut_sum_swap {V : Type*} [Fintype V] (f : V × V → ℤ) :
    Finset.sum Finset.univ (fun p : V × V => f (Prod.swap p)) = Finset.sum Finset.univ f := by
  exact Equiv.sum_comp (Equiv.prodComm V V) f

/-- Pairing `p` with its swap: the two cut-indicators add up to the XOR indicator. -/
theorem mincut_pair_sum {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (T : Finset V) (p : V × V) :
    (if G.Adj p.1 p.2 ∧ p.1 ∈ T ∧ p.2 ∉ T then (1 : ℤ) else 0) +
      (if G.Adj p.2 p.1 ∧ p.2 ∈ T ∧ p.1 ∉ T then (1 : ℤ) else 0) =
    if G.Adj p.1 p.2 ∧ ((p.1 ∈ T ∧ p.2 ∉ T) ∨ (p.1 ∉ T ∧ p.2 ∈ T)) then (1 : ℤ) else 0 := by
  by_cases hAdj : G.Adj p.1 p.2
  · have hAdj2 : G.Adj p.2 p.1 := hAdj.symm
    by_cases ha : p.1 ∈ T <;> by_cases hb : p.2 ∈ T <;> simp_all
  · have hAdj2 : ¬ G.Adj p.2 p.1 := fun h => hAdj (h.symm)
    by_cases ha : p.1 ∈ T <;> by_cases hb : p.2 ∈ T <;> simp_all

/-- Maximality at `S ∆ X`: among ordered adjacent pairs with first end in `X` and
second end outside `X`, at most half are same-side pairs. Proved by pairing each
ordered pair with its swap and comparing `cutSize S` with `cutSize (S ∆ X)`. -/
theorem mincut_pioSame_le_pioCut {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (hS : IsMaxCut G S) (X : Finset V) :
    #(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X ∧
      ¬ ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)))) ≤
    #(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X ∧
      ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)))) := by
  -- `cutSize` as a sum of indicators.
  have hcut : ∀ T : Finset V, (cutSize G T : ℤ) =
      Finset.sum Finset.univ (fun p : V × V =>
        if G.Adj p.1 p.2 ∧ p.1 ∈ T ∧ p.2 ∉ T then (1 : ℤ) else 0) := by
    intro T
    unfold cutSize
    rw [Finset.card_filter]
    simp
  -- Maximality gives `cutSize (S ∆ X) ≤ cutSize S`.
  have hD : (0 : ℤ) ≤ (cutSize G S : ℤ) - (cutSize G (S ∆ X) : ℤ) :=
    sub_nonneg.mpr (by exact_mod_cast hS (S ∆ X))
  -- Pair-sum identities.
  have hpair : ∀ T : Finset V,
      Finset.sum Finset.univ (fun p : V × V =>
        (if G.Adj p.1 p.2 ∧ p.1 ∈ T ∧ p.2 ∉ T then (1 : ℤ) else 0) +
        (if G.Adj p.2 p.1 ∧ p.2 ∈ T ∧ p.1 ∉ T then (1 : ℤ) else 0)) =
      Finset.sum Finset.univ (fun p : V × V =>
        if G.Adj p.1 p.2 ∧ ((p.1 ∈ T ∧ p.2 ∉ T) ∨ (p.1 ∉ T ∧ p.2 ∈ T)) then (1 : ℤ) else 0) := by
    intro T
    exact Finset.sum_congr rfl (fun p _ => mincut_pair_sum G T p)
  -- Swap reindexing for the two cut-indicator sums.
  have hswS : Finset.sum Finset.univ (fun p : V × V =>
        if G.Adj p.2 p.1 ∧ p.2 ∈ S ∧ p.1 ∉ S then (1 : ℤ) else 0) =
      Finset.sum Finset.univ (fun p : V × V =>
        if G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S then (1 : ℤ) else 0) :=
    mincut_sum_swap (fun p : V × V =>
      if G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S then (1 : ℤ) else 0)
  have hswSX : Finset.sum Finset.univ (fun p : V × V =>
        if G.Adj p.2 p.1 ∧ p.2 ∈ S ∆ X ∧ p.1 ∉ S ∆ X then (1 : ℤ) else 0) =
      Finset.sum Finset.univ (fun p : V × V =>
        if G.Adj p.1 p.2 ∧ p.1 ∈ S ∆ X ∧ p.2 ∉ S ∆ X then (1 : ℤ) else 0) :=
    mincut_sum_swap (fun p : V × V =>
      if G.Adj p.1 p.2 ∧ p.1 ∈ S ∆ X ∧ p.2 ∉ S ∆ X then (1 : ℤ) else 0)
  -- `2 * (cutSize S - cutSize (S ∆ X))` equals the difference of the XOR sums.
  have h2D : (2 : ℤ) * ((cutSize G S : ℤ) - (cutSize G (S ∆ X) : ℤ)) =
      Finset.sum Finset.univ (fun p : V × V =>
        (if G.Adj p.1 p.2 ∧ ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)) then (1 : ℤ) else 0) -
        (if G.Adj p.1 p.2 ∧ ((p.1 ∈ S ∆ X ∧ p.2 ∉ S ∆ X) ∨ (p.1 ∉ S ∆ X ∧ p.2 ∈ S ∆ X)) then (1 : ℤ) else 0)) := by
    have e1 : Finset.sum Finset.univ (fun p : V × V =>
        (if G.Adj p.1 p.2 ∧ ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)) then (1 : ℤ) else 0) -
        (if G.Adj p.1 p.2 ∧ ((p.1 ∈ S ∆ X ∧ p.2 ∉ S ∆ X) ∨ (p.1 ∉ S ∆ X ∧ p.2 ∈ S ∆ X)) then (1 : ℤ) else 0)) =
        Finset.sum Finset.univ (fun p : V × V =>
          if G.Adj p.1 p.2 ∧ ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)) then (1 : ℤ) else 0) -
        Finset.sum Finset.univ (fun p : V × V =>
          if G.Adj p.1 p.2 ∧ ((p.1 ∈ S ∆ X ∧ p.2 ∉ S ∆ X) ∨ (p.1 ∉ S ∆ X ∧ p.2 ∈ S ∆ X)) then (1 : ℤ) else 0) :=
      Finset.sum_sub_distrib
        (fun p : V × V =>
          if G.Adj p.1 p.2 ∧ ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)) then (1 : ℤ) else 0)
        (fun p : V × V =>
          if G.Adj p.1 p.2 ∧ ((p.1 ∈ S ∆ X ∧ p.2 ∉ S ∆ X) ∨ (p.1 ∉ S ∆ X ∧ p.2 ∈ S ∆ X))
            then (1 : ℤ) else 0)
    rw [e1, ← hpair S, ← hpair (S ∆ X), Finset.sum_add_distrib, Finset.sum_add_distrib,
      hswS, hswSX, ← hcut S, ← hcut (S ∆ X)]
    ring
  -- Pointwise: the XOR-difference is supported on `Pio ∪ Poi`, with value `±1`.
  have hpt : ∀ p : V × V,
      (if G.Adj p.1 p.2 ∧ ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)) then (1 : ℤ) else 0) -
      (if G.Adj p.1 p.2 ∧ ((p.1 ∈ S ∆ X ∧ p.2 ∉ S ∆ X) ∨ (p.1 ∉ S ∆ X ∧ p.2 ∈ S ∆ X)) then (1 : ℤ) else 0) =
      (if G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X then
        (if (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S) then (1 : ℤ) else -1) else 0) +
      (if G.Adj p.1 p.2 ∧ p.1 ∉ X ∧ p.2 ∈ X then
        (if (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S) then (1 : ℤ) else -1) else 0) := by
    intro p
    by_cases hAdj : G.Adj p.1 p.2
    · by_cases ha : p.1 ∈ S <;> by_cases hb : p.2 ∈ S <;> by_cases hx : p.1 ∈ X <;>
        by_cases hy : p.2 ∈ X <;>
        simp only [Finset.mem_symmDiff, ha, hb, hx, hy, hAdj, and_true, and_false, true_and,
          false_and, or_true, or_false, true_or, false_or, not_true, not_false, if_true,
          if_false] <;> norm_num
    · have hAdj2 : ¬ G.Adj p.2 p.1 := fun h => hAdj (h.symm)
      by_cases ha : p.1 ∈ S <;> by_cases hb : p.2 ∈ S <;> by_cases hx : p.1 ∈ X <;>
        by_cases hy : p.2 ∈ X <;>
        simp only [Finset.mem_symmDiff, ha, hb, hx, hy, hAdj, and_true, and_false, true_and,
          false_and, or_true, or_false, true_or, false_or, not_true, not_false, if_true,
          if_false] <;> norm_num
  -- Swap bijection between the `Poi` and `Pio` sums.
  have hswap : Finset.sum (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∉ X ∧ p.2 ∈ X))
        (fun p => if (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S) then (1 : ℤ) else -1) =
      Finset.sum (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X))
        (fun p => if (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S) then (1 : ℤ) else -1) := by
    apply Finset.sum_bij (fun p _ => Prod.swap p)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      obtain ⟨hAdj, h1, h2⟩ := hp
      exact ⟨hAdj.symm, h2, h1⟩
    · intro a _ b _ hab
      exact (Equiv.prodComm V V).injective hab
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      obtain ⟨hAdj, h1, h2⟩ := hq
      refine ⟨Prod.swap q, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hAdj.symm, h2, h1⟩
      · exact Prod.swap_swap q
    · intro p _
      have hdiff : ((Prod.swap p).1 ∈ S ∧ (Prod.swap p).2 ∉ S) ∨
            ((Prod.swap p).1 ∉ S ∧ (Prod.swap p).2 ∈ S) ↔
          (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S) := by
        show ((p.2 ∈ S ∧ p.1 ∉ S) ∨ (p.2 ∉ S ∧ p.1 ∈ S)) ↔ _
        tauto
      exact if_congr hdiff.symm rfl rfl
  -- The `Pio` sum equals `2 * #PioCut - #Pio`.
  have hPio : Finset.sum (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X))
        (fun p => if (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S) then (1 : ℤ) else -1) =
      2 * (#(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X ∧
        ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)))) : ℤ) -
      (#(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X)) : ℤ) := by
    have h2 : Finset.sum (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X))
          (fun p => if (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S) then (1 : ℤ) else 0) =
        (#(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X ∧
          ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)))) : ℤ) := by
      have hcast : Finset.sum (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X))
            (fun p => if (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S) then (1 : ℤ) else 0) =
          ((Finset.sum (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X))
            (fun p => if (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S) then (1 : ℕ) else 0) : ℕ) : ℤ) := by
        simp
      have hfilt : (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X)).filter
            (fun p => (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)) =
          Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X ∧
            ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S))) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      rw [hcast, ← Finset.card_filter, hfilt]
    have h1 : ∀ p : V × V,
        (if (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S) then (1 : ℤ) else -1) =
        2 * (if (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S) then (1 : ℤ) else 0) - 1 := by
      intro p
      by_cases hd : (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S) <;> simp [hd]
    rw [Finset.sum_congr rfl (fun p _ => h1 p), Finset.sum_sub_distrib, ← Finset.mul_sum, h2,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  -- `#Pio = #PioCut + #PioSame`.
  have hPioSplit : (#(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X)) : ℤ) =
      (#(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X ∧
        ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)))) : ℤ) +
      (#(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X ∧
        ¬ ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)))) : ℤ) := by
    have h : #((Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X)).filter
          (fun p => (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S))) +
        #((Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X)).filter
          (fun p => ¬ ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)))) =
        #(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X)) :=
      Finset.card_filter_add_card_filter_not _
    have e1 : (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X)).filter
          (fun p => (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)) =
        Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X ∧
          ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S))) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have e2 : (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X)).filter
          (fun p => ¬ ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S))) =
        Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X ∧
          ¬ ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S))) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [e1, e2] at h
    have h' : ((#(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X ∧
      ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)))) +
      #(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X ∧
      ¬ ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)))) : ℕ) : ℤ) =
      (#(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X)) : ℤ) := by
      exact_mod_cast h
    push_cast at h'
    exact h'.symm
  -- Assemble: the XOR-difference sum equals `2 * (2 * #PioCut - #Pio)`.
  have hsum2 : Finset.sum Finset.univ (fun p : V × V =>
      (if G.Adj p.1 p.2 ∧ ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)) then (1 : ℤ) else 0) -
      (if G.Adj p.1 p.2 ∧ ((p.1 ∈ S ∆ X ∧ p.2 ∉ S ∆ X) ∨ (p.1 ∉ S ∆ X ∧ p.2 ∈ S ∆ X)) then (1 : ℤ) else 0)) =
      2 * (2 * (#(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X ∧
        ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)))) : ℤ) -
      (#(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X)) : ℤ)) := by
    have e1 : Finset.sum Finset.univ (fun p : V × V =>
        (if G.Adj p.1 p.2 ∧ ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)) then (1 : ℤ) else 0) -
        (if G.Adj p.1 p.2 ∧ ((p.1 ∈ S ∆ X ∧ p.2 ∉ S ∆ X) ∨ (p.1 ∉ S ∆ X ∧ p.2 ∈ S ∆ X)) then (1 : ℤ) else 0)) =
        Finset.sum Finset.univ (fun p : V × V =>
          (if G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X then
            (if (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S) then (1 : ℤ) else -1) else 0) +
          (if G.Adj p.1 p.2 ∧ p.1 ∉ X ∧ p.2 ∈ X then
            (if (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S) then (1 : ℤ) else -1) else 0)) :=
      Finset.sum_congr rfl (fun p _ => hpt p)
    rw [e1, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, hswap, hPio]
    ring
  have hfin : (2 : ℤ) * ((cutSize G S : ℤ) - (cutSize G (S ∆ X) : ℤ)) =
      2 * (2 * (#(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X ∧
        ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)))) : ℤ) -
      (#(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X)) : ℤ)) := by
    rw [h2D, hsum2]
  omega

/-- The `(in,out)` and `(out,in)` parts of `σ` inject into the same-side `Pio` pairs,
via `p ↦ p` on the first part and `p ↦ (p.2, p.1)` on the second; disjointness uses
`σ`'s no-double-orientation. -/
theorem mincut_sigma_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (σ : Finset (V × V))
    (hσ : IsSideOrientation G S σ) (X : Finset V) :
    #(σ.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X)) + #(σ.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X)) ≤
    #(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X ∧
      ¬ ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)))) := by
  obtain ⟨hσadj, hσinj⟩ := hσ
  have hdisj : Disjoint (σ.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X))
      (σ.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    rw [Finset.mem_filter] at hp hq
    exact hq.2.1 hp.2.1
  have hunion : #(σ.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X) ∪
      σ.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X)) =
      #(σ.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X)) + #(σ.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X)) :=
    Finset.card_union_of_disjoint hdisj
  rw [← hunion]
  apply Finset.card_le_card_of_injOn (fun p : V × V => if p.1 ∈ X then p else (p.2, p.1))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_filter] at hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hp with ⟨hpσ, hpX, hpnotX⟩ | ⟨hpσ, hpnotX, hpX⟩
    · have hφ : (if p.1 ∈ X then p else (p.2, p.1)) = p := if_pos hpX
      rw [hφ]
      obtain ⟨hadj, hside⟩ := hσadj p hpσ
      refine ⟨hadj, hpX, hpnotX, ?_⟩
      intro hdiff
      rcases hdiff with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2 (hside.mp h1)
      · exact h1 (hside.mpr h2)
    · have hφ : (if p.1 ∈ X then p else (p.2, p.1)) = (p.2, p.1) := if_neg hpnotX
      rw [hφ]
      obtain ⟨hadj, hside⟩ := hσadj p hpσ
      refine ⟨hadj.symm, hpX, hpnotX, ?_⟩
      intro hdiff
      rcases hdiff with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2 (hside.mpr h1)
      · exact h1 (hside.mp h2)
  · intro a ha b hb hab
    simp only [] at hab
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_filter] at ha hb
    rcases ha with ⟨haσ, ha1, ha2⟩ | ⟨haσ, ha1, ha2⟩ <;>
      rcases hb with ⟨hbσ, hb1, hb2⟩ | ⟨hbσ, hb1, hb2⟩
    · rw [if_pos ha1, if_pos hb1] at hab
      exact hab
    · rw [if_pos ha1, if_neg hb1] at hab
      exfalso
      have hsa : s(a.1, a.2) = s(b.1, b.2) := by
        rw [hab]
        exact Sym2.eq_swap
      have heq := hσinj (Finset.mem_coe.mpr haσ) (Finset.mem_coe.mpr hbσ) hsa
      rw [heq] at ha1
      exact hb1 ha1
    · rw [if_neg ha1, if_pos hb1] at hab
      exfalso
      have hsa : s(a.1, a.2) = s(b.1, b.2) := by
        rw [← hab]
        exact Sym2.eq_swap.symm
      have heq := hσinj (Finset.mem_coe.mpr haσ) (Finset.mem_coe.mpr hbσ) hsa
      rw [heq] at ha1
      exact ha1 hb1
    · rw [if_neg ha1, if_neg hb1] at hab
      have h1 : a.2 = b.2 := congrArg Prod.fst hab
      have h2 : a.1 = b.1 := congrArg Prod.snd hab
      exact Prod.ext h2 h1

/-- The `s`-`t` cut arcs split into the three kinds: cut-edge arcs, `(s, u)` arcs,
and `(v, t)` arcs. -/
theorem mincut_cutArcs {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (σ : Finset (V × V)) (A : Finset (Node V)) :
    #(Finset.univ.filter (fun a : AuxArc G S σ => auxTail G S σ a ∈ A ∧ auxHead G S σ a ∉ A)) =
    #(Finset.univ.filter (fun d : {d : V × V // G.Adj d.1 d.2 ∧ (d.1 ∈ S ↔ d.2 ∉ S)} =>
      Node.vert d.1.1 ∈ A ∧ Node.vert d.1.2 ∉ A)) +
    (#(Finset.univ.filter (fun p : σ => Node.src ∈ A ∧ Node.vert p.1.1 ∉ A)) +
     #(Finset.univ.filter (fun p : σ => Node.vert p.1.2 ∈ A ∧ Node.snk ∉ A))) := by
  classical
  set Cut := Finset.univ.filter (fun a : AuxArc G S σ =>
    auxTail G S σ a ∈ A ∧ auxHead G S σ a ∉ A) with hCutdef
  set U1 := Finset.univ.filter (fun a : AuxArc G S σ =>
    ∃ d : {d : V × V // G.Adj d.1 d.2 ∧ (d.1 ∈ S ↔ d.2 ∉ S)},
      a = Sum.inl d ∧ Node.vert d.1.1 ∈ A ∧ Node.vert d.1.2 ∉ A) with hU1def
  set U2 := Finset.univ.filter (fun a : AuxArc G S σ =>
    ∃ p : σ, a = Sum.inr (Sum.inl p) ∧ Node.src ∈ A ∧ Node.vert p.1.1 ∉ A) with hU2def
  set U3 := Finset.univ.filter (fun a : AuxArc G S σ =>
    ∃ p : σ, a = Sum.inr (Sum.inr p) ∧ Node.vert p.1.2 ∈ A ∧ Node.snk ∉ A) with hU3def
  have hunion : Cut = U1 ∪ U2 ∪ U3 := by
    ext a
    simp only [hCutdef, hU1def, hU2def, hU3def, Finset.mem_filter, Finset.mem_union,
      Finset.mem_univ, true_and]
    constructor
    · intro h
      cases a with
      | inl d => left; left; exact ⟨d, rfl, h.1, h.2⟩
      | inr p =>
        cases p with
        | inl p => left; right; exact ⟨p, rfl, h.1, h.2⟩
        | inr p => right; exact ⟨p, rfl, h.1, h.2⟩
    · intro h
      rcases h with h12 | h3
      · rcases h12 with h1 | h2
        · obtain ⟨d', hEq, h1', h2'⟩ := h1
          rw [hEq]; exact ⟨h1', h2'⟩
        · obtain ⟨p', hEq, h1', h2'⟩ := h2
          rw [hEq]; exact ⟨h1', h2'⟩
      · obtain ⟨p', hEq, h1', h2'⟩ := h3
        rw [hEq]; exact ⟨h1', h2'⟩
  have hdisj12 : Disjoint U1 U2 := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [hU1def, hU2def, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨d, rfl, -, -⟩ := ha
    obtain ⟨p, hcon, -, -⟩ := hb
    exact Sum.inl_ne_inr hcon
  have hdisj123 : Disjoint (U1 ∪ U2) U3 := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [hU1def, hU2def, hU3def, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and] at ha hb
    obtain ⟨p, rfl, -, -⟩ := hb
    rcases ha with ⟨d, hcon, -, -⟩ | ⟨p', hcon, -, -⟩
    · exact Sum.inr_ne_inl hcon
    · exact Sum.inr_ne_inl (Sum.inr.inj hcon)
  have hU1 : #U1 = #(Finset.univ.filter
      (fun d : {d : V × V // G.Adj d.1 d.2 ∧ (d.1 ∈ S ↔ d.2 ∉ S)} =>
        Node.vert d.1.1 ∈ A ∧ Node.vert d.1.2 ∉ A)) := by
    rw [hU1def]
    symm
    apply Finset.card_bij (fun d _ => Sum.inl d)
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact ⟨d, rfl, hd.1, hd.2⟩
    · intro a _ b _ hab
      exact Sum.inl.inj hab
    · intro a ha
      obtain ⟨-, d, rfl, h1, h2⟩ := Finset.mem_filter.mp ha
      exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨h1, h2⟩⟩, rfl⟩
  have hU2 : #U2 = #(Finset.univ.filter (fun p : σ => Node.src ∈ A ∧ Node.vert p.1.1 ∉ A)) := by
    rw [hU2def]
    symm
    apply Finset.card_bij (fun p _ => Sum.inr (Sum.inl p))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact ⟨p, rfl, hp.1, hp.2⟩
    · intro a _ b _ hab
      exact Sum.inl.inj (Sum.inr.inj hab)
    · intro a ha
      obtain ⟨-, p, rfl, h1, h2⟩ := Finset.mem_filter.mp ha
      exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨h1, h2⟩⟩, rfl⟩
  have hU3 : #U3 = #(Finset.univ.filter (fun p : σ => Node.vert p.1.2 ∈ A ∧ Node.snk ∉ A)) := by
    rw [hU3def]
    symm
    apply Finset.card_bij (fun p _ => Sum.inr (Sum.inr p))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact ⟨p, rfl, hp.1, hp.2⟩
    · intro a _ b _ hab
      exact Sum.inr.inj (Sum.inr.inj hab)
    · intro a ha
      obtain ⟨-, p, rfl, h1, h2⟩ := Finset.mem_filter.mp ha
      exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨h1, h2⟩⟩, rfl⟩
  rw [hunion, Finset.card_union_of_disjoint hdisj123, Finset.card_union_of_disjoint hdisj12,
    hU1, hU2, hU3]
  omega

/-- The cut-edge arcs are exactly the `Pio` different-side pairs. -/
theorem mincut_C1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (σ : Finset (V × V)) (A : Finset (Node V))
    (X : Finset V) (hX : ∀ v : V, v ∈ X ↔ Node.vert v ∈ A) :
    #(Finset.univ.filter (fun d : {d : V × V // G.Adj d.1 d.2 ∧ (d.1 ∈ S ↔ d.2 ∉ S)} =>
      Node.vert d.1.1 ∈ A ∧ Node.vert d.1.2 ∉ A)) =
    #(Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X ∧
      ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)))) := by
  apply Finset.card_bij (fun d _ => d.1)
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨d.2.1, (hX d.1.1).mpr hd.1, fun h => hd.2 ((hX d.1.2).mp h), ?_⟩
    by_cases ha : d.1.1 ∈ S
    · exact Or.inl ⟨ha, d.2.2.mp ha⟩
    · exact Or.inr ⟨ha, not_not.mp (fun h => ha (d.2.2.mpr h))⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hadj, hpX, hpnotX, hdiff⟩ := hp
    refine ⟨⟨p, hadj, ?_⟩, ?_, rfl⟩
    · rcases hdiff with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨fun _ => h2, fun _ => h1⟩
      · exact ⟨fun h => absurd h h1, fun h => absurd h2 h⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(hX p.1).mp hpX, fun h => hpnotX ((hX p.2).mpr h)⟩

/-- The `(s, u)` arcs crossing the cut are the `σ`-edges with tail outside `X`. -/
theorem mincut_C2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (σ : Finset (V × V)) (A : Finset (Node V)) (hsrc : Node.src ∈ A)
    (X : Finset V) (hX : ∀ v : V, v ∈ X ↔ Node.vert v ∈ A) :
    #(Finset.univ.filter (fun p : σ => Node.src ∈ A ∧ Node.vert p.1.1 ∉ A)) =
    #(σ.filter (fun p => p.1 ∉ X)) := by
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_filter]
    exact ⟨p.2, fun h => hp.2 ((hX p.1.1).mp h)⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hpσ, hpX⟩ := hp
    refine ⟨⟨p, hpσ⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hsrc, fun h => hpX ((hX p.1).mpr h)⟩

/-- The `(v, t)` arcs crossing the cut are the `σ`-edges with head inside `X`. -/
theorem mincut_C3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (σ : Finset (V × V)) (A : Finset (Node V)) (hsnk : Node.snk ∉ A)
    (X : Finset V) (hX : ∀ v : V, v ∈ X ↔ Node.vert v ∈ A) :
    #(Finset.univ.filter (fun p : σ => Node.vert p.1.2 ∈ A ∧ Node.snk ∉ A)) =
    #(σ.filter (fun p => p.2 ∈ X)) := by
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_filter]
    exact ⟨p.2, (hX p.1.2).mpr hp.1⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hpσ, hpX⟩ := hp
    refine ⟨⟨p, hpσ⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(hX p.2).mp hpX, hsnk⟩

/-- Splitting `σ` (and two of its one-sided filters) by `X`-membership of the ends. -/
theorem mincut_sigma_split {V : Type*} [Fintype V] [DecidableEq V] (σ : Finset (V × V))
    (X : Finset V) :
    #(σ.filter (fun p => p.1 ∉ X)) =
      #(σ.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X)) + #(σ.filter (fun p => p.1 ∉ X ∧ p.2 ∉ X)) ∧
    #(σ.filter (fun p => p.2 ∈ X)) =
      #(σ.filter (fun p => p.1 ∈ X ∧ p.2 ∈ X)) + #(σ.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X)) ∧
    #σ = #(σ.filter (fun p => p.1 ∈ X ∧ p.2 ∈ X)) + #(σ.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X)) +
      #(σ.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X)) + #(σ.filter (fun p => p.1 ∉ X ∧ p.2 ∉ X)) := by
  have h1 : ∀ (P : V × V → Prop) [DecidablePred P] (Q : V × V → Prop) [DecidablePred Q],
      #(σ.filter P) = #(σ.filter (fun p => P p ∧ Q p)) + #(σ.filter (fun p => P p ∧ ¬ Q p)) := by
    intro P _ Q _
    have h : #((σ.filter P).filter Q) + #((σ.filter P).filter (fun a => ¬ Q a)) = #(σ.filter P) :=
      Finset.card_filter_add_card_filter_not _
    rw [Finset.filter_filter, Finset.filter_filter] at h
    exact h.symm
  have hs2 : #(σ.filter (fun p => p.2 ∈ X)) =
      #(σ.filter (fun p => p.1 ∈ X ∧ p.2 ∈ X)) + #(σ.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X)) := by
    have h := h1 (fun p => p.2 ∈ X) (fun p => p.1 ∈ X)
    have e1 : σ.filter (fun p => p.2 ∈ X ∧ p.1 ∈ X) =
        σ.filter (fun p => p.1 ∈ X ∧ p.2 ∈ X) := by
      apply Finset.filter_congr
      intro p _
      tauto
    have e2 : σ.filter (fun p => p.2 ∈ X ∧ ¬ (p.1 ∈ X)) =
        σ.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X) := by
      apply Finset.filter_congr
      intro p _
      tauto
    rw [e1, e2] at h
    exact h
  refine ⟨h1 (fun p => p.1 ∉ X) (fun p => p.2 ∈ X), hs2, ?_⟩
  have hσsplit : #σ = #(σ.filter (fun p => p.1 ∈ X)) + #(σ.filter (fun p => p.1 ∉ X)) :=
    (Finset.card_filter_add_card_filter_not _).symm
  rw [hσsplit, h1 (fun p => p.1 ∈ X) (fun p => p.2 ∈ X), h1 (fun p => p.1 ∉ X) (fun p => p.2 ∈ X)]
  omega

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (hS : IsMaxCut G S) (σ : Finset (V × V))
    (hσ : IsSideOrientation G S σ) :
    ∀ A : Finset (Node V), Node.src ∈ A → Node.snk ∉ A →
      Finset.card σ ≤ Finset.card (Finset.univ.filter (fun a : AuxArc G S σ =>
        auxTail G S σ a ∈ A ∧ auxHead G S σ a ∉ A)) := by
  intro A hsrc hsnk
  set X := Finset.univ.filter (fun v => Node.vert v ∈ A) with hXdef
  have hX : ∀ v : V, v ∈ X ↔ Node.vert v ∈ A := by
    intro v
    rw [hXdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ v, h⟩⟩
  have hsplit := mincut_cutArcs G S σ A
  have hC1 := mincut_C1 G S σ A X hX
  have hC2 := mincut_C2 G σ A hsrc X hX
  have hC3 := mincut_C3 G σ A hsnk X hX
  have hmax := mincut_pioSame_le_pioCut G S hS X
  have hinj := mincut_sigma_le G S σ hσ X
  obtain ⟨hs1, hs2, hs3⟩ := mincut_sigma_split σ X
  omega

/-- Alias under the published node name: the platform verifier looks up the
    published theorem name in the submission environment (dual-naming recipe). -/
theorem OneTwoThree.Weighting.lemma_4_mincut {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (hS : IsMaxCut G S) (σ : Finset (V × V))
    (hσ : IsSideOrientation G S σ) :
    ∀ A : Finset (Node V), Node.src ∈ A → Node.snk ∉ A →
      Finset.card σ ≤ Finset.card (Finset.univ.filter (fun a : AuxArc G S σ =>
        auxTail G S σ a ∈ A ∧ auxHead G S σ a ∉ A)) :=
  solution G S hS σ hσ
