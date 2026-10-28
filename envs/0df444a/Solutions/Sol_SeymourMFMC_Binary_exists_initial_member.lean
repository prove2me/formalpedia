-- Prove2me | solution 1 for SeymourMFMC.Binary.exists_initial_member
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:56:46.220384+00:00
-- url     : https://prove2.me/submissions/b88877b8-c631-4226-8144-b821630c0533

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Linarith
import Definitions.Def_SeymourMFMC_Binary_IsClutter
import Definitions.Def_SeymourMFMC_Binary_IsBinary
import Definitions.Def_SeymourMFMC_Binary_IsMengerian
import Definitions.Def_SeymourMFMC_Binary_IsCritical
import Definitions.Def_SeymourMFMC_Binary_IsNontrivial
import Definitions.Def_SeymourMFMC_Binary_IsInitial
import Theorems.Thm_SeymourMFMC_Binary_noninitial_circuit
import Theorems.Thm_SeymourMFMC_Binary_parity_decomposition

open SeymourMFMC.Binary

private lemma card_sdiff_inter_add_inter {α : Type*} [DecidableEq α]
    (X Y B : Finset α) :
    ((X \ Y) ∩ B).card + ((X ∩ Y) ∩ B).card = (X ∩ B).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    rw [← Finset.union_inter_distrib_right, Finset.sdiff_union_inter]
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_inter, Finset.mem_sdiff] at hx1
    rw [Finset.mem_inter, Finset.mem_inter] at hx2
    exact hx1.1.2 hx2.1.2

private lemma card_symmDiff_inter {α : Type*} [DecidableEq α]
    (X Y B : Finset α) :
    (symmDiff X Y ∩ B).card + 2 * ((X ∩ Y) ∩ B).card = (X ∩ B).card + (Y ∩ B).card := by
  have h1 := card_sdiff_inter_add_inter X Y B
  have h2 := card_sdiff_inter_add_inter Y X B
  rw [Finset.inter_comm Y X] at h2
  have h3 : (symmDiff X Y ∩ B).card = ((X \ Y) ∩ B).card + ((Y \ X) ∩ B).card := by
    rw [Finset.symmDiff_def, Finset.union_inter_distrib_right, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_inter, Finset.mem_sdiff] at hx1 hx2
    exact hx1.1.2 hx2.1.1
  omega

private lemma elim_noninitial {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    [DecidablePred (IsInitial L)]
    (hL : IsClutter L) (hbin : IsBinary L) (hM : IsMengerian L) (hcrit : IsCritical L) :
    ∀ (n : ℕ) (Z : Finset α),
      (Z.filter (fun x => ¬ IsInitial L x)).card = n →
      Z ⊆ ground L →
      (∀ B ∈ blocker L, Odd (Z ∩ B).card) →
      ∃ Z' ⊆ ground L, (∀ B ∈ blocker L, Odd (Z' ∩ B).card) ∧ ∀ z ∈ Z', IsInitial L z := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Z hcard hZG hZodd
    rcases (Z.filter (fun x => ¬ IsInitial L x)).eq_empty_or_nonempty with hemp | hne
    · refine ⟨Z, hZG, hZodd, fun z hz => ?_⟩
      by_contra hni
      have hmem : z ∈ Z.filter (fun x => ¬ IsInitial L x) :=
        Finset.mem_filter.mpr ⟨hz, hni⟩
      rw [hemp] at hmem
      exact Finset.notMem_empty z hmem
    · rcases hne with ⟨x, hx⟩
      have hx_mem := hx
      rw [Finset.mem_filter] at hx
      rcases hx with ⟨hxZ, hxni⟩
      obtain ⟨C, hCcirc, hxC, hCinit, _, _, _⟩ :=
        noninitial_circuit L hL hbin hM hcrit x (hZG hxZ) hxni
      let Z₁ := symmDiff Z C
      have hZ₁G : Z₁ ⊆ ground L := by
        intro y hy
        rw [Finset.mem_symmDiff] at hy
        rcases hy with ⟨hyZ, _⟩ | ⟨hyC, _⟩
        · exact hZG hyZ
        · exact hCcirc.2.1.1 hyC
      have hZ₁odd : ∀ B ∈ blocker L, Odd (Z₁ ∩ B).card := by
        intro B hB
        dsimp only [Z₁]
        have hsum := card_symmDiff_inter Z C B
        rcases hZodd B hB with ⟨k, hk⟩
        rcases hCcirc.2.1.2 B hB with ⟨m, hm⟩
        refine ⟨k + m - ((Z ∩ C) ∩ B).card, ?_⟩
        omega
      have hss : Z₁.filter (fun y => ¬ IsInitial L y) ⊂ Z.filter (fun y => ¬ IsInitial L y) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨x, hx_mem, ?_⟩
          rw [Finset.mem_filter]
          rintro ⟨hxZ₁, _⟩
          rw [Finset.mem_symmDiff] at hxZ₁
          rcases hxZ₁ with ⟨_, hxC'⟩ | ⟨_, hxZ'⟩
          · exact hxC' hxC
          · exact hxZ' hxZ
        · intro y hy
          rw [Finset.mem_filter] at hy ⊢
          rcases hy with ⟨hyZ₁, hyni⟩
          refine ⟨?_, hyni⟩
          rw [Finset.mem_symmDiff] at hyZ₁
          rcases hyZ₁ with ⟨hyZ, _⟩ | ⟨hyC, hyZ⟩
          · exact hyZ
          · exfalso
            have hyx : y ≠ x := fun h => hyZ (h ▸ hxZ)
            exact hyni (hCinit y (Finset.mem_erase.mpr ⟨hyx, hyC⟩))
      have hlt : (Z₁.filter (fun y => ¬ IsInitial L y)).card < n :=
        hcard ▸ Finset.card_lt_card hss
      exact ih _ hlt Z₁ rfl hZ₁G hZ₁odd

theorem solution {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) (hM : IsMengerian L) (hcrit : IsCritical L)
    (hnt : IsNontrivial L) :
    ∃ A ∈ L, ∀ a ∈ A, IsInitial L a := by
  classical
  obtain ⟨A₀, hA₀⟩ := Finset.nonempty_of_ne_empty hnt.1
  have hA₀G : A₀ ⊆ ground L := Finset.le_sup (f := id) hA₀
  have hA₀odd : ∀ B ∈ blocker L, Odd (A₀ ∩ B).card := fun B hB => hbin A₀ hA₀ B hB
  obtain ⟨Z', hZ'G, hZ'odd, hZ'init⟩ :=
    elim_noninitial L hL hbin hM hcrit _ A₀ rfl hA₀G hA₀odd
  obtain ⟨A, hA, Cs, _, _, _, hACs⟩ :=
    (parity_decomposition L hL hbin Z' hZ'G).2 hZ'odd
  refine ⟨A, hA, fun a ha => hZ'init a ?_⟩
  rw [← hACs]
  exact Finset.mem_union_left _ ha
