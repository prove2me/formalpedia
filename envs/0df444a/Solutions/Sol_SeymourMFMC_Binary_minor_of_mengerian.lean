-- Prove2me | solution 1 for SeymourMFMC.Binary.minor_of_mengerian
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:46:49.177983+00:00
-- url     : https://prove2.me/submissions/a87201e5-f99d-4b1d-aac3-fb44a33d2300

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
import Definitions.Def_SeymourMFMC_Binary_IsMengerian
import Definitions.Def_SeymourMFMC_Binary_IsMinor

open SeymourMFMC.Binary

private lemma exists_minimal_subset {α : Type*} [DecidableEq α] (P : Finset α → Prop) :
    ∀ (n : ℕ) (W : Finset α), W.card = n → P W →
      ∃ B ⊆ W, P B ∧ ∀ B' ∈ B.ssubsets, ¬ P B' := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W hcard hPW
    by_cases hmin : ∀ B' ∈ W.ssubsets, ¬ P B'
    · exact ⟨W, Finset.Subset.rfl, hPW, hmin⟩
    · push Not at hmin
      rcases hmin with ⟨B', hB'ss, hPB'⟩
      rw [Finset.mem_ssubsets] at hB'ss
      have hlt : B'.card < n := hcard ▸ Finset.card_lt_card hB'ss
      rcases ih B'.card hlt B' rfl hPB' with ⟨B, hBB', hPB, hBmin⟩
      exact ⟨B, hBB'.trans hB'ss.subset, hPB, hBmin⟩

private lemma exists_blocker_subset {α : Type*} [DecidableEq α]
    (L : Finset (Finset α)) (S : Finset α) (hS : Meets L S) :
    ∃ B ∈ blocker L, B ⊆ S := by
  have hSG : Meets L (S ∩ ground L) := by
    intro A hA
    rcases hS A hA with ⟨x, hx⟩
    rw [Finset.mem_inter] at hx
    refine ⟨x, Finset.mem_inter.mpr ⟨hx.1, Finset.mem_inter.mpr ⟨hx.2, ?_⟩⟩⟩
    exact Finset.le_sup (f := id) hA hx.1
  obtain ⟨B, hBSG, hMB, hBmin⟩ :=
    exists_minimal_subset (Meets L) (S ∩ ground L).card (S ∩ ground L) rfl hSG
  refine ⟨B, ?_, hBSG.trans Finset.inter_subset_left⟩
  rw [blocker, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hBSG.trans Finset.inter_subset_right, hMB, hBmin⟩

private lemma weak_duality {α : Type*} [DecidableEq α]
    (L : Finset (Finset α)) (w : α → ℕ) (q : Finset α → ℕ)
    (hq : ∀ x ∈ ground L, ∑ A ∈ L.filter (fun A => x ∈ A), q A ≤ w x)
    {B : Finset α} (hB : B ∈ blocker L) :
    ∑ A ∈ L, q A ≤ ∑ x ∈ B, w x := by
  rw [blocker, Finset.mem_filter, Finset.mem_powerset] at hB
  rcases hB with ⟨hBG, hMB, _⟩
  have hstep1 : ∑ A ∈ L, q A ≤ ∑ A ∈ L, ∑ x ∈ B, (if x ∈ A then q A else 0) := by
    refine Finset.sum_le_sum (fun A hA => ?_)
    rcases hMB A hA with ⟨x, hx⟩
    rw [Finset.mem_inter] at hx
    have hle := Finset.single_le_sum
      (f := fun y => if y ∈ A then q A else 0) (fun _ _ => Nat.zero_le _) hx.2
    simpa [hx.1] using hle
  rw [Finset.sum_comm] at hstep1
  refine le_trans hstep1 (Finset.sum_le_sum (fun x hxB => ?_))
  rw [← Finset.sum_filter]
  exact hq x (hBG hxB)

private lemma mengerian_of_le {α : Type*} [DecidableEq α]
    (L : Finset (Finset α))
    (h : ∀ w : α → ℕ, ∃ q : Finset α → ℕ,
      (∀ x ∈ ground L, ∑ A ∈ L.filter (fun A => x ∈ A), q A ≤ w x) ∧
        ∃ B ∈ blocker L, ∑ x ∈ B, w x ≤ ∑ A ∈ L, q A) :
    IsMengerian L := by
  refine Or.inr (fun w => ?_)
  obtain ⟨q, hq, B, hB, hle⟩ := h w
  have hge := weak_duality L w q hq hB
  refine ⟨q, hq, B, hB, le_antisymm hge hle, fun B' hB' => ?_⟩
  exact le_trans hle (weak_duality L w q hq hB')

private lemma isMengerian_deletion {α : Type*} [DecidableEq α]
    {L : Finset (Finset α)} (Z : Finset α) (hM : IsMengerian L) :
    IsMengerian (deletion L Z) := by
  rcases hM with rfl | hM
  · refine Or.inl ?_
    ext A
    simp only [deletion, Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => h.1, fun h => ⟨h, h ▸ Finset.disjoint_empty_left Z⟩⟩
  · refine mengerian_of_le (deletion L Z) (fun w' => ?_)
    let w : α → ℕ := fun x => if x ∈ Z then 0 else w' x
    obtain ⟨q, hq, B, hB, hBq, _⟩ := hM w
    refine ⟨q, ?_, ?_⟩
    · intro x hx
      by_cases hxZ : x ∈ Z
      · have hemp : (deletion L Z).filter (fun A => x ∈ A) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro A hA
          rw [Finset.mem_filter, deletion, Finset.mem_filter] at hA
          exact Finset.disjoint_left.mp hA.1.2 hA.2 hxZ
        rw [hemp, Finset.sum_empty]
        exact Nat.zero_le _
      · have hxG : x ∈ ground L :=
          Finset.sup_mono (f := id) (Finset.filter_subset _ L) hx
        have hsub : (deletion L Z).filter (fun A => x ∈ A) ⊆ L.filter (fun A => x ∈ A) :=
          Finset.filter_subset_filter _ (Finset.filter_subset _ L)
        have hle := le_trans (Finset.sum_le_sum_of_subset hsub) (hq x hxG)
        simpa [w, hxZ] using hle
    · have hsum_eq : ∑ A ∈ deletion L Z, q A = ∑ A ∈ L, q A := by
        refine Finset.sum_subset (Finset.filter_subset _ L) (fun A hAL hAdel => ?_)
        rw [deletion, Finset.mem_filter] at hAdel
        have hndisj : ¬ Disjoint A Z := fun hd => hAdel ⟨hAL, hd⟩
        obtain ⟨x, hxA, hxZ⟩ := Finset.not_disjoint_iff.mp hndisj
        have hxG : x ∈ ground L := Finset.le_sup (f := id) hAL hxA
        have h1 : q A ≤ ∑ A' ∈ L.filter (fun A' => x ∈ A'), q A' :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_filter.mpr ⟨hAL, hxA⟩)
        have h2 := hq x hxG
        simp only [w, hxZ, ↓reduceIte] at h2
        omega
      have hMBZ : Meets (deletion L Z) (B \ Z) := by
        intro A hA
        rw [deletion, Finset.mem_filter] at hA
        rw [blocker, Finset.mem_filter] at hB
        rcases hB.2.1 A hA.1 with ⟨x, hx⟩
        rw [Finset.mem_inter] at hx
        refine ⟨x, Finset.mem_inter.mpr ⟨hx.1, Finset.mem_sdiff.mpr ⟨hx.2, ?_⟩⟩⟩
        exact Finset.disjoint_left.mp hA.2 hx.1
      obtain ⟨B₀, hB₀, hB₀sub⟩ := exists_blocker_subset (deletion L Z) (B \ Z) hMBZ
      refine ⟨B₀, hB₀, ?_⟩
      have hle1 : ∑ x ∈ B₀, w' x ≤ ∑ x ∈ B \ Z, w' x :=
        Finset.sum_le_sum_of_subset hB₀sub
      have hle2 : ∑ x ∈ B \ Z, w' x ≤ ∑ x ∈ B, w x := by
        calc ∑ x ∈ B \ Z, w' x
          _ = ∑ x ∈ B \ Z, w x := by
              refine Finset.sum_congr rfl (fun x hx => ?_)
              have hxZ : x ∉ Z := (Finset.mem_sdiff.mp hx).2
              simp [w, hxZ]
          _ ≤ ∑ x ∈ B, w x := Finset.sum_le_sum_of_subset Finset.sdiff_subset
      omega

private lemma isMengerian_contraction {α : Type*} [DecidableEq α]
    {L : Finset (Finset α)} (Z : Finset α) (hM : IsMengerian L) :
    IsMengerian (contraction L Z) := by
  by_cases hex : ∃ A ∈ L, A ⊆ Z
  · refine Or.inl ?_
    rcases hex with ⟨A₀, hA₀, hA₀Z⟩
    have hemp_mem : (∅ : Finset α) ∈ L.image (· \ Z) := by
      rw [Finset.mem_image]
      exact ⟨A₀, hA₀, Finset.sdiff_eq_empty_iff_subset.mpr hA₀Z⟩
    ext A
    simp only [contraction, Finset.mem_filter, Finset.mem_singleton]
    refine ⟨fun h => (h.2 ∅ hemp_mem (Finset.empty_subset A)).symm, ?_⟩
    rintro rfl
    exact ⟨hemp_mem, fun A' _ hA' => Finset.subset_empty.mp hA'⟩
  · push Not at hex
    rcases hM with rfl | hM
    · exfalso
      exact hex ∅ (Finset.mem_singleton_self ∅) (Finset.empty_subset Z)
    · refine mengerian_of_le (contraction L Z) (fun w' => ?_)
      let M : ℕ := (∑ x ∈ ground L, w' x) + 1
      let w : α → ℕ := fun x => if x ∈ Z then M else w' x
      obtain ⟨q, hq, B, hB, hBq, hBmin⟩ := hM w
      have hMW : Meets L (ground L \ Z) := by
        intro A hA
        obtain ⟨x, hxA, hxZ⟩ := Finset.not_subset.mp (hex A hA)
        have hxG : x ∈ ground L := Finset.le_sup (f := id) hA hxA
        exact ⟨x, Finset.mem_inter.mpr ⟨hxA, Finset.mem_sdiff.mpr ⟨hxG, hxZ⟩⟩⟩
      obtain ⟨B₁, hB₁, hB₁sub⟩ := exists_blocker_subset L (ground L \ Z) hMW
      have hB_lt_M : ∑ x ∈ B, w x < M := by
        have h1 : ∑ x ∈ B, w x ≤ ∑ x ∈ B₁, w x := hBmin B₁ hB₁
        have h2 : ∑ x ∈ B₁, w x = ∑ x ∈ B₁, w' x := by
          refine Finset.sum_congr rfl (fun x hx => ?_)
          have hxZ : x ∉ Z := (Finset.mem_sdiff.mp (hB₁sub hx)).2
          simp [w, hxZ]
        have h3 : ∑ x ∈ B₁, w' x ≤ ∑ x ∈ ground L, w' x :=
          Finset.sum_le_sum_of_subset (hB₁sub.trans Finset.sdiff_subset)
        omega
      have hBdisj : Disjoint B Z := by
        rw [Finset.disjoint_left]
        intro x hxB hxZ
        have hle : w x ≤ ∑ y ∈ B, w y :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) hxB
        have hwx : w x = M := if_pos hxZ
        omega
      have hex_min : ∀ A ∈ L, ∃ A' ∈ contraction L Z, A' ⊆ A \ Z := by
        intro A hA
        have hmem : A \ Z ∈ L.image (· \ Z) := Finset.mem_image_of_mem _ hA
        obtain ⟨A', hA'sub, hA'img, hA'min⟩ :=
          exists_minimal_subset (fun C => C ∈ L.image (· \ Z)) (A \ Z).card (A \ Z) rfl hmem
        refine ⟨A', ?_, hA'sub⟩
        rw [contraction, Finset.mem_filter]
        refine ⟨hA'img, fun B' hB' hB'sub => ?_⟩
        by_contra hne
        exact hA'min B' (Finset.mem_ssubsets.mpr (ssubset_of_subset_of_ne hB'sub hne)) hB'
      open Classical in
      let f : Finset α → Finset α :=
        fun A => if hA : A ∈ L then Classical.choose (hex_min A hA) else ∅
      have hf_mem : ∀ A ∈ L, f A ∈ contraction L Z := by
        intro A hA
        simp only [f, hA, ↓reduceDIte]
        exact (Classical.choose_spec (hex_min A hA)).1
      have hf_sub : ∀ A ∈ L, f A ⊆ A \ Z := by
        intro A hA
        simp only [f, hA, ↓reduceDIte]
        exact (Classical.choose_spec (hex_min A hA)).2
      open Classical in
      let q' : Finset α → ℕ :=
        fun A' => ∑ A ∈ L.filter (fun A => f A = A'), q A
      have hq'_sum : ∑ A' ∈ contraction L Z, q' A' = ∑ A ∈ L, q A :=
        Finset.sum_fiberwise_of_maps_to (fun A hA => hf_mem A hA) q
      refine ⟨q', ?_, ?_⟩
      · intro x hxG'
        rw [ground, Finset.mem_sup] at hxG'
        rcases hxG' with ⟨A₀', hA₀'mem, hxA₀'⟩
        rw [contraction, Finset.mem_filter, Finset.mem_image] at hA₀'mem
        rcases hA₀'mem.1 with ⟨A₀, hA₀L, rfl⟩
        have hxZ : x ∉ Z := (Finset.mem_sdiff.mp hxA₀').2
        have hxG : x ∈ ground L :=
          Finset.le_sup (f := id) hA₀L (Finset.mem_sdiff.mp hxA₀').1
        have hfib :
            ∑ A' ∈ (contraction L Z).filter (fun A' => x ∈ A'), q' A' =
              ∑ A ∈ L.filter (fun A => x ∈ f A), q A := by
          have hmaps : ∀ A ∈ L.filter (fun A => x ∈ f A),
              f A ∈ (contraction L Z).filter (fun A' => x ∈ A') := by
            intro A hA
            rw [Finset.mem_filter] at hA ⊢
            exact ⟨hf_mem A hA.1, hA.2⟩
          rw [← Finset.sum_fiberwise_of_maps_to hmaps q]
          refine Finset.sum_congr rfl (fun A' hA' => ?_)
          rw [Finset.mem_filter] at hA'
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext A
          simp only [Finset.mem_filter]
          exact ⟨fun ⟨hAL, hfA⟩ => ⟨⟨hAL, hfA.symm ▸ hA'.2⟩, hfA⟩,
                 fun ⟨⟨hAL, _⟩, hfA⟩ => ⟨hAL, hfA⟩⟩
        have hsub : L.filter (fun A => x ∈ f A) ⊆ L.filter (fun A => x ∈ A) := by
          intro A hA
          rw [Finset.mem_filter] at hA ⊢
          exact ⟨hA.1, Finset.sdiff_subset (hf_sub A hA.1 hA.2)⟩
        have hle := le_trans (Finset.sum_le_sum_of_subset hsub) (hq x hxG)
        rw [hfib]
        simpa [w, hxZ] using hle
      · have hMB' : Meets (contraction L Z) B := by
          intro A' hA'
          rw [contraction, Finset.mem_filter, Finset.mem_image] at hA'
          rcases hA'.1 with ⟨A, hAL, rfl⟩
          rw [blocker, Finset.mem_filter] at hB
          rcases hB.2.1 A hAL with ⟨x, hx⟩
          rw [Finset.mem_inter] at hx
          refine ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hx.1, ?_⟩, hx.2⟩⟩
          exact Finset.disjoint_left.mp hBdisj hx.2
        obtain ⟨B₀, hB₀, hB₀sub⟩ := exists_blocker_subset (contraction L Z) B hMB'
        refine ⟨B₀, hB₀, ?_⟩
        have hle1 : ∑ x ∈ B₀, w' x ≤ ∑ x ∈ B, w' x :=
          Finset.sum_le_sum_of_subset hB₀sub
        have hle2 : ∑ x ∈ B, w' x = ∑ x ∈ B, w x := by
          refine Finset.sum_congr rfl (fun x hxB => ?_)
          have hxZ : x ∉ Z := Finset.disjoint_left.mp hBdisj hxB
          simp [w, hxZ]
        omega

theorem solution {α : Type*} [DecidableEq α] (L L' : Finset (Finset α))
    (hL : IsClutter L) (hM : IsMengerian L) (hminor : IsMinor L' L) :
    IsMengerian L' := by
  have _ := hL
  induction hminor with
  | refl => exact hM
  | tail _ hstep ih =>
    rcases hstep with ⟨Z, rfl | rfl⟩
    · exact isMengerian_deletion Z ih
    · exact isMengerian_contraction Z ih
