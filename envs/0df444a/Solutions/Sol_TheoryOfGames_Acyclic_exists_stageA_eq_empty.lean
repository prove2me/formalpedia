-- Prove2me | solution 1 for TheoryOfGames.Acyclic.exists_stageA_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T10:01:13.416047+00:00
-- url     : https://prove2.me/submissions/6b9f1e6e-b199-4678-8805-23c66ab22082

import Definitions.Def_TheoryOfGames_Acyclic_Construction
import Definitions.Def_TheoryOfGames_Acyclic_Acyclicity

/-!
# (65:S): the construction of 65.7.1 terminates

If `D` is finite and `S` acyclic on `D`, some stage `A_i` of the construction is empty.

Two ingredients:

* **Finite acyclic sets have maxima.** A nonempty finite `E ⊆ D` with no maximum would admit
  an infinite walk `x₀, x₁, x₂, … ∈ E` with `S x_{i+1} x_i` (choose a predecessor in `E` for
  every non-maximal element). By pigeonhole two of the first `|E| + 1` points coincide,
  `x_i = x_j` (`i < j`), and the segment `x_i, x_{i+1}, …, x_j` is a cycle of length
  `m = j − i ≥ 1`, contradicting `(A_m)`.
* **Each round removes the maxima.** `A_{i+1} = (A_i − B_i) − C_i` with `B_i = A_i^m`, so
  `A_{i+1} ⊆ A_i − B_i`. While `A_i ≠ ∅` its set of maxima is nonempty, so the cardinality
  strictly decreases; after finitely many rounds the stage is empty. Formally: strong
  induction on `|D|`, using that acyclicity is inherited by subsets and the shift identity
  `stageA D S (k + j) = stageA (stageA D S k) S j`.
-/

open TheoryOfGames.Acyclic

namespace SSwrapped

variable {α : Type*}

/-- Acyclicity is inherited by subsets. -/
private lemma acyclic_of_subset (D E : Set α) (S : α → α → Prop) (hsub : E ⊆ D)
    (hS : IsAcyclic D S) : IsAcyclic E S := by
  intro m hm x hxmem hxeq
  exact hS m hm x (fun i hi => hsub (hxmem i hi)) hxeq

/-- A nonempty finite subset of an acyclic set has a maximum. -/
private lemma maxima_nonempty_of_finite_acyclic {D : Set α} {S : α → α → Prop}
    (hS : IsAcyclic D S) {E : Set α} (hE : E.Finite) (hsub : E ⊆ D) (hne : E.Nonempty) :
    (maxima E S).Nonempty := by
  classical
  by_contra hmax
  rw [Set.not_nonempty_iff_eq_empty] at hmax
  have hstep : ∀ z : α, z ∈ E → ∃ y : α, y ∈ E ∧ S y z := by
    intro z hz
    by_contra hc
    push Not at hc
    have hzmax : z ∈ maxima E S := ⟨hz, fun y hy => hc y hy⟩
    rw [hmax] at hzmax
    exact Set.notMem_empty z hzmax
  set F : α → α := fun z =>
    if h : ∃ y : α, y ∈ E ∧ S y z then Classical.choose h else z with hFdef
  have hFE : ∀ z ∈ E, F z ∈ E ∧ S (F z) z := by
    intro z hz
    show (if h : ∃ y : α, y ∈ E ∧ S y z then Classical.choose h else z) ∈ E
        ∧ S (if h : ∃ y : α, y ∈ E ∧ S y z then Classical.choose h else z) z
    rw [dif_pos (hstep z hz)]
    exact Classical.choose_spec (hstep z hz)
  set x : ℕ → α := fun n => Nat.rec (hne.some) (fun _ z => F z) n with hxdef
  have hxs : ∀ n : ℕ, x (n + 1) = F (x n) := fun _ => rfl
  have hxmem : ∀ n, x n ∈ E := by
    intro n
    induction n with
    | zero => exact hne.some_mem
    | succ n ih =>
      rw [hxs]
      exact (hFE _ ih).1
  have hxchain : ∀ n, S (x (n + 1)) (x n) := by
    intro n
    rw [hxs]
    exact (hFE _ (hxmem n)).2
  -- pigeonhole: two of the first |E| + 1 points coincide
  haveI : Fintype {a // a ∈ E} := hE.fintype
  set n := Fintype.card {a // a ∈ E} with hn
  have hcardE : 0 < n := Fintype.card_pos_iff.mpr ⟨⟨hne.some, hne.some_mem⟩⟩
  set g : Fin (n + 1) → {a // a ∈ E} := fun i => ⟨x i, hxmem i⟩ with hgdef
  have hnotinj : ¬ Function.Injective g := by
    intro hinj
    have hle := Fintype.card_le_of_injective g hinj
    rw [Fintype.card_fin, hn] at hle
    omega
  obtain ⟨a, b, hab, hne_ab⟩ := Function.not_injective_iff.mp hnotinj
  have hxab : x a = x b := congrArg Subtype.val hab
  obtain ⟨i, j, hij, hxeq⟩ : ∃ i j : ℕ, i < j ∧ x i = x j := by
    rcases lt_trichotomy (a : ℕ) (b : ℕ) with h | h | h
    · exact ⟨a, b, h, hxab⟩
    · exact absurd (Fin.ext h) hne_ab
    · exact ⟨b, a, h, hxab.symm⟩
  -- the segment x i, …, x j is a cycle of length j - i ≥ 1
  have hchain' : ∀ t : ℕ, S ((fun t => x (i + t)) (t + 1)) ((fun t => x (i + t)) t) := by
    intro t
    have h1 : (fun t => x (i + t)) (t + 1) = x (i + t + 1) := rfl
    have h2 : (fun t => x (i + t)) t = x (i + t) := rfl
    rw [h1, h2]
    exact hxchain (i + t)
  have hmem : ∀ t : ℕ, t < j - i → (fun t => x (i + t)) t ∈ D := by
    intro t _
    exact hsub (hxmem (i + t))
  have hclose : (fun t => x (i + t)) (j - i) = (fun t => x (i + t)) 0 := by
    show x (i + (j - i)) = x i
    rw [Nat.add_sub_cancel' (by omega : i ≤ j)]
    exact hxeq.symm
  exact absurd (fun t _ht => hchain' t) (hS (j - i) (by omega) (fun t => x (i + t)) hmem hclose)

end SSwrapped

open SSwrapped

theorem solution {α : Type*} (D : Set α) (S : α → α → Prop)
    (hD : D.Finite) (hS : IsAcyclic D S) :
    ∃ k : ℕ, stageA D S k = ∅ := by
  classical
  have stageA_succ' : ∀ (D' : Set α) (k : ℕ), stageA D' S (k + 1)
      = ((stageA D' S k \ maxima (stageA D' S k) S)
        \ {y | y ∈ stageA D' S k ∧ ∃ x ∈ maxima (stageA D' S k) S, S x y}) := fun _ _ => rfl
  have stageA_add' : ∀ (D' : Set α) (j k : ℕ),
      stageA D' S (k + j) = stageA (stageA D' S k) S j := by
    intro D' j k
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← Nat.add_assoc, stageA_succ', ih, stageA_succ']
  -- strong induction on the cardinality of the finite set
  have main : ∀ (n : ℕ) (D' : Set α) (hfin : D'.Finite), hfin.toFinset.card = n →
      IsAcyclic D' S → ∃ k : ℕ, stageA D' S k = ∅ := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro D' hfin hcard hacyc
      rcases n with _ | n'
      · -- card = 0: the set is empty
        have hempty : D' = ∅ := by
          by_contra hc
          have hne : D'.Nonempty := Set.nonempty_iff_ne_empty.mpr hc
          obtain ⟨x, hx⟩ := hne
          have hpos : 0 < hfin.toFinset.card :=
            Finset.card_pos.mpr ⟨x, (Set.Finite.mem_toFinset hfin).mpr hx⟩
          omega
        refine ⟨0, ?_⟩
        show D' = ∅
        exact hempty
      · -- card = n' + 1: the maxima are nonempty and get removed
        have hne : D'.Nonempty := by
          by_contra hc
          have hempty : D' = ∅ := Set.not_nonempty_iff_eq_empty.mp hc
          subst hempty
          rw [Set.Finite.toFinset_empty hfin, Finset.card_empty] at hcard
          omega
        obtain ⟨b, hb⟩ := maxima_nonempty_of_finite_acyclic hacyc hfin subset_rfl hne
        have hmemD : b ∈ D' := hb.1
        have hsub2 : stageA D' S 1 ⊆ D' \ maxima D' S := by
          have := stageA_succ' D' 0
          rw [show stageA D' S 0 = D' from rfl, Nat.zero_add] at this
          rw [this]
          exact Set.sdiff_subset
        have hcardA₂ : ((hfin.subset (hsub2.trans Set.sdiff_subset)).toFinset).card ≤ n' := by
          have hfinB := hfin.subset (Set.sdiff_subset (t := maxima D' S))
          have hbenot : b ∉ hfinB.toFinset := by
            intro hc
            exact ((Set.Finite.mem_toFinset hfinB).mp hc).2 hb
          have hsube : hfinB.toFinset ⊆ hfin.toFinset.erase b := by
            intro a ha
            rw [Finset.mem_erase]
            refine ⟨fun hcon => hbenot ?_, (Set.Finite.mem_toFinset hfin).mpr ?_⟩
            · rw [← hcon]; exact ha
            · exact ((Set.Finite.mem_toFinset hfinB).mp ha).1
          have hlt : hfinB.toFinset.card < hfin.toFinset.card := by
            have h1 := Finset.card_mono hsube
            rw [Finset.card_erase_of_mem ((Set.Finite.mem_toFinset hfin).mpr hmemD)] at h1
            omega
          have hfin2 := hfin.subset (hsub2.trans (Set.sdiff_subset (s := D') (t := maxima D' S)))
          have hle : hfin2.toFinset.card ≤ hfinB.toFinset.card := by
            refine Finset.card_mono (Set.Finite.toFinset_subset_toFinset.mpr ?_)
            exact hsub2
          omega
        obtain ⟨k', hk'⟩ := ih ((hfin.subset (hsub2.trans Set.sdiff_subset)).toFinset).card
          (by omega) (stageA D' S 1) (hfin.subset (hsub2.trans Set.sdiff_subset)) rfl
          (acyclic_of_subset D' (stageA D' S 1) S (hsub2.trans Set.sdiff_subset) hacyc)
        refine ⟨1 + k', ?_⟩
        rw [stageA_add' D' k' 1, hk']
  exact main hD.toFinset.card D hD rfl hS
