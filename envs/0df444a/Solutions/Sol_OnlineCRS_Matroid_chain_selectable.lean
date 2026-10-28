-- Prove2me | solution 1 for OnlineCRS.Matroid.chain_selectable
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:39:17.068151+00:00
-- url     : https://prove2.me/submissions/ae4b5cdd-388f-4fba-80bb-eda55c86b55c

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_OnlineCRS_Matroid_Construction

open scoped Matroid

open OnlineCRS.Matroid in
theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ) (Nch : ℕ → Finset α) (ℓ : ℕ)
    (hstart : Nch 0 = Finset.univ)
    (hstrict : ∀ j < ℓ, Nch (j + 1) ⊂ Nch j)
    (hend : Nch ℓ = ∅)
    (i : ℕ) (hi : i < ℓ) (e : α) (he : e ∈ Nch i \ Nch (i + 1))
    (A : Finset α) :
    Selectable (chainFamily M Nch ℓ) A e ↔
      e ∉ ((M ／ (Nch (i + 1) : Set α)) ↾ (Nch i : Set α)).closure
        ((((A ∩ (Nch i \ Nch (i + 1)) : Finset α)) : Set α) \ {e}) := by
  classical
  have hmono : ∀ a b, a ≤ b → b ≤ ℓ → Nch b ⊆ Nch a := by
    intro a b hab hb
    induction b, hab using Nat.le_induction with
    | base => exact subset_rfl
    | succ b hab ih => exact (hstrict b (by omega)).subset.trans (ih (by omega))
  have hdisj : ∀ x j k, j < ℓ → k < ℓ → x ∈ Nch j \ Nch (j + 1) → x ∈ Nch k \ Nch (k + 1) →
      j = k := by
    intro x j k hj hk hxj hxk
    obtain ⟨hj1, hj2⟩ := Finset.mem_sdiff.1 hxj
    obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.1 hxk
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hj2 (hmono (j + 1) k (by omega) hk.le hk1)
    · exact hk2 (hmono (k + 1) j (by omega) hj.le hj1)
  set N' := (M ／ (Nch (i + 1) : Set α)) ↾ (Nch i : Set α) with hN'
  set L := Nch i \ Nch (i + 1) with hL
  have heE : e ∈ N'.E := by
    rw [hN', Matroid.restrict_ground_eq]
    exact_mod_cast (Finset.mem_sdiff.1 he).1
  unfold Selectable chainFamily
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hsel
    have hX : ((↑(A ∩ L) : Set α) \ {e}) ⊆ N'.E := by
      rw [hN', Matroid.restrict_ground_eq]
      intro x hx
      have h1 : x ∈ A ∩ L := by exact_mod_cast hx.1
      exact_mod_cast (Finset.mem_sdiff.1 (Finset.mem_inter.1 h1).2).1
    obtain ⟨J, hJ⟩ := N'.exists_isBasis _ hX
    have hJfin : J.Finite := Set.toFinite J
    set JF := hJfin.toFinset with hJFdef
    have hJF : (JF : Set α) = J := hJfin.coe_toFinset
    have hJsub : J ⊆ (↑(A ∩ L) : Set α) \ {e} := hJ.subset
    have hJmem : ∀ x ∈ JF, x ∈ A ∩ L ∧ x ≠ e := by
      intro x hx
      have hxJ : x ∈ J := by rw [← hJF]; exact_mod_cast hx
      have := hJsub hxJ
      exact ⟨by exact_mod_cast this.1, this.2⟩
    have hJFA : JF ⊆ A := fun x hx => (Finset.mem_inter.1 (hJmem x hx).1).1
    have hJFL : JF ⊆ L := fun x hx => (Finset.mem_inter.1 (hJmem x hx).1).2
    have heJ : e ∉ JF := fun h => (hJmem e h).2 rfl
    have hmemFam : ∀ j < ℓ, ((M ／ (Nch (j + 1) : Set α)) ↾ (Nch j : Set α)).Indep
        (↑(JF ∩ (Nch j \ Nch (j + 1))) : Set α) := by
      intro j hj
      by_cases hji : j = i
      · subst hji
        rw [Finset.inter_eq_left.2 hJFL, hJF]
        exact hJ.indep
      · have hempty : JF ∩ (Nch j \ Nch (j + 1)) = ∅ := by
          ext x
          simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
          intro hx hxj
          exact hji (hdisj x j i hj hi hxj (hJFL hx))
        rw [hempty, Finset.coe_empty]
        exact Matroid.empty_indep _
    have hins := hsel JF hJFA hmemFam i hi
    rw [Finset.insert_inter_of_mem he, Finset.inter_eq_left.2 hJFL, Finset.coe_insert, hJF] at hins
    have heJ' : e ∉ J := by rw [← hJF]; exact_mod_cast heJ
    rw [hJ.indep.insert_indep_iff_of_notMem heJ', hJ.closure_eq_closure] at hins
    exact hins.2
  · intro hncl I hIA hI j hj
    by_cases hji : j = i
    · subst hji
      rw [Finset.insert_inter_of_mem he, Finset.coe_insert]
      have hIi := hI j hj
      by_cases heI : e ∈ I ∩ L
      · rw [Set.insert_eq_of_mem (by exact_mod_cast heI)]
        exact hIi
      · rw [hIi.insert_indep_iff_of_notMem (by exact_mod_cast heI)]
        refine ⟨heE, fun hcl => hncl ?_⟩
        apply N'.closure_subset_closure _ hcl
        intro x hx
        have hx' : x ∈ I ∩ L := by exact_mod_cast hx
        refine ⟨?_, ?_⟩
        · have : x ∈ A ∩ L := Finset.mem_inter.2 ⟨hIA (Finset.mem_inter.1 hx').1,
            (Finset.mem_inter.1 hx').2⟩
          exact_mod_cast this
        · intro hxe
          rw [Set.mem_singleton_iff] at hxe
          subst hxe
          exact heI hx'
    · rw [Finset.insert_inter_of_notMem (fun hmem => hji (hdisj e j i hj hi hmem he))]
      exact hI j hj
