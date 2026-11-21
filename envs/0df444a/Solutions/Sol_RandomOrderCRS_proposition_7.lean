-- Prove2me | solution 1 for RandomOrderCRS.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:03:41.142172+00:00
-- url     : https://prove2.me/submissions/4b8b91b0-6843-4b95-80c9-7f34013f5a8f

import Mathlib
import Definitions.Def_RandomOrderCRS_ArrivalModel
import Definitions.Def_RandomOrderCRS_SimpleBlocker

namespace Aux_RandomOrderCRS_proposition_7

open RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

def Adj' (G : SimpleGraph V) (g x : G.edgeSet) : Prop :=
  ∃ v, v ∈ (g : Sym2 V) ∧ v ∈ (x : Sym2 V)

lemma mem_edgeNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (e f : G.edgeSet) :
    f ∈ edgeNbrs G e ↔ f ≠ e ∧ ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V) := by
  unfold edgeNbrs
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

lemma mem_relevantSet (G : SimpleGraph V) [DecidableRel G.Adj] (Y : G.edgeSet → ℝ)
    (S : G.edgeSet → Bool) (e f : G.edgeSet) :
    f ∈ relevantSet G Y S e ↔ IsRelevant G Y S e f := by
  classical
  unfold relevantSet
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

lemma mem_blockerCandidates (G : SimpleGraph V) [DecidableRel G.Adj] (e f h : G.edgeSet) :
    h ∈ blockerCandidates G e f ↔ h ≠ f ∧ (h : Sym2 V) ≠ pair (e : Sym2 V) (f : Sym2 V) ∧
      ∃ w, w ∈ (f : Sym2 V) ∧ w ∉ (e : Sym2 V) ∧ w ∈ (h : Sym2 V) := by
  unfold blockerCandidates
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

lemma fold_inv (G : SimpleGraph V) [DecidableRel G.Adj] (Y : G.edgeSet → ℝ)
    (S : G.edgeSet → Bool) (l : List G.edgeSet) (hl : l.Pairwise (fun a b => Y a < Y b)) :
    (∀ g ∈ l.foldl (greedyStep G S) ∅, g ∈ l ∧ S g = true) ∧
    (∀ x ∈ l, S x = true → (∀ g ∈ l.foldl (greedyStep G S) ∅, Y g < Y x → ¬ Adj' G g x) →
      x ∈ l.foldl (greedyStep G S) ∅) ∧
    (∀ x ∈ l.foldl (greedyStep G S) ∅, ∀ g ∈ l.foldl (greedyStep G S) ∅,
      Y g < Y x → ¬ Adj' G g x) := by
  induction l using List.reverseRecOn with
  | nil =>
    simp
  | append_singleton l z ih =>
    obtain ⟨hl1, -, hl3⟩ := List.pairwise_append.mp hl
    have hz : ∀ a ∈ l, Y a < Y z := fun a ha => hl3 a ha z (List.mem_singleton_self z)
    obtain ⟨A, B, C⟩ := ih hl1
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hM' : l.foldl (greedyStep G S) ∅ = M' at A B C ⊢
    have hmem : ∀ x, x ∈ l ++ [z] ↔ x ∈ l ∨ x = z := by
      intro x; simp
    by_cases hc : S z = true ∧ ¬ Blocked G M' z
    · have hM : greedyStep G S M' z = insert z M' := by
        unfold greedyStep; rw [if_pos hc]
      rw [hM]
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        rcases Finset.mem_insert.mp hg with rfl | hg
        · exact ⟨(hmem _).2 (Or.inr rfl), hc.1⟩
        · exact ⟨(hmem _).2 (Or.inl (A g hg).1), (A g hg).2⟩
      · intro x hx hSx hno
        rcases (hmem x).1 hx with hx | rfl
        · exact Finset.mem_insert_of_mem
            (B x hx hSx (fun g hg => hno g (Finset.mem_insert_of_mem hg)))
        · exact Finset.mem_insert_self _ _
      · intro x hx g hg hYg hadj
        rcases Finset.mem_insert.mp hx with hx1 | hx1
        · rcases Finset.mem_insert.mp hg with hg1 | hg1
          · rw [hx1, hg1] at hYg
            exact lt_irrefl _ hYg
          · obtain ⟨v, hv1, hv2⟩ := hadj
            rw [hx1] at hv2
            exact hc.2 ⟨g, hg1, v, hv1, hv2⟩
        · rcases Finset.mem_insert.mp hg with hg1 | hg1
          · have := hz x (A x hx1).1
            rw [hg1] at hYg
            exact lt_asymm this hYg
          · exact C x hx1 g hg1 hYg hadj
    · have hM : greedyStep G S M' z = M' := by
        unfold greedyStep; rw [if_neg hc]
      rw [hM]
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        exact ⟨(hmem _).2 (Or.inl (A g hg).1), (A g hg).2⟩
      · intro x hx hSx hno
        rcases (hmem x).1 hx with hx | rfl
        · exact B x hx hSx hno
        · exfalso
          have hb : Blocked G M' x := by
            by_contra hb
            exact hc ⟨hSx, hb⟩
          obtain ⟨g, hg, v, hv1, hv2⟩ := hb
          exact hno g hg (hz g (A g hg).1) ⟨v, hv1, hv2⟩
      · exact C

end Aux_RandomOrderCRS_proposition_7

open RandomOrderCRS Aux_RandomOrderCRS_proposition_7 in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : G.edgeSet → ℝ)
    (S : G.edgeSet → Bool) (hY : Function.Injective Y) (e : G.edgeSet) (he : S e = true)
    (hcard : (relevantSet G Y S e).card ≤ 1)
    (hsbl : ∀ f ∈ relevantSet G Y S e, HasSimpleBlocker G Y S e f) :
    e ∈ greedy G (arrivalOrder G Y) S := by
  set σ := arrivalOrder G Y with hσ
  have hYσ : ∀ i, Y (σ i) = ((Y ∘ (Fintype.equivFin G.edgeSet).symm) ∘
      Tuple.sort (Y ∘ (Fintype.equivFin G.edgeSet).symm)) i := fun i => rfl
  have hl : (List.ofFn σ).Pairwise (fun a b => Y a < Y b) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    have hle : Y (σ i) ≤ Y (σ j) := by
      rw [hYσ, hYσ]
      exact Tuple.monotone_sort _ hij.le
    have hne : Y (σ i) ≠ Y (σ j) := by
      intro h
      have := σ.injective (hY h)
      exact (ne_of_lt hij) this
    exact lt_of_le_of_ne hle hne
  have hmemL : ∀ x, x ∈ List.ofFn σ := by
    intro x
    rw [List.mem_ofFn']
    exact ⟨σ.symm x, σ.apply_symm_apply x⟩
  obtain ⟨A, B, C⟩ := fold_inv G Y S (List.ofFn σ) hl
  show e ∈ (List.ofFn σ).foldl (greedyStep G S) ∅
  apply B e (hmemL e) he
  intro g hg hYg hadj
  have hSg := (A g hg).2
  have hgR : g ∈ relevantSet G Y S e := by
    rw [mem_relevantSet]
    refine ⟨?_, hYg, hSg⟩
    rw [mem_edgeNbrs]
    refine ⟨?_, ?_⟩
    · rintro rfl; exact lt_irrefl _ hYg
    · obtain ⟨v, hv1, hv2⟩ := hadj
      exact ⟨v, hv2, hv1⟩
  obtain ⟨h, hcand, hrel, hno⟩ := hsbl g hgR
  rw [mem_blockerCandidates] at hcand
  obtain ⟨-, -, w, hwg, -, hwh⟩ := hcand
  obtain ⟨-, hYh, hSh⟩ := hrel
  have hhM : h ∈ (List.ofFn σ).foldl (greedyStep G S) ∅ := by
    apply B h (hmemL h) hSh
    intro k hk hYk hadjk
    have hSk := (A k hk).2
    have hkn : k ∈ edgeNbrs G h := by
      rw [mem_edgeNbrs]
      refine ⟨?_, ?_⟩
      · rintro rfl; exact lt_irrefl _ hYk
      · obtain ⟨v, hv1, hv2⟩ := hadjk
        exact ⟨v, hv2, hv1⟩
    have hrelk : IsRelevant G Y S h k := ⟨hkn, hYk, hSk⟩
    have hke : k ∈ edgeNbrs G e := by
      by_contra hne
      exact hno k (Finset.mem_sdiff.mpr ⟨hkn, hne⟩) hrelk
    have hkR : k ∈ relevantSet G Y S e := by
      rw [mem_relevantSet]
      exact ⟨hke, lt_trans hYk (lt_trans hYh hYg), hSk⟩
    have hkg : k = g := Finset.card_le_one.mp hcard k hkR g hgR
    rw [hkg] at hYk
    exact lt_asymm hYk hYh
  exact C g hg h hhM hYh ⟨w, hwh, hwg⟩
