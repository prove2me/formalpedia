-- Prove2me | solution 1 for StabilityDichotomies.Solvability.hamming_incidence_separation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:55:15.191519+00:00
-- url     : https://prove2.me/submissions/d081466e-1a42-437a-be75-ce0927498da1

import Mathlib
import Definitions.Def_StabilityDichotomies_Solvability_Incidence
import Theorems.Thm_StabilityDichotomies_Solvability_disagreement_along_path

section
set_option autoImplicit false

namespace StabilityDichotomies.Dev.Hamming

open StabilityDichotomies.Solvability
open scoped Classical

variable {Γ : Language} {V : Type}

lemma adj_isLeft {I : Instance Γ V} {u w : IncidenceVertex I}
    (h : (incidenceGraph I).Adj u w) : u.isLeft = !w.isLeft := by
  rcases u with a | a <;> rcases w with b | b
  · exact absurd h (by simp [incidenceGraph, IncAdjacent])
  · rfl
  · rfl
  · exact absurd h (by simp [incidenceGraph, IncAdjacent])

lemma alt {I : Instance Γ V} {u v : IncidenceVertex I} (p : (incidenceGraph I).Walk u v) :
    2 * p.support.countP (fun w => w.isLeft) =
      p.length + (if u.isLeft then 1 else 0) + (if v.isLeft then 1 else 0) := by
  induction p with
  | nil => simp [List.countP_cons]; split <;> simp
  | @cons a b c h p ih =>
    have hab := adj_isLeft h
    rw [SimpleGraph.Walk.support_cons, List.countP_cons, SimpleGraph.Walk.length_cons]
    rw [hab] at *
    cases hb : b.isLeft <;> simp [hb] at ih ⊢ <;> omega

lemma length_le {I : Instance Γ V} [Fintype V] (c c' : Occurrence I) (x y : V → Bool)
    (p : (incidenceGraph I).Walk (.inr c) (.inr c')) (hp : p.IsPath)
    (hd : ∀ v : V, Sum.inl v ∈ p.support → x v ≠ y v) :
    p.length ≤ 2 * hammingDist x y := by
  have h1 := alt p
  simp at h1
  -- count of left vertices ≤ hammingDist
  have hnd : p.support.Nodup := hp.support_nodup
  have h2 : p.support.countP (fun w => w.isLeft) ≤ hammingDist x y := by
    let S : Finset V := (p.support.filterMap Sum.getLeft?).toFinset
    have hnd2 : (p.support.filterMap Sum.getLeft?).Nodup := by
      apply hnd.filterMap
      intro a a' b ha ha'
      rcases a with a | a <;> rcases a' with a' | a' <;> simp_all
    have hlen : p.support.countP (fun w => w.isLeft) = (p.support.filterMap Sum.getLeft?).length := by
      clear h1 hnd hnd2 hd
      generalize p.support = l
      induction l with
      | nil => simp
      | cons a l ih =>
        rcases a with a | a <;> simp [List.countP_cons, List.filterMap_cons, ih]
    rw [hlen, ← List.toFinset_card_of_nodup hnd2]
    have hsub : S ⊆ Finset.univ.filter (fun i => x i ≠ y i) := by
      intro v hv
      simp only [S, List.mem_toFinset, List.mem_filterMap] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      rcases w with w | w
      · simp at hwv; subst hwv
        simpa using hd _ hw
      · simp at hwv
    exact Finset.card_le_card hsub
  omega

end StabilityDichotomies.Dev.Hamming

namespace StabilityDichotomies.Solvability

theorem chk_hamming_incidence_separation (Γ : Language) (V : Type) [Fintype V]
    (I : Instance Γ V) (hI : MinimallyUnsatisfiable I)
    (c c' : Occurrence I) (hcc' : c ≠ c') (x y : V → Bool)
    (hx : Solution (I.delete (occurrenceConstraint I c)) x)
    (hy : Solution (I.delete (occurrenceConstraint I c')) y) :
    (incidenceGraph I).edist (.inr c) (.inr c') ≤
      ((2 * hammingDist x y : ℕ) : ℕ∞) := by
  obtain ⟨p, hp, hd⟩ := StabilityDichotomies.Solvability.disagreement_along_path
    Γ V I hI c c' hcc' x y hx hy
  calc (incidenceGraph I).edist (.inr c) (.inr c') ≤ p.length := SimpleGraph.edist_le p
    _ ≤ ((2 * hammingDist x y : ℕ) : ℕ∞) := by
      exact_mod_cast StabilityDichotomies.Dev.Hamming.length_le c c' x y p hp hd

end StabilityDichotomies.Solvability
end

theorem solution : type_of% @StabilityDichotomies.Solvability.chk_hamming_incidence_separation := @StabilityDichotomies.Solvability.chk_hamming_incidence_separation
