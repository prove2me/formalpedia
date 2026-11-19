-- Prove2me | solution 1 for SymmetricPSM1041.ORLowerBound.konig_infinite_rooted_tree
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:57:36.682134+00:00
-- url     : https://prove2.me/submissions/eee1e3a3-da35-414f-9526-eae4b9d1d86f

import Definitions.Def_SymmetricPSM1041_ORLowerBound_RootedTree

namespace SymmetricPSM1041.ORLowerBound.KonigAux
open SymmetricPSM1041.ORLowerBound

def desc {V : Type*} (T : RootedTree V) (v : V) : Set V := {w | ∃ k, (T.parent^[k]) w = v}

theorem iter_root {V : Type*} (T : RootedTree V) : ∀ n, (T.parent^[n]) T.root = T.root
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply, T.parent_root, iter_root T n]

theorem step {V : Type*} (T : RootedTree V) (hfinite : ∀ v, (children T v).Finite) (v : V)
    (hv : (desc T v).Infinite) : ∃ c ∈ children T v, (desc T c).Infinite := by
  classical
  by_contra hc
  push_neg at hc
  apply hv
  have hsub' : ∀ k w, (T.parent^[k]) w = v → w ∈ ({v} ∪ ⋃ c ∈ children T v, desc T c) := by
    intro k
    induction k with
    | zero => intro w hk; left; simpa using hk
    | succ k ih =>
      intro w hk
      by_cases hw : T.parent w = w
      · exact ih w (by rw [Function.iterate_succ_apply, hw] at hk; exact hk)
      · rw [Function.iterate_succ_apply] at hk
        rcases ih (T.parent w) hk with h | h
        · simp at h
          by_cases hwr : w = T.root
          · subst hwr; exact absurd T.parent_root hw
          · right; simp only [Set.mem_iUnion]
            exact ⟨w, ⟨hwr, h⟩, 0, rfl⟩
        · right; simp only [Set.mem_iUnion] at h ⊢
          obtain ⟨c, hc', m, hm⟩ := h
          exact ⟨c, hc', m + 1, by rw [Function.iterate_succ_apply]; exact hm⟩
  have hsub : desc T v ⊆ {v} ∪ ⋃ c ∈ children T v, desc T c := fun w ⟨k, hk⟩ => hsub' k w hk
  exact (Set.Finite.union (Set.finite_singleton v)
    ((hfinite v).biUnion fun c hcv => hc c hcv)).subset hsub

end SymmetricPSM1041.ORLowerBound.KonigAux

open SymmetricPSM1041.ORLowerBound SymmetricPSM1041.ORLowerBound.KonigAux in
theorem solution {V : Type*} [Infinite V] (T : RootedTree V)
    (hfinite : ∀ v, (children T v).Finite) :
    ∃ p : ℕ → V, p 0 = T.root ∧ Function.Injective p ∧
      ∀ k, p (k + 1) ∈ children T (p k) := by
  classical
  let G := {v : V // (desc T v).Infinite}
  have h0 : (desc T T.root).Infinite := by
    have : desc T T.root = Set.univ := by
      ext w; obtain ⟨k, hk⟩ := T.reachable w; exact ⟨fun _ => trivial, fun _ => ⟨k, hk⟩⟩
    rw [this]; exact Set.infinite_univ
  let nx : G → G := fun g => ⟨(step T hfinite g.1 g.2).choose, (step T hfinite g.1 g.2).choose_spec.2⟩
  let q : ℕ → G := fun n => nx^[n] ⟨T.root, h0⟩
  have hq : ∀ k, (q (k + 1)).1 ∈ children T (q k).1 := by
    intro k
    simp only [q]; rw [Function.iterate_succ_apply']
    exact (step T hfinite _ (nx^[k] ⟨T.root, h0⟩).2).choose_spec.1
  refine ⟨fun n => (q n).1, rfl, ?_, hq⟩
  -- parent^[m] (p (i+m)) = p i
  have back : ∀ i m, (T.parent^[m]) (q (i + m)).1 = (q i).1 := by
    intro i m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [show i + (m + 1) = (i + m) + 1 by omega, Function.iterate_succ_apply, (hq (i + m)).2, ih]
  intro i j hij
  by_contra hne
  wlog hlt : i < j generalizing i j
  · exact this hij.symm (Ne.symm hne) (by omega)
  obtain ⟨d, rfl⟩ : ∃ d, j = i + (d + 1) := ⟨j - i - 1, by omega⟩
  replace hij : (q i).1 = (q (i + (d + 1))).1 := hij
  have hfix : (T.parent^[d + 1]) (q i).1 = (q i).1 := by
    have := back i (d + 1); rw [← hij] at this; exact this
  obtain ⟨K, hK⟩ := T.reachable (q i).1
  have hall : ∀ n, (T.parent^[(d + 1) * n]) (q i).1 = (q i).1 := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [Nat.mul_succ, Function.iterate_add_apply, hfix, ih]
  have hroot : (q i).1 = T.root := by
    have e1 := hall K
    have : (d + 1) * K = d * K + K := by ring
    rw [this, Function.iterate_add_apply, hK, iter_root] at e1
    exact e1.symm
  have hc := hq (i + d)
  rw [show i + d + 1 = i + (d + 1) by omega, ← hij, hroot] at hc
  exact hc.1 rfl
