-- Prove2me | solution 1 for TwinWidthI.MinorFree.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:06:13.205272+00:00
-- url     : https://prove2.me/submissions/4a574c9d-76ba-45ab-a8e7-cf0230de8277

import Mathlib
import Definitions.Def_TwinWidthI_MinorFree_LexDFS

namespace Aux_TW64
open TwinWidthI.MinorFree

theorem anc {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {n : ℕ}
    (σ : V ≃ Fin n) (par : V → V) (hdfs : IsDFSOrder G σ par) :
    ∀ m : ℕ, ∀ w : V, (σ w : ℕ) = m → ∀ u : V, σ u < σ w →
      (∃ x, (σ w : ℕ) ≤ (σ x : ℕ) ∧ G.Adj u x) → IsAncestor par u w := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro w hw u hu hx
    obtain ⟨x, hx, hux⟩ := hx
    have hu' : (σ u : ℕ) < σ w := hu
    have hpos : 0 < (σ w : ℕ) := lt_of_le_of_lt (Nat.zero_le _) hu'
    obtain ⟨hact, _⟩ := (hdfs w).2 hpos
    obtain ⟨hp_lt, _, hmax⟩ := hact
    have hle : σ u ≤ σ (par w) := hmax u hu' ⟨x, hx, hux⟩
    rcases eq_or_lt_of_le hle with heq | hlt
    · have hup : u = par w := σ.injective heq
      exact ⟨1, by rw [Function.iterate_one, hup]⟩
    · have hx' : (σ (par w) : ℕ) ≤ (σ x : ℕ) := by omega
      obtain ⟨i, hi⟩ := ih (σ (par w) : ℕ) (by omega) (par w) rfl u hlt ⟨x, hx', hux⟩
      exact ⟨i + 1, by rw [Function.iterate_succ_apply, hi]⟩

end Aux_TW64

open TwinWidthI.MinorFree Aux_TW64 in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {n : ℕ}
    (σ : V ≃ Fin n) (par : V → V) (hdfs : IsDFSOrder G σ par) {k : ℕ}
    (a b : Fin k → Fin k → V) (hab : ∀ i j, G.Adj (a i j) (b i j))
    (ha : ∀ i j i' j', i < i' → σ (a i j) < σ (a i' j'))
    (hb : ∀ i j i' j', σ (a i j) < σ (b i' j')) :
    ∀ i j i' j', σ (a i j) ≤ σ (a i' j') → IsAncestor par (a i j) (a i' j') := by
  intro i j i' j' hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact ⟨0, (σ.injective heq).symm⟩
  · exact anc G σ par hdfs _ (a i' j') rfl (a i j) hlt
      ⟨b i j, le_of_lt (hb i' j' i j), hab i j⟩
