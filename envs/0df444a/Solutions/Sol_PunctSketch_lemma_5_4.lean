-- Prove2me | solution 1 for PunctSketch.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T09:22:35.089437+00:00
-- url     : https://prove2.me/submissions/8c30d50b-0586-41d6-ab75-b0f92d562099

import Mathlib
import Definitions.Def_PunctSketch_altFingerprint

open PunctSketch in
open Classical in
theorem solution {n D Q : ℕ} [Fact Q.Prime] (G : SimpleGraph (Fin n)) (Φ : Fin D → Fin n → ZMod Q)
    (F : Finset (Fin n)) (p : Fin D → ZMod Q) (hp : ∀ z ∈ F, altZ Φ p z = 0) (v : Fin n)
    (hv : v ∉ F) :
    altPunctured G Φ p v =
      ∑ u ∈ Finset.univ.filter (fun u => G.Adj v u ∧ u ∉ F),
        ((sgn v u : ℤ) : ZMod Q) * altZ Φ p v * altZ Φ p u := by
  unfold altPunctured altFingerprint
  have hswap : ∑ i, p i * ∑ u ∈ Finset.univ.filter (G.Adj v), ((sgn v u : ℤ) : ZMod Q) * Φ i u =
      ∑ u ∈ Finset.univ.filter (G.Adj v), ((sgn v u : ℤ) : ZMod Q) * altZ Φ p u := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    unfold altZ
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hswap, Finset.mul_sum, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  by_cases h1 : G.Adj v u
  · by_cases hu : u ∈ F
    · rw [if_pos h1, if_neg (fun h => h.2 hu), hp u hu, mul_zero, mul_zero]
    · rw [if_pos h1, if_pos ⟨h1, hu⟩]; ring
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]
