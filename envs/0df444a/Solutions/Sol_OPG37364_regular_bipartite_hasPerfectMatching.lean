-- Prove2me | solution 1 for OPG37364.regular_bipartite_hasPerfectMatching
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T09:08:26.815737+00:00
-- url     : https://prove2.me/submissions/a0c143ba-1ba3-49ed-92d7-82ec91f5db3e

import Definitions.Def_opg37364_matching_cuts
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.Enumerative.DoubleCounting

set_option autoImplicit false

open OPG37364

universe u

/-- Hall's theorem and regular double counting, expressed as an adjacent involution. -/
theorem solution {V : Type u} [Finite V]
    (G : SimpleGraph V) (d : ℕ) (hd : 0 < d)
    (hreg : IsRegularOfDegree G d) (hbip : IsBipartite G) :
    HasPerfectMatching G := by
  classical
  let := Fintype.ofFinite V
  have hdegree (v : V) : G.degree v = d := by
    have h := hreg v
    rw [Set.encard_eq_coe_toFinset_card] at h
    exact_mod_cast h
  have hhall (s : Finset V) : s.card ≤ (s.biUnion fun v => G.neighborFinset v).card := by
    have hcount : s.card * d ≤ (s.biUnion fun v => G.neighborFinset v).card * d := by
      apply Finset.card_mul_le_card_mul G.Adj
      · intro a ha
        have heq : (s.biUnion fun v => G.neighborFinset v).bipartiteAbove G.Adj a =
            G.neighborFinset a := by
          ext b
          simp only [Finset.bipartiteAbove, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
          exact ⟨fun h => h.2, fun h =>
            ⟨Finset.mem_biUnion.mpr ⟨a, ha, (G.mem_neighborFinset _ _).mpr h⟩, h⟩⟩
        rw [heq, G.card_neighborFinset_eq_degree, hdegree]
      · intro b _
        calc
          (s.bipartiteBelow G.Adj b).card ≤ (G.neighborFinset b).card := by
            apply Finset.card_le_card
            intro a ha
            exact (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp ha).2.symm
          _ = d := hdegree b
    exact Nat.le_of_mul_le_mul_right hcount hd
  obtain ⟨f, hf, hadj⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' (fun v => G.neighborFinset v)).mp hhall
  let e : V ≃ V := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  have he (v : V) : G.Adj v (e v) := (G.mem_neighborFinset _ _).mp (hadj v)
  have hei (v : V) : G.Adj v (e.symm v) := by
    simpa only [e.apply_symm_apply] using (he (e.symm v)).symm
  obtain ⟨side, hside⟩ := hbip
  let mate (v : V) : V := if side v = false then e v else e.symm v
  refine ⟨mate, ?_, ?_⟩
  · intro v
    dsimp only [mate]
    split_ifs
    · exact he v
    · exact hei v
  · intro v
    by_cases hv : side v = false
    · have hfside : side (e v) ≠ false := by
        simpa only [hv] using (hside (he v)).symm
      simp [mate, hv, hfside]
    · have hiside : side (e.symm v) = false := by
        have h := hside (hei v)
        cases h₁ : side v <;> cases h₂ : side (e.symm v) <;> simp_all
      simp [mate, hv, hiside]
