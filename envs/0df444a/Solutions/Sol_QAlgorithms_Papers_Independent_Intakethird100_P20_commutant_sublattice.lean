-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.commutant_sublattice
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T04:35:18.561377+00:00
-- url     : https://prove2.me/submissions/85cec708-0e4b-476f-9e0d-2a42daee9f35

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_commutation_symmetric_iff_orthomodular
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_orthocomplement_bounds_and_order
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 2.2; de Groote, Observables I, PDF pp. 22.
Restored in moderation: source background status is not a formalization obstacle. -/
theorem solution {L : Type u} [Lattice L] [BoundedOrder L]
    (perp : L → L) (horth : IsOrthomodular perp) (S : Set L) :
    IsSubOrtholattice perp (latticeCommutant perp S) := by
  have hsym := (commutation_symmetric_iff_orthomodular perp horth.1).mpr horth
  have hbounds := orthocomplement_bounds_and_order perp horth.1
  have hcomp (a b : L) (hab : LatticeCommutes perp a b) :
      LatticeCommutes perp a (perp b) := by
    unfold LatticeCommutes at hab ⊢
    rw [horth.1.2.2 b, sup_comm]
    exact hab
  have hsup (a b c : L) (hab : LatticeCommutes perp a b)
      (hac : LatticeCommutes perp a c) : LatticeCommutes perp a (b ⊔ c) := by
    apply hsym (b ⊔ c) a
    change b ⊔ c = ((b ⊔ c) ⊓ a) ⊔ ((b ⊔ c) ⊓ perp a)
    apply le_antisymm
    · apply sup_le
      · calc
          b = (b ⊓ a) ⊔ (b ⊓ perp a) := hsym a b hab
          _ ≤ ((b ⊔ c) ⊓ a) ⊔ ((b ⊔ c) ⊓ perp a) :=
            sup_le_sup (inf_le_inf_right a le_sup_left) (inf_le_inf_right (perp a) le_sup_left)
      · calc
          c = (c ⊓ a) ⊔ (c ⊓ perp a) := hsym a c hac
          _ ≤ ((b ⊔ c) ⊓ a) ⊔ ((b ⊔ c) ⊓ perp a) :=
            sup_le_sup (inf_le_inf_right a le_sup_right) (inf_le_inf_right (perp a) le_sup_right)
    · exact sup_le inf_le_left inf_le_left
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    unfold LatticeCommutes
    rw [hbounds.1]
    simp
  · intro a ha
    unfold LatticeCommutes
    rw [hbounds.2.1]
    simp
  · intro b hb a ha
    exact hcomp a b (hb a ha)
  · intro b hb c hc
    constructor
    · intro a ha
      have hh := hcomp a (perp b ⊔ perp c)
        (hsup a (perp b) (perp c) (hcomp a b (hb a ha)) (hcomp a c (hc a ha)))
      rw [(horth.1.2.1 (perp b) (perp c)).2, horth.1.2.2 b, horth.1.2.2 c] at hh
      exact hh
    · intro a ha
      exact hsup a b c (hb a ha) (hc a ha)
