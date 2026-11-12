-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.commutant_complete_closure
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T04:37:51.228104+00:00
-- url     : https://prove2.me/submissions/bc21f602-f0e1-4b4b-a5e4-ef9b32c8e749

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_commutation_symmetric_iff_orthomodular
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_commutant_sublattice
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_orthocomplement_complete_demorgan
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 2.2; de Groote, Observables I, PDF pp. 22.
Restored in moderation: source background status is not a formalization obstacle. -/
theorem solution {L : Type u} [CompleteLattice L]
    (perp : L → L) (horth : IsOrthomodular perp) (S : Set L) :
    ∀ t : Set L, t ⊆ latticeCommutant perp S →
      sSup t ∈ latticeCommutant perp S ∧ sInf t ∈ latticeCommutant perp S := by
  have hsym := (commutation_symmetric_iff_orthomodular perp horth.1).mpr horth
  have hC := commutant_sublattice perp horth S
  have hsup (U : Set L) (hU : U ⊆ latticeCommutant perp S) :
      sSup U ∈ latticeCommutant perp S := by
    intro a ha
    apply hsym (sSup U) a
    change sSup U = (sSup U ⊓ a) ⊔ (sSup U ⊓ perp a)
    apply le_antisymm
    · apply sSup_le
      intro b hb
      calc
        b = (b ⊓ a) ⊔ (b ⊓ perp a) := hsym a b (hU hb a ha)
        _ ≤ (sSup U ⊓ a) ⊔ (sSup U ⊓ perp a) :=
          sup_le_sup (inf_le_inf_right a (le_sSup hb))
            (inf_le_inf_right (perp a) (le_sSup hb))
    · exact sup_le inf_le_left inf_le_left
  intro t ht
  refine ⟨hsup t ht, ?_⟩
  have hPt : perp '' t ⊆ latticeCommutant perp S := by
    rintro _ ⟨b, hb, rfl⟩
    exact hC.2.2.1 b (ht hb)
  have hh := hC.2.2.1 (sSup (perp '' t)) (hsup (perp '' t) hPt)
  have hd := (orthocomplement_complete_demorgan perp horth.1 t).1
  rw [← hd, horth.1.2.2 (sInf t)] at hh
  exact hh
