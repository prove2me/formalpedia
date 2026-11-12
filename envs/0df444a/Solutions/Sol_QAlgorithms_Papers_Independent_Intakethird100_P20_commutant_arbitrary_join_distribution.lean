-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.commutant_arbitrary_join_distribution
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T04:26:16.145469+00:00
-- url     : https://prove2.me/submissions/9965c9bb-dc92-42ae-8402-79a7feb9ef9f

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_commutation_symmetric_iff_orthomodular
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- rem-2.2; de Groote, Observables I, PDF pp. 23.
Restored in moderation: source background status is not a formalization obstacle. -/
theorem solution {L : Type u} [CompleteLattice L]
    (perp : L → L) (horth : IsOrthomodular perp) (S : Set L) (a : L) (ha : a ∈ S)
    (t : Set L) (ht : t ⊆ latticeCommutant perp S) :
    a ⊓ sSup t = sSup ((fun b => a ⊓ b) '' t) := by
  have hsym := (commutation_symmetric_iff_orthomodular perp horth.1).mpr horth
  let x := sSup ((fun b => a ⊓ b) '' t)
  have hx : x ≤ a := by
    apply sSup_le
    rintro _ ⟨b, hb, rfl⟩
    exact inf_le_left
  have hbound : sSup t ≤ x ⊔ perp a := by
    apply sSup_le
    intro b hb
    have hba : b ⊓ a ≤ x := by
      rw [inf_comm b a]
      exact le_sSup ⟨b, hb, rfl⟩
    calc
      b = (b ⊓ a) ⊔ (b ⊓ perp a) := hsym a b (ht hb a ha)
      _ ≤ x ⊔ perp a := sup_le_sup hba inf_le_right
  change a ⊓ sSup t = x
  apply le_antisymm
  · calc
      a ⊓ sSup t ≤ a ⊓ (x ⊔ perp a) := inf_le_inf_left a hbound
      _ = x := by
        rw [horth.2 a x (perp a) hx le_rfl, inf_eq_right.mpr hx,
          (horth.1.1 a).1, sup_bot_eq]
  · apply sSup_le
    rintro _ ⟨b, hb, rfl⟩
    exact inf_le_inf_left a (le_sSup hb)
