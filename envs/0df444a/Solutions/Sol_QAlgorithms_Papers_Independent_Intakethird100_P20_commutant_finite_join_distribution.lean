-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.commutant_finite_join_distribution
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T04:29:41.165723+00:00
-- url     : https://prove2.me/submissions/b61194af-677f-4cee-88aa-29bc615280e2

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
theorem solution {L : Type u} [Lattice L] [BoundedOrder L]
    (perp : L → L) (horth : IsOrthomodular perp) (S : Set L) (a : L) (ha : a ∈ S)
    {n : ℕ} (b : Fin n → L) (hb : ∀ i, b i ∈ latticeCommutant perp S) :
    a ⊓ Finset.univ.sup b = Finset.univ.sup (fun i => a ⊓ b i) := by
  have hsym := (commutation_symmetric_iff_orthomodular perp horth.1).mpr horth
  let x := Finset.univ.sup (fun i => a ⊓ b i)
  have hx : x ≤ a := by
    apply Finset.sup_le
    intro i hi
    exact inf_le_left
  have hbound : Finset.univ.sup b ≤ x ⊔ perp a := by
    apply Finset.sup_le
    intro i hi
    have hba : b i ⊓ a ≤ x := by
      rw [inf_comm (b i) a]
      exact Finset.le_sup (s := Finset.univ) (f := fun j : Fin n => a ⊓ b j) (Finset.mem_univ i)
    calc
      b i = (b i ⊓ a) ⊔ (b i ⊓ perp a) := hsym a (b i) (hb i a ha)
      _ ≤ x ⊔ perp a := sup_le_sup hba inf_le_right
  change a ⊓ Finset.univ.sup b = x
  apply le_antisymm
  · calc
      a ⊓ Finset.univ.sup b ≤ a ⊓ (x ⊔ perp a) := inf_le_inf_left a hbound
      _ = x := by
        rw [horth.2 a x (perp a) hx le_rfl, inf_eq_right.mpr hx,
          (horth.1.1 a).1, sup_bot_eq]
  · apply Finset.sup_le
    intro i hi
    exact inf_le_inf_left a (Finset.le_sup (s := Finset.univ) (f := b) hi)
