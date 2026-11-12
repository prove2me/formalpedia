-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.commutation_symmetric_iff_orthomodular
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T04:21:29.693712+00:00
-- url     : https://prove2.me/submissions/6e4273ed-9652-44c9-a12e-89a6f45d7c88

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_orthocomplement_bounds_and_order
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 2.1; de Groote, Observables I, PDF pp. 21.
Restored in moderation: source background status is not a formalization obstacle. -/
theorem solution {L : Type u} [Lattice L] [BoundedOrder L]
    (perp : L → L) (hperp : IsOrthocomplement perp) :
    (∀ a b : L, LatticeCommutes perp a b → LatticeCommutes perp b a) ↔
      IsOrthomodular perp := by
  have hbounds := orthocomplement_bounds_and_order perp hperp
  have hanti {a b : L} (h : a ≤ b) : perp b ≤ perp a := (hbounds.2.2 a b).mp h
  have hinj : Function.Injective perp := by
    intro a b h
    have hh := congrArg perp h
    simpa only [hperp.2.2] using hh
  have hinf0 (a c : L) (hc : c ≤ perp a) : a ⊓ c = ⊥ :=
    le_antisymm ((inf_le_inf_left a hc).trans_eq (hperp.1 a).1) bot_le
  constructor
  · intro hsym
    refine ⟨hperp, ?_⟩
    have hweak (a b : L) (hb : b ≤ a) : a ⊓ (perp a ⊔ b) = b := by
      have hbc : LatticeCommutes perp b a := by
        unfold LatticeCommutes
        rw [inf_eq_left.mpr hb, hinf0 b (perp a) (hanti hb), sup_bot_eq]
      have hac := hsym b a hbc
      have hacp : LatticeCommutes perp a (perp b) := by
        unfold LatticeCommutes at hac ⊢
        rw [hperp.2.2 b, sup_comm]
        exact hac
      have hcp := hsym a (perp b) hacp
      have heq : perp b = (a ⊓ perp b) ⊔ perp a := by
        calc
          perp b = (perp b ⊓ a) ⊔ (perp b ⊓ perp a) := hcp
          _ = (a ⊓ perp b) ⊔ perp a := by
            rw [inf_eq_right.mpr (hanti hb), inf_comm (perp b) a]
      have hh := congrArg perp heq
      rw [hperp.2.2 b, (hperp.2.1 (a ⊓ perp b) (perp a)).2,
        (hperp.2.1 a (perp b)).1, hperp.2.2 b, hperp.2.2 a] at hh
      simpa only [inf_comm] using hh.symm
    intro a b c hb hc
    have heq : a ⊓ (b ⊔ c) = b := by
      apply le_antisymm
      · calc
          a ⊓ (b ⊔ c) ≤ a ⊓ (b ⊔ perp a) := inf_le_inf_left a (sup_le_sup_left hc b)
          _ = b := by rw [sup_comm b (perp a)]; exact hweak a b hb
      · exact le_inf hb le_sup_left
    rw [heq, inf_eq_right.mpr hb, hinf0 a c hc, sup_bot_eq]
  · intro horth a b hab
    have hpa : perp a = perp (a ⊓ b) ⊓ (perp a ⊔ b) := by
      calc
        perp a = perp ((a ⊓ b) ⊔ (a ⊓ perp b)) := congrArg perp hab
        _ = perp (a ⊓ b) ⊓ (perp a ⊔ b) := by
          rw [(hperp.2.1 (a ⊓ b) (a ⊓ perp b)).2,
            (hperp.2.1 a (perp b)).1, hperp.2.2 b]
    have habp : perp a ⊓ b = perp (a ⊓ b) ⊓ b := by
      conv_lhs => rw [hpa]
      rw [inf_assoc, inf_eq_right.mpr (le_sup_right : b ≤ perp a ⊔ b)]
    have hle : perp b ≤ perp (a ⊓ b) := hanti inf_le_right
    have hz : perp (a ⊓ b) ⊓ (a ⊓ b) = ⊥ := by
      rw [inf_comm]
      exact (hperp.1 (a ⊓ b)).1
    have hd : perp ((a ⊓ b) ⊔ (perp a ⊓ b)) = perp b := by
      calc
        perp ((a ⊓ b) ⊔ (perp a ⊓ b)) =
            perp (a ⊓ b) ⊓ ((a ⊓ b) ⊔ perp b) := by
          rw [habp, (hperp.2.1 (a ⊓ b) (perp (a ⊓ b) ⊓ b)).2,
            (hperp.2.1 (perp (a ⊓ b)) b).1, hperp.2.2 (a ⊓ b)]
        _ = perp b := by
          rw [sup_comm (a ⊓ b) (perp b),
            horth.2 (perp (a ⊓ b)) (perp b) (a ⊓ b) hle
              (by rw [hperp.2.2 (a ⊓ b)]),
            inf_eq_right.mpr hle, hz, sup_bot_eq]
    have heq := hinj hd
    unfold LatticeCommutes
    simpa only [inf_comm] using heq.symm
