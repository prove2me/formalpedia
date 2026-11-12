-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.distributive_basic_unions
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T04:52:05.804471+00:00
-- url     : https://prove2.me/submissions/b5eff54e-c414-49e1-aa88-adc6c7b3ca87

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_filter_base_extends_to_quasipoint
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- rem-3.1; de Groote, Observables I, PDF p./pp. 43.
-/
theorem solution {L : Type u} [Lattice L] [BoundedOrder L] :
    (IsDistributive (L := L) → ∀ a b : L, stoneBasic a ∪ stoneBasic b = stoneBasic (a ⊔ b)) ∧
    ((∀ a b : L, stoneBasic a ∪ stoneBasic b = stoneBasic (a ⊔ b)) →
      ∀ a b c : L, stoneBasic ((a ⊓ b) ⊔ (a ⊓ c)) = stoneBasic (a ⊓ (b ⊔ c))) := by
  classical
  have hmeet (a b : L) : stoneBasic (a ⊓ b) = stoneBasic a ∩ stoneBasic b := by
    ext B
    change (a ⊓ b ∈ B.val) ↔ a ∈ B.val ∧ b ∈ B.val
    have hc := quasipoint_upward_and_meet_closed B.val B.property
    exact ⟨fun h => ⟨hc.1 (a ⊓ b) h a inf_le_left,
      hc.1 (a ⊓ b) h b inf_le_right⟩, fun h => hc.2 a h.1 b h.2⟩
  have avoid (B : Set L) (hB : IsQuasipoint B) (a : L) (ha : a ∉ B) :
      ∃ c ∈ B, c ⊓ a = ⊥ := by
    by_contra hn
    push_neg at hn
    obtain ⟨b0, hb0⟩ := hB.1.1
    let D : Set L := {x | ∃ b ∈ B, x = b ⊓ a}
    have hD : IsFilterBase D := by
      refine ⟨⟨b0 ⊓ a, b0, hb0, rfl⟩, ?_, ?_⟩
      · rintro ⟨b, hb, he⟩
        exact hn b hb he.symm
      · rintro x ⟨b, hb, hx⟩ y ⟨c, hc, hy⟩
        subst x
        subst y
        obtain ⟨d, hd, hdb, hdc⟩ := hB.1.2.2 b hb c hc
        exact ⟨d ⊓ a, ⟨d, hd, rfl⟩, inf_le_inf_right a hdb, inf_le_inf_right a hdc⟩
    obtain ⟨C, hC, hDC⟩ := filter_base_extends_to_quasipoint D hD
    have hcup := quasipoint_upward_and_meet_closed C hC
    have hBC : B ⊆ C := by
      intro b hb
      exact hcup.1 (b ⊓ a) (hDC ⟨b, hb, rfl⟩) b inf_le_left
    have haC : a ∈ C := hcup.1 (b0 ⊓ a) (hDC ⟨b0, hb0, rfl⟩) a inf_le_right
    have hCB : C = B := hB.2 C hC.1 hBC
    apply ha
    simpa only [hCB] using haC
  constructor
  · intro hD a b
    ext B
    change (a ∈ B.val ∨ b ∈ B.val) ↔ a ⊔ b ∈ B.val
    have hc := quasipoint_upward_and_meet_closed B.val B.property
    constructor
    · rintro (ha | hb)
      · exact hc.1 a ha (a ⊔ b) le_sup_left
      · exact hc.1 b hb (a ⊔ b) le_sup_right
    · intro hab
      by_cases ha : a ∈ B.val
      · exact Or.inl ha
      · obtain ⟨c, hcmem, hca⟩ := avoid B.val B.property a ha
        have hh := hc.2 c hcmem (a ⊔ b) hab
        rw [hD.1 c a b, hca, bot_sup_eq] at hh
        exact Or.inr (hc.1 (c ⊓ b) hh b inf_le_right)
  · intro h a b c
    rw [← h (a ⊓ b) (a ⊓ c), hmeet a b, hmeet a c, hmeet a (b ⊔ c), ← h b c]
    exact (Set.inter_union_distrib_left (stoneBasic a) (stoneBasic b) (stoneBasic c)).symm
