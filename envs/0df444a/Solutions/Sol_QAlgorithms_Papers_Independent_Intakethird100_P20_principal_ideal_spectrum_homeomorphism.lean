-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.principal_ideal_spectrum_homeomorphism
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T17:17:14.412258+00:00
-- url     : https://prove2.me/submissions/5107d16a-cd7f-4c98-aff8-0b9330cbc5f0

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_restrict_principal_ideal
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_extend_principal_ideal
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_topology_properties
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- principal-ideal-spectrum; de Groote, Observables I, PDF p./pp. 66.
-/
theorem solution {L : Type u} [Lattice L] [BoundedOrder L] (a : L) (ha : a ≠ ⊥) :
    letI : Bot (Set.Iic a) := ⟨⟨⊥, bot_le⟩⟩
    ∃ h : (stoneBasic a) ≃ₜ StoneSpectrum (Set.Iic a),
      (∀ B, (h B).val = {b | b.val ∈ B.val.val}) ∧
      (∀ C, (h.symm C).val.val = {b | ∃ c ∈ C.val, c.val ≤ b}) := by
  classical
  letI : Bot (Set.Iic a) := ⟨⟨⊥, bot_le⟩⟩
  let F : (stoneBasic a) → StoneSpectrum (Set.Iic a) := fun B =>
    ⟨{b | b.val ∈ B.val.val}, quasipoint_restrict_principal_ideal a B.val B.property⟩
  let G : StoneSpectrum (Set.Iic a) → (stoneBasic a) := fun C =>
    ⟨⟨{b | ∃ c ∈ C.val, c.val ≤ b}, quasipoint_extend_principal_ideal a C⟩,
      by obtain ⟨c, hc⟩ := C.property.1.1; exact ⟨c, hc, c.property⟩⟩
  have hGF (B : stoneBasic a) : G (F B) = B := by
    apply Subtype.ext
    apply Subtype.ext
    apply Set.Subset.antisymm
    · rintro x ⟨c, hc, hcx⟩
      exact (quasipoint_upward_and_meet_closed B.val.val B.val.property).1 c.val hc x hcx
    · intro x hx
      have hax := (quasipoint_upward_and_meet_closed B.val.val B.val.property).2
        a B.property x hx
      exact ⟨⟨a ⊓ x, inf_le_left⟩, hax, inf_le_right⟩
  have hFG (C : StoneSpectrum (Set.Iic a)) : F (G C) = C := by
    apply Subtype.ext
    have hR := quasipoint_restrict_principal_ideal a (G C).val (G C).property
    apply C.property.2 _ hR.1
    intro c hc
    exact ⟨c, hc, le_rfl⟩
  have ht := stone_topology_properties (L := L)
  have hF : Continuous F := by
    change @Continuous _ _ _ (TopologicalSpace.generateFrom
      (Set.range (stoneBasic : Set.Iic a → Set (StoneSpectrum (Set.Iic a))))) F
    rw [continuous_generateFrom_iff]
    rintro _ ⟨b, rfl⟩
    change IsOpen ((fun B : stoneBasic a => B.val) ⁻¹' stoneBasic b.val)
    exact ((ht.2.2.2.1 b.val).2).preimage continuous_subtype_val
  have hG0 : Continuous (fun C : StoneSpectrum (Set.Iic a) => (G C).val) := by
    change @Continuous _ _ _ (TopologicalSpace.generateFrom
      (Set.range (stoneBasic : L → Set (StoneSpectrum L)))) _
    rw [continuous_generateFrom_iff]
    rintro _ ⟨b, rfl⟩
    have heq : (fun C : StoneSpectrum (Set.Iic a) => (G C).val) ⁻¹' stoneBasic b =
        ⋃ c : Set.Iic a, ⋃ (_ : c.val ≤ b), stoneBasic c := by
      ext C
      change (∃ c ∈ C.val, c.val ≤ b) ↔ C ∈ ⋃ c : Set.Iic a, ⋃ (_ : c.val ≤ b), stoneBasic c
      simp only [Set.mem_iUnion]
      exact ⟨fun ⟨c, hc, hcb⟩ => ⟨c, hcb, hc⟩, fun ⟨c, hcb, hc⟩ => ⟨c, hc, hcb⟩⟩
    rw [heq]
    exact isOpen_iUnion fun c => isOpen_iUnion fun _ =>
      TopologicalSpace.isOpen_generateFrom_of_mem ⟨c, rfl⟩
  have hG : Continuous G := hG0.subtype_mk (fun C => (G C).property)
  let h : (stoneBasic a) ≃ₜ StoneSpectrum (Set.Iic a) :=
    { toFun := F, invFun := G, left_inv := hGF, right_inv := hFG,
      continuous_toFun := hF, continuous_invFun := hG }
  exact ⟨h, fun B => rfl, fun C => rfl⟩
