-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.lattice_isomorphism_induces_homeomorphism
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:30:47.737355+00:00
-- url     : https://prove2.me/submissions/0ff83fb7-0b8f-489d-b438-69194896abba

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_order_iso_maps_quasipoints
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_topology_properties
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- lattice-isomorphism-spectrum; de Groote, Observables I, PDF p./pp. 55.
-/
theorem solution {L : Type u} {K : Type v} [CompleteLattice L] [CompleteLattice K] (e : L ≃o K) :
    ∃ h : StoneSpectrum L ≃ₜ StoneSpectrum K,
      ∀ B, (h B).val = e '' B.val := by
  classical
  let F : StoneSpectrum L → StoneSpectrum K := fun B =>
    ⟨e '' B.val, order_iso_maps_quasipoints e B.val B.property⟩
  let G : StoneSpectrum K → StoneSpectrum L := fun B =>
    ⟨e.symm '' B.val, order_iso_maps_quasipoints e.symm B.val B.property⟩
  have hGF (B : StoneSpectrum L) : G (F B) = B := by
    apply Subtype.ext
    change e.symm '' (e '' B.val) = B.val
    rw [Set.image_image]
    simp only [Function.comp_def, e.symm_apply_apply, Set.image_id']
  have hFG (B : StoneSpectrum K) : F (G B) = B := by
    apply Subtype.ext
    change e '' (e.symm '' B.val) = B.val
    rw [Set.image_image]
    simp only [Function.comp_def, e.apply_symm_apply, Set.image_id']
  have hF : Continuous F := by
    apply (stone_topology_properties (L := K)).2.2.2.2.1.continuous_iff.mpr
    rintro _ ⟨a, rfl⟩
    have heq : F ⁻¹' stoneBasic a = stoneBasic (e.symm a) := by
      ext B
      change (a ∈ e '' B.val) ↔ e.symm a ∈ B.val
      constructor
      · rintro ⟨x, hx, hxa⟩
        rw [← hxa, e.symm_apply_apply]
        exact hx
      · intro hx
        exact ⟨e.symm a, hx, e.apply_symm_apply a⟩
    rw [heq]
    exact ((stone_topology_properties (L := L)).2.2.2.1 (e.symm a)).2
  have hG : Continuous G := by
    apply (stone_topology_properties (L := L)).2.2.2.2.1.continuous_iff.mpr
    rintro _ ⟨a, rfl⟩
    have heq : G ⁻¹' stoneBasic a = stoneBasic (e a) := by
      ext B
      change (a ∈ e.symm '' B.val) ↔ e a ∈ B.val
      constructor
      · rintro ⟨x, hx, hxa⟩
        rw [← hxa, e.apply_symm_apply]
        exact hx
      · intro hx
        exact ⟨e a, hx, e.symm_apply_apply a⟩
    rw [heq]
    exact ((stone_topology_properties (L := K)).2.2.2.1 (e a)).2
  let h : StoneSpectrum L ≃ₜ StoneSpectrum K :=
    { toFun := F, invFun := G, left_inv := hGF, right_inv := hFG,
      continuous_toFun := hF, continuous_invFun := hG }
  exact ⟨h, fun B => rfl⟩
