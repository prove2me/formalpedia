-- Prove2me | solution 2 for TarchaBraids.prop_3_17_braid_inclusion_injective
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:46:29.726417+00:00
-- url     : https://prove2.me/submissions/c9829833-ac97-4df3-93b6-81a1e6b6c8e1

import Theorems.Thm_TarchaBraids_braid_inclusion_hom_injective
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG TarchaBraids

/-- The far-commutation relation, read off inside the presented group. -/
private theorem incl_rel_comm {n : ℕ} (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
    sigma i * sigma j = sigma j * sigma i := by
  have hr : (FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ * (FreeGroup.of j)⁻¹)
      ∈ braidRels n := Or.inl ⟨i, j, hij, rfl⟩
  have h1 := PresentedGroup.one_of_mem (rels := braidRels n) hr
  simp only [map_mul, map_inv] at h1
  have h2 : sigma i * sigma j * (sigma i)⁻¹ * (sigma j)⁻¹ = 1 := h1
  calc sigma i * sigma j
      = (sigma i * sigma j * (sigma i)⁻¹ * (sigma j)⁻¹) * (sigma j * sigma i) := by group
    _ = 1 * (sigma j * sigma i) := by rw [h2]
    _ = sigma j * sigma i := one_mul _

/-- The braid relation, read off inside the presented group. -/
private theorem incl_rel_braid {n : ℕ} (i j : Fin (n - 1)) (hij : (j : ℕ) = (i : ℕ) + 1) :
    sigma i * sigma j * sigma i = sigma j * sigma i * sigma j := by
  have hr : (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
      (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹) ∈ braidRels n :=
    Or.inr ⟨i, j, hij, rfl⟩
  have h1 := PresentedGroup.one_of_mem (rels := braidRels n) hr
  simp only [map_mul, map_inv] at h1
  have h2 : sigma i * sigma j * sigma i * (sigma j * sigma i * sigma j)⁻¹ = 1 := h1
  calc sigma i * sigma j * sigma i
      = (sigma i * sigma j * sigma i * (sigma j * sigma i * sigma j)⁻¹) *
          (sigma j * sigma i * sigma j) := by group
    _ = 1 * (sigma j * sigma i * sigma j) := by rw [h2]
    _ = sigma j * sigma i * sigma j := one_mul _

theorem _root_.solution {m n : ℕ} (h : m ≤ n) :
    ∃ f : ArtinBraidGroup m →* ArtinBraidGroup n,
      (∀ i : Fin (m - 1), f (sigma i) = sigma (Fin.castLE (Nat.sub_le_sub_right h 1) i)) ∧
      Function.Injective f := by
  have hle : m - 1 ≤ n - 1 := Nat.sub_le_sub_right h 1
  have hrel : ∀ r ∈ braidRels m,
      FreeGroup.lift (fun i : Fin (m - 1) => sigma (Fin.castLE hle i)) r = 1 := by
    intro r hr
    rcases hr with ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩
    · have hij' : 2 ≤ (((((Fin.castLE hle i : Fin (n - 1)) : ℕ) : ℤ) -
          (((Fin.castLE hle j : Fin (n - 1)) : ℕ) : ℤ))).natAbs := by
        simpa using hij
      have hc := incl_rel_comm (Fin.castLE hle i) (Fin.castLE hle j) hij'
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [hc]; group
    · have hij' : ((Fin.castLE hle j : Fin (n - 1)) : ℕ) =
          ((Fin.castLE hle i : Fin (n - 1)) : ℕ) + 1 := by
        simpa using hij
      have hb := incl_rel_braid (Fin.castLE hle i) (Fin.castLE hle j) hij'
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [hb]; group
  have hf : ∀ i : Fin (m - 1),
      PresentedGroup.toGroup hrel (sigma i) = sigma (Fin.castLE hle i) :=
    fun i => PresentedGroup.toGroup.of hrel
  exact ⟨PresentedGroup.toGroup hrel, hf,
    TarchaBraids.braid_inclusion_hom_injective h (PresentedGroup.toGroup hrel) hf⟩

#print axioms solution
