-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.val_sub_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:15:13.345211+00:00
-- url     : https://prove2.me/submissions/ff9fd761-a7e7-4b02-9935-cee4e2411af4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_NakayamaChar
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IntegralRingEmbedding
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_IntegralRingEmbedding_wt_zero_of_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_IntegralRingEmbedding_mem_intRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_IntegralRingEmbedding_isUnit_of_val_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_IntegralRingEmbedding_val_pos_of_mem_max
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_IntegralRingEmbedding_val_root_unity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
open Module
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
namespace ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
theorem _root_.solution {N : ℕ} (hN : 1 ≤ N) (hvN : v (N : F) = 0) {z z' : F} (hz : z ^ N = 1)
    (hz' : z' ^ N = 1) (hne : z ≠ z') : v (z - z') = 0 := by
  have hvz := val_root_unity v hN hz
  have hvz' := val_root_unity v hN hz'
  have hnn : 0 ≤ v (z - z') :=
    le_trans (le_of_eq (by rw [hvz, hvz', min_self])) (AddValuation.map_sub v z z')
  by_contra hne0
  obtain ⟨Z, rfl⟩ : ∃ Z : intRing v, (Z : F) = z := ⟨⟨z, (mem_intRing v).2 (le_of_eq hvz.symm)⟩, rfl⟩
  obtain ⟨Z', rfl⟩ : ∃ Z' : intRing v, (Z' : F) = z' :=
    ⟨⟨z', (mem_intRing v).2 (le_of_eq hvz'.symm)⟩, rfl⟩
  have hZN : Z ^ N = 1 := Subtype.ext (by simpa using hz)
  have hZ'N : Z' ^ N = 1 := Subtype.ext (by simpa using hz')
  have hmax : Z - Z' ∈ IsLocalRing.maximalIdeal (intRing v) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h3 : ((Z : F) - Z') * (w : F) = 1 := by
      have := congrArg Subtype.val hw
      simpa using this
    have h1 : v ((Z : F) - Z') + v (w : F) = 0 := by
      rw [← AddValuation.map_mul, h3, AddValuation.map_one]
    exact hne0 (wt_zero_of_add hnn ((mem_intRing v).1 w.2) h1)
  have hres : IsLocalRing.residue (intRing v) Z = IsLocalRing.residue (intRing v) Z' := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hmax
  have hsum0 : ∑ i ∈ Finset.range N, Z ^ i * Z' ^ (N - 1 - i) = 0 := by
    have h1 := geom_sum₂_mul Z Z' N
    rw [hZN, hZ'N, sub_self] at h1
    have hne' : Z - Z' ≠ 0 := by
      intro h
      apply hne
      rw [sub_eq_zero] at h
      rw [h]
    exact (mul_eq_zero.1 h1).resolve_right hne'
  have hmap := congrArg (IsLocalRing.residue (intRing v)) hsum0
  rw [map_sum, map_zero] at hmap
  simp only [map_mul, map_pow, ← hres] at hmap
  rw [geom_sum₂_self] at hmap
  have hres0 : IsLocalRing.residue (intRing v) Z ≠ 0 :=
    ((isUnit_of_val_zero v Z hvz).map (IsLocalRing.residue (intRing v))).ne_zero
  have hN0 : ((N : ℕ) : IsLocalRing.ResidueField (intRing v)) = 0 :=
    (mul_eq_zero.1 hmap).resolve_right (pow_ne_zero _ hres0)
  rw [← map_natCast (IsLocalRing.residue (intRing v)) N, IsLocalRing.residue_eq_zero_iff] at hN0
  have hpos := val_pos_of_mem_max v (N : intRing v) hN0
  have hc : ((N : intRing v) : F) = (N : F) := by simp
  rw [hc, hvN] at hpos
  exact lt_irrefl _ hpos
end ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
