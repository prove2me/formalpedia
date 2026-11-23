-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.infinite_residues
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:12.855683+00:00
-- url     : https://prove2.me/submissions/f8e4bb09-bb58-4315-9464-fed6d2ca618c

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsTorusPointOneLeNormSum
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_mem_unitBallRing
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_residue_eq_zero_iff_norm_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type*} [NormedField K] [IsUltrametricDist K] (K₀ : Subfield K)
    (hK₀ : ResidueFieldInfiniteOn (K₀ : Set K)) :
    {y : IsLocalRing.ResidueField (unitBallRing K) | ∃ x : unitBallRing K,
      (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y}.Infinite := by
  classical
  intro hfin
  have hrep : ∀ y ∈ {y : IsLocalRing.ResidueField (unitBallRing K) | ∃ x : unitBallRing K,
      (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y},
      ∃ x : unitBallRing K, (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y :=
    fun y hy => hy
  choose! r hr using hrep
  unfold ResidueFieldInfiniteOn at hK₀
  obtain ⟨x, hxK, hx1, hxs⟩ := hK₀ (insert 0 (hfin.toFinset.image fun y => (r y : K)))
  have hx0 : 1 ≤ ‖x‖ := by simpa using hxs 0 (Finset.mem_insert_self _ _)
  have hxn : ‖x‖ = 1 := le_antisymm hx1 hx0
  let xb : unitBallRing K := ⟨x, (mem_unitBallRing x).2 hx1⟩
  have hmem : IsLocalRing.residue _ xb ∈ {y : IsLocalRing.ResidueField (unitBallRing K) |
      ∃ x : unitBallRing K, (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y} :=
    ⟨xb, hxK, hxn, rfl⟩
  obtain ⟨-, -, hreq⟩ := hr _ hmem
  have h0 : IsLocalRing.residue _ (xb - r (IsLocalRing.residue _ xb)) = 0 := by
    rw [map_sub, hreq, sub_self]
  rw [residue_eq_zero_iff_norm_lt_one] at h0
  have h0' : ‖x - (r (IsLocalRing.residue _ xb) : K)‖ < 1 := by simpa [xb] using h0
  have h1 := hxs (r (IsLocalRing.residue _ xb) : K)
    (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨_, hfin.mem_toFinset.2 hmem, rfl⟩))
  linarith
end ReciprocityTheory.MultiplicativeHeights
