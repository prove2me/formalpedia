-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily_eq_of_isFullRankFamily
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:03:34.637985+00:00
-- url     : https://prove2.me/submissions/422b0b50-c453-426b-b331-83c237e4964f

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStB
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_degreeOfFamily_linearCombination
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_IsFrame_relIndex_span_frame_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (h : HermFam K V) {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ}
    {v v' : Fin r → V} (hv : IsFrame K E v) (hv' : IsFrame K E v') :
    degreeOfFamily h E v = degreeOfFamily h E v' := by
  classical
  obtain ⟨hvE, hvli, hvsp⟩ := hv
  obtain ⟨hv'E, hv'li, hv'sp⟩ := hv'
  have hneV := IsFrame.relIndex_span_frame_ne_zero hE ⟨hvE, hvli, hvsp⟩
  have hneV' := IsFrame.relIndex_span_frame_ne_zero hE ⟨hv'E, hv'li, hv'sp⟩
  have hc : ∀ j, ∃ c : Fin r → K, ∑ i, c i • v i = v' j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun K).1 (hvsp (hv'E j))
  choose c hc using hc
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (Finset.univ.image fun p : Fin r × Fin r => c p.2 p.1)
  have hint : ∀ i j, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = (b : 𝓞 K) • c j i := fun i j =>
    hb _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
  choose gm hgm using hint
  have hb0 : (b : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  let g : Matrix (Fin r) (Fin r) (𝓞 K) := Matrix.of gm
  let g₂ : Matrix (Fin r) (Fin r) (𝓞 K) := Matrix.diagonal fun _ => (b : 𝓞 K)
  have hu : (fun j => ∑ i, g i j • v i) = fun j => (b : 𝓞 K) • v' j := by
    funext j
    rw [← hc j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show gm i j • v i = (b : 𝓞 K) • (c j i • v i)
    rw [← algebraMap_smul K (gm i j) (v i), hgm, smul_assoc]
  have hu2 : (fun j => ∑ i, g₂ i j • v' i) = fun j => (b : 𝓞 K) • v' j := by
    funext j
    simp [g₂, Matrix.diagonal_apply, ite_smul]
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hb0
  have huli : LinearIndependent K fun j => (b : 𝓞 K) • v' j := by
    have e1 : (fun j => (b : 𝓞 K) • v' j) = fun j => ((Units.mk0 _ hbK : Kˣ) : K) • v' j := by
      funext j
      rw [Units.val_mk0, algebraMap_smul]
    rw [e1]
    exact hv'li.units_smul fun _ => Units.mk0 _ hbK
  have e1 := degreeOfFamily_linearCombination h E hvli g (by rw [hu]; exact huli)
    (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hvE i)) hneV
  have e2 := degreeOfFamily_linearCombination h E hv'li g₂ (by rw [hu2]; exact huli)
    (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hv'E i)) hneV'
  rw [← e1, ← e2, hu, hu2]
end ReciprocityTheory.GeometryOfNumbersTheory
