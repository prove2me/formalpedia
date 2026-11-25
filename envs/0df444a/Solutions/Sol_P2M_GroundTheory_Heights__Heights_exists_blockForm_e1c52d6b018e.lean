-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_blockForm_e1c52d6b018e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:21.851785+00:00
-- url     : https://prove2.me/submissions/4d99ba65-18b3-4654-8a9a-9f0da785f5df

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VarsSubsetRangeBlockIncl
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockIncl_injective_ce1f2084d84c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_vars_subset_range_blockIncl_db764e5cfd8d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (k₀ : ι) (m : ℕ) (f : MvPolynomial (Coord n) ℤ)
    (hf : IsWeightedHomogeneous (coordDeg n) f (m • Pi.single k₀ 1)) :
    ∃ f' : MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ,
      IsWeightedHomogeneous (coordDeg (fun _ : Unit ↦ n k₀)) f' (fun _ ↦ m) ∧
        rename (blockIncl k₀) f' = f := by
  classical
  obtain ⟨f', rfl⟩ := exists_rename_eq_of_vars_subset_range f (blockIncl k₀)
    (blockIncl_injective k₀) (vars_subset_range_blockIncl k₀ m f hf)
  refine ⟨f', fun d hd ↦ ?_, rfl⟩
  have hmem : Finsupp.mapDomain (blockIncl k₀) d ∈ (rename (blockIncl k₀) f').support := by
    rw [support_rename_of_injective (blockIncl_injective k₀)]
    exact Finset.mem_image_of_mem _ (mem_support_iff.mpr hd)
  have hw := hf (mem_support_iff.mp hmem)
  have hw' : Finsupp.weight (coordDeg n) (Finsupp.mapDomain (blockIncl k₀) d) =
      Finsupp.degree d • Pi.single k₀ 1 := by
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) ↦ c • coordDeg n i)
      (fun _ ↦ zero_smul ℕ _) (fun _ _ _ ↦ add_smul _ _ _)]
    simp only [Finsupp.sum, coordDeg, blockIncl]
    rw [show Finsupp.degree d = ∑ i ∈ d.support, d i from rfl, Finset.sum_smul]
  rw [hw'] at hw
  have hdeg : Finsupp.degree d = m := by
    simpa using congrFun hw k₀
  funext u
  rw [Finsupp.weight_apply]
  simp [Finsupp.sum, coordDeg, Finsupp.degree] at hdeg ⊢
  exact hdeg
end GroundTheory.Heights₂.Heights
