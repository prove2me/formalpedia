-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_exists_rename_of_block_6c006f28b61f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:06.929784+00:00
-- url     : https://prove2.me/submissions/27abf2c8-659c-4115-b36b-9f2fbb914c95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_coordDeg_apply_ad5acafbd2e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_one_eq_sum_351aebacb5b4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_blockInj_injective_c45acc126456

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (secM sec IsMultiHomog)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (k₀ : ι) (m : ℕ) (f : MvPolynomial (Coord n) ℤ)
    (hf : IsWeightedHomogeneous (coordDeg n) f (m • Pi.single k₀ 1)) :
    ∃ g : MvPolynomial (Fin (n k₀ + 1)) ℤ, g.IsHomogeneous m ∧
      rename (fun i ↦ (⟨k₀, i⟩ : Coord n)) g = f := by
  obtain ⟨g, rfl⟩ := exists_rename_eq_of_vars_subset_range f _ (blockInj_injective k₀) (by
    rintro ⟨k, i⟩ hv
    obtain ⟨d, hd, hdv⟩ := (mem_vars_iff_mem_support _).mp hv
    have h := congr_fun (hf (mem_support_iff.mp hd)) k
    rw [weight_coordDeg_apply] at h
    by_cases hk : k = k₀
    · subst hk
      exact ⟨i, rfl⟩
    · exfalso
      have h0 : ∑ j, d ⟨k, j⟩ = 0 := by simpa [Pi.single_apply, hk] using h
      exact (Finsupp.mem_support_iff.mp hdv)
        (Finset.sum_eq_zero_iff.mp h0 i (Finset.mem_univ _)))
  refine ⟨g, ?_, rfl⟩
  rw [← IsHomogeneous.rename_isHomogeneous_iff (blockInj_injective k₀)]
  intro d hd
  rw [weight_one_eq_sum, hf hd]
  simp [Pi.single_apply, mul_ite]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
