-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjArithVar_proof_69b8ee479acc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:33.358712+00:00
-- url     : https://prove2.me/submissions/4a37b937-7d20-4a89-bb86-7384667e459f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_xc_ne_zero_d6f9f1c37a1d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_coord_eq_6fdaee643af6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_aff_indep_da9caeaf1b77

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
open ProjectiveArithmeticVariety
namespace GroundTheory.Heights₂.Heights
namespace ProjArithVar
theorem _root_.solution (h : CoordConeArithVar.Statement) : ProjArithVar.Statement := by
  intro K _ _ i hi
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  obtain ⟨m₀⟩ := (integralBasis K).index_nonempty
  have hω : ∀ m, algebraMap K (ProjField K (n + 1)) (integralBasis K m) / algebraMap K (ProjField K (n + 1)) (integralBasis K m₀) =
      algebraMap K (ProjField K (n + 1)) (integralBasis K m / integralBasis K m₀) := fun m => (map_div₀ _ _ _).symm
  have hω₀ : algebraMap K (ProjField K (n + 1)) (integralBasis K m₀) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K (ProjField K (n + 1))).injective).mpr ((integralBasis K).ne_zero m₀)
  have hx₀ := xc_ne_zero K n 0
  have ratio : ∀ m j, projSpaceCoord K (n + 1) ⟨(), (m, j)⟩ / projSpaceCoord K (n + 1) ⟨(), (m₀, 0)⟩ =
      algebraMap K (ProjField K (n + 1)) (integralBasis K m / integralBasis K m₀) * (xc K n j / xc K n 0) := by
    intro m j
    rw [coord_eq, coord_eq, ← hω]
    field_simp
  show IsArithVar (mCoordIdeal (projSpaceCoord K (n + 1))) (n + 1)
  refine h Unit (projBlocks K (n + 1)) (ProjField K (n + 1)) (projSpaceCoord K (n + 1)) (fun _ => (m₀, 0)) n
    (aff K n) ⟨()⟩ (fun _ => ?_) (aff_indep K n) (fun l => ?_) ?_
  · rw [coord_eq]; exact mul_ne_zero hω₀ hx₀
  · apply IntermediateField.subset_adjoin
    refine ⟨⟨(), (m₀, l.succ)⟩, ?_⟩
    simp only [ratio, div_self ((integralBasis K).ne_zero m₀), map_one, one_mul, aff]
  · rintro r ⟨⟨u, m, j⟩, rfl⟩
    cases u
    show IsAlgebraic _ (projSpaceCoord K (n + 1) ⟨(), (m, j)⟩ / projSpaceCoord K (n + 1) ⟨(), (m₀, 0)⟩)
    rw [ratio]
    refine IsAlgebraic.mul ?_ ?_
    · exact (IsAlgebraic.algebraMap (A := ProjField K (n + 1))
        (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (integralBasis K m / integralBasis K m₀))).tower_top
        (L := IntermediateField.adjoin ℚ (Set.range (aff K n)))
    · have hmem : xc K n j / xc K n 0 ∈ IntermediateField.adjoin ℚ (Set.range (aff K n)) := by
        refine Fin.cases ?_ (fun l => ?_) j
        · rw [div_self hx₀]; exact one_mem _
        · exact IntermediateField.subset_adjoin _ _ ⟨l, rfl⟩
      exact isAlgebraic_algebraMap (R := IntermediateField.adjoin ℚ (Set.range (aff K n)))
        (A := ProjField K (n + 1)) ⟨_, hmem⟩
end ProjArithVar
end GroundTheory.Heights₂.Heights
