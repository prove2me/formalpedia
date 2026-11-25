-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_span_basis_formNorm_le_4126249bc729
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:56:17.25537+00:00
-- url     : https://prove2.me/submissions/acf8b2a4-5f86-4005-98c4-0b7193b84261

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LatticePointLogCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
theorem _root_.solution (n : ℕ) :
    ∃ G : Set (Fin n → ℤ), Submodule.span ℤ G = ⊤ ∧
      ∀ u ∈ G, formNorm (1 : Matrix (Fin n) (Fin n) ℂ) (fun i => (u i : ℂ)) ≤ 1 := by
  classical
  refine ⟨Set.range fun i => Pi.single i 1, ?_, ?_⟩
  · have h : (fun i : Fin n => (Pi.single i (1 : ℤ) : Fin n → ℤ)) = ⇑(Pi.basisFun ℤ (Fin n)) := by
      ext i j
      simp [Pi.basisFun_apply]
    rw [h]
    exact (Pi.basisFun ℤ (Fin n)).span_eq
  · rintro _ ⟨i, rfl⟩
    have hv : (fun j => ((Pi.single i (1 : ℤ) : Fin n → ℤ) j : ℂ)) = Pi.single i 1 := by
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [formNorm, hv, inv_one, transpose_one, one_mulVec, EuclideanSpace.norm_eq]
    simp [Pi.single_apply, apply_ite]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
