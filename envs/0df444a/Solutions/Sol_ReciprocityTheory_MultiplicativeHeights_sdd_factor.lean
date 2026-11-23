-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:51.094745+00:00
-- url     : https://prove2.me/submissions/e016e7b4-30ec-4430-91ee-c2f2e47354ec

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, A = Bᴴ * B ∧ IsUnit B.det := by
  obtain ⟨B, hB⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef)
  refine ⟨B, hB, ?_⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  have hp := hA.det_pos
  rw [hB, star_eq_conjTranspose, det_mul, h0, mul_zero] at hp
  exact lt_irrefl _ hp
end ReciprocityTheory.MultiplicativeHeights
