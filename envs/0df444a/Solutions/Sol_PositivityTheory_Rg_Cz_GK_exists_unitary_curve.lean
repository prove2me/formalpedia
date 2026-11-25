-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.GK.exists_unitary_curve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:34:02.924468+00:00
-- url     : https://prove2.me/submissions/5e08a82c-2af8-4654-93f5-80f1be541a7b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_UnitaryCurves_ExistsUnitaryCurve

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.GK
namespace PositivityTheory.Rg.Cz.GK
theorem _root_.solution {a : ℕ} (Y : Matrix (Fin a) (Fin a) ℂ) (hY : Yᴴ = -Y) :
    ∃ U : ℝ → Matrix (Fin a) (Fin a) ℂ, (∀ t, star (U t) * U t = 1) ∧ U 0 = 1 ∧
      ∀ i j, HasDerivAt (fun t => U t i j) (Y i j) 0 := by
  refine ⟨fun t => NormedSpace.exp (t • Y), fun t => ?_, by simp, fun i j => ?_⟩
  · have h1 : star (NormedSpace.exp (t • Y)) = NormedSpace.exp (-(t • Y)) := by
      rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hY, star_trivial,
        smul_neg]
    rw [h1, Matrix.exp_neg]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))
  · letI : NormedRing (Matrix (Fin a) (Fin a) ℂ) := Matrix.linftyOpNormedRing
    let _ : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) ℂ) := Matrix.linftyOpNormedAlgebra
    let _ : NormedAlgebra ℚ (Matrix (Fin a) (Fin a) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
    let L : Matrix (Fin a) (Fin a) ℂ →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap
        { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
end PositivityTheory.Rg.Cz.GK
