-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.fn_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:43.421948+00:00
-- url     : https://prove2.me/submissions/7c227edb-d15a-4df4-acba-52b291a32a51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoeffMatrixZeroCorrectedLineGramPoly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DiagonalCurvatureCoefficient

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology
variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution (t : ℂ) (s : ℝ) :
    fn hm D Y (s • fun _ => t) = ((GnP hm D Y t).det.eval (s : ℂ)).re := by

  have hlin : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ),
      (Polynomial.evalRingHom (s : ℂ)).mapMatrix (lin A) = 1 + (s : ℂ) • A := by
    intro n A
    unfold lin
    rw [map_add, map_one]
    congr 1
    ext i j
    simp
    exact mul_comm _ _
  have hC : (Polynomial.evalRingHom (s : ℂ)).mapMatrix ((Dc D).map Polynomial.C) = Dc D := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
  have hsub : ∀ M : Matrix (Fin r) (Fin r) ℂ[X],
      (Polynomial.evalRingHom (s : ℂ)).mapMatrix (M.submatrix (Fin.castLE hm) (Fin.castLE hm)) =
        ((Polynomial.evalRingHom (s : ℂ)).mapMatrix M).submatrix (Fin.castLE hm) (Fin.castLE hm) :=
    fun M => rfl
  have hst : star ((s : ℂ) * t) = (s : ℂ) * (starRingEnd ℂ) t := by
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  have key : (GnP hm D Y t).map (Polynomial.eval (s : ℂ)) = Gnz hm D Y ((s : ℂ) * t) := by
    change (Polynomial.evalRingHom (s : ℂ)).mapMatrix (GnP hm D Y t) = _
    unfold GnP GP Gnz Gz
    rw [map_mul, map_mul, hsub, map_mul, map_mul, hlin, hlin, hlin, hlin, hC]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, hst, smul_smul, smul_neg, ← sub_eq_add_neg, Matrix.mul_assoc]
  have hs : (s • fun _ : Fin 1 => t) 0 = (s : ℂ) * t := by
    simp [Complex.real_smul]
  unfold fn
  rw [hs, ← key]
  congr 1
  have h := RingHom.map_det (Polynomial.evalRingHom (s : ℂ)) (GnP hm D Y t)
  simpa using h.symm
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
