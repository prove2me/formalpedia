-- Prove2me | solution 1 for WeierstrassCurve.tate_isogeny_theorem_prime_to_char
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-16T07:33:13.068935+00:00
-- url     : https://prove2.me/submissions/48dba4b3-b066-440e-9ea2-d4d14174e7ac

import Mathlib
import Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom
import Theorems.Thm_WeierstrassCurve_mem_rationalHomSet_of_mem_rationalHomSet_baseChange_of_forall_apply_smul
import Theorems.Thm_WeierstrassCurve_exists_ne_zero_and_char_nsmul_eq_zero_of_comp_self_add_smul_eq_smul_of_dvd_of_not_dvd
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_neg_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_eq_comp_of_mem_rationalHomSet_of_char_nsmul_eq_zero
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_finite_rationalHomSet_units
import Definitions.Def_RPLib_S4T_TateProof

set_option autoImplicit false

-- Reduction of 9b26707e to fifteen Proved FLT-project theorems (S4T-Assembly; route scratch/rp/S4T_ROUTE.md).
theorem solution (F : Type) [Field F] [Fintype F]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic]
    (hcard : Nat.card W.toAffine.Point = Nat.card W'.toAffine.Point)
    (hord : ¬ ((ringChar F : ℤ) ∣ ((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)))) :
    ∃ (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
      (g : W.toAffine.FunctionField →ₐ[F] W'.toAffine.FunctionField) (N : ℕ), (N : F) ≠ 0 ∧
      ∃ h : (W.baseChange W.toAffine.FunctionField).toAffine.Nonsingular
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)))
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X)),
        WeierstrassCurve.Affine.Point.map (W' := W.toAffine) (f.comp g)
            (WeierstrassCurve.Affine.Point.some _ _ h) =
          N • WeierstrassCurve.Affine.Point.some _ _ h := by
  exact RPLib.S4T.TateProof.tate_isogeny_theorem_prime_to_char_of_FLT
    @WeierstrassCurve.exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_mem_rationalHomSet
    @WeierstrassCurve.exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul
    @WeierstrassCurve.exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom
    @WeierstrassCurve.mem_rationalHomSet_of_mem_rationalHomSet_baseChange_of_forall_apply_smul
    @WeierstrassCurve.exists_ne_zero_and_char_nsmul_eq_zero_of_comp_self_add_smul_eq_smul_of_dvd_of_not_dvd
    @WeierstrassCurve.surjective_of_mem_rationalHomSet
    @WeierstrassCurve.exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero
    @WeierstrassCurve.exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq
    @WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet
    @WeierstrassCurve.comp_mem_rationalHomSet
    @WeierstrassCurve.add_mem_rationalHomSet
    @WeierstrassCurve.neg_mem_rationalHomSet
    @WeierstrassCurve.comp_eq_comp_of_mem_rationalHomSet_of_char_nsmul_eq_zero
    @WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
    @WeierstrassCurve.finite_rationalHomSet_units
    F W W' hcard hord
