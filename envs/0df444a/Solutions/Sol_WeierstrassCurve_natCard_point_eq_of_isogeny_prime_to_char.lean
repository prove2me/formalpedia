-- Prove2me | solution 1 for WeierstrassCurve.natCard_point_eq_of_isogeny_prime_to_char
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T15:51:53.672242+00:00
-- url     : https://prove2.me/submissions/9d06d487-65c1-42ef-abd9-42acfd523f58

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateY

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

attribute [local instance] RPLib.Weil.finite_coordinateRing RPLib.Weil.decEqFF

theorem solution (F : Type) [Field F] [Fintype F]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic]
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (g : W.toAffine.FunctionField →ₐ[F] W'.toAffine.FunctionField) (N : ℕ) (hN : (N : F) ≠ 0)
    (hfg : ∃ h : (W.baseChange W.toAffine.FunctionField).toAffine.Nonsingular
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)))
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X)),
        WeierstrassCurve.Affine.Point.map (W' := W.toAffine) (f.comp g)
            (WeierstrassCurve.Affine.Point.some _ _ h) =
          N • WeierstrassCurve.Affine.Point.some _ _ h) :
    Nat.card W.toAffine.Point = Nat.card W'.toAffine.Point := by
  classical
  obtain ⟨h, hfg⟩ := hfg
  have hfg' : Point.map (W' := W.toAffine) (f.comp g) (RPLib.DWS.P0 W) = N • RPLib.DWS.P0 W := hfg
  have := RPLib.DWS.finite_HT (L := AlgebraicClosure F) hN f
  let _ : Fintype (RPLib.DWS.HT (AlgebraicClosure F) N f) := Fintype.ofFinite _
  obtain ⟨n, hn, u, w, hu, -, hwu, -, hfu⟩ :=
    RPLib.DWS.exists_isog_data (L := AlgebraicClosure F) hN f g hfg'
  have hI : RPLib.DWS.IsIsogenous W W' (AlgebraicClosure F) := by
    refine ⟨u, hu, fun hu0 => ?_, hfu⟩
    obtain ⟨P, hP⟩ := RPLib.DWS.exists_nsmul_ne_zero (W := W) (L := AlgebraicClosure F) hn
    apply hP
    rw [← hwu P, hu0, AddMonoidHom.zero_apply, map_zero]
  exact hI.numPoints_eq

