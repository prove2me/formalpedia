-- Prove2me | solution 1 for WeierstrassCurve.isSeparable_torsion_coords_and_torsionBy_of_isSepClosed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-14T01:15:57.503281+00:00
-- url     : https://prove2.me/submissions/d29060a5-e0a7-40f3-ba3f-8108a0031866

import Mathlib
import Definitions.Def_RPLib_S2_Torsion

set_option autoImplicit false

namespace UploadTorsion

open WeierstrassCurve WeierstrassCurve.Affine

/-- Separability of the coordinates of `n`-torsion points over any extension `L / K`, and, when `L` is
separably closed, `#E(L)[n] = n²` and `E(L)[n] ≃+ (ℤ/n)²`, from the library file `RPLib.Torsion`. -/
theorem main {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] [DecidableEq L]
    (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    (∀ {x y : L} (h : (W.baseChange L).toAffine.Nonsingular x y),
        n • (WeierstrassCurve.Affine.Point.some x y h : (W.baseChange L).toAffine.Point) = 0 →
          IsSeparable K x ∧ IsSeparable K y) ∧
      (IsSepClosed L →
        Nat.card (Submodule.torsionBy ℤ (W.baseChange L).toAffine.Point n) = n ^ 2 ∧
          Nonempty (Submodule.torsionBy ℤ (W.baseChange L).toAffine.Point n ≃+ ZMod n × ZMod n)) := by
  classical
  refine ⟨fun {x y} h hP => ?_, fun hL => ?_⟩
  · -- embed `L` into its algebraic closure `M`, which is separably closed
    let f : L →ₐ[K] AlgebraicClosure L := IsScalarTower.toAlgHom K L (AlgebraicClosure L)
    have h' : (W.baseChange (AlgebraicClosure L)).toAffine.Nonsingular (f x) (f y) :=
      (W.toAffine.baseChange_nonsingular f.injective x y).mpr h
    have hP' : (WeierstrassCurve.Affine.Point.some (f x) (f y) h' :
        (W.baseChange (AlgebraicClosure L)).toAffine.Point) ∈
          RPLib.Torsion.tors (W.baseChange (AlgebraicClosure L)) n := by
      rw [RPLib.Torsion.mem_tors]
      have hm := congrArg (WeierstrassCurve.Affine.Point.map (W' := W.toAffine) f) hP
      rw [map_nsmul, map_zero] at hm
      exact hm
    obtain ⟨hx, hy⟩ := RPLib.Torsion.tors_coords_separable W (AlgebraicClosure L) n hn h' hP'
    exact ⟨hx.of_algHom f, hy.of_algHom f⟩
  · have := hL
    have e : Submodule.torsionBy ℤ (W.baseChange L).toAffine.Point n ≃+
        RPLib.Torsion.tors (W.baseChange L) n :=
      { toFun := fun P => ⟨P.1, by
          have hP := P.2
          rw [Submodule.mem_torsionBy_iff, natCast_zsmul] at hP
          exact hP⟩
        invFun := fun P => ⟨P.1, by
          rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
          exact P.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }
    refine ⟨?_, ?_⟩
    · rw [Nat.card_congr e.toEquiv]
      exact RPLib.Torsion.card_tors_baseChange W L n hn
    · obtain ⟨g⟩ := RPLib.Torsion.tors_equiv_baseChange W L n hn
      exact ⟨e.trans g⟩

end UploadTorsion

theorem solution {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] [DecidableEq L]
    (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    (∀ {x y : L} (h : (W.baseChange L).toAffine.Nonsingular x y),
        n • (WeierstrassCurve.Affine.Point.some x y h : (W.baseChange L).toAffine.Point) = 0 →
          IsSeparable K x ∧ IsSeparable K y) ∧
      (IsSepClosed L →
        Nat.card (Submodule.torsionBy ℤ (W.baseChange L).toAffine.Point n) = n ^ 2 ∧
          Nonempty (Submodule.torsionBy ℤ (W.baseChange L).toAffine.Point n ≃+ ZMod n × ZMod n)) := by
  exact UploadTorsion.main W hn

