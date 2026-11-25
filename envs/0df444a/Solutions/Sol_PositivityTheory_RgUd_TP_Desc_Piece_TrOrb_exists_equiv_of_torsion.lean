-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.exists_equiv_of_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:54:53.297189+00:00
-- url     : https://prove2.me/submissions/abfbef99-5d60-4483-bc27-06daf7375fab

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
universe u
namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
theorem _root_.solution {k A : Type*} [Field k] [CommRing A] [Algebra k A] [FiniteDimensional k A]
    (I : Ideal A) [I.IsMaximal] (M M' : Type u) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup M'] [Module k M'] [Module A M'] [IsScalarTower k A M'] [FiniteDimensional k M]
    [FiniteDimensional k M'] (hM : Module.IsTorsionBySet A M I) (hM' : Module.IsTorsionBySet A M' I)
    (h : finrank k M = finrank k M') : Nonempty (M ≃ₗ[A] M') := by
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  letI := hM.module
  letI := hM'.module
  have tw : ∀ (P : Type u) [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
      (hP : Module.IsTorsionBySet A P I), @IsScalarTower k (A ⧸ I) P _ hP.module.toSMul _ := by
    intro P _ _ _ _ hP
    letI := hP.module
    refine ⟨fun c x m => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, hP.mk_smul, hP.mk_smul, mul_smul,
      algebraMap_smul]
  haveI := tw M hM
  haveI := tw M' hM'
  haveI : Module.Finite (A ⧸ I) M := Module.Finite.of_restrictScalars_finite k (A ⧸ I) M
  haveI : Module.Finite (A ⧸ I) M' := Module.Finite.of_restrictScalars_finite k (A ⧸ I) M'
  have h1 := Module.finrank_mul_finrank k (A ⧸ I) M
  have h2 := Module.finrank_mul_finrank k (A ⧸ I) M'
  have hpos : 0 < finrank k (A ⧸ I) := Module.finrank_pos
  have hK : finrank (A ⧸ I) M = finrank (A ⧸ I) M' := Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, h2, h])
  let T := LinearEquiv.ofFinrankEq M M' hK
  refine ⟨{ toFun := T
            map_add' := T.map_add
            map_smul' := fun a m => ?_
            invFun := T.symm
            left_inv := T.left_inv
            right_inv := T.right_inv }⟩
  show T (a • m) = a • T m
  rw [← hM.mk_smul, T.map_smul, hM'.mk_smul]
end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
