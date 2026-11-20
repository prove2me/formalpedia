-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P58.reversal_anti_involution
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T11:23:06.145631+00:00
-- url     : https://prove2.me/submissions/c47a9255-fdaa-463d-a822-6db61ba89c71

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P58
noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intake100.P58

open Accepted

variable {R : Type*} [CommRing R] {k : ℕ}

open QAlgorithms.Papers.Independent.Gap48.P01 in
/-- reversal on the free algebra -/
def AuxRV_rev (R : Type*) [CommRing R] :
    FreeAlgebra R (CyclotomicLetter 2) →ₐ[R] (FreeAlgebra R (CyclotomicLetter 2))ᵐᵒᵖ :=
  FreeAlgebra.lift R (fun l => MulOpposite.op (FreeAlgebra.ι R l))

section
open QAlgorithms.Papers.Independent.Gap48.P01

theorem AuxRV_X (i : ℕ) (inv : Bool) :
    MulOpposite.unop (AuxRV_rev R (nonsplitFreeX R 2 i inv)) = nonsplitFreeX R 2 i inv := by
  unfold nonsplitFreeX; split_ifs <;> simp [AuxRV_rev]

theorem AuxRV_E (i : ℕ) :
    MulOpposite.unop (AuxRV_rev R (nonsplitFreeE R 2 i)) = nonsplitFreeE R 2 i := by
  unfold nonsplitFreeE; split_ifs <;> simp [AuxRV_rev]

theorem AuxRV_Y (inv : Bool) :
    MulOpposite.unop (AuxRV_rev R (nonsplitFreeY R 2 inv)) = nonsplitFreeY R 2 inv := by
  unfold nonsplitFreeY; split_ifs <;> simp [AuxRV_rev]

theorem AuxRV_rel (P : NonsplitParameters R k) ⦃a b : FreeAlgebra R (CyclotomicLetter 2)⦄
    (h : NonsplitBMWRel P 2 a b) :
    RingQuot.mkAlgHom R (NonsplitBMWRel P 2) (MulOpposite.unop (AuxRV_rev R a)) =
      RingQuot.mkAlgHom R (NonsplitBMWRel P 2) (MulOpposite.unop (AuxRV_rev R b)) := by
  have mk := fun {a b} (h : NonsplitBMWRel P 2 a b) => RingQuot.mkAlgHom_rel R h
  cases h with
  | invL i hi => simpa [AuxRV_X] using mk (NonsplitBMWRel.invR i hi)
  | invR i hi => simpa [AuxRV_X] using mk (NonsplitBMWRel.invL i hi)
  | yInvL hn => simpa [AuxRV_Y] using mk (NonsplitBMWRel.yInvR hn)
  | yInvR hn => simpa [AuxRV_Y] using mk (NonsplitBMWRel.yInvL hn)
  | skein i hi =>
    have := mk (NonsplitBMWRel.skein i hi)
    simp only [map_sub, map_mul, map_one, MulOpposite.unop_sub, MulOpposite.unop_mul,
      MulOpposite.unop_one, AuxRV_X, AuxRV_E, AlgHom.commutes, MulOpposite.algebraMap_apply,
      MulOpposite.unop_op]
    rw [← Algebra.commutes]
    simp only [map_mul, map_sub, map_one, map_pow, map_sum, AlgHom.commutes, mul_assoc] at this ⊢
    exact this
  | xFar i j hi hj hd => exfalso; omega
  | braid i hi => exfalso; omega
  | xeFar i j hi hj hd => exfalso; omega
  | eeFar i j hi hj hd => exfalso; omega
  | xe i hi =>
    have := mk (NonsplitBMWRel.ex i hi)
    simp only [map_mul, MulOpposite.unop_mul, AuxRV_X, AuxRV_E, AlgHom.commutes,
      MulOpposite.algebraMap_apply, MulOpposite.unop_op]
    rw [← Algebra.commutes]
    simp only [map_mul, map_sub, map_one, map_pow, map_sum, AlgHom.commutes, mul_assoc] at this ⊢
    exact this
  | ex i hi =>
    have := mk (NonsplitBMWRel.xe i hi)
    simp only [map_mul, MulOpposite.unop_mul, AuxRV_X, AuxRV_E, AlgHom.commutes,
      MulOpposite.algebraMap_apply, MulOpposite.unop_op]
    rw [← Algebra.commutes]
    simp only [map_mul, map_sub, map_one, map_pow, map_sum, AlgHom.commutes, mul_assoc] at this ⊢
    exact this
  | nearL i j hi hj hd => exfalso; omega
  | nearR i j hi hj hd => exfalso; omega
  | tripleE i j hi hj hd => exfalso; omega
  | squareE i hi =>
    have := mk (NonsplitBMWRel.squareE i hi)
    simp only [map_mul, map_pow, MulOpposite.unop_mul, MulOpposite.unop_pow, AuxRV_E,
      AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op]
    rw [← Algebra.commutes]
    simp only [map_mul, map_sub, map_one, map_pow, map_sum, AlgHom.commutes, mul_assoc] at this ⊢
    exact this
  | cyclotomic hn =>
    have := mk (NonsplitBMWRel.cyclotomic (P := P) hn)
    simp only [map_mul, map_pow, map_sum, MulOpposite.unop_mul, MulOpposite.unop_pow,
      Finset.unop_sum, AuxRV_Y, AlgHom.commutes, MulOpposite.algebraMap_apply,
      MulOpposite.unop_op]
    simp_rw [← Algebra.commutes]
    simp only [map_mul, map_sub, map_one, map_pow, map_sum, AlgHom.commutes, mul_assoc] at this ⊢
    exact this
  | affine hn =>
    have := mk (NonsplitBMWRel.affine (P := P) hn)
    simp only [map_mul, MulOpposite.unop_mul, AuxRV_X, AuxRV_Y]
    simp only [map_mul, map_sub, map_one, map_pow, map_sum, AlgHom.commutes, mul_assoc] at this ⊢
    exact this.symm
  | yx i hi => exfalso; omega
  | ye i hi => exfalso; omega
  | unwrapL hn =>
    have := mk (NonsplitBMWRel.unwrapR (P := P) hn)
    simp only [map_mul, MulOpposite.unop_mul, AuxRV_X, AuxRV_Y, AuxRV_E, AlgHom.commutes,
      MulOpposite.algebraMap_apply, MulOpposite.unop_op]
    rw [← Algebra.commutes]
    simp only [map_mul, map_sub, map_one, map_pow, map_sum, AlgHom.commutes, mul_assoc] at this ⊢
    exact this
  | unwrapR hn =>
    have := mk (NonsplitBMWRel.unwrapL (P := P) hn)
    simp only [map_mul, MulOpposite.unop_mul, AuxRV_X, AuxRV_Y, AuxRV_E, AlgHom.commutes,
      MulOpposite.algebraMap_apply, MulOpposite.unop_op]
    rw [← Algebra.commutes]
    simp only [map_mul, map_sub, map_one, map_pow, map_sum, AlgHom.commutes, mul_assoc] at this ⊢
    exact this
  | loop m hn =>
    have := mk (NonsplitBMWRel.loop (P := P) m hn)
    simp only [map_mul, map_pow, MulOpposite.unop_mul, MulOpposite.unop_pow, AuxRV_Y, AuxRV_E,
      AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op]
    rw [← Algebra.commutes]
    simp only [map_mul, map_sub, map_one, map_pow, map_sum, AlgHom.commutes, mul_assoc] at this ⊢
    exact this

/-- the forward map -/
def AuxRV_sf (P : NonsplitParameters R k) : TwoStrandBMW P →ₐ[R] (TwoStrandBMW P)ᵐᵒᵖ :=
  RingQuot.liftAlgHom R ⟨(AlgHom.op (RingQuot.mkAlgHom R (NonsplitBMWRel P 2))).comp (AuxRV_rev R),
    fun a b h => by
      simp only [AlgHom.comp_apply, AlgHom.op_apply_apply]
      rw [AuxRV_rel P h]⟩

theorem AuxRV_sf_mk (P : NonsplitParameters R k) (a : FreeAlgebra R (CyclotomicLetter 2)) :
    AuxRV_sf P (RingQuot.mkAlgHom R (NonsplitBMWRel P 2) a) =
      MulOpposite.op (RingQuot.mkAlgHom R (NonsplitBMWRel P 2) (MulOpposite.unop (AuxRV_rev R a))) := by
  simp [AuxRV_sf, RingQuot.liftAlgHom_mkAlgHom_apply]

theorem AuxRV_invol (P : NonsplitParameters R k) (a : TwoStrandBMW P) :
    MulOpposite.unop (AuxRV_sf P (MulOpposite.unop (AuxRV_sf P a))) = a := by
  let g : TwoStrandBMW P →ₐ[R] TwoStrandBMW P :=
    (AlgEquiv.opOp R (TwoStrandBMW P)).symm.toAlgHom.comp ((AlgHom.op (AuxRV_sf P)).comp (AuxRV_sf P))
  have hg : ∀ a, g a = MulOpposite.unop (AuxRV_sf P (MulOpposite.unop (AuxRV_sf P a))) := fun a => rfl
  have : g = AlgHom.id R _ := by
    apply RingQuot.ringQuot_ext'
    refine FreeAlgebra.hom_ext (funext fun l => ?_)
    change g (RingQuot.mkAlgHom R _ (FreeAlgebra.ι R l)) = RingQuot.mkAlgHom R _ (FreeAlgebra.ι R l)
    rw [hg, AuxRV_sf_mk]
    simp only [AuxRV_rev, FreeAlgebra.lift_ι_apply, MulOpposite.unop_op]
    rw [AuxRV_sf_mk]
    simp [AuxRV_rev]
  rw [← hg, this]; rfl

end

theorem _root_.solution (P : NonsplitParameters R k) (hdelta : RegularDelta P) :
    ∃ star : TwoStrandBMW P ≃ₐ[R] (TwoStrandBMW P)ᵐᵒᵖ,
      (∀ a, MulOpposite.unop (star (MulOpposite.unop (star a))) = a) ∧
      star (y P) = MulOpposite.op (y P) ∧
      star (x P) = MulOpposite.op (x P) ∧
      star (e P) = MulOpposite.op (e P) := by
  let g : (TwoStrandBMW P)ᵐᵒᵖ →ₐ[R] TwoStrandBMW P :=
    (AlgEquiv.opOp R (TwoStrandBMW P)).symm.toAlgHom.comp (AlgHom.op (AuxRV_sf P))
  have hg : ∀ z, g z = MulOpposite.unop (AuxRV_sf P (MulOpposite.unop z)) := fun z => rfl
  refine ⟨AlgEquiv.ofAlgHom (AuxRV_sf P) g ?_ ?_, fun a => AuxRV_invol P a, ?_, ?_, ?_⟩
  · ext z
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hg]
    apply MulOpposite.unop_injective
    exact AuxRV_invol P _
  · refine AlgHom.ext fun z => ?_
    rw [AlgHom.comp_apply, AlgHom.id_apply, hg]
    exact AuxRV_invol P _
  · show AuxRV_sf P (RingQuot.mkAlgHom R _ _) = _
    rw [AuxRV_sf_mk, AuxRV_Y]; rfl
  · show AuxRV_sf P (RingQuot.mkAlgHom R _ _) = _
    rw [AuxRV_sf_mk, AuxRV_X]; rfl
  · show AuxRV_sf P (RingQuot.mkAlgHom R _ _) = _
    rw [AuxRV_sf_mk, AuxRV_E]; rfl

end QAlgorithms.Papers.Independent.Intake100.P58

end
