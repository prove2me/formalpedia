-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P65.affineStar
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-21T21:13:07.494852+00:00
-- url     : https://prove2.me/submissions/5ea67ba1-a6f6-4ee0-b165-702234ff35c9

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

section AuxAS
variable (R : Type u) [CommRing R] (omega : ℕ → R) (n : ℕ)

local notation "mm" => RingQuot.mkAlgHom R (BMWRel R omega n)

lemma AuxAS_mS (i : ℕ) : mm (freeS R n i) = affineS R omega n i := rfl
lemma AuxAS_mE (i : ℕ) : mm (freeE R n i) = affineE R omega n i := rfl
lemma AuxAS_mX (i : ℕ) : mm (freeX R n i) = affineX R omega n i := rfl

def AuxAS_tau : FreeAlgebra R (BMWLetter n) →ₐ[R] (AffineBMW R omega n)ᵐᵒᵖ :=
  FreeAlgebra.lift R (fun l => MulOpposite.op (mm (FreeAlgebra.ι R l)))

lemma AuxAS_tS (i : ℕ) : AuxAS_tau R omega n (freeS R n i) = MulOpposite.op (affineS R omega n i) := by
  rw [← AuxAS_mS]; unfold freeS; split_ifs <;> simp [AuxAS_tau]
lemma AuxAS_tE (i : ℕ) : AuxAS_tau R omega n (freeE R n i) = MulOpposite.op (affineE R omega n i) := by
  rw [← AuxAS_mE]; unfold freeE; split_ifs <;> simp [AuxAS_tau]
lemma AuxAS_tX (i : ℕ) : AuxAS_tau R omega n (freeX R n i) = MulOpposite.op (affineX R omega n i) := by
  rw [← AuxAS_mX]; unfold freeX; split_ifs <;> simp [AuxAS_tau]

lemma AuxAS_rel : ∀ ⦃a b⦄, BMWRel R omega n a b → AuxAS_tau R omega n a = AuxAS_tau R omega n b := by
  intro a b h
  apply MulOpposite.unop_injective
  cases h with
  | involution i hi =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.involution (omega := omega) i hi)
    simp only [map_pow, map_one, AuxAS_mS] at h
    simp only [map_pow, map_one, AuxAS_tS, MulOpposite.unop_pow, MulOpposite.unop_op, MulOpposite.unop_one]
    exact h
  | braidFar i j hi hj hd =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.braidFar (omega := omega) j i hj hi hd.symm)
    simp only [map_mul, AuxAS_mS] at h
    simp only [map_mul, AuxAS_tS, MulOpposite.unop_mul, MulOpposite.unop_op]
    exact h
  | braidNear i hi =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.braidNear (omega := omega) i hi)
    simp only [map_mul, AuxAS_mS] at h
    simp only [map_mul, AuxAS_tS, MulOpposite.unop_mul, MulOpposite.unop_op]
    simpa only [mul_assoc] using h
  | sx i j hi hj hji hji1 =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.sx (omega := omega) i j hi hj hji hji1)
    simp only [map_mul, AuxAS_mS, AuxAS_mX] at h
    simp only [map_mul, AuxAS_tS, AuxAS_tX, MulOpposite.unop_mul, MulOpposite.unop_op]
    exact h.symm
  | idempotent i hi =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.idempotent (omega := omega) i hi)
    simp only [map_pow, map_mul, AlgHom.commutes, AuxAS_mE] at h
    simp only [map_pow, map_mul, AlgHom.commutes, AuxAS_tE, MulOpposite.unop_pow, MulOpposite.unop_mul,
      MulOpposite.unop_op, MulOpposite.algebraMap_apply]
    rw [h, Algebra.commutes]
  | seFar i j hi hj hd =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.seFar (omega := omega) i j hi hj hd)
    simp only [map_mul, AuxAS_mS, AuxAS_mE] at h
    simp only [map_mul, AuxAS_tS, AuxAS_tE, MulOpposite.unop_mul, MulOpposite.unop_op]
    exact h.symm
  | eeFar i j hi hj hd =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.eeFar (omega := omega) j i hj hi hd.symm)
    simp only [map_mul, AuxAS_mE] at h
    simp only [map_mul, AuxAS_tE, MulOpposite.unop_mul, MulOpposite.unop_op]
    exact h
  | ex i j hi hj hji hji1 =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.ex (omega := omega) i j hi hj hji hji1)
    simp only [map_mul, AuxAS_mE, AuxAS_mX] at h
    simp only [map_mul, AuxAS_tE, AuxAS_tX, MulOpposite.unop_mul, MulOpposite.unop_op]
    exact h.symm
  | xxCommute i j hi hj =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.xxCommute (omega := omega) i j hi hj)
    simp only [map_mul, AuxAS_mX] at h
    simp only [map_mul, AuxAS_tX, MulOpposite.unop_mul, MulOpposite.unop_op]
    exact h.symm
  | skeinLeft i hi =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.skeinRight (omega := omega) i hi)
    simp only [map_mul, map_sub, map_one, AuxAS_mS, AuxAS_mE, AuxAS_mX] at h
    simp only [map_mul, map_sub, map_one, AuxAS_tS, AuxAS_tE, AuxAS_tX, MulOpposite.unop_mul,
      MulOpposite.unop_op, MulOpposite.unop_sub, MulOpposite.unop_one]
    exact h
  | skeinRight i hi =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.skeinLeft (omega := omega) i hi)
    simp only [map_mul, map_sub, map_one, AuxAS_mS, AuxAS_mE, AuxAS_mX] at h
    simp only [map_mul, map_sub, map_one, AuxAS_tS, AuxAS_tE, AuxAS_tX, MulOpposite.unop_mul,
      MulOpposite.unop_op, MulOpposite.unop_sub, MulOpposite.unop_one]
    exact h
  | unwrap a ha hn =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.unwrap (omega := omega) a ha hn)
    simp only [map_pow, map_mul, AlgHom.commutes, AuxAS_mE, AuxAS_mX] at h
    simp only [map_pow, map_mul, AlgHom.commutes, AuxAS_tE, AuxAS_tX, MulOpposite.unop_pow,
      MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.algebraMap_apply]
    rw [← mul_assoc, h, Algebra.commutes]
  | es i hi =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.se (omega := omega) i hi)
    simp only [map_mul, AuxAS_mS, AuxAS_mE] at h
    simp only [map_mul, AuxAS_tS, AuxAS_tE, MulOpposite.unop_mul, MulOpposite.unop_op]
    exact h
  | se i hi =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.es (omega := omega) i hi)
    simp only [map_mul, AuxAS_mS, AuxAS_mE] at h
    simp only [map_mul, AuxAS_tS, AuxAS_tE, MulOpposite.unop_mul, MulOpposite.unop_op]
    exact h
  | tangleLeft i hi =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.tangleRight (omega := omega) i hi)
    simp only [map_mul, AuxAS_mS, AuxAS_mE] at h
    simp only [map_mul, AuxAS_tS, AuxAS_tE, MulOpposite.unop_mul, MulOpposite.unop_op]
    simpa only [mul_assoc] using h
  | tangleRight i hi =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.tangleLeft (omega := omega) i hi)
    simp only [map_mul, AuxAS_mS, AuxAS_mE] at h
    simp only [map_mul, AuxAS_tS, AuxAS_tE, MulOpposite.unop_mul, MulOpposite.unop_op]
    simpa only [mul_assoc] using h
  | tangleLeftReverse i hi =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.tangleRightReverse (omega := omega) i hi)
    simp only [map_mul, AuxAS_mS, AuxAS_mE] at h
    simp only [map_mul, AuxAS_tS, AuxAS_tE, MulOpposite.unop_mul, MulOpposite.unop_op]
    simpa only [mul_assoc] using h
  | tangleRightReverse i hi =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.tangleLeftReverse (omega := omega) i hi)
    simp only [map_mul, AuxAS_mS, AuxAS_mE] at h
    simp only [map_mul, AuxAS_tS, AuxAS_tE, MulOpposite.unop_mul, MulOpposite.unop_op]
    simpa only [mul_assoc] using h
  | untwistLeft i hi =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.untwistLeft (omega := omega) i hi)
    simp only [map_mul, AuxAS_mE] at h
    simp only [map_mul, AuxAS_tE, MulOpposite.unop_mul, MulOpposite.unop_op]
    simpa only [mul_assoc] using h
  | untwistRight i hi =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.untwistRight (omega := omega) i hi)
    simp only [map_mul, AuxAS_mE] at h
    simp only [map_mul, AuxAS_tE, MulOpposite.unop_mul, MulOpposite.unop_op]
    simpa only [mul_assoc] using h
  | antisymLeft i hi =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.antisymRight (omega := omega) i hi)
    simp only [map_mul, map_add, map_zero, AuxAS_mE, AuxAS_mX] at h
    simp only [map_mul, map_add, map_zero, AuxAS_tE, AuxAS_tX, MulOpposite.unop_mul,
      MulOpposite.unop_op, MulOpposite.unop_add, MulOpposite.unop_zero]
    exact h
  | antisymRight i hi =>
    have h := RingQuot.mkAlgHom_rel R (BMWRel.antisymLeft (omega := omega) i hi)
    simp only [map_mul, map_add, map_zero, AuxAS_mE, AuxAS_mX] at h
    simp only [map_mul, map_add, map_zero, AuxAS_tE, AuxAS_tX, MulOpposite.unop_mul,
      MulOpposite.unop_op, MulOpposite.unop_add, MulOpposite.unop_zero]
    exact h

def AuxAS_sigma : AffineBMW R omega n →ₐ[R] (AffineBMW R omega n)ᵐᵒᵖ :=
  RingQuot.liftAlgHom R ⟨AuxAS_tau R omega n, AuxAS_rel R omega n⟩

lemma AuxAS_sig_m (a) : AuxAS_sigma R omega n (mm a) = AuxAS_tau R omega n a :=
  RingQuot.liftAlgHom_mkAlgHom_apply R _ _ a

/-- the generator image is fixed -/
lemma AuxAS_gen (l : BMWLetter n) :
    MulOpposite.unop (AuxAS_sigma R omega n (mm (FreeAlgebra.ι R l))) = mm (FreeAlgebra.ι R l) := by
  rw [AuxAS_sig_m]; simp [AuxAS_tau]

end AuxAS

lemma AuxAS_ind (R : Type u) [CommRing R] (omega : ℕ → R) (n : ℕ) (P : AffineBMW R omega n → Prop)
    (hg : ∀ l, P (RingQuot.mkAlgHom R (BMWRel R omega n) (FreeAlgebra.ι R l)))
    (hc : ∀ c : R, P (algebraMap R _ c))
    (hadd : ∀ a b, P a → P b → P (a + b)) (hmul : ∀ a b, P a → P b → P (a * b)) :
    ∀ a, P a := by
  intro a
  obtain ⟨x, rfl⟩ := RingQuot.mkAlgHom_surjective R (BMWRel R omega n) a
  induction x using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes]; exact hc c
  | grade1 l => exact hg l
  | mul a b ha hb => rw [map_mul]; exact hmul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb

theorem affineStar (R : Type u) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (n : ℕ) (hn : 1 ≤ n) :
    ∃! star : AffineBMW R omega n ≃ₗ[R] AffineBMW R omega n,
      (∀ a b, star (a*b) = star b * star a) ∧
      (∀ i, i+1 < n → star (affineS R omega n i) = affineS R omega n i ∧
        star (affineE R omega n i) = affineE R omega n i) ∧
      (∀ j, j < n → star (affineX R omega n j) = affineX R omega n j) ∧
      Function.Involutive star := by
  let f : AffineBMW R omega n → AffineBMW R omega n := fun a => MulOpposite.unop (AuxAS_sigma R omega n a)
  have fmul : ∀ a b, f (a*b) = f b * f a := by
    intro a b; simp [f]
  have fadd : ∀ a b, f (a+b) = f a + f b := by
    intro a b; simp [f]
  have fc : ∀ c : R, f (algebraMap R _ c) = algebraMap R _ c := by
    intro c; simp [f, MulOpposite.algebraMap_apply]
  have fg : ∀ l, f (RingQuot.mkAlgHom R (BMWRel R omega n) (FreeAlgebra.ι R l)) =
      RingQuot.mkAlgHom R (BMWRel R omega n) (FreeAlgebra.ι R l) := AuxAS_gen R omega n
  have finv : Function.Involutive f := by
    intro a
    induction a using AuxAS_ind R omega n with
    | hg l => rw [fg, fg]
    | hc c => rw [fc, fc]
    | hadd a b ha hb => rw [fadd, fadd, ha, hb]
    | hmul a b ha hb => rw [fmul, fmul, ha, hb]
  let starE : AffineBMW R omega n ≃ₗ[R] AffineBMW R omega n :=
    { toFun := f
      invFun := f
      map_add' := fadd
      map_smul' := by intro c a; simp [f]
      left_inv := finv
      right_inv := finv }
  have hS : ∀ i, f (affineS R omega n i) = affineS R omega n i := by
    intro i; simp only [f, ← AuxAS_mS, AuxAS_sig_m, AuxAS_tS, MulOpposite.unop_op]
  have hE : ∀ i, f (affineE R omega n i) = affineE R omega n i := by
    intro i; simp only [f, ← AuxAS_mE, AuxAS_sig_m, AuxAS_tE, MulOpposite.unop_op]
  have hX : ∀ i, f (affineX R omega n i) = affineX R omega n i := by
    intro i; simp only [f, ← AuxAS_mX, AuxAS_sig_m, AuxAS_tX, MulOpposite.unop_op]
  refine ⟨starE, ⟨fmul, fun i _ => ⟨hS i, hE i⟩, fun j _ => hX j, finv⟩, ?_⟩
  rintro st ⟨smul', sSE, sX, -⟩
  have s1 : st 1 = 1 := by
    have := smul' (st.symm 1) 1
    rw [mul_one, LinearEquiv.apply_symm_apply, mul_one] at this
    exact this.symm
  apply LinearEquiv.ext
  intro a
  show st a = f a
  induction a using AuxAS_ind R omega n with
  | hg l =>
    rw [fg]
    cases l with
    | s i =>
      have e : RingQuot.mkAlgHom R (BMWRel R omega n) (FreeAlgebra.ι R (BMWLetter.s i)) =
          affineS R omega n i.val := by
        rw [← AuxAS_mS]; unfold freeS; rw [dif_pos i.isLt]
      rw [e]; exact (sSE i.val (by have := i.isLt; omega)).1
    | e i =>
      have e : RingQuot.mkAlgHom R (BMWRel R omega n) (FreeAlgebra.ι R (BMWLetter.e i)) =
          affineE R omega n i.val := by
        rw [← AuxAS_mE]; unfold freeE; rw [dif_pos i.isLt]
      rw [e]; exact (sSE i.val (by have := i.isLt; omega)).2
    | x j =>
      have e : RingQuot.mkAlgHom R (BMWRel R omega n) (FreeAlgebra.ι R (BMWLetter.x j)) =
          affineX R omega n j.val := by
        rw [← AuxAS_mX]; unfold freeX; rw [dif_pos j.isLt]
      rw [e]; exact sX j.val j.isLt
  | hc c =>
    rw [fc, Algebra.algebraMap_eq_smul_one, map_smul, s1]
  | hadd a b ha hb => rw [map_add, fadd, ha, hb]
  | hmul a b ha hb => rw [smul', fmul, ha, hb]

end QAlgorithms.Papers.Independent.Intake100.P65

end

open QAlgorithms.Papers.Independent.Renew46.P16

theorem solution (R : Type*) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (n : ℕ) (hn : 1 ≤ n) :
    ∃! star : AffineBMW R omega n ≃ₗ[R] AffineBMW R omega n,
      (∀ a b, star (a*b) = star b * star a) ∧
      (∀ i, i+1 < n → star (affineS R omega n i) = affineS R omega n i ∧
        star (affineE R omega n i) = affineE R omega n i) ∧
      (∀ j, j < n → star (affineX R omega n j) = affineX R omega n j) ∧
      Function.Involutive star :=
  QAlgorithms.Papers.Independent.Intake100.P65.affineStar R omega n hn
