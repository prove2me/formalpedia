-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P11.generator_fixing_involutions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T06:09:50.803109+00:00
-- url     : https://prove2.me/submissions/64915002-4051-4352-a818-930ededac0c9

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11
noncomputable section

open scoped BigOperators Classical

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open QAlgorithms.Papers.Independent.Support21.P11
open QAlgorithms.Papers.Independent.Renew46.P16

theorem g66n2_anti_ext {S X A B : Type*} [CommRing S] [Ring A] [Algebra S A] [Ring B] [Algebra S B]
    (φ : FreeAlgebra S X →ₐ[S] A) (hφ : Function.Surjective φ) (f g : A →ₗ[S] B)
    (hf : ∀ a b, f (a * b) = f b * f a) (hg : ∀ a b, g (a * b) = g b * g a)
    (h1 : f 1 = g 1) (hι : ∀ x, f (φ (FreeAlgebra.ι S x)) = g (φ (FreeAlgebra.ι S x))) (a : A) :
    f a = g a := by
  obtain ⟨t, rfl⟩ := hφ a
  induction t using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_smul, map_smul, h1]
  | grade1 x => exact hι x
  | mul a b ha hb => rw [map_mul, hf, hg, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem g66n2_anti_ext' {S X A B : Type*} [CommRing S] [Ring A] [Algebra S A] [Ring B] [Algebra S B]
    (φ : FreeAlgebra S X →ₐ[S] A) (hφ : Function.Surjective φ) (f g : A → B)
    (fa : ∀ a b, f (a + b) = f a + f b) (ga : ∀ a b, g (a + b) = g a + g b)
    (fs : ∀ (c : S) a, f (c • a) = c • f a) (gs : ∀ (c : S) a, g (c • a) = c • g a)
    (hf : ∀ a b, f (a * b) = f b * f a) (hg : ∀ a b, g (a * b) = g b * g a)
    (h1 : f 1 = g 1) (hι : ∀ x, f (φ (FreeAlgebra.ι S x)) = g (φ (FreeAlgebra.ι S x))) (a : A) :
    f a = g a := by
  obtain ⟨t, rfl⟩ := hφ a
  induction t using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, fs, gs, h1]
  | grade1 x => exact hι x
  | mul a b ha hb => rw [map_mul, hf, hg, ha, hb]
  | add a b ha hb => rw [map_add, fa, ga, ha, hb]

theorem g66n2_invol {S X A : Type*} [CommRing S] [Ring A] [Algebra S A]
    (φ : FreeAlgebra S X →ₐ[S] A) (hφ : Function.Surjective φ) (f : A →ₗ[S] A)
    (hf : ∀ a b, f (a * b) = f b * f a)
    (h1 : f 1 = 1) (hι : ∀ x, f (φ (FreeAlgebra.ι S x)) = φ (FreeAlgebra.ι S x)) (a : A) :
    f (f a) = a := by
  obtain ⟨t, rfl⟩ := hφ a
  induction t using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_smul, map_smul, h1, h1]
  | grade1 x => rw [hι, hι]
  | mul a b ha hb => rw [map_mul, hf, hf, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

def g66n2_toStar {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (F : A →ₐ[S] Aᵐᵒᵖ) :
    A →ₗ[S] A :=
  (MulOpposite.opLinearEquiv S).symm.toLinearMap ∘ₗ F.toLinearMap

theorem g66n2_toStar_apply {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (F : A →ₐ[S] Aᵐᵒᵖ)
    (a : A) : g66n2_toStar F a = (F a).unop := rfl

theorem g66n2_toStar_mul {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (F : A →ₐ[S] Aᵐᵒᵖ)
    (a b : A) : g66n2_toStar F (a * b) = g66n2_toStar F b * g66n2_toStar F a := by
  simp [g66n2_toStar_apply]

theorem g66n2_toStar_one {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (F : A →ₐ[S] Aᵐᵒᵖ) :
    g66n2_toStar F 1 = 1 := by
  simp [g66n2_toStar_apply]

section Aff
variable (S : Type*) [CommRing S] (omega : ℕ → S) (n : ℕ)

def g66n2_F : FreeAlgebra S (BMWLetter n) →ₐ[S] (AffineBMW S omega n)ᵐᵒᵖ :=
  FreeAlgebra.lift S (fun l => MulOpposite.op (affineBMWQuotientMap S omega n (FreeAlgebra.ι S l)))

theorem g66n2_FS (i : ℕ) : g66n2_F S omega n (freeS S n i) =
    MulOpposite.op (affineBMWQuotientMap S omega n (freeS S n i)) := by
  unfold freeS; split_ifs <;> simp [g66n2_F]

theorem g66n2_FE (i : ℕ) : g66n2_F S omega n (freeE S n i) =
    MulOpposite.op (affineBMWQuotientMap S omega n (freeE S n i)) := by
  unfold freeE; split_ifs <;> simp [g66n2_F]

theorem g66n2_FX (i : ℕ) : g66n2_F S omega n (freeX S n i) =
    MulOpposite.op (affineBMWQuotientMap S omega n (freeX S n i)) := by
  unfold freeX; split_ifs <;> simp [g66n2_F]

theorem g66n2_Frel : ∀ ⦃x y⦄, BMWRel S omega n x y → g66n2_F S omega n x = g66n2_F S omega n y := by
  have q : ∀ {x y}, BMWRel S omega n x y → affineBMWQuotientMap S omega n x =
      affineBMWQuotientMap S omega n y := fun h => RingQuot.mkAlgHom_rel S h
  intro x y h
  apply MulOpposite.unop_injective
  cases h with
  | involution i hi =>
    have h' := q (BMWRel.involution i hi)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | braidFar i j hi hj hd =>
    have h' := q (BMWRel.braidFar i j hi hj hd)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | braidNear i hi =>
    have h' := q (BMWRel.braidNear i hi)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | sx i j hi hj hji hji1 =>
    have h' := q (BMWRel.sx i j hi hj hji hji1)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | idempotent i hi =>
    have h' := q (BMWRel.idempotent i hi)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | seFar i j hi hj hd =>
    have h' := q (BMWRel.seFar i j hi hj hd)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | eeFar i j hi hj hd =>
    have h' := q (BMWRel.eeFar i j hi hj hd)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | ex i j hi hj hji hji1 =>
    have h' := q (BMWRel.ex i j hi hj hji hji1)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | xxCommute i j hi hj =>
    have h' := q (BMWRel.xxCommute i j hi hj)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | skeinLeft i hi =>
    have h' := q (BMWRel.skeinRight i hi)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | skeinRight i hi =>
    have h' := q (BMWRel.skeinLeft i hi)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | unwrap a ha hn =>
    have h' := q (BMWRel.unwrap a ha hn)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | es i hi =>
    have h' := q (BMWRel.se i hi)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | se i hi =>
    have h' := q (BMWRel.es i hi)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | tangleLeft i hi =>
    have h' := q (BMWRel.tangleRight i hi)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | tangleRight i hi =>
    have h' := q (BMWRel.tangleLeft i hi)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | tangleLeftReverse i hi =>
    have h' := q (BMWRel.tangleRightReverse i hi)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | tangleRightReverse i hi =>
    have h' := q (BMWRel.tangleLeftReverse i hi)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | untwistLeft i hi =>
    have h' := q (BMWRel.untwistLeft i hi)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | untwistRight i hi =>
    have h' := q (BMWRel.untwistRight i hi)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | antisymLeft i hi =>
    have h' := q (BMWRel.antisymRight i hi)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm
  | antisymRight i hi =>
    have h' := q (BMWRel.antisymLeft i hi)
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul] at h'
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, map_smul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, g66n2_FS, g66n2_FE, g66n2_FX, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_add, MulOpposite.unop_sub, MulOpposite.unop_pow, MulOpposite.unop_one,
      MulOpposite.unop_zero, MulOpposite.algebraMap_apply, MulOpposite.unop_smul]
    first | exact h' | exact h'.symm

end Aff

theorem g66n2_star_pow {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (f : A →ₗ[S] A)
    (hf : ∀ a b, f (a * b) = f b * f a) (h1 : f 1 = 1) (x : A) (k : ℕ) : f (x ^ k) = f x ^ k := by
  induction k with
  | zero => simp [h1]
  | succ k ih => rw [pow_succ, hf, ih, pow_succ']

theorem g66n2_star_aeval {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (f : A →ₗ[S] A)
    (hf : ∀ a b, f (a * b) = f b * f a) (h1 : f 1 = 1) (x : A) (p : Polynomial S) :
    f (Polynomial.aeval x p) = Polynomial.aeval (f x) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | monomial k c =>
    simp only [Polynomial.aeval_monomial, ← Algebra.smul_def, map_smul, g66n2_star_pow f hf h1]

theorem g66n2_letters {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (n : ℕ)
    (φ : FreeAlgebra S (BMWLetter n) →ₐ[S] A) (f : A →ₗ[S] A)
    (h : IsGeneratorReversal n (fun i => φ (freeS S n i)) (fun i => φ (freeE S n i))
      (fun j => φ (freeX S n j)) f) (l : BMWLetter n) :
    f (φ (FreeAlgebra.ι S l)) = φ (FreeAlgebra.ι S l) := by
  obtain ⟨-, -, -, hse, hx⟩ := h
  cases l with
  | s i =>
    have := (hse i.val (by have := i.isLt; omega)).1
    simpa [freeS, i.isLt] using this
  | e i =>
    have := (hse i.val (by have := i.isLt; omega)).2
    simpa [freeE, i.isLt] using this
  | x i =>
    have := hx i.val i.isLt
    simpa [freeX, i.isLt] using this

theorem g66n2_unique {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (n : ℕ)
    (φ : FreeAlgebra S (BMWLetter n) →ₐ[S] A) (hφ : Function.Surjective φ) (f g : A →ₗ[S] A)
    (hf : IsGeneratorReversal n (fun i => φ (freeS S n i)) (fun i => φ (freeE S n i))
      (fun j => φ (freeX S n j)) f)
    (hg : IsGeneratorReversal n (fun i => φ (freeS S n i)) (fun i => φ (freeE S n i))
      (fun j => φ (freeX S n j)) g) : f = g := by
  ext a
  refine g66n2_anti_ext φ hφ f g hf.2.2.1 hg.2.2.1 (hf.2.1.trans hg.2.1.symm) (fun l => ?_) a
  rw [g66n2_letters n φ f hf, g66n2_letters n φ g hg]

section Main
variable (S : Type*) [CommRing S] (omega : ℕ → S) (n : ℕ)

def g66n2_FA : AffineBMW S omega n →ₐ[S] (AffineBMW S omega n)ᵐᵒᵖ :=
  RingQuot.liftAlgHom S ⟨g66n2_F S omega n, g66n2_Frel S omega n⟩

theorem g66n2_FA_mk (t : FreeAlgebra S (BMWLetter n)) :
    g66n2_FA S omega n (affineBMWQuotientMap S omega n t) = g66n2_F S omega n t := by
  unfold g66n2_FA affineBMWQuotientMap
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]

def g66n2_starA : AffineBMW S omega n →ₗ[S] AffineBMW S omega n := g66n2_toStar (g66n2_FA S omega n)

theorem g66n2_starA_rev : IsGeneratorReversal n (affineS S omega n) (affineE S omega n)
    (affineX S omega n) (g66n2_starA S omega n) := by
  have hmul := g66n2_toStar_mul (g66n2_FA S omega n)
  have h1 := g66n2_toStar_one (g66n2_FA S omega n)
  refine ⟨fun a => g66n2_invol (affineBMWQuotientMap S omega n) (RingQuot.mkAlgHom_surjective _ _)
    _ hmul h1 (fun l => ?_) a, h1, hmul, fun i _ => ⟨?_, ?_⟩, fun j _ => ?_⟩
  · simp [g66n2_starA, g66n2_toStar_apply, g66n2_FA_mk, g66n2_F]
  · simp [g66n2_starA, g66n2_toStar_apply, affineS, g66n2_FA_mk, g66n2_FS]
  · simp [g66n2_starA, g66n2_toStar_apply, affineE, g66n2_FA_mk, g66n2_FE]
  · simp [g66n2_starA, g66n2_toStar_apply, affineX, g66n2_FA_mk, g66n2_FX]


theorem g66n2_starA_mk (t : FreeAlgebra S (BMWLetter n)) :
    g66n2_starA S omega n (affineBMWQuotientMap S omega n t) = (g66n2_F S omega n t).unop := by
  rw [g66n2_starA, g66n2_toStar_apply, g66n2_FA_mk]

variable (r : ℕ) (u : Fin r → S)

def g66n2_G : AffineBMW S omega n →ₐ[S] (CyclotomicBMW S omega n r u)ᵐᵒᵖ :=
  (AlgHom.op (cyclotomicMap S omega n r u)).comp (g66n2_FA S omega n)

theorem g66n2_G_apply (a : AffineBMW S omega n) :
    (g66n2_G S omega n r u a).unop = cyclotomicMap S omega n r u (g66n2_starA S omega n a) := rfl

theorem g66n2_Grel : ∀ ⦃a b⦄, cyclotomicRel S omega n r u a b →
    g66n2_G S omega n r u a = g66n2_G S omega n r u b := by
  rintro a b ⟨rfl, rfl⟩
  apply MulOpposite.unop_injective
  rw [g66n2_G_apply, g66n2_G_apply, map_zero, map_zero]
  have hrev := g66n2_starA_rev S omega n
  have hp : cyclotomicPolynomial S omega n r u =
      Polynomial.aeval (affineX S omega n 0) (parameterPolynomial u) := by
    unfold cyclotomicPolynomial parameterPolynomial
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    simp [Function.comp_def]
  have h0 : cyclotomicMap S omega n r u (cyclotomicPolynomial S omega n r u) = 0 :=
    (RingQuot.mkAlgHom_rel S (show cyclotomicRel S omega n r u
      (cyclotomicPolynomial S omega n r u) 0 from ⟨rfl, rfl⟩)).trans (map_zero _)
  rw [hp, g66n2_star_aeval _ hrev.2.2.1 hrev.2.1]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- x_0 is zero at level 0
    have : affineX S omega 0 0 = 0 := by simp [affineX, freeX]
    rw [this, map_zero]
    rw [hp, this] at h0
    exact h0
  · rw [hrev.2.2.2.2 0 hn, ← hp, h0]

def g66n2_GC : CyclotomicBMW S omega n r u →ₐ[S] (CyclotomicBMW S omega n r u)ᵐᵒᵖ :=
  RingQuot.liftAlgHom S ⟨g66n2_G S omega n r u, g66n2_Grel S omega n r u⟩

def g66n2_starC : CyclotomicBMW S omega n r u →ₗ[S] CyclotomicBMW S omega n r u :=
  g66n2_toStar (A := CyclotomicBMW S omega n r u) (g66n2_GC S omega n r u)

theorem g66n2_starC_app (x : CyclotomicBMW S omega n r u) :
    g66n2_starC S omega n r u x = (g66n2_GC S omega n r u x).unop := rfl

theorem g66n2_starC_map (a : AffineBMW S omega n) :
    g66n2_starC S omega n r u (cyclotomicMap S omega n r u a) =
      cyclotomicMap S omega n r u (g66n2_starA S omega n a) := by
  rw [g66n2_starC_app, g66n2_GC, cyclotomicMap, RingQuot.liftAlgHom_mkAlgHom_apply]
  rfl

theorem g66n2_starC_rev : IsGeneratorReversal n (cyclotomicS S omega n r u)
    (cyclotomicE S omega n r u) (cyclotomicX S omega n r u) (g66n2_starC S omega n r u) := by
  have hmul : ∀ a b, g66n2_starC S omega n r u (a * b) =
      g66n2_starC S omega n r u b * g66n2_starC S omega n r u a := by
    intro a b; rw [g66n2_starC_app, g66n2_starC_app, g66n2_starC_app, map_mul, MulOpposite.unop_mul]
  have h1 : g66n2_starC S omega n r u 1 = 1 := by
    rw [g66n2_starC_app, map_one, MulOpposite.unop_one]
  have hA := g66n2_starA_rev S omega n
  refine ⟨fun a => g66n2_invol ((cyclotomicMap S omega n r u).comp (affineBMWQuotientMap S omega n))
    ((RingQuot.mkAlgHom_surjective _ _).comp (RingQuot.mkAlgHom_surjective _ _))
    (g66n2_starC S omega n r u) hmul h1 (fun l => ?_) a, h1, hmul, fun i hi => ⟨?_, ?_⟩, fun j hj => ?_⟩
  · rw [AlgHom.comp_apply, g66n2_starC_map, g66n2_starA_mk]
    simp [g66n2_F]
  · rw [cyclotomicS, g66n2_starC_map, (hA.2.2.2.1 i hi).1]
  · rw [cyclotomicE, g66n2_starC_map, (hA.2.2.2.1 i hi).2]
  · rw [cyclotomicX, g66n2_starC_map, hA.2.2.2.2 j hj]

end Main

theorem solution (R : Type*) [CommRing R] (omega : ℕ → R)
    (n r : ℕ) (u : Fin r → R) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    (∃! star : AffineBMW R omega n →ₗ[R] AffineBMW R omega n,
      IsGeneratorReversal n (affineS R omega n) (affineE R omega n)
        (affineX R omega n) star) ∧
    (∃! star : CyclotomicBMW R omega n r u →ₗ[R] CyclotomicBMW R omega n r u,
      IsGeneratorReversal n (cyclotomicS R omega n r u) (cyclotomicE R omega n r u)
        (cyclotomicX R omega n r u) star) ∧
    (∀ (aff : AffineBMW R omega n →ₗ[R] AffineBMW R omega n)
      (cyc : CyclotomicBMW R omega n r u →ₗ[R] CyclotomicBMW R omega n r u),
      IsGeneratorReversal n (affineS R omega n) (affineE R omega n)
        (affineX R omega n) aff →
      IsGeneratorReversal n (cyclotomicS R omega n r u) (cyclotomicE R omega n r u)
        (cyclotomicX R omega n r u) cyc →
      ∀ z : AffineBMW R omega n,
        cyc (cyclotomicMap R omega n r u z) = cyclotomicMap R omega n r u (aff z)) := by
  have hA := g66n2_starA_rev R omega n
  have hC := g66n2_starC_rev R omega n r u
  have sA := RingQuot.mkAlgHom_surjective R (BMWRel R omega n)
  have sC := (RingQuot.mkAlgHom_surjective R (cyclotomicRel R omega n r u)).comp sA
  refine ⟨⟨g66n2_starA R omega n, hA, fun f hf =>
    g66n2_unique n (affineBMWQuotientMap R omega n) sA f _ hf hA⟩,
    ⟨g66n2_starC R omega n r u, hC, fun f hf =>
    g66n2_unique (A := CyclotomicBMW R omega n r u) n
      ((cyclotomicMap R omega n r u).comp (affineBMWQuotientMap R omega n)) sC f
      (g66n2_starC R omega n r u) hf hC⟩, ?_⟩
  intro aff cyc haff hcyc z
  refine g66n2_anti_ext' (B := CyclotomicBMW R omega n r u) (affineBMWQuotientMap R omega n) sA
    (fun z => cyc (cyclotomicMap R omega n r u z)) (fun z => cyclotomicMap R omega n r u (aff z))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ z
  · intro a b; simp only [map_add]
  · intro a b; simp only [map_add]
  · intro c a; simp only [map_smul]
  · intro c a; simp only [map_smul]
  · intro a b
    simp only [map_mul]
    exact hcyc.2.2.1 _ _
  · intro a b
    simp only [haff.2.2.1 a b, map_mul]
  · simp only [map_one, haff.2.1]
    exact hcyc.2.1
  · intro l
    show cyc (cyclotomicMap R omega n r u _) = cyclotomicMap R omega n r u (aff _)
    rw [g66n2_letters n (affineBMWQuotientMap R omega n) aff haff l]
    exact g66n2_letters (A := CyclotomicBMW R omega n r u) n
      ((cyclotomicMap R omega n r u).comp (affineBMWQuotientMap R omega n)) cyc hcyc l
