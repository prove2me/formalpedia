-- Prove2me | solution 1 for PDivisibleGroup.Hopf.map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/39cb9223-f5df-5f28-9dd1-eaeb56904ae3

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_Hopf_map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange

set_option autoImplicit false

open scoped TensorProduct
open Function

universe u u' v w w'

namespace K4dBody

section Fibre

variable {O : Type u} [CommRing O] {κ : Type u'} [CommRing κ] [Algebra O κ]
variable {A : Type v} [CommRing A] [Bialgebra O A]

private noncomputable def redLeft (κ : Type u') [CommRing κ] [Algebra O κ] (A : Type v) [CommRing A]
    [Algebra O A] : A →ₐ[O] (κ ⊗[O] A) ⊗[κ] (κ ⊗[O] A) :=
  (Algebra.TensorProduct.includeLeft (S := O)).comp Algebra.TensorProduct.includeRight

private noncomputable def redRight (κ : Type u') [CommRing κ] [Algebra O κ] (A : Type v) [CommRing A]
    [Algebra O A] : A →ₐ[O] (κ ⊗[O] A) ⊗[κ] (κ ⊗[O] A) :=
  ((Algebra.TensorProduct.includeRight :
        κ ⊗[O] A →ₐ[κ] (κ ⊗[O] A) ⊗[κ] (κ ⊗[O] A)).restrictScalars O).comp
      Algebra.TensorProduct.includeRight

private noncomputable def pi2 (κ : Type u') [CommRing κ] [Algebra O κ] (A : Type v) [CommRing A]
    [Algebra O A] : A ⊗[O] A →ₐ[O] (κ ⊗[O] A) ⊗[κ] (κ ⊗[O] A) :=
  Algebra.TensorProduct.lift (redLeft κ A) (redRight κ A)
    (fun _ _ => Commute.all (S := (κ ⊗[O] A) ⊗[κ] (κ ⊗[O] A)) _ _)

private theorem pi2_tmul (x y : A) :
    pi2 κ A (x ⊗ₜ[O] y) = ((1 : κ) ⊗ₜ[O] x) ⊗ₜ[κ] ((1 : κ) ⊗ₜ[O] y) := by
  rw [pi2, Algebra.TensorProduct.lift_tmul]
  change (((1 : κ) ⊗ₜ[O] x) ⊗ₜ[κ] (1 : κ ⊗[O] A)) * ((1 : κ ⊗[O] A) ⊗ₜ[κ] ((1 : κ) ⊗ₜ[O] y)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

private theorem comul_one_tmul (a : A) :
    Coalgebra.comul (R := κ) ((1 : κ) ⊗ₜ[O] a) = pi2 κ A (Coalgebra.comul (R := O) a) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply κ 1]
  induction Coalgebra.comul (R := O) a using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero]
  | tmul x y =>
    rw [pi2_tmul]
    rfl
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]

private theorem counit_tmul' (c : κ) (a : A) :
    Coalgebra.counit (R := κ) (c ⊗ₜ[O] a) = algebraMap O κ (Coalgebra.counit (R := O) a) * c := by
  rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def]

private theorem convMul_apply_one_tmul {T : Type w} [CommRing T] [Algebra κ T] [Algebra O T]
    [IsScalarTower O κ T]
    (φ ψ : WithConv (κ ⊗[O] A →ₐ[κ] T)) (a : A) :
    (φ * ψ) ((1 : κ) ⊗ₜ[O] a) =
      Algebra.TensorProduct.lift
        ((φ.ofConv.restrictScalars O).comp Algebra.TensorProduct.includeRight)
        ((ψ.ofConv.restrictScalars O).comp Algebra.TensorProduct.includeRight)
        (fun _ _ => Commute.all (S := T) _ _) (Coalgebra.comul (R := O) a) := by
  rw [AlgHom.convMul_apply, comul_one_tmul]
  induction Coalgebra.comul (R := O) a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [pi2_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem nsmulAlgHom_tmul (n : ℕ) (c : κ) (a : A) :
    PDivisibleGroup.Hopf.nsmulAlgHom κ (κ ⊗[O] A) n (c ⊗ₜ[O] a) =
      c ⊗ₜ[O] PDivisibleGroup.Hopf.nsmulAlgHom O A n a := by

  have key : ∀ a : A, PDivisibleGroup.Hopf.nsmulAlgHom κ (κ ⊗[O] A) n ((1 : κ) ⊗ₜ[O] a) =
      (1 : κ) ⊗ₜ[O] PDivisibleGroup.Hopf.nsmulAlgHom O A n a := by
    induction n with
    | zero =>
      intro a
      rw [PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply, PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply,
        counit_tmul', mul_one, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    | succ n ih =>
      intro a
      rw [PDivisibleGroup.Hopf.nsmulAlgHom_succ, PDivisibleGroup.Hopf.nsmulAlgHom_succ]
      change (WithConv.toConv (PDivisibleGroup.Hopf.nsmulAlgHom κ (κ ⊗[O] A) n) *
          WithConv.toConv (AlgHom.id κ (κ ⊗[O] A))) ((1 : κ) ⊗ₜ[O] a) =
        (1 : κ) ⊗ₜ[O] (WithConv.toConv (PDivisibleGroup.Hopf.nsmulAlgHom O A n) *
          WithConv.toConv (AlgHom.id O A)) a
      rw [convMul_apply_one_tmul, AlgHom.convMul_apply]
      induction Coalgebra.comul (R := O) a using TensorProduct.induction_on with
      | zero => simp only [map_zero, TensorProduct.tmul_zero]
      | tmul x y =>
        rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
        change PDivisibleGroup.Hopf.nsmulAlgHom κ (κ ⊗[O] A) n ((1 : κ) ⊗ₜ[O] x) * ((1 : κ) ⊗ₜ[O] y) =
          (1 : κ) ⊗ₜ[O] (PDivisibleGroup.Hopf.nsmulAlgHom O A n x * y)
        rw [ih, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  have hc : c ⊗ₜ[O] a = c • ((1 : κ) ⊗ₜ[O] a) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hc, map_smul, key, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem nsmulAlgHom_baseChange (n : ℕ) :
    PDivisibleGroup.Hopf.nsmulAlgHom κ (κ ⊗[O] A) n =
      Algebra.TensorProduct.map (AlgHom.id κ κ) (PDivisibleGroup.Hopf.nsmulAlgHom O A n) := by
  refine Algebra.TensorProduct.ext' fun c a => ?_
  rw [nsmulAlgHom_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

end Fibre

end K4dBody

theorem solution
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (A : Type w) [CommRing A] [Bialgebra R A] (n : ℕ) :
    Algebra.TensorProduct.map (AlgHom.id S S) (PDivisibleGroup.Hopf.nsmulAlgHom R A n) =
      PDivisibleGroup.Hopf.nsmulAlgHom S (S ⊗[R] A) n :=
  (K4dBody.nsmulAlgHom_baseChange (O := R) (κ := S) (A := A) n).symm

end S_PDivisibleGroup_Hopf_map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange
end P2MW
export P2MW.S_PDivisibleGroup_Hopf_map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange (solution)
