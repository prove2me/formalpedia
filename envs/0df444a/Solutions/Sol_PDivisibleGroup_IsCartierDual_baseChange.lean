-- Prove2me | solution 1 for PDivisibleGroup.IsCartierDual.baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7205e8af-755d-58f7-a2ff-bde72a66a718

import Mathlib
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_HopfAlgebra_CharacterClosure
import Theorems.Thm_CartierDual_dualBaseChangeLin_bijective_integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_IsCartierDual_baseChange

set_option autoImplicit false

open scoped TensorProduct
open Coalgebra Bialgebra

namespace PDivDualBC

variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S]

section DualBC

variable (A : Type) [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

theorem counit_dbc (w : S ⊗[R] CartierDual R A) :
    counit (R := S) (CartierDual.dualBaseChangeLin R S A w) = counit (R := S) w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul s φ =>
    rw [CartierDual.counit_apply, TensorProduct.counit_tmul, CartierDual.counit_apply,
      CommSemiring.counit_apply, show (1 : S ⊗[R] A) = (1 : S) ⊗ₜ[R] (1 : A) from rfl,
      CartierDual.dualBaseChangeLin_tmul_tmul, mul_one, Algebra.smul_def, mul_comm]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

noncomputable def dbcBialgHom : S ⊗[R] CartierDual R A →ₐc[S] CartierDual S (S ⊗[R] A) :=
  { CartierDual.dualBaseChangeLin R S A with
    map_one' := (CartierDual.dualBaseChangeLin_bijective_integral R S A).2.1
    map_mul' := (CartierDual.dualBaseChangeLin_bijective_integral R S A).2.2.1
    counit_comp := LinearMap.ext fun w => counit_dbc S A w
    map_comp_comul := LinearMap.ext fun w =>
      (CartierDual.dualBaseChangeLin_bijective_integral R S A).2.2.2.1 w }

theorem dbcBialgHom_apply (w : S ⊗[R] CartierDual R A) :
    dbcBialgHom S A w = CartierDual.dualBaseChangeLin R S A w := rfl

noncomputable def dbcEquiv : S ⊗[R] CartierDual R A ≃ₐc[S] CartierDual S (S ⊗[R] A) :=
  BialgEquiv.ofBijective (dbcBialgHom S A)
    (CartierDual.dualBaseChangeLin_bijective_integral R S A).1

theorem dbcEquiv_apply (w : S ⊗[R] CartierDual R A) :
    dbcEquiv S A w = CartierDual.dualBaseChangeLin R S A w := rfl

end DualBC

section MapEquiv

variable {A B : Type} [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B] (e : A ≃ₐc[R] B)

noncomputable def mapEquiv : S ⊗[R] A ≃ₐc[S] S ⊗[R] B :=
  BialgEquiv.ofBialgHom
    (Bialgebra.TensorProduct.map (BialgHom.id S S) (e : A →ₐc[R] B))
    (Bialgebra.TensorProduct.map (BialgHom.id S S) (e.symm : B →ₐc[R] A))
    (by
      refine BialgHom.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul s b =>
        change s ⊗ₜ[R] e (e.symm b) = s ⊗ₜ[R] b
        rw [e.apply_symm_apply]
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (by
      refine BialgHom.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul s a =>
        change s ⊗ₜ[R] e.symm (e a) = s ⊗ₜ[R] a
        rw [e.symm_apply_apply]
      | add x y hx hy => rw [map_add, map_add, hx, hy])

theorem mapEquiv_tmul (s : S) (a : A) : mapEquiv S e (s ⊗ₜ[R] a) = s ⊗ₜ[R] e a := rfl

end MapEquiv

variable {p h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G') [Nontrivial S]

noncomputable def equivBC (v : ℕ) :
    (G'.baseChange S).level v ≃ₐc[S] CartierDual S ((G.baseChange S).level v) :=
  (mapEquiv S (D.equiv v)).trans (dbcEquiv S (G.level v))

omit [Nontrivial S] in
theorem equivBC_tmul_tmul (v : ℕ) (s : S) (x : G'.level v) (s' : S) (a : G.level v) :
    ((mapEquiv S (D.equiv v)).trans (dbcEquiv S (G.level v))) (s ⊗ₜ[R] x) (s' ⊗ₜ[R] a) =
      s * s' * algebraMap R S (D.equiv v x a) := by
  change dbcEquiv S (G.level v) (mapEquiv S (D.equiv v) (s ⊗ₜ[R] x)) (s' ⊗ₜ[R] a) = _
  rw [mapEquiv_tmul, dbcEquiv_apply, CartierDual.dualBaseChangeLin_tmul_tmul]

theorem equivBC_transition (v : ℕ) (x : (G'.baseChange S).level (v + 1))
    (a : (G.baseChange S).level (v + 1)) :
    equivBC S D v ((G'.baseChange S).transition v x) ((G.baseChange S).transition v a) =
      equivBC S D (v + 1) x
        (PDivisibleGroup.Hopf.nsmulAlgHom S ((G.baseChange S).level (v + 1)) p a) := by
  change ((mapEquiv S (D.equiv v)).trans (dbcEquiv S (G.level v)))
      (Bialgebra.TensorProduct.map (BialgHom.id S S) (G'.transition v) x)
      (Bialgebra.TensorProduct.map (BialgHom.id S S) (G.transition v) a) =
    ((mapEquiv S (D.equiv (v + 1))).trans (dbcEquiv S (G.level (v + 1)))) x
      (PDivisibleGroup.Hopf.nsmulAlgHom S (S ⊗[R] G.level (v + 1)) p a)
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, CartierDual.zero_apply_pt, CartierDual.zero_apply_pt]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, CartierDual.add_apply_pt, CartierDual.add_apply_pt, hx, hy]
  | tmul s x0 =>
    rw [Bialgebra.TensorProduct.map_tmul]
    change ((mapEquiv S (D.equiv v)).trans (dbcEquiv S (G.level v))) (s ⊗ₜ[R] G'.transition v x0)
        (Bialgebra.TensorProduct.map (BialgHom.id S S) (G.transition v) a) = _
    induction a using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul s' a0 =>
      rw [Bialgebra.TensorProduct.map_tmul, PDivisibleGroup.Hopf.nsmulAlgHom_baseChange_tmul]
      change ((mapEquiv S (D.equiv v)).trans (dbcEquiv S (G.level v))) (s ⊗ₜ[R] G'.transition v x0)
          (s' ⊗ₜ[R] G.transition v a0) = _
      rw [equivBC_tmul_tmul, equivBC_tmul_tmul, D.equiv_transition]

private noncomputable def _root_.PDivDualBC.baseChange : (G.baseChange S).CartierDuality (G'.baseChange S) where
  equiv := equivBC S D
  equiv_transition := equivBC_transition S D

p2m_export "PDivDualBC" "baseChange"
end PDivDualBC

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} {G G' : PDivisibleGroup R p h} (hGG' : G.IsCartierDual G')
    (S : Type) [CommRing S] [Algebra R S] [Nontrivial S] :
    (G.baseChange S).IsCartierDual (G'.baseChange S) :=
  ⟨PDivDualBC.baseChange S hGG'.some⟩

end S_PDivisibleGroup_IsCartierDual_baseChange
end P2MW
export P2MW.S_PDivisibleGroup_IsCartierDual_baseChange (solution)
