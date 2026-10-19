-- Prove2me | solution 1 for PermanentRollout.rootOfUnity_node_product_algebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/ff418ddd-e15b-4f3a-af84-b8284e27aa66

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommRing R] [Algebra ℂ R]
    {d : ℕ} (hd : 0 < d) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ d) (x y : R) :
    (∏ j ∈ Finset.range d,
      (x + algebraMap ℂ R (2 * ζ ^ j) * y)) =
      x ^ d - (algebraMap ℂ R (-2) * y) ^ d := by
  let alpha : Polynomial ℂ := Polynomial.C (-2) * Polynomial.X
  have hroot : IsPrimitiveRoot (Polynomial.C ζ) d :=
    hζ.map_of_injective Polynomial.C_injective
  have hfactor := X_pow_sub_C_eq_prod hroot hd
    (α := alpha) (a := alpha ^ d) rfl
  let coeffHom : Polynomial ℂ →+* R :=
    Polynomial.eval₂RingHom (algebraMap ℂ R) y
  have hterm (j : ℕ) :
      Polynomial.eval₂ coeffHom x
        ((Polynomial.X : Polynomial (Polynomial ℂ)) -
          Polynomial.C ((Polynomial.C ζ) ^ j * alpha)) =
        x + algebraMap ℂ R (2 * ζ ^ j) * y := by
    simp [coeffHom, alpha, Polynomial.eval₂_pow]
    ring
  calc
    (∏ j ∈ Finset.range d,
      (x + algebraMap ℂ R (2 * ζ ^ j) * y)) =
        Polynomial.eval₂ coeffHom x
          (∏ j ∈ Finset.range d,
            ((Polynomial.X : Polynomial (Polynomial ℂ)) -
              Polynomial.C ((Polynomial.C ζ) ^ j * alpha))) := by
                rw [Polynomial.eval₂_finsetProd]
                apply Finset.prod_congr rfl
                intro j _
                exact (hterm j).symm
    _ = x ^ d - (algebraMap ℂ R (-2) * y) ^ d := by
      rw [← hfactor]
      simp [coeffHom, alpha, Polynomial.eval₂_pow]
end PermanentRollout
