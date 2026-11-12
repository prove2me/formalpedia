-- Prove2me | solution 1 for TensorBTD.Cogradient.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-11T12:18:02.941393+00:00
-- url     : https://prove2.me/submissions/baeccece-2964-438d-8cc7-18115ec0892c

import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_TensorBTD_Cogradient_Setting

open TensorBTD.Cogradient
open Matrix

theorem solution {N J : ℕ} {I : Fin N → ℕ} (A : (n : Fin N) → Matrix (Fin (I n)) (Fin J) ℂ)
    (p : Equiv.Perm (Fin N)) :
    (krString A p)ᴴ * krString A p = Matrix.of fun j j' => ∏ n, ((A n)ᴴ * A n) j j' := by
  classical
  ext j j'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, krString, Matrix.of_apply]
  simp_rw [star_prod, ← Finset.prod_mul_distrib]
  calc
    _ = ∏ k, ∑ a : Fin (I (p k)), star (A (p k) a j) * A (p k) a j' :=
      (Fintype.prod_sum (fun k a => star (A (p k) a j) * A (p k) a j')).symm
    _ = _ := Fintype.prod_equiv p _ _ (fun _ => rfl)

#print axioms solution
