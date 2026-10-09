-- Prove2me | solution 1 for OCB2012.cj_posSemidef_of_completelyPositive
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T10:15:05.89493+00:00
-- url     : https://prove2.me/submissions/160a50fe-e469-405c-928a-fa6494a4f2c3

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Definitions.Def_OCB2012_cj

open Matrix
open scoped Kronecker ComplexOrder

open OCB2012 in
theorem solution {x1 x2 : Type*} [Fintype x1] [Fintype x2]
    [DecidableEq x1] [DecidableEq x2] (Φ : Matrix x1 x1 ℂ →ₗ[ℂ] Matrix x2 x2 ℂ)
    (hΦ : PeresTerno.IsCompletelyPositive Φ) : (cjMatrix Φ).PosSemidef := by
  set n := Fintype.card x1
  let e : x1 ≃ Fin n := Fintype.equivFin x1
  -- the unnormalized maximally entangled vector `∑ᵢ |i⟩|e i⟩`, as a one-row matrix
  let B : Matrix Unit (x1 × Fin n) ℂ := Matrix.of fun _ p => if p.2 = e p.1 then 1 else 0
  have hR : (Bᴴ * B).PosSemidef := posSemidef_conjTranspose_mul_self B
  have hA := hΦ n (Bᴴ * B) hR
  have key : cjMatrix Φ =
      ((PeresTerno.ampliate Φ (Bᴴ * B)).submatrix (fun p : x1 × x2 => (p.2, e p.1))
        (fun p : x1 × x2 => (p.2, e p.1)))ᵀ := by
    ext ⟨i, k⟩ ⟨j, l⟩
    have hm : (fun i' j' => (Bᴴ * B) (i', e j) (j', e i)) = single j i (1 : ℂ) := by
      ext i' j'
      simp [B, mul_apply, single, e, Equiv.apply_eq_iff_eq, eq_comm, and_comm, ite_and]
    simp only [cjMatrix, of_apply, transpose_apply, submatrix_apply, PeresTerno.ampliate]
    rw [hm]
  rw [key]
  exact (hA.submatrix _).transpose
