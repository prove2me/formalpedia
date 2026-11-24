-- Prove2me | solution 1 for PhosphorylationSharpness.next_dense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:24:41.317302+00:00
-- url     : https://prove2.me/submissions/338b67a5-026f-4e22-ac0d-698068396d5a

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Theorems.Thm_PhosphorylationSharpness_dense_step

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial
namespace PhosphorylationSharpness
theorem _root_.solution {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m)
    {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    DensePositive (nextN a b p q) (m+1) ∧
      DensePositive (nextJ a b p q) (m+1) := by
  constructor
  · simpa [nextN] using dense_step hp hq ((a+1)*(b+1)) 8 (2*(a+b)) 0
      (by positivity) (by norm_num) (by positivity) (by norm_num)
  · simpa [nextJ] using dense_step hq hp ((a-1)*(b-1)) 8 0 (4*(a+b))
      (mul_pos (by linarith) (by linarith)) (by norm_num) (by norm_num) (by positivity)
end PhosphorylationSharpness
