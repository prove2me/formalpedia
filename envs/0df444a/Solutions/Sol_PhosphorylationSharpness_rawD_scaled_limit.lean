-- Prove2me | solution 1 for PhosphorylationSharpness.rawD_scaled_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:28:12.592072+00:00
-- url     : https://prove2.me/submissions/1a27e54d-6318-4f84-a155-e745ec160f06

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
import Theorems.Thm_PhosphorylationSharpness_quotient_scaled_limit

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology
namespace PhosphorylationSharpness
theorem _root_.solution {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) (i : ℕ) :
    Tendsto (fun r : ℝ => (rawD p q r).coeff i/r^m) atTop
      (𝓝 (4*p.coeff m*q.coeff i)) := by
  have h := (quotient_scaled_limit hp hq i).const_mul 4
  convert h using 1 <;> simp [rawD, mul_div_assoc, mul_assoc]
end PhosphorylationSharpness
