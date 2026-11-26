-- Prove2me | solution 1 for Sendov.rotate_rotate_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:06:11.98957+00:00
-- url     : https://prove2.me/submissions/1e1fedf2-d048-4b91-bfe6-97e48460d544

import Definitions.Def_Sendov_Interior
import Definitions.Def_Sendov_Boundary
import Definitions.Def_Sendov_Conjecture

set_option autoImplicit false
open Sendov
open Polynomial
namespace Sendov
theorem _root_.solution {ω : ℂ} (hω : ω ≠ 0) (p : ℂ[X]) : rotate ω⁻¹ (rotate ω p) = p := by
  have h : (C ω * X : ℂ[X]).comp (C ω⁻¹ * X) = X := by
    rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hω, C_1, one_mul]
  rw [rotate, rotate, comp_assoc, h, comp_X]
end Sendov
