-- Prove2me | solution 1 for Reformulated.TransposeInverseTheory.coe_transposeInv_inv
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:38:08.993811+00:00
-- url     : https://prove2.me/submissions/d5c7dcca-476c-4104-92a6-41eeb2b07943

import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_TransposeInverse_TransposeInv
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Reformulated Reformulated.TransposeInverseTheory
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
theorem _root_.solution (g : GL n R) :
    (((transposeInv g)⁻¹ : GL n R) : Matrix n n R) = (g : Matrix n n R)ᵀ := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | decide
    | (intros; omega)
    | (intros; simp)
    | (intros; simp_all)
    | (intros; norm_num)
    | (intros; positivity)
    | (intros; aesop)
    | (intros; nlinarith)
    | (intros; field_simp; ring)
    | (intros; ext; simp)
    | (intros; constructor <;> intro h <;> simpa using h)
    | (intros; exact?)
  trace "HIT_18_1"

