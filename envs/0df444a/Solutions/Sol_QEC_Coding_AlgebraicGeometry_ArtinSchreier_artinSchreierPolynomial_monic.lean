-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial_monic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:42:40.238792+00:00
-- url     : https://prove2.me/submissions/60a2402f-47fc-4f07-ab07-72580ff615a8

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreier

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ArtinSchreier
open scoped WithZero BigOperators
open Polynomial
variable {F : Type*} [Field F]
namespace QEC.Coding.AlgebraicGeometry.ArtinSchreier
theorem _root_.solution (u : F) :
    (artinSchreierPolynomial u).Monic := by
  rw [artinSchreierPolynomial]
  convert monic_X_pow_add (p := X - C u) (show degree (X - C u) < (32 : ℕ) by
    calc
      degree (X - C u) ≤ max (degree X) (degree (C u)) := degree_sub_le _ _
      _ ≤ 1 := by exact max_le (by simp) (degree_C_le.trans (by norm_num))
      _ < (32 : ℕ) := by norm_num) using 1; ring
end QEC.Coding.AlgebraicGeometry.ArtinSchreier
