-- Prove2me | solution 1 for SkutellaCQP.NoRel.zqp_eq_zcqp_add
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:07:36.861747+00:00
-- url     : https://prove2.me/submissions/81dc7555-14ad-4ff1-ba92-0b3ca9056333

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

open SkutellaCQP.NoRel

open Matrix

local notation "vec" => SkutellaCQP.NoRel.vec

/-- The identity in the proof of Theorem 2.6 (p. 12):
`Z_QP(a) = Z_CQP(a) + ½ (c^T a - a^T diag(c) a)` for every `a ∈ ℝ^{mn}`. -/
theorem solution {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (a : Fin m → Fin n → ℝ) :
    ZQP p w a = ZCQP p w a +
      (1 / 2) * (cvec p w ⬝ᵥ vec a - vec a ⬝ᵥ (Matrix.diagonal (cvec p w) *ᵥ vec a)) := by
  unfold ZQP ZCQP
  rw [Matrix.add_mulVec, dotProduct_add]
  ring



#print axioms solution
