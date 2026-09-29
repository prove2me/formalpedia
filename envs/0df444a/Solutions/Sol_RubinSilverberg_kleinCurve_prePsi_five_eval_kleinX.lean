-- Prove2me | solution 1 for RubinSilverberg.kleinCurve_prePsi_five_eval_kleinX
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b991aee0-f738-58c1-b573-4f1ee7c4c883

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.Tactic.Ring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_kleinCurve_prePsi_five_eval_kleinX

open Polynomial WeierstrassCurve RubinSilverberg

namespace M4cP4RS

section Cert

variable {K : Type*} [Field K]

theorem preΨ'_five {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
  have h := W.preΨ'_odd 0
  simpa [preΨ'_four, preΨ'_two, preΨ'_one, preΨ'_three] using h

theorem eval_preΨ'_five_of_short {R : Type*} [CommRing R] (W : WeierstrassCurve R) (h₁ : W.a₁ = 0)
    (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (x : R) :
    (W.preΨ' 5).eval x =
      5 * x ^ 12 + 62 * W.a₄ * x ^ 10 + 380 * W.a₆ * x ^ 9 - 105 * W.a₄ ^ 2 * x ^ 8
        + 240 * W.a₄ * W.a₆ * x ^ 7 - (300 * W.a₄ ^ 3 + 240 * W.a₆ ^ 2) * x ^ 6
        - 696 * W.a₄ ^ 2 * W.a₆ * x ^ 5 - (125 * W.a₄ ^ 4 + 1920 * W.a₄ * W.a₆ ^ 2) * x ^ 4
        - (80 * W.a₄ ^ 3 * W.a₆ + 1600 * W.a₆ ^ 3) * x ^ 3
        - (50 * W.a₄ ^ 5 + 240 * W.a₄ ^ 2 * W.a₆ ^ 2) * x ^ 2
        - (100 * W.a₄ ^ 4 * W.a₆ + 640 * W.a₄ * W.a₆ ^ 3) * x
        + (W.a₄ ^ 6 - 32 * W.a₄ ^ 3 * W.a₆ ^ 2 - 256 * W.a₆ ^ 4) := by
  rw [preΨ'_five]
  simp only [eval_sub, eval_mul, eval_pow, eval_add, eval_C, eval_X, eval_ofNat, preΨ₄, Ψ₂Sq, Ψ₃,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, h₁, h₂, h₃]
  ring

theorem main [CharZero K] (u : K) :
    ((kleinCurve u).preΨ' 5).eval (kleinX u) = 0 := by
  rw [eval_preΨ'_five_of_short (kleinCurve u) rfl rfl rfl]
  show 5 * kleinX u ^ 12 + 62 * (-kleinH u / 48) * kleinX u ^ 10 + 380 * (kleinT u / 864) * kleinX u ^ 9
      - 105 * (-kleinH u / 48) ^ 2 * kleinX u ^ 8
      + 240 * (-kleinH u / 48) * (kleinT u / 864) * kleinX u ^ 7
      - (300 * (-kleinH u / 48) ^ 3 + 240 * (kleinT u / 864) ^ 2) * kleinX u ^ 6
      - 696 * (-kleinH u / 48) ^ 2 * (kleinT u / 864) * kleinX u ^ 5
      - (125 * (-kleinH u / 48) ^ 4 + 1920 * (-kleinH u / 48) * (kleinT u / 864) ^ 2) * kleinX u ^ 4
      - (80 * (-kleinH u / 48) ^ 3 * (kleinT u / 864) + 1600 * (kleinT u / 864) ^ 3) * kleinX u ^ 3
      - (50 * (-kleinH u / 48) ^ 5 + 240 * (-kleinH u / 48) ^ 2 * (kleinT u / 864) ^ 2) * kleinX u ^ 2
      - (100 * (-kleinH u / 48) ^ 4 * (kleinT u / 864) + 640 * (-kleinH u / 48) * (kleinT u / 864) ^ 3)
          * kleinX u
      + ((-kleinH u / 48) ^ 6 - 32 * (-kleinH u / 48) ^ 3 * (kleinT u / 864) ^ 2 - 256 * (kleinT u / 864) ^ 4)
      = 0
  unfold kleinX kleinH kleinT
  ring

end Cert

end M4cP4RS

theorem solution {K : Type*} [Field K] [CharZero K] (u : K) :
    ((kleinCurve u).preΨ' 5).eval (kleinX u) = 0 :=
  M4cP4RS.main u

end S_RubinSilverberg_kleinCurve_prePsi_five_eval_kleinX
end P2MW
export P2MW.S_RubinSilverberg_kleinCurve_prePsi_five_eval_kleinX (solution)
