-- Prove2me | solution 1 for QLLL.SAT.classical_lll
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:48:12.257981+00:00
-- url     : https://prove2.me/submissions/7e93846c-4160-4600-ad5e-cf44313beb36

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Classical_KSAT
import Theorems.Thm_QLLL_Valuation_lll
import Mathlib
import Std.Sat.CNF

section

open QLLL
open QLLL.SAT
open Finset Std.Sat
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

theorem solution {m : ℕ} {A : Fin m → Finset Ω} {Γ : Fin m → Finset (Fin m)}
    {y : Fin m → ℝ} (hΓ : (counting Ω).IsDependencyGraph A Γ)
    (hy₀ : ∀ i, 0 ≤ y i) (hy₁ : ∀ i, y i < 1)
    (hA : ∀ i, 1 - y i * ∏ j ∈ Γ i, (1 - y j) ≤ counting Ω (A i)) :
    ∏ i, (1 - y i) ≤ counting Ω (univ.inf A) :=
  Valuation.lll (counting Ω) hΓ hy₀ hy₁ hA

end
