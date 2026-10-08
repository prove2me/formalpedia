-- Prove2me | solution 1 for QLLL.SAT.classical_lll_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:50:28.762805+00:00
-- url     : https://prove2.me/submissions/7ac33969-1099-4ea1-b95b-27f33b979384

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Classical_KSAT
import Theorems.Thm_QLLL_Valuation_lll_symmetric
import Mathlib
import Std.Sat.CNF

section

open QLLL
open QLLL.SAT
open Finset Std.Sat
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

theorem solution {m : ℕ} {A : Fin m → Finset Ω}
    {Γ : Fin m → Finset (Fin m)} {p : ℝ} {d : ℕ}
    (hΓ : (counting Ω).IsDependencyGraph A Γ) (hd : ∀ i, (Γ i).card ≤ d)
    (hA : ∀ i, 1 - p ≤ counting Ω (A i)) (hp : p * Real.exp 1 * (d + 1) ≤ 1) :
    0 < counting Ω (univ.inf A) :=
  Valuation.lll_symmetric (counting Ω) hΓ hd hA hp

end
