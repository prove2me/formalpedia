-- Prove2me | solution 1 for Pseudorandom.CoordGap.neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:55.249976+00:00
-- url     : https://prove2.me/submissions/12e7a632-ac65-433b-bc81-eff194e0cdf5

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*}
namespace Pseudorandom
namespace CoordGap
theorem _root_.solution {ι : Type*} [DecidableEq ι] {f : (ι → α) → ℝ} {c : ι → ℝ}
    (h : CoordGap f c) : CoordGap (fun ω => -f ω) c := by
  intro i ω a b
  have := h i ω a b
  rw [← abs_neg]; convert this using 2; ring
end CoordGap
end Pseudorandom
