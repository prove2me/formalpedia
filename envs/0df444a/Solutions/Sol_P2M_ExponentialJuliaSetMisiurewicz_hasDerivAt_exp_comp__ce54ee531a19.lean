-- Prove2me | solution 1 for P2M_ExponentialJuliaSetMisiurewicz_hasDerivAt_exp_comp__ce54ee531a19
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:56.413367+00:00
-- url     : https://prove2.me/submissions/5a892a3c-30a4-4f1c-8ed2-c215883fd4f1

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Definitions.Def_ExpChaotic_Basic

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' z) :
    HasDerivAt (Complex.exp ∘ f)
      (Complex.exp (f z) * f') z := by
  exact (Complex.hasDerivAt_exp (f z)).comp z hf
end ExponentialJuliaSetMisiurewicz
