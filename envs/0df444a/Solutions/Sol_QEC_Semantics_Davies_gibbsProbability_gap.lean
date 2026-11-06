-- Prove2me | solution 1 for QEC.Semantics.Davies.gibbsProbability_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:08:12.977784+00:00
-- url     : https://prove2.me/submissions/c1f89dc7-318c-4215-84e6-91d1b2b6f2b6

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity

set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
namespace QEC.Semantics.Davies
theorem _root_.solution (e : ι → ℝ) (β : ℝ) (i j : ι) :
    gibbsProbability β e j = Real.exp (-β * (e j-e i)) * gibbsProbability β e i := by
  unfold gibbsProbability
  rw [← mul_div_assoc, ← Real.exp_add]
  congr 2
  ring
end QEC.Semantics.Davies
