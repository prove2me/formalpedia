-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.Parameters.switch_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:05:45.790513+00:00
-- url     : https://prove2.me/submissions/61d97523-cda4-48bf-81e2-aae4db8feea4

import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Theorems.Thm_ThreeSum1960614_uniform_entropy_bound

namespace Set
end Set
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters

namespace ThreeSum1960614.Machine

/-!
Expansion-232 analytic interface for the actual machine-source modules.
The definition bodies use the audited rational quartic parameter choice.
Closed analytic proofs supply the bounds; no program correctness contract
is assumed by this interface. Additional operational exponents must remain
the individual raw ledger costs for the universal rational-r bridge.
-/

noncomputable section
namespace ThreeSum.Parameters
open _root_.ThreeSum.Parameters

open _root_.Set


















































theorem entropy_phi_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1/2)) :
    _root_.ThreeSum.Parameters.entropy t < _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio*(1+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi t) := by
  simpa only [_root_.ThreeSum.Parameters.entropy,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi,_root_.ThreeSum1960614.entropy,
    _root_.ThreeSum1960614.rho,_root_.ThreeSum1960614.phi] using _root_.ThreeSum1960614.uniform_entropy_bound t ht















end ThreeSum.Parameters

end

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters

open _root_.Set
section

theorem ThreeSum1960614.Machine.ThreeSum.Parameters.switch_entropy_bound__implementation_79eb8cb48d {a t mu : ℝ}
    (ha : a ∈ Icc (0 : ℝ) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction) (ht : t ∈ Icc (0 : ℝ) (1/2))
    (hmu : 0 < mu) (hswitch : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi t < _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold a+9/((1-a)*mu)) :
    (1-a)*_root_.ThreeSum.Parameters.entropy t < _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio*(1+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving-2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)+9*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio/mu := by
  have hden : 0 < 1-a := by dsimp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction] at ha; linarith [ha.2]
  have hr : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio := by norm_num [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio]
  have hh := mul_lt_mul_of_pos_left (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropy_phi_bound ht) hden
  have hp := mul_lt_mul_of_pos_left hswitch (mul_pos hden hr)
  have hid : (1-a)*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio*(1+(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold a+9/((1-a)*mu))) =
      _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio*(1+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving-2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)+9*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio/mu := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold
    field_simp [ne_of_gt hden,ne_of_gt hmu]
    ring
  rw [← hid]
  nlinarith
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.Parameters.switch_entropy_bound__implementation_79eb8cb48d) := (@ThreeSum1960614.Machine.ThreeSum.Parameters.switch_entropy_bound__implementation_79eb8cb48d)

#print axioms solution
