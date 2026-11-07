-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.minimumDistance_ge_of_ceil_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:18:52.708267+00:00
-- url     : https://prove2.me/submissions/e2601304-3d6e-4402-b3b8-a8cdcef48059

import Definitions.Def_QEC_Coding_QuantumTanner_Parameters
import Definitions.Def_QEC_Coding_QuantumTanner_SampleParameters

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical QEC.Coding.SmallSetExpansion
universe v
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    {I : Type v} [Fintype I] (C : LinearCode (ZMod 2) I)
    (bound : ℝ) (d : Nat) (hLower : HasMinimumDistanceAtLeast C (Nat.ceil bound))
    (hMinimum : MinimumDistance C d) : bound ≤ (d : ℝ) := by
  obtain ⟨x, hx, hx0, hWeight, _⟩ := hMinimum
  exact Nat.ceil_le.mp (hWeight ▸ hLower x hx hx0)
end QEC.Coding.QuantumTanner
