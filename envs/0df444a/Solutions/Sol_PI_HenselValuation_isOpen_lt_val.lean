-- Prove2me | solution 1 for PI.HenselValuation.isOpen_lt_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:49.335363+00:00
-- url     : https://prove2.me/submissions/bf86b10b-bf80-4f3d-9ee3-524ae37eb3f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Hensel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HenselOpenValuation_IsOpenLeVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Polynomial Topology
open PI PI.HenselValuation
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace PI.HenselValuation
theorem _root_.solution (γ : ValueGroupWithZero F) : IsOpen {x : F | γ < valuation F x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx' : γ < valuation F x := hx
  have hx0 : valuation F x ≠ 0 := (lt_of_le_of_lt zero_le hx').ne'
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 _ hx0, fun y hy => ?_⟩
  have hy' : valuation F (y - x) < valuation F x := by simpa using hy
  show γ < valuation F y
  rw [Valuation.map_eq_of_sub_lt _ hy']
  exact hx'
end PI.HenselValuation
