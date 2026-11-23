-- Prove2me | solution 1 for PI.Residue.mem_lat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:39.630854+00:00
-- url     : https://prove2.me/submissions/fa7d36fb-c189-4926-8127-31b8ad642842

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BUnfold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable {K : Type} [Field K] [NumberField K]
namespace PI.Residue
theorem _root_.solution {J : (Ideal (𝓞 K))⁰} {x : mixedSpace K} :
    x ∈ lat K J ↔ ∃ a : 𝓞 K, a ∈ (J : Ideal (𝓞 K)) ∧ mixedEmbedding K (a : K) = x := by
  rw [lat, mem_idealLattice]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, ?_, rfl⟩
    rw [SetLike.mem_coe, FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal]
    exact ⟨a, ha, rfl⟩
end PI.Residue
