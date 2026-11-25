-- Prove2me | solution 1 for PI.UnimodIdxWork.mem_conj_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:33:21.876402+00:00
-- url     : https://prove2.me/submissions/4a31fe67-d5c2-4205-b482-fff69e043181

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnimodIdx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularIndex_PairwiseDisjointCosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Pointwise Set Function
noncomputable section
open PI PI.UnimodIdxWork
variable {G : Type} [Group G]
namespace PI.UnimodIdxWork
theorem _root_.solution (K : Subgroup G) (g y : G) :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro h
    exact ⟨g⁻¹ * y * g, h, by simp [mul_assoc]⟩
end PI.UnimodIdxWork
