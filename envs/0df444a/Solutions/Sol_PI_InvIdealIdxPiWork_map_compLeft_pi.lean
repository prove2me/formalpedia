-- Prove2me | solution 1 for PI.InvIdealIdxPiWork.map_compLeft_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:54.662674+00:00
-- url     : https://prove2.me/submissions/1cb2ebb0-a6f1-4d97-b026-80d89c351053

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_InvIdealIdxPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvertibleIdealIndex_SubmodulePiToAddSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvIdealIdxPiWork
open NumberField nonZeroDivisors
namespace PI.InvIdealIdxPiWork
theorem _root_.solution {ι : Type} {G G' : Type*} [AddGroup G] [AddGroup G'] (φ : G →+ G')
    (A : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).map (φ.compLeft ι) =
      AddSubgroup.pi Set.univ (fun i => (A i).map φ) := by
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_pi, Set.mem_univ, true_implies, forall_const]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    exact ⟨x i, hx i, rfl⟩
  · intro h
    choose x hx hxy using h
    exact ⟨x, hx, funext hxy⟩
end PI.InvIdealIdxPiWork
