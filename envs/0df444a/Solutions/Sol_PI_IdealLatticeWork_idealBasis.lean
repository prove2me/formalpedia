-- Prove2me | solution 1 for PI.IdealLatticeWork.idealBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:46.591827+00:00
-- url     : https://prove2.me/submissions/cf56ab7a-4eea-4a36-b4d5-616b32703e87

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdealLatticeBasis_IdealBasisAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdealLatticeBasis_IdealBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.IdealLatticeWork
namespace PI.IdealLatticeWork
theorem _root_.solution : IdealBasis := by
  intro K _ _ b cc hcc
  classical
  let bI := Ideal.selfBasis b cc hcc
  refine ⟨(bI 0 : 𝓞 K), (bI 0).2, (bI 1 : 𝓞 K), (bI 1).2, ?_, ?_⟩
  · intro c hc
    refine ⟨bI.repr ⟨c, hc⟩ 0, bI.repr ⟨c, hc⟩ 1, ?_⟩
    have h := congrArg Subtype.val (bI.sum_repr ⟨c, hc⟩)
    rw [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul_of_tower,
      Submodule.coe_smul_of_tower] at h
    exact h.symm
  · refine ⟨b.repr (bI 0) 0, b.repr (bI 0) 1, b.repr (bI 1) 0, b.repr (bI 1) 1, ?_, ?_, ?_⟩
    · have h := b.sum_repr (bI 0 : 𝓞 K)
      rw [Fin.sum_univ_two] at h
      exact h.symm
    · have h := b.sum_repr (bI 1 : 𝓞 K)
      rw [Fin.sum_univ_two] at h
      exact h.symm
    · have h := Ideal.natAbs_det_basis_change b cc bI
      rw [Module.Basis.det_apply, Matrix.det_fin_two] at h
      simp only [Module.Basis.toMatrix_apply, Function.comp_apply] at h
      rw [← h]
      congr 1
      ring
end PI.IdealLatticeWork
