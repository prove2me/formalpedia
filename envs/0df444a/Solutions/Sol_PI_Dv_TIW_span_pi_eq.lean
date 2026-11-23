-- Prove2me | solution 1 for PI.Dv.TIW.span_pi_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:05:58.81684+00:00
-- url     : https://prove2.me/submissions/098ac1a5-34db-42f4-87cf-fea3e3b29ae8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.TIW
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V) :
    Submodule.span K ((Submodule.pi Set.univ M : Submodule (𝓞 K) (ι → V)) : Set (ι → V)) =
      Submodule.pi Set.univ (fun i => Submodule.span K (M i : Set V)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx i _
    exact Submodule.subset_span (hx i (Set.mem_univ i))
  · rw [← Submodule.iSup_map_single]
    refine iSup_le fun i => ?_
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    intro m hm
    rw [SetLike.mem_coe, Submodule.mem_comap]
    apply Submodule.subset_span
    intro j _
    by_cases h : j = i
    · subst h; simpa using hm
    · simp [h]
end PI.Dv.TIW
