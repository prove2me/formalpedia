-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.resF_sum_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:00.114797+00:00
-- url     : https://prove2.me/submissions/ddca436d-1d06-43c2-b9a8-1cae60aa397f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_DensGSDvr
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_resF_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula
open Classical ValuativeRel
variable (F : Type) [Field F] [ValuativeRel F]
namespace PI.UnitaryGroupMassFormula.CntFormula
theorem _root_.solution {ι : Type} [Fintype ι] (c x : ι → F) (hc : ∀ i, c i ∈ 𝒪[F]) (hx : ∀ i, x i ∈ 𝒪[F]) :
    resF F (∑ i, c i * x i) = ∑ i, resF F (c i) * resF F (x i) := by
  have hs : ((∑ i, (⟨c i, hc i⟩ : 𝒪[F]) * ⟨x i, hx i⟩ : 𝒪[F]) : F) = ∑ i, c i * x i := by
    simp
  rw [← hs, resF_coe, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← resF_coe F ⟨c i, hc i⟩, ← resF_coe F ⟨x i, hx i⟩]
end PI.UnitaryGroupMassFormula.CntFormula
