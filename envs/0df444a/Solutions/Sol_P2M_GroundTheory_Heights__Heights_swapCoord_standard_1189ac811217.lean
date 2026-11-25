-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_swapCoord_standard_1189ac811217
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:41:01.003396+00:00
-- url     : https://prove2.me/submissions/1e972233-2455-49aa-8ec5-1fcd1a3c8e67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsExamples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    (FullLattice.standard K 2).carrier.map ((swapCoord (K := K)).toLinearMap.restrictScalars (𝓞 K)) =
      (FullLattice.standard K 2).carrier := by
  rw [FullLattice.standard, Submodule.map_span, ← Set.range_comp]
  congr 1
  ext x
  simp only [Set.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨Equiv.swap 0 1 i, ?_⟩
    funext j
    fin_cases i <;> fin_cases j <;> rfl
  · rintro ⟨i, rfl⟩
    refine ⟨Equiv.swap 0 1 i, ?_⟩
    funext j
    fin_cases i <;> fin_cases j <;> rfl
end GroundTheory.Heights₂.Heights
