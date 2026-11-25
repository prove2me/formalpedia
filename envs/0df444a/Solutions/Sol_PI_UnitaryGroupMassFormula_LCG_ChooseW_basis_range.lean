-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ChooseW.basis_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:05.184831+00:00
-- url     : https://prove2.me/submissions/b4396ddc-e922-4a6f-b67e-9719d4491788

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_Choose
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
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.ChooseW
variable {K : Type*} [Field K] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.LCG.ChooseW
theorem _root_.solution (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (hk : A.rank = k) :
    ∃ z : Fin k → Fin n → K, LinearIndependent K (fun c => A *ᵥ z c) ∧
      ∀ w, A *ᵥ w ∈ Submodule.span K (Set.range fun c => A *ᵥ z c) := by
  let R := LinearMap.range A.mulVecLin
  let bas := Module.finBasisOfFinrankEq K R hk
  have hz : ∀ c, ∃ z, A *ᵥ z = (bas c : Fin n → K) := fun c => by
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (bas c).2
    exact ⟨z, by simpa using hz⟩
  choose z hz using hz
  have hspan : Submodule.span K (Set.range fun c => (bas c : Fin n → K)) = R := by
    rw [show (fun c => (bas c : Fin n → K)) = R.subtype ∘ bas from rfl, Set.range_comp,
      ← Submodule.map_span, bas.span_eq, Submodule.map_top, Submodule.range_subtype]
  refine ⟨z, ?_, ?_⟩
  · simp only [hz]
    exact bas.linearIndependent.map' R.subtype (Submodule.ker_subtype R)
  · intro w
    simp only [hz]
    rw [hspan]
    exact LinearMap.mem_range.mpr ⟨w, by simp⟩
end PI.UnitaryGroupMassFormula.LCG.ChooseW
