-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ChooseW.scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:17.507948+00:00
-- url     : https://prove2.me/submissions/d67fd974-da65-4667-b448-48bac0442779

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
namespace PI.UnitaryGroupMassFormula.LCG.ChooseW
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ m : ℤ, m ≠ 0 ∧ (m : E) • w ∈ Λ := by
  classical
  have hw : w ∈ Submodule.span E (Λ : Set (Fin n → E)) := hΛ ▸ Submodule.mem_top
  obtain ⟨N, f, g, hfg⟩ := Submodule.mem_span_set'.mp hw
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [← hfg, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ ((y : E) * f i) := by
    have := hint (f i) (Finset.mem_image_of_mem f (Finset.mem_univ i))
    simpa [zsmul_eq_mul] using this
  rw [smul_smul]
  have := Λ.smul_mem (⟨(y : E) * f i, hi⟩ : 𝓞 E) (g i).2
  convert this using 1
  exact (algebraMap_smul E _ _).symm
end PI.UnitaryGroupMassFormula.LCG.ChooseW
