-- Prove2me | solution 1 for PI.GalTorsConj.W.conj_sum_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:22.129867+00:00
-- url     : https://prove2.me/submissions/b862e264-f77c-4aa9-b954-232a5b06d9b3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulMain
import Theorems.Thm_PI_GalTorsConj_W_conj_add_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Formalism.L2.Th1.F
variable {M₁ : IntermediateField ℚ ℂ} {ρ₁ : M₁ →ₐ[ℚ] ℂ}
namespace PI.GalTorsConj.W
theorem _root_.solution {ι : Type*} (s : Finset ι) (f f' : ι → ℂ) (h : ∀ i ∈ s, Cj1 M₁ ρ₁ (f i) (f' i)) :
    Cj1 M₁ ρ₁ (∑ i ∈ s, f i) (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨M₁.zero_mem, map_zero ρ₁⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact conj_add_alt (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end PI.GalTorsConj.W
