-- Prove2me | solution 1 for PIW.AdelClassFin.DictInter.one_mem_tSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:43:47.702267+00:00
-- url     : https://prove2.me/submissions/cadebd4a-474a-4226-b1f9-1d2335337843

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
import Theorems.Thm_PIW_AdelClassFin_DictInter_tau_tmul
import Theorems.Thm_PIW_AdelClassFin_DictInter_algebraMap_mem_intAd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
open PIW.AdelClassFin.DictInter
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PIW.AdelClassFin.DictInter
theorem _root_.solution : (1 : E ⊗[F] Af F) ∈ tSet F E := by
  show ∀ w ∈ dualSet F E, tau w ((1 : E) ⊗ₜ[F] (1 : Af F)) ∈ Formalism.UG.intAd F
  intro w hw
  have hw1 := (show ∀ a : 𝓞 E, Algebra.trace F E (w * (a : E)) ∈ (algebraMap (𝓞 F) F).range from hw) 1
  obtain ⟨x, hx⟩ := hw1
  rw [tau_tmul, ← Algebra.algebraMap_eq_smul_one]
  have hx' : Algebra.trace F E (w * (1 : E)) = algebraMap (𝓞 F) F x := by
    rw [hx]
    rfl
  rw [hx']
  exact algebraMap_mem_intAd x
end PIW.AdelClassFin.DictInter
