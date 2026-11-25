-- Prove2me | solution 1 for PI.AmpRootJacW.phi_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:56:42.011255+00:00
-- url     : https://prove2.me/submissions/1abd9fdb-d66d-4bc1-b9e8-b64b302dbb1c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero
import Theorems.Thm_PI_AmpRootJacW_invC_eq
import Theorems.Thm_PI_AmpRootJacW_shear_mp
import Theorems.Thm_PI_AmpRootJacW_mp_unitConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.AmpRootJacW
variable {n : ℕ}
namespace PI.AmpRootJacW
theorem _root_.solution (S : Finset (Fin n × Fin n)) (hS : ∀ q ∈ S, q.1 < q.2) (τ : S ≃ S) (c : S → ℂ)
    (hc : ∀ q, ‖c q‖ = 1) :
    MeasurePreserving (fun (v : S → ℂ) q => c q * star (invC S v (τ q))) volume volume := by
  have h1 := mp_unitConj τ (fun q => -c q) (fun q => by rw [norm_neg]; exact hc q)
  have h2 := shear_mp S hS
  convert h1.comp h2 using 1
  funext v q
  simp only [Function.comp_apply, invC_eq S hS v (τ q), star_neg, star_add]
  ring
end PI.AmpRootJacW
