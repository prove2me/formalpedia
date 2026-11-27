-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.HostPrimeFacts.unram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:19:40.003888+00:00
-- url     : https://prove2.me/submissions/aa91a845-cb97-4276-b10f-17741c9480c6

import Definitions.Def_Formalism_PeriodIntegrals_EtaHostFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HostPrimeSplitting_FinrankOE
import Theorems.Thm_PI_UnitaryGroupMassFormula_HostPrimeFacts_cj_fix
import Theorems.Thm_PI_UnitaryGroupMassFormula_HostPrimeFacts_cj_smul_P
import Theorems.Thm_PI_UnitaryGroupMassFormula_HostPrimeFacts_ef_le_two
import Theorems.Thm_PI_UnitaryGroupMassFormula_HostPrimeFacts_approx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open scoped Pointwise
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.HostPrimeFacts
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
namespace PI.UnitaryGroupMassFormula.HostPrimeFacts
theorem _root_.solution : PI.EtaHostFacts.Unram := by
  intro R H P h1
  haveI := P.isPrime
  have he := Ideal.ramificationIdx_pos P.asIdeal (𝓞 H.F)
  have hf := Ideal.inertiaDeg_pos P.asIdeal (𝓞 H.F)
  have hef := ef_le_two H P
  by_contra hne
  have h2 : 2 * P.asIdeal.inertiaDeg (𝓞 H.F) ≤
      P.asIdeal.ramificationIdx (𝓞 H.F) * P.asIdeal.inertiaDeg (𝓞 H.F) :=
    Nat.mul_le_mul_right _ (by omega)
  have hf1 : P.asIdeal.inertiaDeg (𝓞 H.F) = 1 := by
    generalize P.asIdeal.ramificationIdx (𝓞 H.F) * P.asIdeal.inertiaDeg (𝓞 H.F) = m at *
    omega
  have hfix := cj_smul_P H P h1
  apply H.der.unramEF P.asIdeal P.isPrime P.ne_bot
  intro x
  show (cj H) • x - x ∈ P.asIdeal
  obtain ⟨a, ha⟩ := approx H P hf1 x
  have h3 : (cj H) • (x - algebraMap (𝓞 H.F) (𝓞 H.E) a) ∈ (cj H) • P.asIdeal :=
    Ideal.smul_mem_pointwise_smul _ _ _ ha
  rw [hfix, smul_sub, cj_fix] at h3
  have h4 : (cj H) • x - x = ((cj H) • x - algebraMap (𝓞 H.F) (𝓞 H.E) a) -
      (x - algebraMap (𝓞 H.F) (𝓞 H.E) a) := by ring
  rw [h4]
  exact sub_mem h3 ha
end PI.UnitaryGroupMassFormula.HostPrimeFacts
