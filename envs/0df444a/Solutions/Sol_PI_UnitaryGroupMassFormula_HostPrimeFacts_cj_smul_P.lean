-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.HostPrimeFacts.cj_smul_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:07.914672+00:00
-- url     : https://prove2.me/submissions/f1b161fa-3f60-40cc-ac4e-f3c5f23a3d64

import Definitions.Def_Formalism_PeriodIntegrals_EtaHostFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HostPrimeSplitting_FinrankOE
import Theorems.Thm_PI_UnitaryGroupMassFormula_HostPrimeFacts_cj_inv_fix
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open scoped Pointwise
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.HostPrimeFacts
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
namespace PI.UnitaryGroupMassFormula.HostPrimeFacts
theorem _root_.solution (P : HeightOneSpectrum (𝓞 H.E))
    (h1 : (aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card = 1) :
    (cj H) • P.asIdeal = P.asIdeal := by
  have hne : (cj H) • P.asIdeal ≠ ⊥ := by
    intro h
    apply P.ne_bot
    have h' := congrArg (fun I : Ideal (𝓞 H.E) => (cj H)⁻¹ • I) h
    simpa only [inv_smul_smul, Ideal.smul_bot] using h'
  haveI := P.isPrime
  let Q : HeightOneSpectrum (𝓞 H.E) := ⟨(cj H) • P.asIdeal, Ideal.IsPrime.smul (cj H), hne⟩
  have hunder : Q.under (𝓞 H.F) = P.under (𝓞 H.F) := by
    apply HeightOneSpectrum.ext
    ext a
    simp only [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap]
    show algebraMap (𝓞 H.F) (𝓞 H.E) a ∈ (cj H) • P.asIdeal ↔ _
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, cj_inv_fix]
  have hP : P ∈ aboveF (L := H.E) H.F (P.under (𝓞 H.F)) := by
    simp only [aboveF, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hQ : Q ∈ aboveF (L := H.E) H.F (P.under (𝓞 H.F)) := by
    simp only [aboveF, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact hunder
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
  rw [hx, Finset.mem_singleton] at hP hQ
  exact congrArg HeightOneSpectrum.asIdeal (hQ.trans hP.symm)
end PI.UnitaryGroupMassFormula.HostPrimeFacts
