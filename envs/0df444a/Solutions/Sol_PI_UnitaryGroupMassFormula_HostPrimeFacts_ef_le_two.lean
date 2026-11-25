-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.HostPrimeFacts.ef_le_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:56.422053+00:00
-- url     : https://prove2.me/submissions/a4fe62a2-4fc6-45c8-a3e5-59795747f2c2

import Definitions.Def_Formalism_PeriodIntegrals_EtaHostFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HostPrimeSplitting_FinrankOE
import Theorems.Thm_PI_UnitaryGroupMassFormula_HostPrimeFacts_finrank_OE
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
theorem _root_.solution (P : HeightOneSpectrum (𝓞 H.E)) :
    P.asIdeal.ramificationIdx (𝓞 H.F) * P.asIdeal.inertiaDeg (𝓞 H.F) ≤ 2 := by
  set v := P.under (𝓞 H.F)
  haveI := v.isPrime
  haveI : Fintype (v.asIdeal.primesOver (𝓞 H.E)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 H.E)
  rw [finrank_OE] at hsum
  haveI : P.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hmem : P.asIdeal ∈ v.asIdeal.primesOver (𝓞 H.E) := ⟨P.isPrime, inferInstance⟩
  have hle := Finset.single_le_sum
    (f := fun q : v.asIdeal.primesOver (𝓞 H.E) => q.1.ramificationIdx (𝓞 H.F) * q.1.inertiaDeg (𝓞 H.F))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨P.asIdeal, hmem⟩)
  simp only at hle
  omega
end PI.UnitaryGroupMassFormula.HostPrimeFacts
