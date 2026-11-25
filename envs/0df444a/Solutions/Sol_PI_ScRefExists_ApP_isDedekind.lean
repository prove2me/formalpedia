-- Prove2me | solution 1 for PI.ScRefExists.ApP.isDedekind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:44:11.28684+00:00
-- url     : https://prove2.me/submissions/8fad9fce-96bb-4910-8321-9b06666adfcc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PrincipalIdealRingAtPrime
import Theorems.Thm_PI_ScRefExists_ApP_isLoc
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


section
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
namespace PI.ScRefExists.ApP
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
private theorem coe_algebraMap_int_ringOfIntegers (n : ℤ) :
    ((algebraMap ℤ (𝓞 I.E) n : 𝓞 I.E) : I.E) = (n : I.E) := by
  rw [algebraMap_int_eq, eq_intCast]
  exact map_intCast (algebraMap (𝓞 I.E) I.E) n
private theorem algebraMapSubmonoid_primeCompl_le_nonZeroDivisors (p : ℕ) [Fact p.Prime] :
    Algebra.algebraMapSubmonoid (𝓞 I.E) (Pz p).primeCompl ≤ nonZeroDivisors (𝓞 I.E) := by
  rintro _ ⟨n, hn, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro h
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (Pz p).zero_mem
  apply hn0
  have h2 := congrArg ((↑) : 𝓞 I.E → I.E) h
  rw [coe_algebraMap_int_ringOfIntegers] at h2
  simpa using h2
end PI.ScRefExists.ApP
end
end

set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
open PI PI.ScRefExists PI.ScRefExists.ApP
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.ApP
theorem _root_.solution {p : ℕ} [Fact p.Prime] : IsDedekindDomain (Ap I p) := by
  haveI := isLoc I (p := p)
  exact IsLocalization.isDedekindDomain (𝓞 I.E) (algebraMapSubmonoid_primeCompl_le_nonZeroDivisors I p) (Ap I p)
end PI.ScRefExists.ApP
