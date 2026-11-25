-- Prove2me | solution 1 for UpperTheory.Ram.mem_sq_of_dvd_condN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:48:54.545172+00:00
-- url     : https://prove2.me/submissions/2bb0e7f2-a45f-4493-890f-bc7f32e1ac31

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_CondSq
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostAx_mem_sq_of_dvd_QS
import Theorems.Thm_Formalism_HC_HostRaw_dvd_condN_iff
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


section
open NumberField IsDedekindDomain
namespace UpperTheory.Ram
private theorem mem_sq_of_sqrt {E : Type} [Field E] [NumberField E] {p : ℕ} {a : E} (ha : a ^ 2 = -(p : E))
    (P : Ideal (𝓞 E)) (hP : P.IsPrime) (hv : (p : 𝓞 E) ∈ P) : (p : 𝓞 E) ∈ P ^ 2 := by
  have hint : IsIntegral ℤ a := by
    refine IsIntegral.of_pow two_pos ?_
    rw [ha]
    have e : -(p : E) = algebraMap ℤ E (-(p : ℤ)) := by simp
    rw [e]
    exact isIntegral_algebraMap
  set b : 𝓞 E := ⟨a, hint⟩ with hb
  have hb2 : b ^ 2 = -(p : 𝓞 E) := by
    apply RingOfIntegers.ext
    push_cast
    exact ha
  have hbP : b ∈ P := by
    apply hP.mem_of_pow_mem 2
    rw [hb2]
    exact P.neg_mem hv
  have hsq : b ^ 2 ∈ P ^ 2 := Ideal.pow_mem_pow hbP 2
  rw [hb2] at hsq
  simpa using (P ^ 2).neg_mem hsq
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
end UpperTheory.Ram
end

set_option autoImplicit false
open NumberField IsDedekindDomain
open UpperTheory UpperTheory.Ram
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
namespace UpperTheory.Ram
theorem _root_.solution {p : ℕ} (hp : p.Prime) (h : p ∣ H.QS * H.q * H.d) (P : Ideal (𝓞 H.E)) (hP : P.IsPrime)
    (hv : (p : 𝓞 H.E) ∈ P) : (p : 𝓞 H.E) ∈ P ^ 2 := by
  haveI := hP
  have hc : p ∣ H.condN := h
  rcases (H.dvd_condN_iff hp).1 hc with hq | rfl | rfl
  · exact H.toHostAx.mem_sq_of_dvd_QS H.QS_exact hp hq P hv
  · exact mem_sq_of_sqrt H.sqq_sq P hP hv
  · exact mem_sq_of_sqrt H.sqd_sq P hP hv
end UpperTheory.Ram
