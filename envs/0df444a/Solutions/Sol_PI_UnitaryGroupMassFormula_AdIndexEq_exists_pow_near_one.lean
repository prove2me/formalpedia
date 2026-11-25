-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.exists_pow_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:27.994808+00:00
-- url     : https://prove2.me/submissions/df10b871-5081-46f9-b5d7-9df125b169cf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPow
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_inR_neg
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_inR_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_inR_pow
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_exists_pow_sub
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v)
    {t : v.adicCompletion I.F} (htO : t ∈ v.adicCompletionIntegers I.F)
    (hsum : α + sigV I v α = incL I v t) (hα : sigV I v α * α = 1) (N : ℕ) (hN : 0 < N) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ w w', InR I v α w ∧ InR I v α w' ∧ α ^ m - 1 = incL I v N * w ∧
      sigV I v α ^ m - 1 = incL I v N * w' := by
  have ht : α * α = incL I v t * α - 1 := by
    rw [← hsum]
    linear_combination (-1 : Av I v) * hα
  have hsig : InR I v α (sigV I v α) :=
    ⟨t, -1, htO, neg_mem (one_mem _), by
      simp only [map_neg, map_one]
      linear_combination hsum⟩
  obtain ⟨i, j, hij, w0, hw0, e0⟩ := exists_pow_sub I v α htO ht N hN
  obtain ⟨m, rfl⟩ : ∃ m, j = i + m := ⟨j - i, by omega⟩
  have hm : 1 ≤ m := by omega
  have hpi : sigV I v α ^ i * α ^ i = 1 := by rw [← mul_pow, hα, one_pow]
  have hpm : sigV I v α ^ m * α ^ m = 1 := by rw [← mul_pow, hα, one_pow]
  have e1 : α ^ m - 1 = incL I v N * (sigV I v α ^ i * w0) := by
    have : α ^ m - 1 = sigV I v α ^ i * (α ^ (i + m) - α ^ i) := by
      rw [pow_add]
      linear_combination (1 - α ^ m) * hpi
    rw [this, e0]
    ring
  refine ⟨m, hm, sigV I v α ^ i * w0, -(sigV I v α ^ m) * (sigV I v α ^ i * w0),
    inR_mul I v α htO ht (inR_pow I v α htO ht hsig i) hw0,
    inR_mul I v α htO ht (inR_neg I v α (inR_pow I v α htO ht hsig m))
      (inR_mul I v α htO ht (inR_pow I v α htO ht hsig i) hw0), e1, ?_⟩
  have : sigV I v α ^ m - 1 = -(sigV I v α ^ m) * (α ^ m - 1) := by
    linear_combination hpm
  rw [this, e1]
  ring
end PI.UnitaryGroupMassFormula.AdIndexEq
