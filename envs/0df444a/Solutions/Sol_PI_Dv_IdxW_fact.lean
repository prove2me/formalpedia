-- Prove2me | solution 1 for PI.Dv.IdxW.fact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:40:17.855821+00:00
-- url     : https://prove2.me/submissions/4bbeb34f-60a6-4b4f-9772-33c56d84a5bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_SmulMemSpanSmul
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
open PI PI.Dv PI.Dv.IdxW
open NumberField IsDedekindDomain Module
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.IdxW
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {c : 𝓞 K} (hc : c ≠ 0) :
    ∃ k : ℕ, Formalism.BasicNotions.vAdd w (algebraMap (𝓞 K) K c) = k ∧ c ∈ w.asIdeal ^ k ∧
      ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∀ y ∈ w.asIdeal ^ k, s * y ∈ Ideal.span {c} := by
  classical
  set v := w.intValuation c with hv
  have hv0 : v ≠ 0 := w.intValuation_ne_zero c hc
  have hv1 : v ≤ 1 := w.intValuation_le_one c
  have hval : w.valuation K (algebraMap (𝓞 K) K c) = v := w.valuation_of_algebraMap c
  obtain ⟨m, hm⟩ : ∃ m : ℤ, v = WithZero.exp m := ⟨WithZero.log v, (WithZero.exp_log hv0).symm⟩
  have hm0 : m ≤ 0 := by
    rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv1
    exact hv1
  have hkm : (((-m).toNat : ℕ) : ℤ) = -m := by omega
  have hck : c ∈ w.asIdeal ^ (-m).toNat := by
    rw [← w.intValuation_le_pow_iff_mem, ← hv, hm, hkm, neg_neg]
  have hck1 : c ∉ w.asIdeal ^ ((-m).toNat + 1) := by
    intro h
    have h' := (w.intValuation_le_pow_iff_mem c _).2 h
    rw [← hv, hm, WithZero.exp_le_exp] at h'
    push_cast at h'
    omega
  refine ⟨(-m).toNat, ?_, hck, ?_⟩
  · simp only [Formalism.BasicNotions.vAdd, hval, hm, WithZero.log_exp]
    omega
  obtain ⟨J, hJ⟩ : w.asIdeal ^ (-m).toNat ∣ Ideal.span {c} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hck)
  have hJp : ¬ J ≤ w.asIdeal := by
    intro hle
    apply hck1
    have hle' : Ideal.span {c} ≤ w.asIdeal ^ ((-m).toNat + 1) := by
      rw [hJ, pow_succ]
      exact Ideal.mul_mono_right hle
    exact hle' (Ideal.mem_span_singleton_self c)
  obtain ⟨s, hsJ, hsp⟩ := SetLike.not_le_iff_exists.1 hJp
  refine ⟨s, hsp, fun y hy => ?_⟩
  rw [hJ, mul_comm s y]
  exact Ideal.mul_mem_mul hy hsJ
end PI.Dv.IdxW
