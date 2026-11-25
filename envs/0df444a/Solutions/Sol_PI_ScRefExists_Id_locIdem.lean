-- Prove2me | solution 1 for PI.ScRefExists.Id.locIdem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:27:36.142967+00:00
-- url     : https://prove2.me/submissions/2710d91f-f8df-4e45-ab68-229ab04df023

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLiftOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_HenselRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLoc
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_LocalEndW_isAdicComplete
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
open NumberField IsDedekindDomain Polynomial
open PI PI.ScRefExists PI.ScRefExists.Id
namespace PI.ScRefExists.Id
theorem _root_.solution : LocIdem := by
  intro F _ _ v g α β hg hgv hα hβ
  classical
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  have memO : ∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 := fun x => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  let ϖ : v.adicCompletionIntegers F := ⟨((g : ℕ) : v.adicCompletion F), (memO _).2 hgv.le⟩
  let aO : v.adicCompletionIntegers F := ⟨α, (memO _).2 hα⟩
  let bO : v.adicCompletionIntegers F := ⟨β, (memO _).2 hβ⟩
  have hϖ : ϖ ≠ 0 := by
    intro h
    have h' : ((g : ℕ) : v.adicCompletion F) = 0 := congrArg Subtype.val h
    exact (Nat.cast_ne_zero.mpr (by omega : g ≠ 0)) h'
  have h1 : ‖(ϖ : v.adicCompletion F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr hgv
  haveI := PI.LocalEndW.isAdicComplete v ϖ hϖ h1
  let f : Polynomial (v.adicCompletionIntegers F) := X ^ 2 - C (1 + ϖ * aO) * X + C (ϖ * bO)
  have hf : f.Monic := by simp only [f]; monicity!
  have h0 : f.eval 0 ∈ Ideal.span {ϖ} := by
    have e : f.eval 0 = bO * ϖ := by
      simp only [f, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C]; ring
    rw [e, Ideal.mem_span_singleton']
    exact ⟨bO, rfl⟩
  have hd : f.derivative.eval 0 = -(1 + ϖ * aO) := by simp [f]
  have hm : Ideal.Quotient.mk (Ideal.span {ϖ}) (-(1 + ϖ * aO)) = -1 := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {ϖ})), ← map_neg, Ideal.Quotient.eq,
      Ideal.mem_span_singleton']
    exact ⟨-aO, by ring⟩
  obtain ⟨ρ, hρ, hρI⟩ := HenselianRing.is_henselian (I := Ideal.span {ϖ}) f hf 0 h0
    (by rw [hd, hm]; exact isUnit_one.neg)
  rw [sub_zero, Ideal.mem_span_singleton'] at hρI
  obtain ⟨r0, rfl⟩ := hρI
  have hroot : (r0 * ϖ) ^ 2 - (1 + ϖ * aO) * (r0 * ϖ) + ϖ * bO = 0 := by
    have h : f.eval (r0 * ϖ) = 0 := hρ
    simpa only [f, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C] using h
  have hu : IsUnit (1 + ϖ * (aO - 2 * r0)) := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have hy : Valued.v ((aO - 2 * r0 : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 :=
      (memO _).1 (aO - 2 * r0).2
    have hlt : Valued.v ((ϖ : v.adicCompletion F) *
        ((aO - 2 * r0 : v.adicCompletionIntegers F) : v.adicCompletion F)) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hy) hgv
    exact (Valued.v).map_one_add_of_lt hlt
  obtain ⟨U, hU⟩ := hu
  obtain ⟨wO, hwO⟩ : ∃ w : v.adicCompletionIntegers F, w = ((U⁻¹ : (v.adicCompletionIntegers F)ˣ) :
      v.adicCompletionIntegers F) := ⟨_, rfl⟩
  have huw : (1 + ϖ * (aO - 2 * r0)) * wO = 1 := by rw [← hU, hwO]; exact U.mul_inv
  obtain ⟨c1, hc1⟩ : ∃ c : v.adicCompletionIntegers F, c = -(aO - 2 * r0) * wO := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c : v.adicCompletionIntegers F, c = r0 * wO := ⟨_, rfl⟩
  have hA : (1 + ϖ * aO) * (1 + ϖ * c1) ^ 2 - 2 * (1 + ϖ * c1) * (ϖ * c2) = 1 + ϖ * c1 := by
    rw [hc1, hc2]
    linear_combination ((1 + ϖ * (-(aO - 2 * r0) * wO)) * (1 - (1 + ϖ * aO))) * huw
  have hB : (ϖ * c2) ^ 2 - ϖ * bO * (1 + ϖ * c1) ^ 2 = -(ϖ * c2) := by
    rw [hc1, hc2]
    linear_combination (-(r0 * ϖ) * wO + ϖ * bO * (2 * wO - ((1 + ϖ * (aO - 2 * r0)) * wO - 1))) * huw
      + (-wO ^ 2) * hroot
  have hC : (ϖ * c2) ^ 2 - (1 + ϖ * aO) * (ϖ * c2) * (1 + ϖ * c1) + ϖ * bO * (1 + ϖ * c1) ^ 2 = 0 := by
    rw [hc1, hc2]
    linear_combination ((1 + ϖ * aO) * (r0 * ϖ) * wO - 2 * (ϖ * bO) * wO
      + ϖ * bO * ((1 + ϖ * (aO - 2 * r0)) * wO - 1)) * huw + wO ^ 2 * hroot
  refine ⟨(c1 : v.adicCompletion F), (c2 : v.adicCompletion F), (memO _).1 c1.2, (memO _).1 c2.2,
    ?_, ?_, ?_⟩
  · have e := congrArg (v.adicCompletionIntegers F).subtype hA
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat] at e
    exact e
  · have e := congrArg (v.adicCompletionIntegers F).subtype hB
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, map_neg] at e
    exact e
  · have e := congrArg (v.adicCompletionIntegers F).subtype hC
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, map_zero] at e
    exact e
end PI.ScRefExists.Id
