-- Prove2me | solution 1 for PI.VolStabS.addIntF_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:50:21.12905+00:00
-- url     : https://prove2.me/submissions/3b8a6e1b-bdc8-4add-ba65-dc7c63fdf308

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensSAInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField
open scoped nonZeroDivisors
namespace PI.VolStabS
private theorem exists_trace_mul_eq_linearMap (F : Type) [Field F] [NumberField F] (f : F →ₗ[ℚ] ℚ) :
    ∃ β : F, ∀ y : F, f y = Algebra.trace ℚ F (β * y) := by
  have hnd := traceForm_nondegenerate ℚ F
  obtain ⟨β, hβ⟩ : ∃ β, (LinearMap.BilinForm.toDual (Algebra.traceForm ℚ F) hnd) β = f :=
    ⟨_, LinearEquiv.apply_symm_apply _ f⟩
  refine ⟨β, fun y => ?_⟩
  rw [← hβ, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply]
end PI.VolStabS
end
end

set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open PI PI.VolStabS
namespace PI.VolStabS
theorem _root_.solution : AddIntF := by
  intro F _ _ Λ ⟨c0, hc0, hc0Λ⟩ hnot g hg
  have hmul : ∀ (r : 𝓞 F) (x : F), x ∈ Λ → algebraMap (𝓞 F) F r * x ∈ Λ := by
    intro r x hx
    have h1 := Λ.smul_mem r hx
    rw [Algebra.smul_def] at h1
    exact h1
  obtain ⟨bb, hbb⟩ : ∃ bb, bb = NumberField.integralBasis F := ⟨_, rfl⟩
  have hmem : ∀ i, c0 * bb i ∈ Λ := by
    intro i
    rw [hbb, NumberField.integralBasis_apply, mul_comm]
    exact hmul _ _ hc0Λ
  choose n hn using fun i => hg _ (hmem i)
  let h0 : F →ₗ[ℚ] ℚ := bb.constr ℚ (fun i => (n i : ℚ))
  have hh0 : ∀ y : F, g (c0 * y) = ((h0 y : ℚ) : ℂ) := by
    let L1 : F →+ ℂ := g.comp (AddMonoidHom.mulLeft c0)
    let L2 : F →+ ℂ := (Rat.castHom ℂ).toAddMonoidHom.comp h0.toAddMonoidHom
    have hL : L1.toRatLinearMap = L2.toRatLinearMap := by
      refine bb.ext (fun i => ?_)
      simp [L1, L2, h0, hn i]
    intro y
    have h1 := congrArg (fun L : F →ₗ[ℚ] ℂ => L y) hL
    simpa [L1, L2] using h1
  obtain ⟨β, hβ⟩ := exists_trace_mul_eq_linearMap F h0
  have hgx : ∀ x : F, g x = ((Algebra.trace ℚ F (β * c0⁻¹ * x) : ℚ) : ℂ) := by
    intro x
    have h1 := hh0 (c0⁻¹ * x)
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul] at h1
    rw [h1, hβ, mul_assoc]
  intro a
  by_contra ha
  have hβ0 : β * c0⁻¹ ≠ 0 := by
    intro h0'
    apply ha
    rw [hgx, h0', zero_mul, map_zero, Rat.cast_zero]
  have h10 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    intro h
    have h1 : (1 : F) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [FractionalIdeal.mem_one_iff]
      exact ⟨1, map_one _⟩
    rw [h, FractionalIdeal.mem_zero_iff] at h1
    exact one_ne_zero h1
  have hdual : ∀ x ∈ Λ,
      β * c0⁻¹ * x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    intro x hx
    rw [FractionalIdeal.mem_dual h10]
    intro b hb
    rw [FractionalIdeal.mem_one_iff] at hb
    obtain ⟨r, rfl⟩ := hb
    obtain ⟨m, hm⟩ := hg _ (hmul r x hx)
    rw [RingHom.mem_range]
    refine ⟨m, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast]
    have h1 := hgx (algebraMap (𝓞 F) F r * x)
    have h2 : ((Algebra.trace ℚ F (β * c0⁻¹ * (algebraMap (𝓞 F) F r * x)) : ℚ) : ℂ)
        = ((m : ℚ) : ℂ) := by
      rw [← h1, hm, Rat.cast_intCast]
    rw [Rat.cast_inj] at h2
    rw [← h2]
    congr 1
    ring
  obtain ⟨d, hd, hdint⟩ :=
    (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).isFractional
  have hd0 : algebraMap (𝓞 F) F d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  apply hnot ((algebraMap (𝓞 F) F d * (β * c0⁻¹))⁻¹) (inv_ne_zero (mul_ne_zero hd0 hβ0))
  intro x hx
  obtain ⟨r, hr⟩ := hdint _ (hdual x hx)
  refine ⟨r, ?_⟩
  rw [Algebra.smul_def] at hr
  have hr' : (r : F) = algebraMap (𝓞 F) F r := rfl
  rw [hr', hr, show algebraMap (𝓞 F) F d * (β * c0⁻¹ * x)
      = algebraMap (𝓞 F) F d * (β * c0⁻¹) * x by ring,
    inv_mul_cancel_left₀ (mul_ne_zero hd0 hβ0)]
end PI.VolStabS
