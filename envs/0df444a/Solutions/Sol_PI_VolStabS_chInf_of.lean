-- Prove2me | solution 1 for PI.VolStabS.chInf_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:50:24.831006+00:00
-- url     : https://prove2.me/submissions/f761c5f4-b3ef-4b8d-a3ba-baaa5e0a4953

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensSAChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.VolStabS
namespace PI.VolStabS
theorem _root_.solution (hL : ChLift) (hA : AddIntF) : ChInf := by
  intro F _ _ Λ hne hnot χ hχ hΛ x
  obtain ⟨ℓ, hℓc, hℓ⟩ := hL F χ hχ
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]

  let g : F →+ ℂ := (AddMonoidHom.mulLeft (2 * (Real.pi : ℂ) * Complex.I)⁻¹).comp
    (ℓ.comp (algebraMap F (InfiniteAdeleRing F)).toAddMonoidHom)
  have hgv : ∀ a, g a = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ℓ (algebraMap F _ a) := fun a => rfl
  have hgint : ∀ a ∈ Λ, ∃ n : ℤ, g a = n := by
    intro a ha
    have h1 := hΛ a ha
    rw [hℓ, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    refine ⟨n, ?_⟩
    rw [hgv, hn, inv_mul_eq_iff_eq_mul₀ h2, mul_comm]
  have hg0 := hA F Λ hne hnot g hgint
  have hℓ0 : ∀ a : F, ℓ (algebraMap F (InfiniteAdeleRing F) a) = 0 := by
    intro a
    have h3 := hg0 a
    rw [hgv] at h3
    exact (mul_eq_zero.mp h3).resolve_left (inv_ne_zero h2)

  have hfun : (ℓ : InfiniteAdeleRing F → ℂ) = fun _ => 0 :=
    (InfiniteAdeleRing.denseRange_algebraMap F).equalizer hℓc continuous_const
      (funext fun a => hℓ0 a)
  rw [hℓ, congrFun hfun x, Complex.exp_zero]
end PI.VolStabS
