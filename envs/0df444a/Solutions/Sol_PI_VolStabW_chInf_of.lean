-- Prove2me | solution 1 for PI.VolStabW.chInf_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:29.430208+00:00
-- url     : https://prove2.me/submissions/12fbf6cb-4809-494c-adcd-a0ef797b3ad0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSAChar

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
open PI PI.VolStabW
namespace PI.VolStabW
theorem _root_.solution (hL : ChLift) (hA : AddIntF) : ChInf := by
  intro F _ _ Λ h0 hb χ hχ hΛ x
  obtain ⟨ℓ, hℓc, hℓ⟩ := hL F χ hχ
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  let g : F →+ ℂ :=
    { toFun := fun a => ℓ (algebraMap F (InfiniteAdeleRing F) a) / (2 * Real.pi * Complex.I)
      map_zero' := by simp
      map_add' := fun a b => by simp [add_div] }
  have hg : ∀ a ∈ Λ, ∃ n : ℤ, g a = n := fun a ha => by
    have := hΛ a ha
    rw [hℓ, Complex.exp_eq_one_iff] at this
    obtain ⟨n, hn⟩ := this
    exact ⟨n, by simp only [g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hn]; field_simp⟩
  have hg0 := hA F Λ h0 hb g hg
  have hz : ∀ a : F, ℓ (algebraMap F (InfiniteAdeleRing F) a) = 0 := fun a => by
    have := hg0 a
    simp only [g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, div_eq_zero_iff, h2, or_false] at this
    exact this
  have : ℓ x = 0 := (InfiniteAdeleRing.denseRange_algebraMap F).induction_on x
    (isClosed_eq hℓc continuous_const) hz
  rw [hℓ, this, Complex.exp_zero]
end PI.VolStabW
