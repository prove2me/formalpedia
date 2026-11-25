-- Prove2me | solution 1 for PI.VolStabSW.chInf_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:54:15.295088+00:00
-- url     : https://prove2.me/submissions/59d235fb-36d1-4d55-a20d-131c02f6fb18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensSAChar

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
open PI PI.VolStabSW
namespace PI.VolStabSW
theorem _root_.solution (hL : ChLift) (hA : AddIntF) : ChInf := by
  intro F _ _ Λ hne hnd χ hχ h1 x
  obtain ⟨ℓ, hℓc, hℓ⟩ := hL F χ hχ
  have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let g : F →+ ℂ := AddMonoidHom.mk' (fun a => ℓ (algebraMap F (InfiniteAdeleRing F) a) /
    (2 * Real.pi * Complex.I)) (by intro a b; simp only [map_add, add_div])
  have hint : ∀ a ∈ Λ, ∃ n : ℤ, g a = n := by
    intro a ha
    have he : Complex.exp (ℓ (algebraMap F (InfiniteAdeleRing F) a)) = 1 := by
      rw [← hℓ]
      exact h1 a ha
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
    refine ⟨n, ?_⟩
    show ℓ (algebraMap F (InfiniteAdeleRing F) a) / (2 * Real.pi * Complex.I) = n
    rw [hn, mul_div_assoc, div_self hI, mul_one]
  have hg := hA F Λ hne hnd g hint
  have hzero : ∀ a : F, ℓ (algebraMap F (InfiniteAdeleRing F) a) = 0 := by
    intro a
    have h := hg a
    change ℓ (algebraMap F (InfiniteAdeleRing F) a) / (2 * Real.pi * Complex.I) = 0 at h
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h hI
  have hdense : DenseRange (algebraMap F (InfiniteAdeleRing F)) := by
    first
      | exact InfiniteAdeleRing.denseRange_algebraMap F
      | exact InfiniteAdeleRing.denseRange_algebraMap
      | exact NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  have hx : ℓ x = 0 :=
    hdense.induction_on x (isClosed_eq hℓc continuous_const) hzero
  rw [hℓ, hx, Complex.exp_zero]
end PI.VolStabSW
