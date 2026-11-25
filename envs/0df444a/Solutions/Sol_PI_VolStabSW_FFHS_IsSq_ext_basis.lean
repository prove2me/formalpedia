-- Prove2me | solution 1 for PI.VolStabSW.FFHS.IsSq.ext_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:51:02.93572+00:00
-- url     : https://prove2.me/submissions/e130812d-2c9d-45fe-9e0c-906b6fa27f96

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFHS
import Theorems.Thm_PI_VolStabSW_FFHS_IsSq_lin_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FFHS
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}
namespace PI.VolStabSW.FFHS
namespace IsSq
theorem _root_.solution {h' : V → V → K} (hs : IsSq σ h) (hs' : IsSq σ h') {ι : Type}
    (b : Basis ι K V) (hb : ∀ i j, h (b i) (b j) = h' (b i) (b j)) (x y : V) : h x y = h' x y := by
  have h1 : ∀ i y, h (b i) y = h' (b i) y := by
    intro i y
    have e := b.ext (f₁ := hs.lin (b i)) (f₂ := hs'.lin (b i)) (fun j => hb i j)
    exact LinearMap.congr_fun e y
  have h3 : ∀ x y, h y x = h' y x := by
    intro x y
    have e := b.ext (f₁ := hs.lin y) (f₂ := hs'.lin y) (fun i => by
      simp only [IsSq.lin_apply]
      rw [hs.herm (b i) y, hs'.herm (b i) y, h1])
    exact LinearMap.congr_fun e x
  exact h3 y x
end IsSq
end PI.VolStabSW.FFHS
