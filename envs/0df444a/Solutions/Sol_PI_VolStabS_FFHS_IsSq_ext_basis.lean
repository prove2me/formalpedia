-- Prove2me | solution 1 for PI.VolStabS.FFHS.IsSq.ext_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:53:50.384898+00:00
-- url     : https://prove2.me/submissions/74dc2e7e-63a3-4b43-b14b-b07e7c6a7182

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFHS
import Theorems.Thm_PI_VolStabS_FFHS_IsSq_lin_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.FFHS
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}
namespace PI.VolStabS.FFHS
namespace IsSq
theorem _root_.solution {h' : V → V → K} (hs : IsSq σ h) (hs' : IsSq σ h') {ι : Type}
    (b : Basis ι K V) (hb : ∀ i j, h (b i) (b j) = h' (b i) (b j)) (x y : V) : h x y = h' x y := by
  have step1 : ∀ i y, h (b i) y = h' (b i) y := fun i y => by
    have : hs.lin (b i) = hs'.lin (b i) := b.ext (fun j => hb i j)
    exact LinearMap.congr_fun this y
  have step2 : ∀ x, hs.lin x = hs'.lin x := fun x => b.ext (fun i => by
    simp only [IsSq.lin_apply]
    rw [hs.herm (b i) x, hs'.herm (b i) x, step1])
  exact LinearMap.congr_fun (step2 x) y
end IsSq
end PI.VolStabS.FFHS
