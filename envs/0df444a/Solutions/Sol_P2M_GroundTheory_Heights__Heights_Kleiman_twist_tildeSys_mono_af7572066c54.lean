-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twist_tildeSys_mono_af7572066c54
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:13:48.106004+00:00
-- url     : https://prove2.me/submissions/b54f51be-ed69-44ab-b58a-4d01ced1bdb8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {M₁ M₂ : FinGradedSub (S := k) (x := x) Ω}
    (h : ∀ c, M₂.piece c ≤ M₁.piece c) (X : SubSystem k x Ω) (I : Chart x) :
    ∀ y ∈ ((M₂.tildeSys 0).twist X).sub I, y ∈ ((M₁.tildeSys 0).twist X).sub I := by
  intro y hy
  refine Submodule.span_mono ?_ hy
  rintro _ ⟨q, hq, z, hz, rfl⟩
  refine ⟨q, hq, z, Submodule.span_mono ?_ hz, rfl⟩
  rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
  exact ⟨m, s, a, e, hs, hse, h a hm, hae, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman
