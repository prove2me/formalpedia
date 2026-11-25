-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumVanish_proof_7f139f099c8c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:54:08.714902+00:00
-- url     : https://prove2.me/submissions/228d3ab8-e07b-4686-b681-c94d571d2a8b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumVanish
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_degLT_zero_8822dfd84ef9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace IntNumVanish
theorem _root_.solution (h1 : HilbDegBound.Statement.{u})
    (h2 : HilbFnVanishBlock.Statement.{u}) (h3 : DegLTClosure.Statement)
    (h4 : EventualValueFacts.Statement) : IntNumVanish.Statement.{u} := by
  intro F _ K _ _ ι _ n Q hQ hQh hcase bs

  suffices hdeg : DegLT (hilbFn Q) n by
    exact (h4 K (mixedDiff bs (hilbFn Q)) 0 0).1 (hdeg bs)
  rcases hcase with hirr | hdim
  ·
    have hblock : ∃ k, ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ Q := by
      by_contra hne
      exact hirr fun k => by_contra fun h => hne ⟨k, fun i => by_contra fun hi => h ⟨i, hi⟩⟩
    obtain ⟨k, hk⟩ := hblock
    have hzero : (0 : (K → ℤ) → ℤ) =ᶠ[Filter.atTop] hilbFn Q := by
      filter_upwards [Filter.eventually_ge_atTop (fun _ : K => (1 : ℤ))] with m hm
      exact (h2 F K ι Q k hk m (hm k)).symm
    exact (h3 K n 0 (hilbFn Q) 0 0).2.2.2.2 hzero (degLT_zero n)
  · exact h1 F K ι n Q hQ hQh hdim
end IntNumVanish
end GroundTheory.Heights₂.Heights.NumbersDVR
