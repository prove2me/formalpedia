-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_finite_mem_asIdeal_2187e53e05da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:41.607809+00:00
-- url     : https://prove2.me/submissions/d79aafae-1c3f-48cd-bbd0-824b99ff2672

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct ComplexAt
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution {b : 𝓞 K} (hb : b ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | b ∈ v.asIdeal}.Finite := by
  have e : {v : HeightOneSpectrum (𝓞 K) | b ∈ v.asIdeal} =
      {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ Ideal.span {b}} := by
    ext v
    simp only [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]
  rw [e]
  apply Ideal.finite_factors
  simp only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot, hb, not_false_eq_true]
end GroundTheory.Heights₂.Heights.LatticeLemmas
