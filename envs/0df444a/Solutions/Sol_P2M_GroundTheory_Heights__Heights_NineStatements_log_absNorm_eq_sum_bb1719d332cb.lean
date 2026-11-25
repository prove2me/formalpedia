-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_eq_sum_bb1719d332cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:48.432676+00:00
-- url     : https://prove2.me/submissions/69afb7e1-ed91-43b3-aef2-8d46ec67d95e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PNormCountBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.NineStatements
theorem _root_.solution {L : Type} [Field L] [NumberField L] {I : FractionalIdeal (𝓞 L)⁰ L}
    (hI : I ≠ 0) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (hT : ∀ v, FractionalIdeal.count L v I ≠ 0 → v ∈ T) :
    Real.log (FractionalIdeal.absNorm I : ℝ) =
      ∑ v ∈ T, (FractionalIdeal.count L v I : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := L) hI
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_] at hfac
  · have h1 : (FractionalIdeal.absNorm I : ℝ) =
        ∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ) ^ (FractionalIdeal.count L v I) := by
      conv_lhs => rw [← hfac]
      rw [map_prod, Rat.cast_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast]
    rw [h1, Real.log_prod]
    · exact Finset.sum_congr rfl fun v _ => Real.log_zpow _ _
    · intro v _
      apply zpow_ne_zero
      rw [Ne, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    apply hT v
    intro h0
    apply hv
    rw [h0, zpow_zero]
end GroundTheory.Heights₂.Heights.NineStatements
