-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_exists_C_mul_mem_4f0656e53394
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:24:09.116239+00:00
-- url     : https://prove2.me/submissions/08c2754a-766d-49fd-a00d-7c3e981878c3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
variable {K : Type*} [Field K] [NumberField K]
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace GroundTheory.Heights₂.Heights.Vertical.SecBFinite
theorem _root_.solution {σ : Type*} (J : Ideal (MvPolynomial σ (𝓞 K))) (h : MvPolynomial σ (𝓞 K))
    (hh : MvPolynomial.map (algebraMap (𝓞 K) K) h ∈ J.map (MvPolynomial.map (algebraMap (𝓞 K) K))) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ C d * h ∈ J := by
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff
    ((nonZeroDivisors (𝓞 K)).map (C (σ := σ))) (MvPolynomial σ K)).mp hh
  obtain ⟨d, hd, rfl⟩ := Submonoid.mem_map.mp hs
  refine ⟨d, nonZeroDivisors.ne_zero hd, ?_⟩
  have hda : C d * h = a := by
    apply MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K)
    rw [map_mul, mul_comm]
    exact hx
  rw [hda]
  exact ha
end GroundTheory.Heights₂.Heights.Vertical.SecBFinite
