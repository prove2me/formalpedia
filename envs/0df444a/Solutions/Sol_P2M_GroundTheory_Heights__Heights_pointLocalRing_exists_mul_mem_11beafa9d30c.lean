-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_pointLocalRing_exists_mul_mem_11beafa9d30c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:36:08.893791+00:00
-- url     : https://prove2.me/submissions/767b511e-57f2-447a-abab-3bd4e17ebad1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PointLocalRingOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Topology
noncomputable section
variable {σ : Type*}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (g : MvPolynomial σ ℂ)
    (hg : algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) g = 0) :
    ∃ s : MvPolynomial σ ℂ, eval w s ≠ 0 ∧ s * g ∈ I := by
  set p := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
  have hmem : algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) g ∈
      I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p)) :=
    Ideal.Quotient.eq_zero_iff_mem.1 hg
  obtain ⟨⟨j, s⟩, hjs⟩ := (IsLocalization.mem_map_algebraMap_iff p.primeCompl (Localization.AtPrime p)).1 hmem
  refine ⟨s, fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩
  have hinj := IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
  have : (s : MvPolynomial σ ℂ) * g = j := hinj (by rw [map_mul, mul_comm]; exact hjs)
  rw [this]
  exact j.2
end GroundTheory.Heights₂.Heights
