-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_pointLocalRing_eval_ne_zero_of_isUnit_a20956d1da78
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:56.887054+00:00
-- url     : https://prove2.me/submissions/7f70dde4-e8af-460d-8daa-3bb76b94c7b3

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
theorem _root_.solution (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) (u : MvPolynomial σ ℂ)
    (hu : IsUnit (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) u)) : eval w u ≠ 0 := by
  intro h0
  set p := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
  have hle : I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ g).2 (RingHom.mem_ker.2 (hw g hg))
  have hum : algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) u ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ u).2 (RingHom.mem_ker.2 h0)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hv' : Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p)))
      (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) u * z) = Ideal.Quotient.mk _ 1 := by
    rw [map_mul, map_one]
    exact hv
  have hd := hle (Ideal.Quotient.eq.1 hv')
  have h1 : (1 : Localization.AtPrime p) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
    have := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).sub_mem
      (Ideal.mul_mem_right z _ hum) hd
    simp at this
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)
end GroundTheory.Heights₂.Heights
