-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_IntegralPointThroughPrime_proof_f638112ced1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:50.270819+00:00
-- url     : https://prove2.me/submissions/eed88b76-21b5-4288-bbcd-b68e35a7f240

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsClosedPointGenericFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPointAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PIntegralPointThroughPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_exists_maximal_of_fibre_9a1f67ed3c4c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain NumberField
namespace GroundTheory.Heights₂.Heights.FourB
namespace IntegralPointThroughPrime
theorem _root_.solution (h₁ : ClosedPointOfGenericFibre.Statement)
    (h₂ : IntegralPointOfAlgebraicDomain.Statement) : IntegralPointThroughPrime.Statement := by
  intro F _ _ R _ _ _ _ _ v P u g ⟨hP, hPv, hu, hg⟩
  obtain ⟨M, hM, hPM, huM⟩ := exists_maximal_of_fibre F R v P u hP hPv hu
  have hMv : M.comap (algebraMap (𝓞 F) R) = v.asIdeal :=
    ((v.isMaximal.eq_of_le (Ideal.IsPrime.comap (algebraMap (𝓞 F) R) (hK := hM.isPrime)).ne_top
      (hPv ▸ Ideal.comap_mono hPM))).symm
  obtain ⟨Q, hQ, hQM, hQ0, hgQ, hQalg⟩ := h₁ F R M g ⟨hM, hg⟩
  have := hQ
  have : Algebra.FiniteType (𝓞 F) (R ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (𝓞 F) Q)
      (Ideal.Quotient.mkₐ_surjective (𝓞 F) Q)
  set M' : Ideal (R ⧸ Q) := M.map (Ideal.Quotient.mk Q)
  have hcomap : M'.comap (Ideal.Quotient.mk Q) = M := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.2 hQM]
  have hM' : M'.IsMaximal := hM.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hQM)
  have hq : algebraMap (𝓞 F) (R ⧸ Q) = (Ideal.Quotient.mk Q).comp (algebraMap (𝓞 F) R) := rfl
  have hinj : Function.Injective (algebraMap (𝓞 F) (R ⧸ Q)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hq, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      ← Ideal.mem_comap, hQ0, Ideal.mem_bot] at hx
    exact hx
  have hM'v : M'.comap (algebraMap (𝓞 F) (R ⧸ Q)) = v.asIdeal := by
    rw [hq, ← Ideal.comap_comap, hcomap, hMv]
  obtain ⟨L, iL, aL, fL, y, hy, hyinj, hint, hunit, hnon⟩ :=
    h₂ F (R ⧸ Q) v M' ⟨hinj, hQalg, hM', hM'v⟩
  refine ⟨L, iL, aL, fL, y.comp (Ideal.Quotient.mk Q), ?_, fun a => hint _, ?_, ?_, ?_⟩
  · rw [RingHom.comp_assoc, ← hq, hy]
  · intro h
    apply hgQ
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hyinj (by rw [map_zero]; exact h)
  · refine hunit _ fun h => huM ?_
    rw [← hcomap]
    exact h
  · intro a ha
    exact hnon _ (Ideal.mem_map_of_mem _ (hPM ha))
end IntegralPointThroughPrime
end GroundTheory.Heights₂.Heights.FourB
