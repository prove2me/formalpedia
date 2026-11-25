-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_curveClosure_d5266bbc86d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:18:58.798869+00:00
-- url     : https://prove2.me/submissions/afd8424e-4555-43f3-9fc9-4a6f02fbc44a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsNefGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefGeneric

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
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {S : Type u} [CommRing S] [IsDomain S] {F : Type u} [Field F] [Algebra S F]
    [IsFractionRing S F] {N : ℕ} (pp : Ideal (Poly F N)) [pp.IsPrime] :
    (∀ s : S, (C s : Poly S N) ∈ pp.comap (MvPolynomial.map (algebraMap S F)) → s = 0) ∧
      (pp.comap (MvPolynomial.map (algebraMap S F))).map (MvPolynomial.map (algebraMap S F)) = pp := by
  refine ⟨fun s hs => ?_, ?_⟩
  · by_contra h0
    have hs' : (C (algebraMap S F s) : Poly F N) ∈ pp := by
      rw [Ideal.mem_comap, map_C] at hs; exact hs
    have hu : IsUnit (C (algebraMap S F s) : Poly F N) :=
      (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective S F)).mpr h0)).map C
    exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ hs' hu)
  · let _ : Algebra (Poly S N) (Poly F N) := MvPolynomial.algebraMvPolynomial
    have : IsLocalization ((nonZeroDivisors S).map (C : S →+* Poly S N)) (Poly F N) :=
      MvPolynomial.isLocalization (nonZeroDivisors S) F
    exact IsLocalization.map_under ((nonZeroDivisors S).map (C : S →+* Poly S N)) (Poly F N) pp
end GroundTheory.Heights₂.Heights.Kleiman
