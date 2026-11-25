-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_length_slice_of_isCohenMacaulay_b86f712f19d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:51.631605+00:00
-- url     : https://prove2.me/submissions/88c6c51e-656e-486b-816c-061a194cfd16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthTransverseSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalizeQuotientStages
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthTransverseSlice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isPrime_map_quotient_localization_e8b632bf4d4d


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
open MvPolynomial Matrix ComplexSets IsLocalRing
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (hCM : CMLengthParameters.Statement.{0})
    (hLS : LocalizeQuotientStages.Statement.{0}) {R : Type} [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime]
    [IsCohenMacaulayLocalRing (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m)))]
    (hW : W ∈ I.minimalPrimes) (hWm : W ≤ m) (huniq : ∀ W' ∈ I.minimalPrimes, W' ≤ m → W' = W)
    (d : ℕ) (lin : Fin d → R) (hlin : ∀ i, lin i ∈ m)
    (hdim : ringKrullDim (Localization.AtPrime m ⧸ W.map (algebraMap R (Localization.AtPrime m))) = (d : ℕ))
    (hT : ∀ g ∈ m, ∃ s ∉ m, s * g ∈ W ⊔ Ideal.span (Set.range lin)) :
    Module.length (Localization.AtPrime W) (Localization.AtPrime W ⧸ I.map (algebraMap R (Localization.AtPrime W))) =
      Module.length (Localization.AtPrime m)
        (Localization.AtPrime m ⧸ (I ⊔ Ideal.span (Set.range lin)).map (algebraMap R (Localization.AtPrime m))) := by
  classical
  have hIW : I ≤ W := hW.1.2
  have hP := isPrime_map_quotient_localization m W I hWm hIW

  have hunit : ∀ s ∉ m, IsUnit (((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) s) := fun s hs =>
    ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime m) m s).2 hs).map
      (Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m))))

  have hall : ∀ Q : Ideal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))), Q.IsPrime →
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) ≤ Q := by
    intro Q hQ
    have hIQ : I ≤ Q.comap ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) := fun f hf => by
      rw [Ideal.mem_comap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hf)]
      exact Q.zero_mem
    have hQm : Q.comap ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) ≤ m := fun f hf => by
      by_contra h
      exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hf (hunit f h))
    obtain ⟨W', hW', hW'Q⟩ := Ideal.exists_minimalPrimes_le hIQ
    have : W' = W := huniq W' hW' (hW'Q.trans hQm)
    subst this
    exact Ideal.map_le_iff_le_comap.2 hW'Q
  have hmin : minimalPrimes (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) =
      {W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m)))} := by
    ext Q
    rw [Set.mem_singleton_iff]
    constructor
    · intro hQ
      exact le_antisymm (hQ.2 ⟨hP, bot_le⟩ (hall Q hQ.1.1)) (hall Q hQ.1.1)
    · rintro rfl
      exact ⟨⟨hP, bot_le⟩, fun Q hQ _ => hall Q hQ.1⟩

  have hPdef : W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) =
      (W.map (algebraMap R (Localization.AtPrime m))).map (Ideal.Quotient.mk _) := by
    rw [Ideal.map_map]
  have hdimP : ringKrullDim ((Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) ⧸
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m)))) = (d : ℕ) := by
    rw [ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hPdef).trans
      (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.map_mono hIW)))]
    exact hdim

  have hmB : m.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) =
      maximalIdeal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) := by
    rw [← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal]
    exact map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hspan : Ideal.span (Set.range fun i => ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) (lin i)) =
      (Ideal.span (Set.range lin)).map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  have hmax : Ideal.span (Set.range fun i => ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) (lin i)) ⊔
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) =
      maximalIdeal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) := by
    rw [hspan, ← Ideal.map_sup, sup_comm, ← hmB]
    apply le_antisymm
    · refine Ideal.map_mono (sup_le hWm ?_)
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hlin i
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      obtain ⟨s, hs, hsg⟩ := hT g hg
      rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ (hunit s hs), ← map_mul]
      exact Ideal.mem_map_of_mem _ hsg
  have key := hCM _ _ d _ hmin hdimP hmax
  rw [hLS R m W I hWm hIW _ rfl] at key
  rw [← key, ← Module.length_eq_of_surjective (S := Localization.AtPrime m)
    (R := Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) Ideal.Quotient.mk_surjective,
    hspan, ← Ideal.map_map, Ideal.map_sup]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ (Localization.AtPrime m) _ _).toLinearEquiv.length_eq
end GroundTheory.Heights₂.Heights
