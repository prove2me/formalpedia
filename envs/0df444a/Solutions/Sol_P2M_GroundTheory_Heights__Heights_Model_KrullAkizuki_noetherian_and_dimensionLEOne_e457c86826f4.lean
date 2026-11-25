-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_KrullAkizuki_noetherian_and_dimensionLEOne_e457c86826f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:03.605077+00:00
-- url     : https://prove2.me/submissions/63940bbb-141f-42bc-8cbb-f261275d4b75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsKrullAkizuki
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PKrullAkizuki

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open GroundTheory.Heights₂.Heights.Model.KrullAkizuki
namespace GroundTheory.Heights₂.Heights.Model.KrullAkizuki
theorem _root_.solution
    {R : Type} [CommRing R] [IsDomain R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L]
    [IsScalarTower R K L] (S : Subalgebra R L)
    (h : ∀ b : R, b ≠ 0 → IsFiniteLength R (S ⧸ Ideal.span {algebraMap R S b})) :
    IsNoetherianRing S ∧ Ring.DimensionLEOne S := by

  have hmeet : ∀ I : Ideal S, I ≠ ⊥ → ∃ b : R, b ≠ 0 ∧ algebraMap R S b ∈ I := by
    intro I hI
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have halg : Algebra.IsAlgebraic R L :=
      (IsFractionRing.comap_isAlgebraic_iff (K := K)).mpr inferInstance
    have hx : IsAlgebraic R x :=
      Subalgebra.isAlgebraic_iff_isAlgebraic_val.mpr (halg.isAlgebraic _)
    obtain ⟨b, hb, hb0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (Ideal.comap_ne_bot_of_algebraic_mem hx0 hxI hx)
    exact ⟨b, hb0, hb⟩
  refine ⟨(isNoetherianRing_iff_ideal_fg S).mpr fun I => ?_, ⟨fun {P} hP0 hP => ?_⟩⟩
  · rcases eq_or_ne I ⊥ with rfl | hI
    · exact Submodule.fg_bot
    obtain ⟨b, hb0, hbI⟩ := hmeet I hI
    have : IsNoetherian R (S ⧸ Ideal.span {algebraMap R S b}) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp (h b hb0)).1
    have : IsNoetherian S (S ⧸ Ideal.span {algebraMap R S b}) :=
      isNoetherian_of_tower R inferInstance
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (Ideal.span {algebraMap R S b}).mkQ
      (IsNoetherian.noetherian _) ?_
    rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem I).mpr hbI)]
    exact Submodule.fg_span_singleton _
  · obtain ⟨b, hb0, hbP⟩ := hmeet P hP0
    have hle : Ideal.span {algebraMap R S b} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hbP
    have hfl : IsFiniteLength R (S ⧸ P) :=
      (h b hb0).of_surjective (f := (Ideal.Quotient.factorₐ R hle).toLinearMap)
        (Ideal.Quotient.factor_surjective hle)
    have : IsArtinian R (S ⧸ P) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
    have : IsArtinianRing (S ⧸ P) := isArtinian_of_tower R inferInstance
    have : IsDomain (S ⧸ P) := Ideal.Quotient.isDomain P
    exact Ideal.Quotient.maximal_of_isField P (IsArtinianRing.isField_of_isDomain _)
end GroundTheory.Heights₂.Heights.Model.KrullAkizuki
