-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_eq_sum_d4330b1b5c31
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:29:22.003352+00:00
-- url     : https://prove2.me/submissions/aca06374-c6e6-45c0-af4c-e2b14e86282d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PLengthDecomp
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_localizedModule_eq_of_isLocalizedModule_efd0ccbc6ab4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_step_77fe98b2628b

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
open Module IsLocalRing LinearMap Submodule
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
open Classical
variable {B : Type*} [CommRing B]
variable {R : Type*} [CommRing R] [Algebra R B]
variable {N : Type*} [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]
namespace GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
theorem _root_.solution [Fintype (MaximalSpectrum B)] (hN : IsFiniteLength B N) :
    length R N = ∑ n : MaximalSpectrum B,
      length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl N) *
        length R (B ⧸ n.asIdeal) := by
  obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp hN
  have H : ∀ k, length R (s k) = ∑ n : MaximalSpectrum B,
      length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl (s k)) *
        length R (B ⧸ n.asIdeal) := by
    intro k
    induction k using Fin.induction with
    | zero =>
      rw [← RelSeries.head, hs_bot]
      simp [Module.length_eq_zero]
    | succ i hi =>
      obtain ⟨m, h1, h2⟩ := step (R := R) (s.step i)
      rw [h1, hi]
      simp_rw [h2, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have := H (Fin.last _)
  rw [← RelSeries.last, hs_top] at this
  rw [← ((Submodule.topEquiv (R := B) (M := N)).restrictScalars R).length_eq, this]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [length_localizedModule_eq_of_isLocalizedModule n.asIdeal
    ((LocalizedModule.mkLinearMap n.asIdeal.primeCompl N).comp
      (Submodule.topEquiv (R := B) (M := N)).toLinearMap)]
end GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
