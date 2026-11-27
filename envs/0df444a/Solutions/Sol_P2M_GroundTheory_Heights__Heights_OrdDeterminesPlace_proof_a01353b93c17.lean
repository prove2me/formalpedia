-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrdDeterminesPlace_proof_a01353b93c17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:07:54.062059+00:00
-- url     : https://prove2.me/submissions/05e7532f-d49d-469c-8fe7-2d75c60600c3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOrdDeterminesPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_POrdDeterminesPlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_curveNormalisation_le_a06ad3adf3e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_ord_eq_ord_polynomial_bd5f17fea660

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
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace OrdDeterminesPlace
theorem _root_.solution (hfin : CurveNormalisationFinite.Statement) : OrdDeterminesPlace.Statement := by
  intro n I q hrad hdim P P' hord
  have : Module.Finite (curveLocalRing I q) (curveNormalisation I q) := hfin n I q hrad
  have : IsNoetherianRing (curveNormalisation I q) := IsNoetherianRing.of_finite (curveLocalRing I q) _

  have hdimP : ∀ Q : MaximalSpectrum (curveNormalisation I q), Ring.KrullDimLE 1 (Localization.AtPrime Q.asIdeal) := by
    intro Q
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height Q.asIdeal]
    calc (Q.asIdeal.height : WithBot ℕ∞) ≤ ringKrullDim (curveNormalisation I q) :=
          Ideal.height_le_ringKrullDim_of_ne_top Q.isMaximal.ne_top
      _ ≤ ringKrullDim (curveLocalRing I q) := ringKrullDim_curveNormalisation_le I q
      _ = 1 := by rw [hdim]

  have hO : ∀ a : curveLocalRing I q,
      Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
        Ring.ord (Localization.AtPrime P'.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P'.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) := by
    intro a
    obtain ⟨f, hf⟩ := exists_ord_eq_ord_polynomial I q a
    rw [hf P, hf P', hord f]
  by_contra hne
  obtain ⟨x, hxP, hxP'⟩ : ∃ x, x ∈ P.asIdeal ∧ x ∉ P'.asIdeal := by
    by_contra! H
    exact hne (MaximalSpectrum.ext (P.isMaximal.eq_of_le P'.isMaximal.ne_top H))

  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (curveLocalRing I q))
    (show ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))) from x).1
  have hax : algebraMap (curveLocalRing I q) (curveNormalisation I q) a =
      algebraMap (curveLocalRing I q) (curveNormalisation I q) s * x := by
    apply Subtype.ext
    change algebraMap (curveLocalRing I q) (FractionRing (curveLocalRing I q)) a =
      algebraMap (curveLocalRing I q) (FractionRing (curveLocalRing I q)) s * (show ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))) from x).1
    rw [← hs, IsLocalization.mk'_spec']

  have hsN : algebraMap (curveLocalRing I q) (curveNormalisation I q) s ∈ nonZeroDivisors (curveNormalisation I q) := by
    have hu : IsUnit (algebraMap (curveLocalRing I q) (FractionRing (curveLocalRing I q)) s) :=
      IsLocalization.map_units _ s
    exact mem_nonZeroDivisors_of_injective (f := (integralClosure (curveLocalRing I q)
      (FractionRing (curveLocalRing I q))).val) Subtype.val_injective hu.mem_nonZeroDivisors
  have hsP : ∀ Q : MaximalSpectrum (curveNormalisation I q),
      algebraMap (curveNormalisation I q) (Localization.AtPrime Q.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) s) ∈
        nonZeroDivisors (Localization.AtPrime Q.asIdeal) := fun Q ↦
    IsLocalization.nonZeroDivisors_le_comap Q.asIdeal.primeCompl _ hsN

  have h' : Ring.ord (Localization.AtPrime P'.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P'.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
      Ring.ord (Localization.AtPrime P'.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P'.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) s)) := by
    rw [hax, map_mul, Ring.ord_mul_of_isUnit_right]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ P'.asIdeal x).2 hxP'

  have hP : Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) a)) =
      Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) s)) +
      Ring.ord (Localization.AtPrime P.asIdeal)
        (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal) x) := by
    rw [hax, map_mul, Ring.ord_mul' _ (hsP P)]
  have hfin' : Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
        (algebraMap (curveLocalRing I q) (curveNormalisation I q) s)) ≠ ⊤ := by
    have := hdimP P
    exact Ring.ord_ne_top (hsP P)
  rw [hO a, h', ← hO s] at hP
  have hx0 : Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal) x) = 0 := by
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hfin'
    rw [← hk] at hP
    generalize Ring.ord (Localization.AtPrime P.asIdeal)
      (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal) x) = y at hP ⊢
    induction y using ENat.recTopCoe with
    | top => simp at hP
    | coe m => norm_cast at hP ⊢; omega

  rw [Ring.ord, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top] at hx0
  exact (IsLocalization.AtPrime.isUnit_to_map_iff _ P.asIdeal x).1 hx0 hxP
end OrdDeterminesPlace
end GroundTheory.Heights₂.Heights
