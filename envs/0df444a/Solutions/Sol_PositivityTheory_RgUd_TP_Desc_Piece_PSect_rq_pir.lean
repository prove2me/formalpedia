-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.rq_pir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:38.472143+00:00
-- url     : https://prove2.me/submissions/19aa1d99-7407-407e-9649-f6aa754b6ede

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_RqLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect
open Module Polynomial
variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
private theorem isPrincipalIdealRing_pi {ι : Type*} [Finite ι] (R : ι → Type*) [∀ i, CommRing (R i)]
    (hR : ∀ i, IsPrincipalIdealRing (R i)) : IsPrincipalIdealRing (∀ i, R i) := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun J => ?_⟩
  have hsurj : ∀ i, Function.Surjective (Pi.evalRingHom R i) := fun i y => ⟨Pi.single i y, by simp⟩
  have hgen : ∀ i, ∃ a : R i, J.map (Pi.evalRingHom R i) = Ideal.span {a} := fun i => by
    obtain ⟨a, ha⟩ := (hR i).principal (J.map (Pi.evalRingHom R i))
    exact ⟨a, ha⟩
  choose g hg using hgen
  have hgJ : g ∈ J := by
    have hpre : ∀ i, ∃ h ∈ J, h i = g i := fun i => by
      have hm : g i ∈ J.map (Pi.evalRingHom R i) := by
        rw [hg i]
        exact Ideal.subset_span rfl
      obtain ⟨h, hh, he⟩ := (Ideal.mem_map_iff_of_surjective _ (hsurj i)).mp hm
      exact ⟨h, hh, he⟩
    choose h hh he using hpre
    have e : g = ∑ i, Pi.single i (1 : R i) * h i := by
      funext j
      simp only [Finset.sum_apply, Pi.mul_apply]
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, one_mul, he]
      · intro i _ hij
        rw [Pi.single_eq_of_ne (Ne.symm hij), zero_mul]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [e]
    exact J.sum_mem (fun i _ => J.mul_mem_left _ (hh i))
  refine ⟨g, le_antisymm ?_ ?_⟩
  · intro x hx
    have hc : ∀ i, ∃ c : R i, c * g i = x i := fun i => by
      have hm : x i ∈ J.map (Pi.evalRingHom R i) := Ideal.mem_map_of_mem _ hx
      rw [hg i] at hm
      exact Ideal.mem_span_singleton'.mp hm
    choose c hc using hc
    exact Ideal.mem_span_singleton'.mpr ⟨c, funext hc⟩
  · exact (Ideal.span_le).mpr (Set.singleton_subset_iff.mpr hgJ)
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
end
end

set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PSect
open Module Polynomial
variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect
theorem _root_.solution [FiniteDimensional k A] [IsReduced A] (χ : k[X]) (q : ℕ) :
    IsPrincipalIdealRing (Rq A χ q) := by
  classical
  have hA : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hPI : IsPrincipalIdealRing ((I : MaximalSpectrum A) → (A ⧸ I.asIdeal)[X]) :=
    isPrincipalIdealRing_pi _ (fun I => by
      have := I.isMaximal
      letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field _
      exact EuclideanDomain.to_principal_ideal_domain)
  have hPI' : IsPrincipalIdealRing ((∀ I : MaximalSpectrum A, A ⧸ I.asIdeal)[X]) :=
    IsPrincipalIdealRing.of_surjective (Polynomial.piEquiv (fun I : MaximalSpectrum A => A ⧸ I.asIdeal)).symm
      (Polynomial.piEquiv _).symm.surjective
  have hAX : IsPrincipalIdealRing A[X] :=
    IsPrincipalIdealRing.of_surjective (Polynomial.mapEquiv (IsArtinianRing.equivPi A).symm.toRingEquiv)
      (Polynomial.mapEquiv _).surjective
  exact IsPrincipalIdealRing.of_surjective (Ideal.Quotient.mk (Iq A χ q)) Ideal.Quotient.mk_surjective
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
