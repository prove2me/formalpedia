-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.rq_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:30.415409+00:00
-- url     : https://prove2.me/submissions/5f027c81-a7ec-477e-a28b-df2780c83afa

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_RqLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PSect
open Module Polynomial
variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect
theorem _root_.solution {B : Type*} [Ring B] [Algebra k B] (ι : A →ₐ[k] B) (x : B) (hc : ∀ a, Commute (ι a) x)
    (χ : k[X]) (hχ : aeval x χ = 0) (q : ℕ)
    (hq : ∀ P : A[X], IsNilpotent (P.eval₂ ι.toRingHom x) → (P.eval₂ ι.toRingHom x) ^ q = 0) :
    ∃ ρ : Rq A χ q →ₐ[k] B, ∀ P : A[X], ρ (Ideal.Quotient.mk _ P) = P.eval₂ ι.toRingHom x := by
  let f : A[X] →+* B := Polynomial.eval₂RingHom' ι.toRingHom x hc
  have hf : ∀ P : A[X], f P = P.eval₂ ι.toRingHom x := fun P => rfl
  have hχ0 : f (χ.map (algebraMap k A)) = 0 := by
    rw [hf, Polynomial.eval₂_map]
    have e : ι.toRingHom.comp (algebraMap k A) = algebraMap k B := by
      ext c
      exact ι.commutes c
    rw [e, ← Polynomial.aeval_def, hχ]
  have hspan : ∀ P ∈ Ideal.span {χ.map (algebraMap k A)}, f P = 0 := by
    intro P hP
    obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton'.mp hP
    rw [map_mul, hχ0, mul_zero]
  have hle : Iq A χ q ≤ RingHom.ker f := by
    unfold Iq
    apply sup_le
    · intro P hP
      exact (RingHom.mem_ker).mpr (hspan P hP)
    · rw [Ideal.span_le]
      rintro _ ⟨r, hr, rfl⟩
      obtain ⟨m, hm⟩ := hr
      have hnil : IsNilpotent (r.eval₂ ι.toRingHom x) := ⟨m, by rw [← hf, ← map_pow, hspan _ hm]⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, hf]
      exact hq r hnil
  let F : A[X] →ₐ[k] B :=
    { f with
      commutes' := fun c => by
        show Polynomial.eval₂ ι.toRingHom x (algebraMap k A[X] c) = algebraMap k B c
        rw [Polynomial.algebraMap_apply, Polynomial.eval₂_C]
        exact ι.commutes c }
  exact ⟨Ideal.Quotient.liftₐ _ F (fun a ha => hle ha), fun P => rfl⟩
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
