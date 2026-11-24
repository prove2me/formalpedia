-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncidenceGeneric_hom_aeval_926da0c2fb59
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T01:29:42.967074+00:00
-- url     : https://prove2.me/submissions/71a6fa3b-9be8-4075-b68d-9101f291d94a

import Mathlib
open MvPolynomial


theorem solution {F σ R T : Type*} [Field F] [CommRing R] [CommRing T] [Algebra F R] [Algebra F T]
    (Φ : R →+* T) (hΦ : ∀ r : F, Φ (algebraMap F R r) = algebraMap F T r) (y : σ → R)
    (g : MvPolynomial σ F) : Φ (aeval y g) = aeval (fun s => Φ (y s)) g := by
  let φ : R →ₐ[F] T := ⟨Φ,hΦ⟩
  change φ ((aeval y) g) = _
  have e : φ.comp (aeval y) = aeval (fun s => Φ (y s)) := by ext; simp [φ]
  exact DFunLike.congr_fun e g
