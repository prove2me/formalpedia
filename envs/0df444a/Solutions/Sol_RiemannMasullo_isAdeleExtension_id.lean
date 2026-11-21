-- Prove2me | solution 1 for RiemannMasullo.isAdeleExtension_id
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:44:41.864907+00:00
-- url     : https://prove2.me/submissions/fdcbf8ce-0ae2-4cb9-a7e5-95372dfe29f2

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L255-L260
import Mathlib
import Definitions.Def_RiemannMasullo_AdelicExtensions

open RiemannMasullo
open Filter Function NumberField IsDedekindDomain Topology
open scoped NNReal RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing TensorProduct
variable (F : Type*) [Field F] [NumberField F]
local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)

theorem solution : IsAdeleExtension F (RingHom.id F) (RingHom.id 𝔸[F]) := by
  refine ⟨continuous_id, fun _ ↦ rfl, fun _ _ h ↦ h, ?_⟩
  intro v w h
  have hvw : v = w := HeightOneSpectrum.ext (h.trans w.asIdeal.comap_id)
  subst w
  exact fun _ ha ↦ ha
