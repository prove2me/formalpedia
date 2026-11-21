-- Prove2me | solution 1 for RiemannMasullo.diagonal_mem_integralAdelesOutside
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:44:41.226359+00:00
-- url     : https://prove2.me/submissions/83022144-0329-452d-ba5c-77c3b74c6364

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L227-L232
import Mathlib
import Definitions.Def_RiemannMasullo_AdelicExtensions

open RiemannMasullo
open Filter Function NumberField IsDedekindDomain Topology
open scoped NNReal RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing TensorProduct
variable (F : Type*) [Field F] [NumberField F]
local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)

theorem solution (S : Finset (Primes(F))) (x : F) :
    algebraMap F 𝔸[F] x ∈ integralAdelesOutside F S ↔ x ∈ (S : Set (Primes(F))).integer F := by
  simp only [integralAdelesOutside, Subring.mem_iInf]
  change (∀ v : Primes(F), v ∉ S → Valued.v (x : v.adicCompletion F) ≤ 1) ↔
    ∀ v : Primes(F), v ∉ S → v.valuation F x ≤ 1
  simp only [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
