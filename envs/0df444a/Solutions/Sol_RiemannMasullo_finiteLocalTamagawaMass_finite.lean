-- Prove2me | solution 1 for RiemannMasullo.finiteLocalTamagawaMass_finite
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:53:42.025063+00:00
-- url     : https://prove2.me/submissions/acd2707c-52be-4ee2-bcb5-6cb8bb5c8941

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec3.lean#L165-L166
import Mathlib
import Theorems.Thm_RiemannMasullo_compactSpace_adicCompletionIntegers
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion
import Definitions.Def_RiemannMasullo_LocalAdditiveTamagawaMeasures
open RiemannMasullo
open Function MeasureTheory NumberField IsDedekindDomain InfinitePlace.Completion Set
open scoped Classical ENNReal NNReal NumberField.AdeleRing Pointwise

variable (F : Type*) [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
noncomputable local instance (v : InfinitePlace F) : MeasurableSpace v.Completion := borel _
noncomputable local instance (v : Primes(F)) : MeasurableSpace (v.adicCompletion F) := borel _
noncomputable local instance (v : Primes(F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
noncomputable local instance (v : Primes(F)) : LocallyCompactSpace (v.adicCompletion F) :=
  RiemannMasullo.locallyCompactSpace_adicCompletion v
local notation "differentExp(" F ", " v ")" =>
  multiplicity (HeightOneSpectrum.asIdeal v) (differentIdeal ℤ (𝓞 F))
local notation "differentMass(" F ", " v ")" =>
  Inv.inv (ENNReal.ofReal (Real.sqrt (Nat.cast (Ideal.absNorm (HeightOneSpectrum.asIdeal v)) ^
    differentExp(F, v))))

theorem solution :
    {v : Primes(F) | differentMass(F, v) ≠ 1}.Finite := by
  have hd : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  apply (Ideal.finite_factors hd).subset
  intro v hv
  by_contra hn
  have h : differentExp(F, v) = 0 := multiplicity_eq_zero.mpr hn
  exact hv (by simp [h])

