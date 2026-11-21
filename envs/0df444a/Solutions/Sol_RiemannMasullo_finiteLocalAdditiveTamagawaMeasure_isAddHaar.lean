-- Prove2me | solution 1 for RiemannMasullo.finiteLocalAdditiveTamagawaMeasure_isAddHaar
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:55:25.957627+00:00
-- url     : https://prove2.me/submissions/b5f1108f-f33e-4362-8edc-94bd9aefcdd2

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec3.lean#L160-L161
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

theorem solution (v : Primes(F)) :
    (finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure := by
  let O : Set (v.adicCompletion F) := v.adicCompletionIntegers F
  let μ := Measure.addHaar (G := v.adicCompletion F)
  have hc : IsCompact O := isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers (K := F) v)
  have hp : 0 < μ O := (Valued.isOpen_integer _).measure_pos μ ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  have hf : μ O ≠ ∞ := hc.measure_lt_top.ne
  have hn : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff v.asIdeal).mpr
      (Ring.HasFiniteQuotients.finiteQuotient v.ne_bot))
  have hpos : 0 < Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^ differentExp(F, v)) :=
    Real.sqrt_pos.2 (pow_pos hn _)
  have hmass : differentMass(F, v) ≠ ∞ := ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hpos).ne'
  change ((differentMass(F, v) / μ O) • μ).IsAddHaarMeasure
  apply Measure.IsAddHaarMeasure.smul
  · exact ENNReal.div_ne_zero.mpr ⟨by simp, hf⟩
  · exact ENNReal.div_ne_top hmass hp.ne'

