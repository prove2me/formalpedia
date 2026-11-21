-- Prove2me | solution 1 for RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure_unitBox
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:53:42.558849+00:00
-- url     : https://prove2.me/submissions/00788743-9be0-4ed5-863d-4a4139d96653

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec3.lean#L131-L136
import Mathlib
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

theorem solution (v : InfinitePlace F) :
    (∀ h : v.IsReal, infiniteLocalAdditiveTamagawaMeasure F v
      ((ringEquivRealOfIsReal h).symm '' Icc (0 : ℝ) 1) = 1) ∧
    (∀ h : v.IsComplex, infiniteLocalAdditiveTamagawaMeasure F v
      ((ringEquivComplexOfIsComplex h).symm '' {z : ℂ | z.re ∈ Icc 0 1 ∧ z.im ∈ Icc 0 1}) = 2) :=
  by
    classical
    letI : BorelSpace v.Completion := ⟨rfl⟩
    constructor
    · intro h
      rw [infiniteLocalAdditiveTamagawaMeasure, dif_pos h]
      have hm : MeasurableEmbedding (ringEquivRealOfIsReal h).symm :=
        (isometryEquivRealOfIsReal h).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      rw [hm.map_apply, Set.preimage_image_eq _ (ringEquivRealOfIsReal h).symm.injective]
      norm_num [Real.volume_Icc]
    · intro h
      have hn := InfinitePlace.not_isReal_iff_isComplex.mpr h
      rw [infiniteLocalAdditiveTamagawaMeasure, dif_neg hn]
      have hm : MeasurableEmbedding (ringEquivComplexOfIsComplex h).symm :=
        (isometryEquivComplexOfIsComplex h).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      rw [hm.map_apply, Set.preimage_image_eq _ (ringEquivComplexOfIsComplex h).symm.injective,
        Measure.smul_apply]
      let I := Set.Icc (0 : ℝ) 1
      have hvol : (volume : Measure ℂ) {z | z.re ∈ I ∧ z.im ∈ I} = 1 := by
        change volume (Complex.measurableEquivRealProd ⁻¹' (I ×ˢ I)) = 1
        rw [Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod,
          Measure.prod_prod]
        norm_num [I, Real.volume_Icc]
      rw [hvol]
      norm_num

