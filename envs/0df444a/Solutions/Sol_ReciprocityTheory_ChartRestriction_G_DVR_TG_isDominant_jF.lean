-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.isDominant_jF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:50.534055+00:00
-- url     : https://prove2.me/submissions/1f3d3e8a-d86d-497f-92f5-251196e3a179

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
noncomputable section
variable {R : Type} [CommRing R] [IsDomain R]
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] : IsDominant (jF R) := by
  constructor
  let x : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  have hx : (jF R).base x = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap R (FractionRing R)) (IsLocalRing.maximalIdeal (FractionRing R)) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)]
  have hsub : ({(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} : Set (PrimeSpectrum R)) ⊆
      Set.range (jF R).base :=
    Set.singleton_subset_iff.2 ⟨x, hx⟩
  refine dense_iff_closure_eq.2 (Set.eq_univ_of_forall fun y => closure_mono hsub ?_)
  rw [PrimeSpectrum.closure_singleton]
  exact (PrimeSpectrum.mem_zeroLocus _ _).2 (by simp)
end ReciprocityTheory.ChartRestriction.G.DVR.TG
