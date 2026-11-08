-- Prove2me | solution 1 for QEC.Coding.OriginalNormalizationComparison.ChartLocalization.localizationAlgEquivAt_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:14:38.311209+00:00
-- url     : https://prove2.me/submissions/e05cbb5a-9eb2-4520-9a94-bddbf17bf599

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNormalizationComparison
import Mathlib.RingTheory.Localization.BaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLaurentNormalizationComparison

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.OriginalNormalizationComparison QEC.Coding.OriginalNormalizationComparison.ChartLocalization
open scoped TensorProduct
noncomputable section
variable {R S A D : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing D]
  [Algebra R S] [Algebra R A] [Algebra S D]
variable {P U V : Type*} [CommRing P] [CommRing U] [CommRing V]
  [Algebra U V] [Algebra D P]
variable [Algebra S U] [Algebra S V] [Algebra S P]
  [IsScalarTower S U V] [hDP : IsScalarTower S D P]
include hDP
namespace QEC.Coding.OriginalNormalizationComparison.ChartLocalization
theorem _root_.solution
    (u : U) (d : D) (f : U ≃ₐ[S] D) (hf : f u = d)
    [IsLocalization.Away u V] [IsLocalization.Away d P] (x : U) :
    localizationAlgEquivAt u d f hf (algebraMap U V x) = algebraMap D P (f x) := by
  change localizationRingEquivAt u d f.toRingEquiv hf (algebraMap U V x) = _
  exact localizationRingEquivAt_algebraMap u d f.toRingEquiv hf x
end QEC.Coding.OriginalNormalizationComparison.ChartLocalization
