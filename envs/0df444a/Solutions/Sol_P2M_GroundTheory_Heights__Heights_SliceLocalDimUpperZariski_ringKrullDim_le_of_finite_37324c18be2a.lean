-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_ringKrullDim_le_of_finite_37324c18be2a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:16:26.635264+00:00
-- url     : https://prove2.me/submissions/db88f6bf-275a-48ad-880d-eda618febc9e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimUpperZariski
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLocalDimUpperZariski

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SliceLocalDimUpperZariski
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Finite) : ringKrullDim S ≤ ringKrullDim R := by
  let _ := f.toAlgebra
  have : Module.Finite R S := hf
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  refine Order.krullDim_le_of_strictMono
    (fun p : PrimeSpectrum S => PrimeSpectrum.comap (algebraMap R S) p) ?_
  intro p p' h
  have h' : p.asIdeal < p'.asIdeal := h
  exact Ideal.IsIntegral.comap_lt_comap (R := R) h'
end SliceLocalDimUpperZariski
end GroundTheory.Heights₂.Heights
