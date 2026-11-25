-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleF_mul_4c79274eac24
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:20:25.786965+00:00
-- url     : https://prove2.me/submissions/c9a405c7-76c1-43f5-a6b1-f11d14430efe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
open Classical
namespace GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F) :
    singleF F v (x * y) = singleF F v x * singleF F v y := by
  apply FiniteAdeleRing.ext; intro w
  change Pi.single v (x * y) w = Pi.single v x w * Pi.single v y w
  by_cases h : w = v
  · subst h; simp
  · simp [h]
end GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
