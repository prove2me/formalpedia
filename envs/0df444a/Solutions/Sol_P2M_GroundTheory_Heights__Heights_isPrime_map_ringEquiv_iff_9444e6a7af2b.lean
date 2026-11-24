-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isPrime_map_ringEquiv_iff_9444e6a7af2b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:04.265603+00:00
-- url     : https://prove2.me/submissions/9fedbc8b-b68e-4d32-b2ed-6edc0e76f246

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {A A' : Type*} [CommRing A] [CommRing A'] (σ : A ≃+* A')
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (V : Ideal A) : (V.map σ).IsPrime ↔ V.IsPrime := by
  constructor
  · intro hV
    rw [← Ideal.comap_map_of_bijective σ σ.bijective (I := V)]
    exact Ideal.comap_isPrime σ (V.map σ)
  · intro hV
    exact Ideal.map_isPrime_of_equiv σ
end GroundTheory.Heights₂.Heights
