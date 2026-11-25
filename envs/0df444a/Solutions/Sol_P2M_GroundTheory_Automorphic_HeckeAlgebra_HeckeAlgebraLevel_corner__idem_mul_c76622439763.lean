-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_HeckeAlgebra_HeckeAlgebraLevel_corner__idem_mul_c76622439763
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:10:01.998519+00:00
-- url     : https://prove2.me/submissions/e59a8b1b-d4f4-4eb4-8fb1-8b39323cec87

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
open GroundTheory.Automorphic.HeckeAlgebra
open GroundTheory.Automorphic.HeckeAlgebra.HeckeAlgebraLevel
namespace GroundTheory.Automorphic.HeckeAlgebra.HeckeAlgebraLevel
theorem _root_.solution (f : HeckeAlgebra μ) :
    cornerₗ hKc hKo (idem μ hKc hKo * f) = cornerₗ hKc hKo f := by
  apply ext hKc hKo
  have he : ∀ x : HeckeAlgebra μ, idem μ hKc hKo * (idem μ hKc hKo * x) = idem μ hKc hKo * x :=
    fun x => by rw [← mul_assoc, (isIdempotentElem_idem hKc hKo).eq]
  simp only [val_cornerₗ, mul_assoc, he]
end GroundTheory.Automorphic.HeckeAlgebra.HeckeAlgebraLevel
