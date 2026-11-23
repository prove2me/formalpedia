-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.IsFrame.length_eq_latticeRank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:46.572353+00:00
-- url     : https://prove2.me/submissions/310207c0-6d28-43ec-a584-8b623f7066b5

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_IsFrame_ds_spanK_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.GeometryOfNumbersTheory
namespace IsFrame
theorem _root_.solution {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    r = latRank K E := by
  unfold latRank
  rw [← hv.ds_spanK_eq, finrank_span_eq_card hv.2.1, Fintype.card_fin]
end IsFrame
end ReciprocityTheory.GeometryOfNumbersTheory
