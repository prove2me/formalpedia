-- Prove2me | solution 1 for P2M_GlobalTheory_DegCnt_NFGeom_mem_perp__b010c7cdb5ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:02.933497+00:00
-- url     : https://prove2.me/submissions/1dab89a0-c55b-43d1-afd0-18faedd926e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.NFGeom
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r)
omit [NumberField K]
namespace GlobalTheory.DegCnt.NFGeom
namespace _root_.GlobalTheory.DegCnt.NFGeom
theorem _root_.solution (S : Submodule K V) (y : V) :
    y ∈ _root_.GlobalTheory.HermLat.perp H S ↔ ∀ x ∈ S, H.B x y = 0 := by
  rw [_root_.GlobalTheory.HermLat.mem_perp_iff]
  exact ⟨fun h x hx => _root_.Formalism.HermitianLatticeCounting.P.B_swap0 H (h x hx), fun h x hx => _root_.Formalism.HermitianLatticeCounting.P.B_swap0 H (h x hx)⟩
end _root_.GlobalTheory.DegCnt.NFGeom
end GlobalTheory.DegCnt.NFGeom
