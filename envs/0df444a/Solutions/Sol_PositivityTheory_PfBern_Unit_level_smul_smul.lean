-- Prove2me | solution 1 for PositivityTheory.PfBern.Unit.level_smul_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:29:49.813878+00:00
-- url     : https://prove2.me/submissions/c1a5dfc8-bddf-4b11-9540-f21f39da680b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_UnitaryKirillovModel_LevelSmulSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Unit
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
variable {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
namespace PositivityTheory.PfBern.Unit
theorem _root_.solution (c : ℂ) (h : HeckeAlgebraLevel μ K hKc hKo) (w : fixedVectors ρ K) :
    (c • h) • w = c • (h • w) := Subtype.ext (by
  change heckeAct μ ρ ((c • (h : HeckeAlgebra μ) : HeckeAlgebra μ) : G → ℂ) (w : V) =
    c • heckeAct μ ρ ((h : HeckeAlgebra μ) : G → ℂ) (w : V)
  rw [HeckeAlgebra.coe_smul]
  exact heckeAct_smul_left c (h : HeckeAlgebra μ).mem (smooth_of_mem_fixedVectors hKo w.2))
end PositivityTheory.PfBern.Unit
