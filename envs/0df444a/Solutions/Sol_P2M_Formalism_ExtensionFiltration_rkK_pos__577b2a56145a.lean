-- Prove2me | solution 1 for P2M_Formalism_ExtensionFiltration_rkK_pos__577b2a56145a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:51.813406+00:00
-- url     : https://prove2.me/submissions/937062bd-016d-4106-8a97-af359aaad381

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentSlope
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open scoped Pointwise
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
omit [StarRing K] [IsTotallyComplex K]
namespace Formalism.ExtensionFiltration
theorem _root_.solution (M : Submodule (𝓞 K) V) (hM0 : M ≠ ⊥) [FiniteDimensional K V] : 0 < rkK (K := K) M := by
  unfold rkK
  apply Nat.pos_of_ne_zero
  intro h
  apply hM0
  rw [Submodule.finrank_eq_zero] at h
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ Submodule.span K (M : Set V) := Submodule.subset_span hx
  rw [h] at hx'
  exact (Submodule.mem_bot _).mpr ((Submodule.mem_bot K).mp hx')
end Formalism.ExtensionFiltration
