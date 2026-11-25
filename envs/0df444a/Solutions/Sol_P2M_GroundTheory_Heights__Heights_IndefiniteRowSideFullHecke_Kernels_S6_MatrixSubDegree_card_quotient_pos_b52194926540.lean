-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_card_quotient_pos_b52194926540
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:19.29424+00:00
-- url     : https://prove2.me/submissions/e7fef566-c3df-4547-9bb6-7e32611fdcfa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsSmulMemFamilyOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CardQuotientEqGenIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights TensorProduct
open scoped nonZeroDivisors ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6.MatrixSubDegree
theorem _root_.solution {K : Type} [Field K] [NumberField K] {E : Type*}
    [AddCommGroup E] [Module (𝓞 K) E] (F : Submodule (𝓞 K) E) [Module.Finite (𝓞 K) F] {r : ℕ}
    (s : Fin r → F) (hs : LinearIndependent (𝓞 K) s) (hr : Module.finrank (𝓞 K) F = r) :
    (0 : ℝ) < Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
  have := finite_quotient_span hs (by rw [Fintype.card_fin, hr])
  exact_mod_cast Nat.card_pos
end S6.MatrixSubDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
