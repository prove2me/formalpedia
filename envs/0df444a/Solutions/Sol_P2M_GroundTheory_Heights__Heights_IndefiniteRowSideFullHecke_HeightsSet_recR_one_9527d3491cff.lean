-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_recR_one_9527d3491cff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:08:20.902163+00:00
-- url     : https://prove2.me/submissions/5543fa0a-4c1e-4873-96b9-372bc3936c7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSmoothHermConstLine

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → Geo.HermLine ι) → ℝ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
theorem _root_.solution (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → Geo.HermLine ι) (E : Geo.HermLine ι) :
    recR I P L E 1 = -arInt P 1 E L := by
  have h : divSupp P 1 = ∅ := by
    ext V
    simp only [divSupp, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hV _
    have hp : V.IsPrime := hV.1.1
    have hle : P ⊔ Ideal.span {1} ≤ V := hV.1.2
    rw [Ideal.span_singleton_one, sup_top_eq, top_le_iff] at hle
    exact hp.ne_top hle
  unfold recR
  rw [h, finsum_mem_empty, zero_sub]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
