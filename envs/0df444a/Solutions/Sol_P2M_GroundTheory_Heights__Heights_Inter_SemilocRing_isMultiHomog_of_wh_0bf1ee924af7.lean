-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocRing_isMultiHomog_of_wh_0bf1ee924af7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:31.12164+00:00
-- url     : https://prove2.me/submissions/cfa2aa5e-64ff-4e34-b4d0-06fd07b13c2d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IdDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocRing
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open Classical
namespace GroundTheory.Heights₂.Heights.Inter.SemilocRing
theorem _root_.solution {s : MRing ι} {a : K → ℕ} (h : IsWeightedHomogeneous (blkW (ι := ι)) s a) :
    IsMultiHomog s a := by
  intro m hm k
  rw [← h (mem_support_iff.mp hm), Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [blkW]
  · intro b _ hb
    simp [blkW, Ne.symm hb]
  · simp
end GroundTheory.Heights₂.Heights.Inter.SemilocRing
