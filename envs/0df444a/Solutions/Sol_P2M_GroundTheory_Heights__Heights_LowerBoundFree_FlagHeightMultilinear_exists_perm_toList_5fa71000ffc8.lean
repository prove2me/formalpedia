-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_exists_perm_toList_5fa71000ffc8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:40.105687+00:00
-- url     : https://prove2.me/submissions/416ea7bf-dcd6-4b36-8885-e77230c983ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFlagGrassSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PHFlProdLinear

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear
theorem _root_.solution {α : Type} [DecidableEq α] {d : ℕ} (r : Fin d → α) :
    ∃ σ : Equiv.Perm (Fin d), ∀ (k : Fin d) (h : (k : ℕ) < (Multiset.map r Finset.univ.val).toList.length),
      (Multiset.map r Finset.univ.val).toList.get ⟨k, h⟩ = r (σ k) := by
  set l := (Multiset.map r Finset.univ.val).toList with hl
  have hlen : l.length = d := by simp [hl, Multiset.length_toList]
  let r' : Fin d → α := fun k => l.get ⟨k, by rw [hlen]; exact k.2⟩
  have hmap : Multiset.map r' Finset.univ.val = Multiset.map r Finset.univ.val := by
    rw [Fin.univ_val_map]
    have hof : List.ofFn r' = l := List.ext_get (by simp [hlen]) (fun k h1 h2 => by simp [r'])
    rw [hof, hl, Multiset.coe_toList]
  have hcard : ∀ a, Fintype.card {k // r' k = a} = Fintype.card {k // r k = a} := by
    intro a
    have h := congrArg (Multiset.count a) hmap
    rw [Multiset.count_map, Multiset.count_map] at h
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [Finset.card, Finset.filter_val]
    convert h using 3 <;> exact eq_comm
  refine ⟨Equiv.ofFiberEquiv (fun a => Fintype.equivOfCardEq (hcard a)), fun k h => ?_⟩
  exact (Equiv.ofFiberEquiv_map (fun a => Fintype.equivOfCardEq (hcard a)) k).symm
end GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear
