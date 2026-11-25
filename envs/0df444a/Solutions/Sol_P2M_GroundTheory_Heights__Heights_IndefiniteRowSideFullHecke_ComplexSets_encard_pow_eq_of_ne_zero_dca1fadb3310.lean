-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_encard_pow_eq_of_ne_zero_dca1fadb3310
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:32.247425+00:00
-- url     : https://prove2.me/submissions/c91e7836-f7f2-42f2-98c3-f7c6be75799e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsPowerUnitCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPowerUnitCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Filter Topology Matrix Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {m : ℕ} (hm : m ≠ 0) {t : ℂ} (ht : t ≠ 0) :
    {a : ℂ | a ^ m = t}.encard = m := by
  have hζ := Complex.isPrimitiveRoot_exp m hm
  have hset : {a : ℂ | a ^ m = t} = ↑(nthRootsFinset m t) := by
    ext a
    simp [mem_nthRootsFinset (Nat.pos_of_ne_zero hm)]
  classical
  rw [hset, Set.encard_coe_eq_coe_finsetCard, nthRootsFinset_def,
    Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup ht), hζ.card_nthRoots,
    if_pos ⟨t ^ ((m : ℂ)⁻¹), Complex.cpow_nat_inv_pow t hm⟩]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
