-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsNear_proof_821536a8ed45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:57:48.947216+00:00
-- url     : https://prove2.me/submissions/f626ca55-0d4d-4324-b53b-2989f23f3a92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRootsNear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsNear_pow_card_le_norm_prod_4142eeda9e0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsNear_continuous_eval__b98193422951

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace RootsNear
theorem _root_.solution : RootsNear.Statement := by
  intro e G hG y₀ t₀ h0 ε hε
  have hpos : (0 : ℝ) < ε ^ G.natDegree := pow_pos hε _
  have ht := (RootsNear.continuous_eval₂ G t₀).tendsto y₀
  rw [h0] at ht
  filter_upwards [ht (Metric.ball_mem_nhds 0 hpos)] with y hy
  rw [Set.mem_preimage, mem_ball_zero_iff] at hy
  by_contra hno
  push Not at hno
  set p := G.map (aeval y).toRingHom with hp
  have hpm : p.Monic := hG.map _
  have hdeg : p.natDegree = G.natDegree := hG.natDegree_map _
  have hcard : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hpm hcard
  have hev : G.eval₂ (aeval y).toRingHom t₀ = (p.roots.map fun a => t₀ - a).prod := by
    rw [← Polynomial.eval_map, ← hp]
    conv_lhs => rw [← hprod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have hle := RootsNear.pow_card_le_norm_prod p.roots t₀ hε.le (fun a ha => by
    have ha' : p.eval₂ (RingHom.id ℂ) a = 0 := by
      rw [Polynomial.eval₂_id]; exact (Polynomial.mem_roots hpm.ne_zero).1 ha
    have := hno a (by rw [hp, Polynomial.eval₂_map] at ha'; simpa using ha')
    exact this)
  rw [hcard, hdeg, ← hev] at hle
  exact absurd hy (not_lt.2 hle)
end RootsNear
end GroundTheory.Heights₂.Heights.HilbertSamuel
