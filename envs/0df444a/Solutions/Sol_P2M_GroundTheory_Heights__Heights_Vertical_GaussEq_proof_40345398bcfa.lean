-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GaussEq_proof_40345398bcfa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:54:11.046953+00:00
-- url     : https://prove2.me/submissions/4ebd9d98-ec85-4622-b324-3e8b6eb96c04

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGaussEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_gaussNormOf_rename_9e948dcb4a17
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_specFirst_map_0340cfe6fa1a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_gaussNorm_map_eq_one_4c5bd7b79347
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_eq_gaussNormOf_d4ed71b31023


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace GaussEq
theorem _root_.solution (h1 : OrdEq.Statement) (h2 : GaussDVR.Statement) (h3 : ParDVRIsDVR.Statement) :
    GaussEq.Statement := by
  intro K _ _ n e I g u v hI hf hu hprim
  have := h3 K e n v
  have hord := h1 K n e I g u v hI hf hu hprim
  refine ⟨?_, gaussNorm_map_eq_one v g hprim⟩
  set h := rename (Sum.inl : Fin e × Fin n → Par e n) (specFirst g u) with hh
  have hne : h ≠ 0 := by
    intro h0
    rw [h0, map_zero, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_zero] at hord
    exact ENat.top_ne_natCast _ hord
  have hG := h2 K e n v h hne
  rw [hord, ENat.toNat_natCast] at hG
  have hmap : h.map (algebraMap (𝓞 K) K) =
      rename (Sum.inl : Fin e × Fin n → Par e n) ((specFirst g u).map (algebraMap (𝓞 K) K)) := by
    rw [hh, map_rename]
  rw [hmap, gaussNorm_eq_gaussNormOf, gaussNormOf_rename _ Sum.inl_injective, ← gaussNorm_eq_gaussNormOf,
    ← specFirst_map] at hG
  exact hG
end GaussEq
end GroundTheory.Heights₂.Heights.Vertical
