-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_deg_bundle_eq_deg_sub_b1b8aabe0ebf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:47:01.001318+00:00
-- url     : https://prove2.me/submissions/62ee943b-74b8-44f3-ab23-6afdd98241bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_arithDegree_congr_5fb6b845d5f9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct ComplexAt
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution (Nm : HermitianNorms K V) (M L : FullLattice K V)
    (hLM : L.carrier ≤ M.carrier) :
    (Nm.bundle L).deg = ((Nm.bundle M).sub (L.carrier.comap M.carrier.subtype)).deg := by
  unfold HermitianBundle.deg HermitianBundle.arithDegree
  congr 1
  refine (arithDegree_congr _ _ (Submodule.comapSubtypeEquivOfLe hLM) fun σ x y ↦ ?_).symm
  rfl
end GroundTheory.Heights₂.Heights.LatticeLemmas
