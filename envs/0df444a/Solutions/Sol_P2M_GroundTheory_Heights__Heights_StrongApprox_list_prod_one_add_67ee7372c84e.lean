-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_list_prod_one_add_67ee7372c84e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:20:46.032264+00:00
-- url     : https://prove2.me/submissions/4cb133c4-5e8e-4ead-8e4d-d6b7c78041ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PTruncation
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
namespace GroundTheory.Heights₂.Heights.StrongApprox
theorem _root_.solution {ι R : Type*} [Ring R] (B : ι → R) (hB : ∀ v w, v ≠ w → B v * B w = 0)
    (l : List ι) (hl : l.Nodup) : (l.map fun v => 1 + B v).prod = 1 + (l.map B).sum := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [ih hl.2]
    have h0 : ∀ l' : List ι, v ∉ l' → B v * (l'.map B).sum = 0 := by
      intro l' hv'
      induction l' with
      | nil => simp
      | cons w l' ih' =>
        rw [List.mem_cons, not_or] at hv'
        rw [List.map_cons, List.sum_cons, mul_add, hB v w hv'.1, ih' hv'.2, add_zero]
    rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, h0 l hl.1]
    abel
end GroundTheory.Heights₂.Heights.StrongApprox
