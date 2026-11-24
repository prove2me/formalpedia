-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_zeroSet_sliceIdeal_81bd9c1d3ddc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:42.009598+00:00
-- url     : https://prove2.me/submissions/b9e3dcd7-a6a0-46e0-bfc9-381ab8f31196

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_linPoly_64fe785a0385

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ)
    (q : Fin n → ℂ) : zeroSet (sliceIdeal J L q) = zeroSet J ∩ {x | L *ᵥ x = L *ᵥ q} := by
  ext x
  simp only [zeroSet, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨fun f hf => h f (Ideal.mem_sup_left hf), funext fun i => ?_⟩
    have := h _ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    rwa [map_sub, eval_linPoly, eval_C, sub_eq_zero] at this
  · rintro ⟨hJ, hL⟩ f hf
    have hle : sliceIdeal J L q ≤ RingHom.ker (eval x) := by
      refine sup_le (fun g hg => RingHom.mem_ker.2 (hJ g hg)) ?_
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, eval_linPoly, eval_C, hL, sub_self]
    exact RingHom.mem_ker.1 (hle hf)
end GroundTheory.Heights₂.Heights
