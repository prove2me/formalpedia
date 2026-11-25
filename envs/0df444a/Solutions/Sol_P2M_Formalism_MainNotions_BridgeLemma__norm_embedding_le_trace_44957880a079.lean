-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__norm_embedding_le_trace_44957880a079
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:30.930338+00:00
-- url     : https://prove2.me/submissions/dc2376b6-c480-470a-8b23-2d0ca2a99738

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_TraceInnerPosOfOrthonormalPair
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Module Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (a : K) (ha : ∀ σ : K →ₐ[ℚ] ℂ, ∃ r : ℝ, 0 ≤ r ∧ σ a = (r : ℂ)) (φ : K →+* ℂ) :
    ‖φ a‖ ≤ ((Algebra.trace ℚ K a : ℚ) : ℝ) := by
  classical
  choose r hr0 hr using ha
  have htr : ((Algebra.trace ℚ K a : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, r σ := by
    apply Complex.ofReal_injective
    have h1 := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := a)
    rw [show ((((Algebra.trace ℚ K a : ℚ) : ℝ)) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ K a) by simp, h1]
    push_cast
    exact Finset.sum_congr rfl fun σ _ => hr σ
  rw [htr]
  have hφ : φ a = ((r φ.toRatAlgHom : ℝ) : ℂ) := hr φ.toRatAlgHom
  rw [hφ, Complex.norm_of_nonneg (hr0 _)]
  exact Finset.single_le_sum (fun σ _ => hr0 σ) (Finset.mem_univ _)
end Formalism.MainNotions.BridgeLemma₂
