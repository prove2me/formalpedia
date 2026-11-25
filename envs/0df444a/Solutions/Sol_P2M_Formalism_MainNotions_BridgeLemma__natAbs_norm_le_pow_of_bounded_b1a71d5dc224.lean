-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__natAbs_norm_le_pow_of_bounded_b1a71d5dc224
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:29.963182+00:00
-- url     : https://prove2.me/submissions/4922d985-7480-479a-b73b-863538cdfac9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__prod_norm_embeddings_eq_abs_norm_alt_a07d0a0fed57

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Formalism.HermitianLatticesTheory Module
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (K : Type) [Field K] [NumberField K] (d : 𝓞 K) (B : ℝ)
    (hd : ∀ φ : K →+* ℂ, ‖φ (d : K)‖ ≤ B) : ((Algebra.norm ℤ d).natAbs : ℝ) ≤ B ^ finrank ℚ K := by
  have h1 : ((Algebra.norm ℤ d).natAbs : ℝ) = |((Algebra.norm ℚ (d : K) : ℚ) : ℝ)| := by
    rw [← Algebra.coe_norm_int d, Nat.cast_natAbs]
    push_cast
    rfl
  rw [h1, ← prod_norm_embeddings_eq_abs_norm_alt]
  calc ∏ φ : K →+* ℂ, ‖φ (d : K)‖ ≤ ∏ _φ : K →+* ℂ, B :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun φ _ => hd φ)
    _ = B ^ finrank ℚ K := by rw [Finset.prod_const, Finset.card_univ, NumberField.Embeddings.card]
end Formalism.MainNotions.BridgeLemma₂
