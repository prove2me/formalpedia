-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__prod_norm_embeddings_eq_abs_norm_alt_a07d0a0fed57
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:25.461349+00:00
-- url     : https://prove2.me/submissions/35d7db4c-4489-4aba-b27f-f72c4aa5c0dd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm

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
variable (K : Type) [Field K] [NumberField K]
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (a : K) : ∏ φ : K →+* ℂ, ‖φ a‖ = |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ a
  have h2 : ∏ φ : K →+* ℂ, φ a = ∏ σ : K →ₐ[ℚ] ℂ, σ a :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun φ => rfl)
  rw [← norm_prod, h2, ← h]
  simp
end Formalism.MainNotions.BridgeLemma₂
