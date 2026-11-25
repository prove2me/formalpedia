-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__one_le_abs_norm_of_ne_zero_alt_c6845006cab4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:31:21.709816+00:00
-- url     : https://prove2.me/submissions/692cfbd7-1029-45f8-8e32-832de5dea746

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
theorem _root_.solution (a : 𝓞 K) (ha : a ≠ 0) : (1 : ℝ) ≤ |((Algebra.norm ℚ (a : K) : ℚ) : ℝ)| := by
  rw [← Algebra.coe_norm_int a]
  have h0 : Algebra.norm ℤ a ≠ 0 := by
    rw [Ne, Algebra.norm_eq_zero_iff]; exact ha
  have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ a| := Int.one_le_abs h0
  exact_mod_cast h1
end Formalism.MainNotions.BridgeLemma₂
