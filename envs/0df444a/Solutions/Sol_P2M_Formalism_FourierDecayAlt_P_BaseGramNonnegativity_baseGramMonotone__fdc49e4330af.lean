-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_baseGramMonotone__fdc49e4330af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:37:13.7424+00:00
-- url     : https://prove2.me/submissions/02faaf9f-db6b-44e2-8c83-585c72b68f02

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_baseGram_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_baseGram_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BaseGramNonnegativity
open Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.TB
variable {E W : Type} [Field E] (D : Data E W)
namespace Formalism.FourierDecayAlt.P.BaseGramNonnegativity
theorem _root_.solution : BaseGramMonotone := by
  intro E W _ D hG hW ε hε k w Y κ κ' hκ hκκ'
  refine ⟨baseGram_nonneg D hG hW hε k w Y κ hκ, ?_⟩
  have := baseGram_nonneg D hG hW hε k w Y _ hκκ'
  rw [baseGram_sub] at this
  linarith
end Formalism.FourierDecayAlt.P.BaseGramNonnegativity
