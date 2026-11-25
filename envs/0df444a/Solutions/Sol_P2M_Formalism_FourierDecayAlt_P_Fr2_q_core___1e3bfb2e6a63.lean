-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Fr2_q_core___1e3bfb2e6a63
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:14.985002+00:00
-- url     : https://prove2.me/submissions/24ebd348-2011-45ab-b87a-d59379b5aa6e

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr2_q_core__291ef32df1e7
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_interlaces_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr2
namespace Formalism.FourierDecayAlt.P.Fr2
theorem _root_.solution (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u' l + 2 ≤ -Y ∧ -Y ≤ u l - 2) :
    ∏ i ∈ Icc 1 k, ((Y - 1 + 1/2 + u i) * (Y - 1 + 1/2 + u' i)) < 0 := by
  have := q_core' k u' u ρ l Y hl1 hlk (interlaces_swap h) hA
  rwa [prod_congr rfl (fun i _ => mul_comm (Y - 1 + 1/2 + u' i) (Y - 1 + 1/2 + u i))] at this
end Formalism.FourierDecayAlt.P.Fr2
