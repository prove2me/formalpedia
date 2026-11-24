-- Prove2me | solution 1 for P2M_Formalism_GM_leadingTermLemmas_map_smul__bc719bbdb6cf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:00.728794+00:00
-- url     : https://prove2.me/submissions/300aad70-8c48-4a81-ac79-9111285d7246

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable (K : Type) [Field K] [CharZero K]
local notation "ι" => algebraMap ℚ K
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (c : ℚ) (g : MvPolynomial σ ℚ) : map ι (c • g) = (ι c) • map ι g := by
  rw [smul_eq_C_mul, map_mul, map_C, smul_eq_C_mul]
end Formalism.GM.leadingTermLemmas
