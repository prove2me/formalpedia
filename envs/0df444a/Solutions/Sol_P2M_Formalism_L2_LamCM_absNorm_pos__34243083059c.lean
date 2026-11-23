-- Prove2me | solution 1 for P2M_Formalism_L2_LamCM_absNorm_pos__34243083059c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:48.776667+00:00
-- url     : https://prove2.me/submissions/3eecfb94-e880-4be3-9b00-c16ff1e7870a

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM
theorem _root_.solution {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    (0 : ℝ) < ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  have h1 := FractionalIdeal.absNorm_nonneg I
  have h2 : (FractionalIdeal.absNorm I : ℚ) ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
  exact_mod_cast lt_of_le_of_ne h1 (Ne.symm h2)
end Formalism.L2.LamCM
