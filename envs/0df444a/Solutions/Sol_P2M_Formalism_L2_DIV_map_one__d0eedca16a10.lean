-- Prove2me | solution 1 for P2M_Formalism_L2_DIV_map_one__d0eedca16a10
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:08:21.859799+00:00
-- url     : https://prove2.me/submissions/ec226089-6dfe-441d-89da-53877a764152

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} :
    (1 : Matrix (Fin n) (Fin n) K).map σ = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)
end Formalism.L2.DIV
