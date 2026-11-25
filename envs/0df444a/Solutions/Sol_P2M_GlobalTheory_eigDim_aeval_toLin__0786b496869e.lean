-- Prove2me | solution 1 for P2M_GlobalTheory_eigDim_aeval_toLin__0786b496869e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:34:24.162137+00:00
-- url     : https://prove2.me/submissions/ae47b374-bd4a-404d-a4f6-19acf2b284c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (f : K[X]) :
    aeval (Matrix.toLin' M) f = Matrix.toLin' (aeval M f) :=
  Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix n n K ≃ₐ[K] _) M f
end GlobalTheory
