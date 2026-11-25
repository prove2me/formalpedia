-- Prove2me | solution 1 for P2M_GlobalTheory_dot_self_nonneg__607dd4203c70
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:34:20.980899+00:00
-- url     : https://prove2.me/submissions/365a837d-8ddf-4c9b-a5e2-a7714b69da86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SchurComplementBlockQuadraticLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (n : ℕ) (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
end GlobalTheory
