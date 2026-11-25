-- Prove2me | solution 1 for P2M_GlobalTheory_PolyNorm_shift_poly__31f4ccca3525
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:31:27.13799+00:00
-- url     : https://prove2.me/submissions/d420806d-6e3e-4d6a-8f66-fd08a22849d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul
import Theorems.Thm_GlobalTheory_PolyNorm_ev_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm
variable (N : ℤ[X] → ℚ) (Φ : (r : ℕ) → MvPolynomial (Fin r) ℚ)
  (hN : ∀ r (F : ℤ[X]), F.natDegree < r → N F = ev (Φ r) (F.map (Int.castRingHom ℚ)))
include hN
namespace GlobalTheory.PolyNorm
theorem _root_.solution (F G : ℤ[X]) :
    ∃ p : ℚ[X], ∀ t : ℕ, N ((F + t) * (G + t)) = p.eval (t : ℚ) := by
  refine ⟨ev (Φ (F.natDegree + G.natDegree + 1)) ((F.map (Int.castRingHom ℚ[X]) + C X) *
    (G.map (Int.castRingHom ℚ[X]) + C X)), fun t => ?_⟩
  rw [hN (F.natDegree + G.natDegree + 1), ← coe_evalRingHom, ev_map]
  · congr 1
    simp [Polynomial.map_map, RingHom.ext_int ((evalRingHom (t:ℚ)).comp _) (Int.castRingHom ℚ)]
  · refine lt_of_le_of_lt natDegree_mul_le ?_
    rw [← C_eq_natCast, natDegree_add_C, natDegree_add_C]; omega
end GlobalTheory.PolyNorm
