-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_simple_roots_le_65e0c52da8c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:40:40.513864+00:00
-- url     : https://prove2.me/submissions/c114dcd8-99e2-4249-9684-c60ffbcc6dd6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_local_antilipschitz_ab32a154bc26
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_le_of_local_antilipschitz_c1a501dd5ea8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Metric Filter Topology Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH
namespace GroundTheory.Heights₂.Heights.ZeroLocusDimH
theorem _root_.solution {n r : ℕ} (π : Fin r → MvPolynomial (Fin n) ℂ)
    (P : Fin n → Polynomial (MvPolynomial (Fin r) ℂ)) (V : Set (Fin n → ℂ))
    (hV : ∀ x ∈ V, ∀ i, Polynomial.eval (x i) ((P i).map (MvPolynomial.eval (paramMap π x))) = 0) :
    dimH {x | x ∈ V ∧ ∀ i, Polynomial.eval (x i)
      ((Polynomial.derivative (P i)).map (MvPolynomial.eval (paramMap π x))) ≠ 0} ≤
      2 * (r : ENNReal) := by
  refine dimH_le_of_local_antilipschitz (paramMap π) _ fun x₀ hx₀ => ?_
  obtain ⟨U, hU, K, hK, hKU⟩ := local_antilipschitz π P V hV x₀ hx₀.2
  exact ⟨U, hU, K, hK, fun x hx x' hx' => hKU x ⟨hx.1.1, hx.2⟩ x' ⟨hx'.1.1, hx'.2⟩⟩
end GroundTheory.Heights₂.Heights.ZeroLocusDimH
