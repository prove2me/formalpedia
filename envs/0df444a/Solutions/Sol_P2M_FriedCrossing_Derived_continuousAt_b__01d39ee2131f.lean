-- Prove2me | solution 1 for P2M_FriedCrossing_Derived_continuousAt_b__01d39ee2131f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:07:11.086049+00:00
-- url     : https://prove2.me/submissions/f65f1c3f-eb26-4400-98d6-22d6f408b838

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_Derived_contDiff_M__e4c66d3c2429
import Theorems.Thm_FriedCrossing_Derived_hasDerivAt_M
import Theorems.Thm_P2M_FriedCrossing_Derived_continuousAt_N__entry_00e3f1d1fcad
import Theorems.Thm_FriedCrossing_Hadamard_continuousAt_Ndiv_entry


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}
namespace FriedCrossing.Derived
theorem _root_.solution (h : ClusterC3 M A)
    (hsemi : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    ContinuousAt (Function.uncurry (bτ M sStar)) (0, 0) := by
  have hN := continuousAt_Ndiv_entry M (Mτ M) sStar hsemi (hasDerivAt_M h)
    (fun i j => (contDiff_Mτ h i j).continuous.continuousAt)
  have hNτ := continuousAt_Nτ_entry (M := M) h
  change ContinuousAt (fun q : ℝ × ℝ => bτ M sStar q.1 q.2) (0, 0)
  simp only [bτ]
  exact (((hNτ 0 0).mul (hN 1 1)).add ((hN 0 0).mul (hNτ 1 1))).sub
    (((hNτ 0 1).mul (hN 1 0)).add ((hN 0 1).mul (hNτ 1 0)))
end FriedCrossing.Derived
