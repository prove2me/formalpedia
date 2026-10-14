-- Prove2me | solution 1 for ThreeSum1960614.quartic_parameter_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-14T07:22:53.829821+00:00
-- url     : https://prove2.me/submissions/611cc51f-a057-401f-96ca-b428c3a3e4e1

import Theorems.Thm_ThreeSum1960614_encoding_parameter_bounds
import Theorems.Thm_ThreeSum1960614_initial_entropy_bound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
open ThreeSum1960614

theorem solution :
    4648781151243719 / 1000000000000000 < E 232 ∧
    E 232 < 4648781151243720 / 1000000000000000 ∧
    1557987216578 / 1000000000000000 < kappa 232 ∧
    kappa 232 < 1557987216579 / 1000000000000000 ∧
    entropy theta < 244168414687344 / 1000000000000000 ∧
    v < phi theta ∧ threshold tau < phi (1 / 2) ∧
    0 < epsilon * (E 232 + beta) ∧ epsilon * (E 232 + beta) < 1 ∧
    (∀ z ∈ costs, z < principal) ∧ principal < (target : ℝ) := by
  obtain ⟨hEl, hEu, hkl, hku⟩ := ThreeSum1960614.encoding_parameter_bounds
  have hh := ThreeSum1960614.initial_entropy_bound
  refine ⟨hEl, hEu, hkl, hku, hh, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [v, saving, beta, phi, theta]
  · norm_num [threshold, tau, v, saving, beta, phi]
  · dsimp [epsilon, beta]
    nlinarith only [hEl]
  · dsimp [epsilon, beta]
    nlinarith only [hEu]
  · intro z hz
    simp only [costs, ledger, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp [epsilon, beta, saving, tau, rho, principal]
    all_goals nlinarith only [hEl, hEu, hku, hh]
  · norm_num [principal, target]
