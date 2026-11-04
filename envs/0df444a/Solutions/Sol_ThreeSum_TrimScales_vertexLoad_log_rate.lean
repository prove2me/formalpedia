-- Prove2me | solution 1 for ThreeSum.TrimScales.vertexLoad_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:34:22.467936+00:00
-- url     : https://prove2.me/submissions/c0246dc3-61a5-476c-bd65-2539a57ce96b

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Theorems.Thm_ThreeSum_BinomialEntropy_vertex_table_rate
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos
import Theorems.Thm_ThreeSum_Scales_localPrime_log_rate


set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.TrimScales
theorem _root_.solution :
    Tendsto (fun h : ℕ => Real.log (vertexLoad h) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 (Parameters.kappa / 2)) := by
  have h := BinomialEntropy.vertex_table_rate.sub localPrime_log_rate
  have heq : (Parameters.E + 1 / 2 + Parameters.kappa / 2) - (Parameters.E + 1 / 2) =
      Parameters.kappa / 2 := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [] with h
  have hV : (0 : ℝ) < LocalCoverBounds.vertexCount (512 * h) h := by
    exact_mod_cast (Nat.choose_pos (by omega : h ≤ 512 * h))
  have hp : (0 : ℝ) < LocalCoverBounds.localPrime h := by
    exact_mod_cast LocalCoverBounds.localPrime_pos h
  rw [vertexLoad, Real.log_div hV.ne' hp.ne', sub_div]
  rfl
end ThreeSum.TrimScales
