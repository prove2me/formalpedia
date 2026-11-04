-- Prove2me | solution 1 for ThreeSum.StageBounds.amplifiedCoreWork_eventually_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:11:43.193864+00:00
-- url     : https://prove2.me/submissions/c632a28a-cc81-47e3-ba72-441c477e0ef1

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
import Theorems.Thm_ThreeSum_StageBounds_amplifiedCoreWork_powerBound
import Theorems.Thm_ThreeSum_Parameters_certificate_lt_target


set_option autoImplicit false
open ThreeSum ThreeSum.StageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.StageBounds
theorem _root_.solution {W H P H1 : ℕ → ℕ} (C k : ℕ)
    (hW : ∀ᶠ n : ℕ in atTop, W n * radix n ≤ wantedNumerator n)
    (hscore : ∀ᶠ n : ℕ in atTop, P n * H n ≤ scoreLoss k n * H1 n)
    (hinit : ∀ᶠ n : ℕ in atTop, H1 n ≤ candidateCount n * rawTripleBound n)
    (hmod : ∀ᶠ n : ℕ in atTop, radix n ≤ primeLoss radix n * P n) :
    ∀ᶠ n : ℕ in atTop, (amplifiedCoreWork C W H n : ℝ) ≤ (n : ℝ) ^ targetExponent := by
  have hh := (amplifiedCoreWork_powerBound C k hW hscore hinit hmod)
    (targetExponent - certificateExponent) (sub_pos.mpr certificate_lt_target)
  have hid : certificateExponent + (targetExponent - certificateExponent) = targetExponent := by ring
  rw [hid] at hh
  exact hh
end ThreeSum.StageBounds
