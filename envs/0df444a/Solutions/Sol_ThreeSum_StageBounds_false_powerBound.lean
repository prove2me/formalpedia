-- Prove2me | solution 1 for ThreeSum.StageBounds.false_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:28.340002+00:00
-- url     : https://prove2.me/submissions/81bdd294-1293-4b94-ad80-352078844a8b

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
import Theorems.Thm_ThreeSum_MassScales_falseMajorant_eventually_le
import Theorems.Thm_ThreeSum_MassScales_false_mass_le


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
theorem _root_.solution {H P H1 : ℕ → ℕ} (k : ℕ)
    (hscore : ∀ᶠ n : ℕ in atTop, P n * H n ≤ scoreLoss k n * H1 n)
    (hinit : ∀ᶠ n : ℕ in atTop, H1 n ≤ candidateCount n * rawTripleBound n)
    (hmod : ∀ᶠ n : ℕ in atTop, radix n ≤ primeLoss radix n * P n) :
    PowerBound H (2 - (1 / 2 - bandShift) / 5) := by
  intro d hd
  filter_upwards [hscore, hinit, hmod, falseMajorant_eventually_le k hd] with n hs hi hm he
  exact (false_mass_le hs hi hm).trans he
end ThreeSum.StageBounds
