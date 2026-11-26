-- Prove2me | solution 1 for TunnellMap.BlockGen.blocksFromK_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:02:22.981423+00:00
-- url     : https://prove2.me/submissions/89dab219-63da-40f7-92ec-413bef120f05

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
import Theorems.Thm_TunnellMap_BlockGen_blockRecordsK_eq

set_option autoImplicit true
open TunnellMap
open OrderedGenerator
open TunnellMap.BlockGen
variable {n : ℤ} {p : Triple}
variable {s : BResidual n}
namespace TunnellMap.BlockGen
theorem _root_.solution (hn : 0 ≤ n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    ∀ (fuel : ℕ) (h : ℤ), 1 ≤ h → (hMax n + 1 - h).toNat ≤ fuel →
      blocksFromK s F fuel h = blocksFrom s F h := by
  intro fuel
  induction fuel with
  | zero =>
      intro h h1 hfuel
      have hgt : ¬ h ≤ hMax n := by omega
      rw [blocksFromK, blocksFrom, if_neg hgt]
  | succ fuel ih =>
      intro h h1 hfuel
      rw [blocksFromK, blocksFrom]
      by_cases hle : h ≤ hMax n
      · rw [if_pos hle, if_pos hle, blockRecordsK_eq hn F h1 hle,
          ih (h + 1) (by omega) (by omega)]
      · rw [if_neg hle, if_neg hle]
end TunnellMap.BlockGen
