-- Prove2me | solution 1 for TunnellMap.paperTunnellMapTotal_quarterTurn_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:12:05.349415+00:00
-- url     : https://prove2.me/submissions/7d03887d-a7f1-4013-8a68-7c6d80093bc8

import Definitions.Def_TunnellMap_FallbackFreeMap
import Definitions.Def_TunnellMap_BranchSpec
import Theorems.Thm_TunnellMap_paperTunnellMapTotal_val_eq

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.z % 2 = 0)
    (h₁ : (8 : ℤ) ∣ (p.1.x + 2 * p.1.z + p.1.y)) :
    (paperTunnellMapTotal hn hnpos hsq hbal p).1 =
      ⟨4 * ((p.1.x + 2 * p.1.z + p.1.y) / 8) - p.1.y, p.1.x - 2 * p.1.z,
        (p.1.x + 2 * p.1.z + p.1.y) / 8⟩ := by
  refine paperTunnellMapTotal_val_eq hn hnpos hsq hbal ?_
  have hd : SourceUsedTriple p.1 := Or.inl h₁
  let q : BOddRep n := ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩
  rw [paperTunnellMapExecOpt, dif_neg hz]
  change Option.map (fun a : ARep n => a.1) (oddMapExecOpt hnpos hsq q) = _
  rw [oddMapExecOpt, dif_pos hd,
    directMapExec, directDomainExec, dif_pos h₁]
  rfl
end TunnellMap
