-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.forward_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:37:13.693065+00:00
-- url     : https://prove2.me/submissions/b2751777-5be7-41b3-85e2-771e5b2bc7c3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_intervalMap_commutes0
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_full_identity
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val)
    (f2 : (SuffixData S n).family.Cochain0 0)
    (hf2 : (SuffixData S n).family.coboundary0 0 f2 = lowerWord S n sigma e u) :
    (SuffixData S n).family.coboundary0 (TopIndex n)
        (intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _) f2 +
          residualPotential S n e u) = topWord S n sigma e := by
  rw [map_add,intervalMap_commutes0 _ n (Nat.le_refl _) 0 (Nat.zero_le _),hf2]
  exact (full_identity S n sigma e u hu).symm
end QEC.Coding.BDL26HistoryLogicalResidual
