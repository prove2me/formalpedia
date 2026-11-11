-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.full_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:03:30.026786+00:00
-- url     : https://prove2.me/submissions/142b676e-29db-4cc2-8bc2-a1d45d081acf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actual_fullspan
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_combine_full_words


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    topWord S n sigma e =
      intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _) (lowerWord S n sigma e u) +
        (SuffixData S n).family.coboundary0 (TopIndex n) (residualPotential S n e u) := by
  let tau := perturbTop S n sigma e
  let l := descentWord S n (TopIndex n) u 0 (Nat.zero_le _)
  let l' := descentWord S n (TopIndex n) (u+e) 0 (Nat.zero_le _)
  let bs := baseCorrection S n sigma
  let bt := baseCorrection S n tau
  let q := accumulatedPotential S n (TopIndex n) u 0 n (Nat.le_refl _) (Nat.zero_le _)
  let q' := accumulatedPotential S n (TopIndex n) (u+e) 0 n (Nat.le_refl _) (Nat.zero_le _)
  have hs := actual_fullspan S n sigma u hu
  have ht := actual_fullspan S n tau (u+e) (shared_valid S n sigma e u hu)
  have heq := combine_full_words
    (intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _))
    ((SuffixData S n).family.coboundary0 (TopIndex n)) u e
    (fullCorrection S n sigma) (fullCorrection S n tau) (l+bs) (l'+bt) q q' hs ht
  have hinside : (l+bs)+(l'+bt)=(l+l')+bs+bt := by ac_rfl
  rw [hinside] at heq
  exact heq
end QEC.Coding.BDL26HistoryLogicalResidual
