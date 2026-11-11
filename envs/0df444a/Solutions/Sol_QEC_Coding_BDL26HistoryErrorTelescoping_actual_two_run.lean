-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.actual_two_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:16:59.663481+00:00
-- url     : https://prove2.me/submissions/227013ff-b365-436b-ab95-583b4f872937

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_add_self
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_combine_full_words
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_descentWord_readout
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actual_fullspan
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_readout
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualReadout_top
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_perturbTop_preimage
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_actualHistory_syndrome
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_BDL26CochainFamily_coboundary1_comp_coboundary0
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    ∃ (h : (SuffixData S n).family.Cochain1 0)
      (R : (SuffixData S n).family.Cochain0 (TopIndex n)),
      (SuffixData S n).family.coboundary1 0 h =
        actualReadout S n sigma 0 + actualReadout S n (perturbTop S n sigma e) 0 ∧
      e + historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) +
          historyLiftedCorrection (SuffixData S n) (actualHistory S n (perturbTop S n sigma e)) =
        intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
          (h + (actualBase S n).decode (actualInputs S n sigma 0) +
            (actualBase S n).decode (actualInputs S n (perturbTop S n sigma e) 0)) +
          (SuffixData S n).family.coboundary0 (TopIndex n) R ∧
      (SuffixData S n).family.coboundary1 (TopIndex n)
        ((SuffixData S n).family.coboundary0 (TopIndex n) R) = 0 ∧
      (SuffixData S n).family.coboundary1 0
        (h + (actualBase S n).decode (actualInputs S n sigma 0) +
          (actualBase S n).decode (actualInputs S n (perturbTop S n sigma e) 0)) = 0 ∧
      (SuffixData S n).family.coboundary1 (TopIndex n)
        (e + historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) +
          historyLiftedCorrection (SuffixData S n) (actualHistory S n (perturbTop S n sigma e))) = 0 := by
  obtain ⟨u,hu,hue⟩ := perturbTop_preimage S n sigma e
  let tau := perturbTop S n sigma e
  let l := descentWord S n (TopIndex n) u 0 (Nat.zero_le _)
  let l' := descentWord S n (TopIndex n) (u+e) 0 (Nat.zero_le _)
  let q := accumulatedPotential S n (TopIndex n) u 0 n (Nat.le_refl _) (Nat.zero_le _)
  let q' := accumulatedPotential S n (TopIndex n) (u+e) 0 n (Nat.le_refl _) (Nat.zero_le _)
  let bs := (actualBase S n).decode (actualInputs S n sigma 0)
  let bt := (actualBase S n).decode (actualInputs S n tau 0)
  have hv := hu.trans (actualReadout_top S n sigma).symm
  have hv' := hue.trans (actualReadout_top S n tau).symm
  have hl : (SuffixData S n).family.coboundary1 0 l = actualReadout S n sigma 0 :=
    descentWord_readout S n sigma (TopIndex n) u hv 0 (Nat.zero_le _)
  have hl' : (SuffixData S n).family.coboundary1 0 l' = actualReadout S n tau 0 :=
    descentWord_readout S n tau (TopIndex n) (u+e) hv' 0 (Nat.zero_le _)
  have hb : (SuffixData S n).family.coboundary1 0 bs = actualReadout S n sigma 0 :=
    ((actualBase S n).rightInverse _).trans (actualInputs_readout S n sigma 0).symm
  have hb' : (SuffixData S n).family.coboundary1 0 bt = actualReadout S n tau 0 :=
    ((actualBase S n).rightInverse _).trans (actualInputs_readout S n tau 0).symm
  have hs := actual_fullspan S n sigma u hu
  have ht := actual_fullspan S n tau (u+e) hue
  have heq := combine_full_words
    (intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _))
    ((SuffixData S n).family.coboundary0 (TopIndex n)) u e
    (historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma))
    (historyLiftedCorrection (SuffixData S n) (actualHistory S n tau))
    (l+bs) (l'+bt) q q' hs ht
  have hinside : (l+bs)+(l'+bt)=(l+l')+bs+bt := by ac_rfl
  rw [hinside] at heq
  refine ⟨l+l',q+q',?_,heq,?_,?_,?_⟩
  · rw [map_add,hl,hl']
  · exact LinearMap.congr_fun ((SuffixData S n).family.coboundary1_comp_coboundary0
      (TopIndex n)) (q+q')
  · change (SuffixData S n).family.coboundary1 0 ((l+l')+bs+bt)=0
    rw [map_add,map_add,map_add,hl,hl',hb,hb']
    calc
      (actualReadout S n sigma 0 + actualReadout S n tau 0) + actualReadout S n sigma 0 +
          actualReadout S n tau 0 =
        (actualReadout S n sigma 0 + actualReadout S n sigma 0) +
          (actualReadout S n tau 0 + actualReadout S n tau 0) := by ac_rfl
      _ = 0 := by rw [word_add_self,word_add_self,add_zero]
  · rw [map_add,map_add]
    have hs' : (SuffixData S n).family.coboundary1 (TopIndex n)
        (historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma)) = sigma.val :=
      actualHistory_syndrome S n sigma
    have ht' : (SuffixData S n).family.coboundary1 (TopIndex n)
        (historyLiftedCorrection (SuffixData S n) (actualHistory S n tau)) = tau.val :=
      actualHistory_syndrome S n tau
    rw [hs',ht']
    change (SuffixData S n).family.coboundary1 (TopIndex n) e + sigma.val +
      (sigma.val + (SuffixData S n).family.coboundary1 (TopIndex n) e) = 0
    calc
      _ = ((SuffixData S n).family.coboundary1 (TopIndex n) e +
          (SuffixData S n).family.coboundary1 (TopIndex n) e) + (sigma.val+sigma.val) := by ac_rfl
      _ = 0 := by rw [word_add_self,word_add_self,add_zero]
end QEC.Coding.BDL26HistoryErrorTelescoping
