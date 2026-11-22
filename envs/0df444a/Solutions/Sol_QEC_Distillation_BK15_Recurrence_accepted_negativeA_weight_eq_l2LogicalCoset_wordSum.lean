-- Prove2me | solution 1 for QEC.Distillation.BK15.Recurrence.accepted_negativeA_weight_eq_l2LogicalCoset_wordSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T21:22:04.517152+00:00
-- url     : https://prove2.me/submissions/9343d4cd-008b-4ea3-b578-1468a875396a

import Definitions.Def_QEC_Distillation_BK15_NegativeAWordZ_QECert
import Definitions.Def_QEC_Distillation_BK15_NegativeAHistoryIndicator_QECert

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Recurrence
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput Protocol
open scoped BigOperators TensorProduct
set_option linter.constructorNameAsVariable false
namespace QEC.Distillation.BK15.Recurrence
theorem _root_.solution
    (epsilon : BK15Epsilon) :
    acceptedNegativeAWeight epsilon =
      ∑ word ∈ l2LogicalCosetWords, bk15WordWeight epsilon word := by
  classical
  rw [acceptedNegativeAWeight_eq_word_z_sum_QECert]
  simp_rw [sum_negativeA_trace_decoded_accepted_history_QECert]
  have hfilter :
      (Finset.univ.filter fun word : Word => word ∈ l2LogicalCosetWords) =
        l2LogicalCosetWords := by
    ext word
    simp
  calc
    ∑ word : Word, bk15WordWeight epsilon word *
        (if word ∈ l2LogicalCosetWords then 1 else 0) =
      ∑ word : Word,
        if word ∈ l2LogicalCosetWords then bk15WordWeight epsilon word else 0 := by
          apply Finset.sum_congr rfl
          intro word _
          by_cases hmember : word ∈ l2LogicalCosetWords <;> simp [hmember]
    _ = ∑ word ∈ Finset.univ.filter
        (fun word : Word => word ∈ l2LogicalCosetWords),
          bk15WordWeight epsilon word := by
            rw [Finset.sum_filter]
    _ = ∑ word ∈ l2LogicalCosetWords, bk15WordWeight epsilon word := by
          rw [hfilter]
end QEC.Distillation.BK15.Recurrence