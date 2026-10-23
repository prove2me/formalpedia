-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.conjugate_kraus_reshuffling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:42:03.71476+00:00
-- url     : https://prove2.me/submissions/a771ac4b-07b2-4628-9f23-6a51fbcff107

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

open Matrix

theorem x8_main [Nonempty A] [Nonempty B] [Nonempty K]
    (F : K → Matrix B A ℂ) (hF : IsKrausFamily F) :
    (∀ b j a, rowKraus F b j a = F j b a) ∧
    complementaryChannel (indexedKrausDilation F) = krausApply (rowKraus F) := by
  refine ⟨fun _ _ _ => rfl, ?_⟩
  funext rho; ext k k'
  simp only [complementaryChannel, krausApply, traceLeft, Matrix.of_apply, Matrix.sum_apply,
    mul_apply, conjTranspose_apply, indexedKrausDilation, rowKraus]

end QAlgorithms.Papers.Independent.Gap48.P36

open QAlgorithms.Papers.Independent.Gap48.P36 in
theorem solution {A B K : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype K] [DecidableEq K] [Nonempty A] [Nonempty B] [Nonempty K]
    (F : K → Matrix B A ℂ) (hF : QAlgorithms.IsKrausFamily F) :
    (∀ b j a, QAlgorithms.Papers.Independent.Claimed50.P48.rowKraus F b j a = F j b a) ∧
    QAlgorithms.Papers.Independent.Information100.P67.complementaryChannel
        (QAlgorithms.Papers.Independent.Claimed50.P48.indexedKrausDilation F) =
      QAlgorithms.krausApply (QAlgorithms.Papers.Independent.Claimed50.P48.rowKraus F) :=
  x8_main F hF
