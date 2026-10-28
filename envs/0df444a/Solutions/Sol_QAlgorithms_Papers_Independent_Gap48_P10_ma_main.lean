-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P10.ma_main
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T10:26:41.114913+00:00
-- url     : https://prove2.me/submissions/319c1e08-c4de-438f-8fc4-61f6a2d81dc5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_ma_existence
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_ma_uniqueness
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_ma_tcount_nonincrease
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_ma_linear_symbolic_normalization

noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

local notation "Mat" => Matrix Bool Bool ℂ

theorem solution :
    (∀ U : Mat, CliffordT U → ∃! M : NormalForm, maValue M = U) ∧
    (∀ (M : NormalForm) (w : List Input), inputWordMatrix w = maValue M →
      normalTCount M ≤ inputTCount w) ∧
    LinearNormalizer maTokens maValue := by
  refine ⟨?_, ?_, ma_linear_symbolic_normalization⟩
  · intro U hU
    obtain ⟨M, hM, -, -⟩ := ma_existence U hU
    exact ⟨M, hM, fun M' hM' => ma_uniqueness (hM'.trans hM.symm)⟩
  · intro M w hw
    obtain ⟨N, hN, hc, -, -⟩ := ma_tcount_nonincrease (inputWordMatrix w) (inputTCount w) ⟨w, rfl, rfl⟩
    have := ma_uniqueness (hN.trans hw)
    subst this
    exact hc

end
