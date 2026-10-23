-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P14.weakComplementDuality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:05:43.326035+00:00
-- url     : https://prove2.me/submissions/24192449-f9b6-4fa7-8d7f-4f420202f181

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14 in
theorem solution {I J : Type} [Nonempty I]
    (U : (Hilbert (I × J) ≃ₗᵢ[ℂ] Hilbert (I × J))) (sigma : State J) :
    WeaklyDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients) ↔
      AntiDegradable (weakComplement U sigma.coefficients) (dilationReceiver U sigma.coefficients) := by
  constructor
  · rintro ⟨hE, hF, hT⟩
    exact ⟨hF, hE, hT⟩
  · rintro ⟨hF, hE, hT⟩
    exact ⟨hE, hF, hT⟩

end
