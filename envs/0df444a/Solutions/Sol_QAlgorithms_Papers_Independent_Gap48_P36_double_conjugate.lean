-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.double_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:42:02.685089+00:00
-- url     : https://prove2.me/submissions/7d4b39d4-4f70-4acb-96ee-e7dc1589e070

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

theorem x8_main [Nonempty A] [Nonempty B] [Nonempty C]
    (Phi : Superop A B) (PhiC : Superop A C) (hPhi : IsChannel Phi)
    (hc : CPComplementary Phi PhiC) : CPComplementary PhiC Phi := by
  obtain ⟨V, h1, h2⟩ := hc
  refine ⟨Matrix.of fun (cb : C × B) a => V (cb.2, cb.1) a, ?_, ?_⟩
  · rw [← h2]; funext rho; ext c c'
    simp [receiverChannel, complementaryChannel, QAlgorithms.traceRight, traceLeft, mul_apply,
      conjTranspose_apply]
  · rw [← h1]; funext rho; ext b b'
    simp [receiverChannel, complementaryChannel, QAlgorithms.traceRight, traceLeft, mul_apply,
      conjTranspose_apply]

end QAlgorithms.Papers.Independent.Gap48.P36

open QAlgorithms.Papers.Independent.Gap48.P36 in
theorem solution {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
    (Phi : QAlgorithms.Superop A B) (PhiC : QAlgorithms.Superop A C) (hPhi : QAlgorithms.IsChannel Phi)
    (hc : QAlgorithms.Papers.Independent.Claimed50.P48.CPComplementary Phi PhiC) :
    QAlgorithms.Papers.Independent.Claimed50.P48.CPComplementary PhiC Phi :=
  x8_main Phi PhiC hPhi hc
