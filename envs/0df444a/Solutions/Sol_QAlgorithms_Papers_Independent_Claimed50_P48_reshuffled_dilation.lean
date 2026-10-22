-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P48.reshuffled_dilation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:16:50.870653+00:00
-- url     : https://prove2.me/submissions/dae358c7-efd6-44d7-9b92-782a5acfa0ed

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]


/-- PDF p.9: computed reshuffling of arbitrary V. Tr_B(S*S)=V*V;
only trace-preserving dilations make it I. -/
theorem solution [Nonempty A] (V : Matrix (B × C) A ℂ) :
    (∀ rho, complementaryChannel V rho = dilationReshuffle V * (rho ⊗ₖ (1 : Matrix B B ℂ)) * (dilationReshuffle V)ᴴ) ∧
    traceRight ((dilationReshuffle V)ᴴ * dilationReshuffle V) = Vᴴ * V ∧
    (Vᴴ * V = 1 → traceRight ((dilationReshuffle V)ᴴ * dilationReshuffle V) = 1) ∧
    (∀ (a : A → ℂ) (b : B → ℂ) (c : C → ℂ),
      (∑ j, ∑ k, conj (conj (b j) * c k) * (∑ i, V (j,k) i * a i)) =
        ∑ k, conj (c k) * (∑ i, ∑ j, dilationReshuffle V k (i,j) * (a i * b j))) := by
  have h2 : traceRight ((dilationReshuffle V)ᴴ * dilationReshuffle V) = Vᴴ * V := by
    ext i j
    simp only [traceRight, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      dilationReshuffle, Fintype.sum_prod_type]
  refine ⟨fun rho => ?_, h2, fun h => h2.trans h, fun a b c => ?_⟩
  · ext c c'
    simp only [complementaryChannel, traceLeft, Matrix.of_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, dilationReshuffle, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_mul]
    rw [Finset.sum_comm]
  · simp only [dilationReshuffle, map_mul, Complex.conj_conj, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring



end
