-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.ebt_hadamard_construction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:49:12.83671+00:00
-- url     : https://prove2.me/submissions/e83730c8-df5c-4ab5-a416-edb7ec9549b5

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

theorem x8_gram (x : K → EuclideanSpace ℂ B) (k k' : K) :
    QAlgorithms.Papers.Independent.Claimed50.P48.gram x k k' = ∑ b, star (x k' b) * x k b := by
  simp [QAlgorithms.Papers.Independent.Claimed50.P48.gram, PiLp.inner_apply, mul_comm]

theorem x8_main [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty K]
    (w : K → EuclideanSpace ℂ A) (x : K → EuclideanSpace ℂ B)
    (hF : IsKrausFamily (rankOneKraus w x)) :
    complementaryChannel (indexedKrausDilation (rankOneKraus w x)) =
      arbitraryVectorComplement (QAlgorithms.Papers.Independent.Claimed50.P48.gram x) w ∧
    (∀ v : Matrix K C ℂ, v * vᴴ = QAlgorithms.Papers.Independent.Claimed50.P48.gram x →
      krausApply (gramKraus v w) =
        arbitraryVectorComplement (QAlgorithms.Papers.Independent.Claimed50.P48.gram x) w) ∧
    (∀ v : Matrix K C ℂ, IsKrausFamily (gramKraus v w) →
      HasRankOneKraus (complementaryChannel (indexedKrausDilation (gramKraus v w)))) := by
  refine ⟨?_, ?_, ?_⟩
  · funext rho; ext k k'
    simp only [arbitraryVectorComplement, x8_gram, complementaryChannel, traceLeft,
      Matrix.of_apply, mul_apply, conjTranspose_apply, indexedKrausDilation, rankOneKraus,
      Finset.sum_mul, Finset.mul_sum, star_mul']
    conv_lhs => rw [Finset.sum_comm]; arg 2; ext a'; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ =>
      Finset.sum_congr rfl fun b _ => ?_
    simp [RCLike.star_def]
    ring
  · intro v hv
    funext rho; ext k k'
    have hv' : ∀ k k', QAlgorithms.Papers.Independent.Claimed50.P48.gram x k k' =
        ∑ j, v k j * star (v k' j) := by
      intro k k'; rw [← hv, mul_apply]; simp [conjTranspose_apply]
    simp only [arbitraryVectorComplement, hv', krausApply, Matrix.sum_apply, mul_apply,
      conjTranspose_apply, gramKraus, Finset.sum_mul, Finset.mul_sum, star_mul']
    conv_lhs => rw [Finset.sum_comm]; arg 2; ext a'; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ =>
      Finset.sum_congr rfl fun b _ => ?_
    simp [RCLike.star_def]
    ring
  · intro v _
    let e := Fintype.equivFin K
    refine ⟨Fintype.card K, fun m => w (e.symm m),
      fun m => WithLp.toLp 2 (fun j => v (e.symm m) j), ?_⟩
    funext rho; ext j j'
    simp only [complementaryChannel, traceLeft, Matrix.of_apply, mul_apply, conjTranspose_apply,
      indexedKrausDilation, gramKraus, krausApply, Matrix.sum_apply, rankOneKraus]
    rw [← Equiv.sum_comp e.symm]

end QAlgorithms.Papers.Independent.Gap48.P36

open scoped Matrix in
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P36 QAlgorithms.Papers.Independent.Claimed50.P48
  QAlgorithms.Papers.Independent.Information100.P67 in
theorem solution {A B C K : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype K] [DecidableEq K]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty K]
    (w : K → EuclideanSpace ℂ A) (x : K → EuclideanSpace ℂ B)
    (hF : IsKrausFamily (rankOneKraus w x)) :
    complementaryChannel (indexedKrausDilation (rankOneKraus w x)) =
      arbitraryVectorComplement (gram x) w ∧
    (∀ v : Matrix K C ℂ, v * vᴴ = gram x →
      krausApply (gramKraus v w) = arbitraryVectorComplement (gram x) w) ∧
    (∀ v : Matrix K C ℂ, IsKrausFamily (gramKraus v w) →
      HasRankOneKraus (complementaryChannel (indexedKrausDilation (gramKraus v w)))) :=
  x8_main w x hF
