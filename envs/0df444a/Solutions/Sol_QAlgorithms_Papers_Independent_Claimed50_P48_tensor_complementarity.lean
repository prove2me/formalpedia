-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P48.tensor_complementarity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:19:34.648467+00:00
-- url     : https://prove2.me/submissions/1b53126c-582f-4656-826f-60dea9274579

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

theorem g68l_rc_entry {B' C' A' : Type*} [Fintype B'] [Fintype C'] [Fintype A']
    (V : Matrix (B' × C') A' ℂ) (X : Matrix A' A' ℂ) (b b' : B') :
    receiverChannel V X b b' = ∑ k, ∑ i, ∑ j, V (b,k) i * X i j * conj (V (b',k) j) := by
  simp only [receiverChannel, traceRight, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, RCLike.star_def]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_comm

theorem g68l_cc_entry {B' C' A' : Type*} [Fintype B'] [Fintype C'] [Fintype A']
    (V : Matrix (B' × C') A' ℂ) (X : Matrix A' A' ℂ) (k k' : C') :
    complementaryChannel V X k k' = ∑ b, ∑ i, ∑ j, V (b,k) i * X i j * conj (V (b,k') j) := by
  simp only [complementaryChannel, traceLeft, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, RCLike.star_def]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_comm

theorem g68l_rc_single {B' C' A' : Type*} [Fintype B'] [Fintype C'] [Fintype A'] [DecidableEq A']
    (V : Matrix (B' × C') A' ℂ) (a c : A') (b b' : B') :
    receiverChannel V (Matrix.single a c 1) b b' = ∑ k, V (b,k) a * conj (V (b',k) c) := by
  rw [g68l_rc_entry]
  simp [Matrix.single_apply, ite_and]

theorem g68l_cc_single {B' C' A' : Type*} [Fintype B'] [Fintype C'] [Fintype A'] [DecidableEq A']
    (V : Matrix (B' × C') A' ℂ) (a c : A') (k k' : C') :
    complementaryChannel V (Matrix.single a c 1) k k' = ∑ b, V (b,k) a * conj (V (b,k') c) := by
  rw [g68l_cc_entry]
  simp [Matrix.single_apply, ite_and]

theorem g68l_tc1 (V : Matrix (B × C) A ℂ) (W : Matrix (B2 × C2) A2 ℂ) :
    receiverChannel (tensorDilation V W) = superopTensor (receiverChannel V) (receiverChannel W) := by
  funext X; ext ⟨b, b2⟩ ⟨b', b2'⟩
  rw [g68l_rc_entry]
  simp only [superopTensor, Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, g68l_rc_single,
    tensorDilation, Fintype.sum_prod_type, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [← Fintype.sum_prod_type']
  let e : (C × C2 × A × A2 × A × A2) ≃ (A × A2 × A × A2 × C2 × C) :=
    { toFun := fun x => (x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, x.2.1, x.1)
      invFun := fun y => (y.2.2.2.2.2, y.2.2.2.2.1, y.1, y.2.1, y.2.2.1, y.2.2.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine Fintype.sum_equiv e _ _ (fun x => ?_)
  simp only [e, Equiv.coe_fn_mk]; ring

theorem g68l_tc2 (V : Matrix (B × C) A ℂ) (W : Matrix (B2 × C2) A2 ℂ) :
    complementaryChannel (tensorDilation V W) = superopTensor (complementaryChannel V) (complementaryChannel W) := by
  funext X; ext ⟨k, k2⟩ ⟨k', k2'⟩
  rw [g68l_cc_entry]
  simp only [superopTensor, Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, g68l_cc_single,
    tensorDilation, Fintype.sum_prod_type, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [← Fintype.sum_prod_type']
  let e : (B × B2 × A × A2 × A × A2) ≃ (A × A2 × A × A2 × B2 × B) :=
    { toFun := fun x => (x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, x.2.1, x.1)
      invFun := fun y => (y.2.2.2.2.2, y.2.2.2.2.1, y.1, y.2.1, y.2.2.1, y.2.2.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine Fintype.sum_equiv e _ _ (fun x => ?_)
  simp only [e, Equiv.coe_fn_mk]; ring

/-- PDF p.4: explicitly regrouped superopTensor dilation and full-map equality. -/
theorem solution [Nonempty A] [Nonempty A2]
    (V : Matrix (B × C) A ℂ) (W : Matrix (B2 × C2) A2 ℂ) :
    receiverChannel (tensorDilation V W) = superopTensor (receiverChannel V) (receiverChannel W) ∧
    complementaryChannel (tensorDilation V W) = superopTensor (complementaryChannel V) (complementaryChannel W) ∧
    CPComplementary (superopTensor (receiverChannel V) (receiverChannel W))
      (superopTensor (complementaryChannel V) (complementaryChannel W)) := by
  exact ⟨g68l_tc1 V W, g68l_tc2 V W, ⟨tensorDilation V W, g68l_tc1 V W, g68l_tc2 V W⟩⟩



end
