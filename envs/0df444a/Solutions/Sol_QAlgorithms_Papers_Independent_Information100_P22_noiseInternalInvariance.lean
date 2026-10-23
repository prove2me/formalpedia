-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P22.noiseInternalInvariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:22:39.635296+00:00
-- url     : https://prove2.me/submissions/5f3f3e82-2b4c-4788-907a-ca50a97ce7d1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

def X7NI_sgn (z : F2) : ℂ := if z = 0 then 1 else -1

lemma X7NI_01 (z : F2) : z = 0 ∨ z = 1 := by revert z; decide

lemma X7NI_two (z : F2) : z + z = 0 := by rcases X7NI_01 z with rfl | rfl <;> decide

lemma X7NI_sgn_add (x y : F2) : X7NI_sgn (x + y) = X7NI_sgn x * X7NI_sgn y := by
  rcases X7NI_01 x with rfl | rfl <;> rcases X7NI_01 y with rfl | rfl <;> simp [X7NI_sgn] <;> decide

lemma X7NI_sgn_star (z : F2) : star (X7NI_sgn z) = X7NI_sgn z := by
  unfold X7NI_sgn; split_ifs <;> simp

lemma X7NI_sgn_sq (z : F2) : X7NI_sgn z * star (X7NI_sgn z) = 1 := by
  rw [X7NI_sgn_star]; unfold X7NI_sgn; split_ifs <;> simp

lemma X7NI_ite (q : F2) [Decidable (q = 0)] : (if q = 0 then (1:ℂ) else -1) = X7NI_sgn q := by
  unfold X7NI_sgn; split_ifs <;> rfl

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

section general
variable {m k : ℕ}

lemma X7NI_rhoS (R R' : EuclideanSpace ℂ (Signals m k × Signals m k)) (d : Signals m k → ℂ)
    (hd : ∀ n, d n * star (d n) = 1) (hR : ∀ s n, R' (s, n) = d n * R (s, n)) :
    rhoS R' = rhoS R := by
  ext s s'
  simp only [rhoS, traceRight, pureDensity, Matrix.of_apply, hR]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [map_mul]
  have := hd n
  simp only [RCLike.star_def] at this
  linear_combination (R (s, n) * (starRingEnd ℂ) (R (s', n))) * this

lemma X7NI_encoded (R R' : EuclideanSpace ℂ (Signals m k × Signals m k)) (d : Signals m k → ℂ)
    (hR : ∀ s n, R' (s, n) = d n * R (s, n)) (U : Op (Qubits k × Signals m k))
    (X : Op (Qubits k)) (y y' : Full m k) :
    encoded R' U X y y' = d y.2 * encoded R U X y y' * star (d y'.2) := by
  have he : encoding R' U = Matrix.diagonal (fun y : Full m k => d y.2) * encoding R U := by
    ext y a
    simp only [encoding, hR, Matrix.diagonal_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => by ring)
  unfold encoded
  rw [he, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.diagonal_mul, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.mul_diagonal]
  rw [Pi.star_apply]; ring

lemma X7NI_auth (R R' : EuclideanSpace ℂ (Signals m k × Signals m k)) (d : Signals m k → ℂ)
    (hR : ∀ s n, R' (s, n) = d n * R (s, n)) (U : Op (Qubits k × Signals m k)) (i : Fin m)
    (X : Op (Qubits k)) :
    authorized R' U i X = Matrix.diagonal (fun p : Qubits k × Signals m k => d p.2) *
      authorized R U i X * (Matrix.diagonal (fun p : Qubits k × Signals m k => d p.2))ᴴ := by
  rw [Matrix.diagonal_conjTranspose]
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [authorized, X7NI_encoded R R' d hR, Finset.mul_sum, Finset.sum_mul, Pi.star_apply]

lemma X7NI_joint (R R' : EuclideanSpace ℂ (Signals m k × Signals m k)) (d : Signals m k → ℂ)
    (hd : ∀ n, d n * star (d n) = 1)
    (hR : ∀ s n, R' (s, n) = d n * R (s, n)) (U : Op (Qubits k × Signals m k)) :
    jointSignals R' U = jointSignals R U := by
  funext X
  ext s s'
  simp only [jointSignals, traceLeft, traceRight, Matrix.of_apply, X7NI_encoded R R' d hR]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun n _ => ?_))
  have := hd n
  linear_combination (encoded R U X ((a, s), n) ((a, s'), n)) * this

lemma X7NI_transfer {J : Type*} [Fintype J] [DecidableEq J]
    (A B : Superop (Qubits k) J) (W : Matrix J J ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (h : ∀ X, B X = W * A X * Wᴴ) :
    (∃ D : Superop J (Qubits k), IsChannel D ∧ ∀ X, D (A X) = X) →
      (∃ D : Superop J (Qubits k), IsChannel D ∧ ∀ X, D (B X) = X) := by
  rintro ⟨D, ⟨n, E, hE, hD⟩, hrec⟩
  refine ⟨fun Y => D (Wᴴ * Y * W), ⟨n, fun j => E j * Wᴴ, ?_, ?_⟩, ?_⟩
  · unfold IsKrausFamily at hE ⊢
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    have : ∑ j, (W * (E j)ᴴ) * (E j * Wᴴ) = W * (∑ j, (E j)ᴴ * E j) * Wᴴ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Matrix.mul_assoc]
    rw [this, hE, Matrix.mul_one, hW2]
  · intro ρ
    simp only [hD, krausApply, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Matrix.mul_assoc]
  · intro X
    simp only [h]
    have : Wᴴ * (W * A X * Wᴴ) * W = A X := by
      calc Wᴴ * (W * A X * Wᴴ) * W = (Wᴴ * W) * A X * (Wᴴ * W) := by
            simp only [Matrix.mul_assoc]
        _ = A X := by rw [hW1, Matrix.one_mul, Matrix.mul_one]
    rw [this, hrec]

lemma X7NI_rec (R R' : EuclideanSpace ℂ (Signals m k × Signals m k)) (d : Signals m k → ℂ)
    (hd : ∀ n, d n * star (d n) = 1)
    (hR : ∀ s n, R' (s, n) = d n * R (s, n)) (U : Op (Qubits k × Signals m k)) (i : Fin m) :
    Recoverable R U i → Recoverable R' U i := by
  apply X7NI_transfer _ _ (Matrix.diagonal (fun p : Qubits k × Signals m k => d p.2))
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]; congr 1; funext p
    have := hd p.2; rw [mul_comm] at this; exact this
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]; congr 1; funext p
    exact hd p.2
  · exact X7NI_auth R R' d hR U i

end general

lemma X7NI_graph {m k : ℕ} (G H : CutGraph (Wires m k)) (hS : G.AS = H.AS) (hB : G.B = H.B)
    (s n : Signals m k) :
    graphVector H (s, n) =
      X7NI_sgn (quadratic G.AN n + quadratic H.AN n) * graphVector G (s, n) := by
  simp only [graphVector, WithLp.ofLp_toLp]
  rw [X7NI_ite, X7NI_ite, ← hS, ← hB]
  rw [mul_left_comm, ← X7NI_sgn_add]
  congr 2
  linear_combination (-1 : F2) * X7NI_two (quadratic G.AN n)

end

end QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : QAlgorithms.Papers.Independent.Information100.P22.CutGraph I) :
    Fintype (QAlgorithms.Papers.Independent.Information100.P22.cutKernel G) := Fintype.ofFinite _

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 in
theorem solution (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (P Q : Axis) (hPQ : P ≠ Q) (G H : CutGraph (Wires m k))
    (hS : G.AS = H.AS) (hB : G.B = H.B) :
    rhoS (graphVector G) = rhoS (graphVector H) ∧ cutKernel G = cutKernel H ∧
    vnEntropy (rhoS (graphVector G)) = vnEntropy (rhoS (graphVector H)) ∧
    (((cutKernel G : Set _) ⊆ exceptionalSpace P Q G.AS) ↔
      ((cutKernel H : Set _) ⊆ exceptionalSpace P Q H.AS)) ∧
    (AllRecoverable (graphVector G) (twoPauliEncoder m k P Q) ↔
      AllRecoverable (graphVector H) (twoPauliEncoder m k P Q)) ∧
    jointSignals (graphVector G) (twoPauliEncoder m k P Q) =
      jointSignals (graphVector H) (twoPauliEncoder m k P Q) := by
  set d : Signals m k → ℂ := fun n => X7NI_sgn (quadratic G.AN n + quadratic H.AN n) with hd_def
  have hd : ∀ n, d n * star (d n) = 1 := fun n => X7NI_sgn_sq _
  have hGH : ∀ s n, graphVector H (s, n) = d n * graphVector G (s, n) :=
    fun s n => X7NI_graph G H hS hB s n
  have hHG : ∀ s n, graphVector G (s, n) = d n * graphVector H (s, n) := by
    intro s n
    rw [hGH, ← mul_assoc]
    have := hd n
    rw [X7NI_sgn_star] at this
    rw [this, one_mul]
  have h1 : rhoS (graphVector G) = rhoS (graphVector H) :=
    (X7NI_rhoS (graphVector G) (graphVector H) d hd hGH).symm
  have h2 : cutKernel G = cutKernel H := by
    unfold cutKernel; rw [hB]
  refine ⟨h1, h2, by rw [h1], by rw [h2, hS], ?_, ?_⟩
  · constructor
    · intro h i; exact X7NI_rec _ _ d hd hGH _ i (h i)
    · intro h i; exact X7NI_rec _ _ d hd hHG _ i (h i)
  · exact (X7NI_joint (graphVector G) (graphVector H) d hd hGH _).symm

end
