-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P41.krausEnsembleCorrespondence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T06:55:40.279731+00:00
-- url     : https://prove2.me/submissions/5bafa315-71b3-460a-b298-55239d0cd0a6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P41

open QAlgorithms

open QAlgorithms.Entanglement (IsCompletelyPositive)

open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)

open QAlgorithms.Papers.Independent.Dependency50.P38 (vectorizeInputFirst)

open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)

open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)

open QAlgorithms.Papers.Independent.Renew46.P43 (IsCountablePOVM classicalKLTerm countableEntropy)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

-- The accepted generic dilation functions fix classical equality on each factor.
-- Match that instance for Fin before forming their product unitary groups.

local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _


namespace X4KEC
open Matrix

lemma pd_apply {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ) (p q : Fin d × Fin d) :
    pureDensity (normalizedOperatorVector A) p q = (d : ℂ)⁻¹ * (A p.2 p.1 * conj (A q.2 q.1)) := by
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
  have hs : ((Real.sqrt d : ℂ)) * (Real.sqrt d : ℂ) = d := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hd]; simp
  simp only [pureDensity, normalizedOperatorVector, vectorizeInputFirst, Matrix.of_apply,
    PiLp.smul_apply, PiLp.toLp_apply, Matrix.vec, smul_eq_mul, map_mul, map_inv₀, Complex.conj_ofReal]
  rw [show ((Real.sqrt d : ℂ))⁻¹ * A p.2 p.1 * ((Real.sqrt d : ℂ)⁻¹ * conj (A q.2 q.1)) =
    ((Real.sqrt d : ℂ) * (Real.sqrt d : ℂ))⁻¹ * (A p.2 p.1 * conj (A q.2 q.1)) by
      rw [mul_inv]; ring, hs]

lemma conj_entry {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (a b i j : Fin d) :
    (A * Matrix.single a b (1:ℂ) * Aᴴ) i j = A i a * conj (A j b) := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

lemma conj_entry' {d : ℕ} (A X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (A * X * Aᴴ) i j = ∑ a, ∑ b, X a b * (A i a * conj (A j b)) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, Finset.sum_mul]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

lemma bij (d : ℕ) [NeZero d] :
    Function.Bijective (fun A : Matrix (Fin d) (Fin d) ℂ => normalizedOperatorVector A) := by
  have hd : (Real.sqrt d : ℂ) ≠ 0 := by
    have : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
    exact_mod_cast this.ne'
  refine ⟨fun A B h => ?_, fun v => ⟨Matrix.of fun b a => (Real.sqrt d : ℂ) * v (a, b), ?_⟩⟩
  · ext i j
    have := congrArg (fun w : EuclideanSpace ℂ (Fin d × Fin d) => w (j, i)) h
    simpa [normalizedOperatorVector, vectorizeInputFirst, Matrix.vec, hd] using this
  · ext ⟨a, b⟩
    simp [normalizedOperatorVector, vectorizeInputFirst, Matrix.vec, Function.uncurry, flip,
      inv_mul_cancel_left₀ hd]

end X4KEC

open X4KEC in
theorem _root_.solution {K : Type*} [Countable K] {d : ℕ} [NeZero d]
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) (hTP : ∀ X, (Phi X).trace = X.trace) :
    Function.Bijective (fun A : K → Matrix (Fin d) (Fin d) ℂ =>
      fun k => normalizedOperatorVector (A k)) ∧
    ∀ A : K → Matrix (Fin d) (Fin d) ℂ,
      CountableOperatorSum Phi A ↔
      HasSum (fun k => pureDensity (normalizedOperatorVector (A k)))
        (((d : ℂ)⁻¹) • choi Phi) := by
  refine ⟨⟨(bij d).1.comp_left, (bij d).2.comp_left⟩, fun A => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine Pi.hasSum.2 fun p => Pi.hasSum.2 fun q => ?_
    simp only [pd_apply, Matrix.smul_apply, smul_eq_mul]
    refine HasSum.mul_left _ ?_
    have h1 := Pi.hasSum.1 (Pi.hasSum.1 (h.2 (Matrix.single p.1 q.1 1)) p.2) q.2
    simpa [conj_entry, choi] using h1
  · have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
    have hc : ∀ p q : Fin d × Fin d,
        HasSum (fun k => A k p.2 p.1 * conj (A k q.2 q.1)) (choi Phi p q) := by
      intro p q
      have h1 := (Pi.hasSum.1 (Pi.hasSum.1 h p) q).mul_left (d : ℂ)
      simp only [pd_apply, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hd,
        one_mul] at h1
      exact h1
    refine ⟨Pi.hasSum.2 fun a' => Pi.hasSum.2 fun a => ?_, fun X => ?_⟩
    · have h2 := hasSum_sum (s := Finset.univ) fun b _ => hc (a, b) (a', b)
      have e1 : ∀ k, ((A k)ᴴ * A k) a' a = ∑ b, A k (a, b).2 (a, b).1 * conj (A k (a', b).2 (a', b).1) := by
        intro k; simp [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm]
      have e2 : ∑ b, choi Phi (a, b) (a', b) = (1 : Matrix (Fin d) (Fin d) ℂ) a' a := by
        have := hTP (Matrix.single a a' 1)
        simp only [Matrix.trace, Matrix.diag] at this
        simp only [choi, this, Matrix.single_apply, Matrix.one_apply]
        rw [Finset.sum_eq_single a (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
        by_cases h : a = a' <;> simp [h, eq_comm]
      simp only [e1]; rw [← e2]; exact h2
    · refine Pi.hasSum.2 fun i => Pi.hasSum.2 fun j => ?_
      simp only [conj_entry']
      have h2 := hasSum_sum (s := Finset.univ) fun a _ => hasSum_sum (s := Finset.univ)
        fun b _ => (hc (a, i) (b, j)).mul_left (X a b)
      have e : Phi X i j = ∑ a, ∑ b, X a b * choi Phi (a, i) (b, j) := by
        conv_lhs => rw [Matrix.matrix_eq_sum_single X]
        simp only [map_sum, Matrix.sum_apply, choi]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [show Matrix.single a b (X a b) = X a b • Matrix.single a b (1:ℂ) by simp, map_smul]
        rfl
      rw [e]; exact h2

end QAlgorithms.Papers.Independent.Support50.P41

end

#print axioms solution
