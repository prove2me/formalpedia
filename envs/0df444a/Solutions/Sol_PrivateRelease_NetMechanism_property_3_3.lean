-- Prove2me | solution 1 for PrivateRelease.NetMechanism.property_3_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T10:22:07.154041+00:00
-- url     : https://prove2.me/submissions/5ff7e085-9996-4438-8fd8-db76e6723cd6

import Mathlib
import Definitions.Def_PrivateRelease_NetMechanism_ExpMech

open MeasureTheory PrivateRelease.NetMechanism
namespace ExponentialPrivacy

lemma sensitivity {X O : Type} [Fintype X] {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (z z' : Fin n → X)
    (hz : PrivLearn.Generic.Neighbors z z') (r : O) (hr : r ∈ R) :
    |q z r - q z' r| ≤ scoreSens R q := by
  classical
  have h1 : |q z r - q z' r| ≤ GS (fun t => q t r) := by
    unfold GS
    exact le_ciSup (f := fun t : {t : (Fin n → X) × (Fin n → X) // PrivLearn.Generic.Neighbors t.1 t.2} => |q t.1.1 r - q t.1.2 r|) (Set.finite_range _).bddAbove ⟨(z,z'),hz⟩
  have h2 : GS (fun t => q t r) ≤ scoreSens R q := by
    unfold scoreSens
    exact le_ciSup (f := fun t : R => GS (fun z => q z t.1)) (Set.finite_range _).bddAbove ⟨r,hr⟩
  exact h1.trans h2

lemma neighbors_symm {X : Type} {n : ℕ} {z z' : Fin n → X}
    (h : PrivLearn.Generic.Neighbors z z') : PrivLearn.Generic.Neighbors z' z := by
  obtain ⟨i,hi,hrest⟩ := h
  exact ⟨i,Ne.symm hi,fun j hj => (hrest j hj).symm⟩

noncomputable def weight {X O : Type} {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε : ℝ) (z : Fin n → X) (r : O) : ℝ :=
  Real.exp (ε * q z r / (2 * scoreSens R q))

noncomputable def normConst {X O : Type} {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε : ℝ) (z : Fin n → X) : ℝ :=
  ∑ r ∈ R, weight R q ε z r

lemma norm_pos {X O : Type} {n : ℕ} (R : Finset O) (q : (Fin n → X) → O → ℝ)
    (ε : ℝ) (z : Fin n → X) (hR : R.Nonempty) : 0 < normConst R q ε z := by
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) hR

lemma weight_bound {X O : Type} [Fintype X] {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε : ℝ) (hq : 0 < scoreSens R q) (hε : 0 < ε)
    (z z' : Fin n → X) (hz : PrivLearn.Generic.Neighbors z z') (r : O) (hr : r ∈ R) :
    weight R q ε z r ≤ Real.exp (ε/2) * weight R q ε z' r := by
  have hdiff := (le_abs_self (q z r-q z' r)).trans (sensitivity R q z z' hz r hr)
  have hscaled := mul_le_mul_of_nonneg_left hdiff hε.le
  have he : ε*q z r/(2*scoreSens R q) ≤ ε/2+ε*q z' r/(2*scoreSens R q) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*scoreSens R q)).mpr
    have hcancel : (ε/2+ε*q z' r/(2*scoreSens R q))*(2*scoreSens R q) =
        ε*scoreSens R q+ε*q z' r := by field_simp <;> ring
    rw [hcancel]; linarith
  simpa only [weight, Real.exp_add] using Real.exp_le_exp.mpr he

lemma probability_bound {X O : Type} [Fintype X] {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε : ℝ) (hR : R.Nonempty)
    (hq : 0 < scoreSens R q) (hε : 0 < ε)
    (z z' : Fin n → X) (hz : PrivLearn.Generic.Neighbors z z') (r : O) (hr : r ∈ R) :
    weight R q ε z r / normConst R q ε z ≤
      Real.exp ε * (weight R q ε z' r / normConst R q ε z') := by
  have hZ := norm_pos R q ε z hR
  have hZ' := norm_pos R q ε z' hR
  have hw := weight_bound R q ε hq hε z z' hz r hr
  have hn : normConst R q ε z' ≤ Real.exp (ε/2) * normConst R q ε z := by
    unfold normConst
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j hj => weight_bound R q ε hq hε z' z (neighbors_symm hz) j hj)
  have hmul1 := mul_le_mul_of_nonneg_right hw hZ'.le
  have hmul2 := mul_le_mul_of_nonneg_left hn
    (show 0 ≤ Real.exp (ε/2) * weight R q ε z' r by unfold weight; positivity)
  have he : Real.exp (ε/2)*Real.exp (ε/2)=Real.exp ε := by
    rw [← Real.exp_add]; congr 1; ring
  have hp : weight R q ε z r * normConst R q ε z' ≤
      (Real.exp ε * weight R q ε z' r) * normConst R q ε z := by
    calc _ ≤ (Real.exp (ε/2) * weight R q ε z' r) * normConst R q ε z' := hmul1
      _ ≤ (Real.exp (ε/2) * weight R q ε z' r) *
          (Real.exp (ε/2) * normConst R q ε z) := hmul2
      _ = _ := by rw [show (Real.exp (ε/2) * weight R q ε z' r) *
          (Real.exp (ε/2) * normConst R q ε z) =
          (Real.exp (ε/2)*Real.exp (ε/2))*weight R q ε z' r*normConst R q ε z by ring,he]
  rw [← mul_div_assoc]
  exact (div_le_div_iff₀ hZ hZ').mpr hp

lemma normalized {X O : Type} [MeasurableSpace O] {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε : ℝ) (hR : R.Nonempty) (z : Fin n → X) :
    IsProbabilityMeasure (expMech R q ε z) := by
  classical
  have hZ := norm_pos R q ε z hR
  have hn : ∑ r ∈ R, weight R q ε z r / normConst R q ε z = 1 := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hZ)
  constructor
  simp only [expMech, Measure.finsetSum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  change (∑ r ∈ R, ENNReal.ofReal (weight R q ε z r / normConst R q ε z)) = 1
  rw [← ENNReal.ofReal_sum_of_nonneg (s := R) (f := fun r => weight R q ε z r / normConst R q ε z) (fun r _ => by unfold weight; positivity),hn]
  exact ENNReal.ofReal_one

end ExponentialPrivacy

theorem exponential_mechanism {X O : Type} [Fintype X] [MeasurableSpace O] {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε : ℝ) (hR : R.Nonempty) (hq : 0 < scoreSens R q)
    (hε : 0 < ε) :
    PrivLearn.Generic.IsDP (expMech R q ε) ε ∧
      ∀ z : Fin n → X, IsProbabilityMeasure (expMech R q ε z) := by
  classical
  constructor
  · intro z z' hz S hS
    unfold expMech
    rw [Measure.finsetSum_apply,Measure.finsetSum_apply,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    rw [Measure.smul_apply,Measure.smul_apply]
    change ENNReal.ofReal (ExponentialPrivacy.weight R q ε z r / ExponentialPrivacy.normConst R q ε z) *
      Measure.dirac r S ≤ ENNReal.ofReal (Real.exp ε) *
      (ENNReal.ofReal (ExponentialPrivacy.weight R q ε z' r / ExponentialPrivacy.normConst R q ε z') * Measure.dirac r S)
    rw [← mul_assoc,← ENNReal.ofReal_mul (Real.exp_pos ε).le]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
      (ExponentialPrivacy.probability_bound R q ε hR hq hε z z' hz r hr)) zero_le
  · exact ExponentialPrivacy.normalized R q ε hR

#print axioms exponential_mechanism

open PrivateRelease.NetMechanism

open MeasureTheory

/-- Property 3.3 (p. 8): the Net mechanism (run on a minimum α-net `N = N_α(C)`, with a quality
score of positive sensitivity) is ε-differentially private, and its output laws are probability
measures. -/
theorem solution {X : Type} [Fintype X] {n : ℕ} (QC : Set (Multiset X → ℝ)) (ε α : ℝ)
    (N : Finset (Database X)) (hN : IsMinNet QC α N) (hsens : 0 < netSens n QC N)
    (hε : 0 < ε) :
    PrivLearn.Generic.IsDP (netMech (n := n) QC ε N) ε ∧
      ∀ z : Fin n → X, IsProbabilityMeasure (netMech QC ε N z)  := by
  have hnonempty : N.Nonempty := by
    by_contra hh
    have he : N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
    subst N
    simpa [netSens,scoreSens] using hsens
  exact exponential_mechanism N (netScore QC) ε hnonempty hsens hε



#print axioms solution
