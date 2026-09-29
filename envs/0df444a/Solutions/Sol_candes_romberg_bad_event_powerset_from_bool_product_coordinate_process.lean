-- Prove2me | solution 1 for candes_romberg_bad_event_powerset_from_bool_product_coordinate_process
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-30T02:55:44.242593+00:00
-- url     : https://prove2.me/submissions/ea3bc1de-a98f-427b-9bdc-f579e4fc657d

import Definitions.Def_matrix_completion_bernoulli
import Definitions.Def_matrix_completion_bernoulli_measure
import Theorems.Thm_bernoulli_powerset_event_prob_eq_product_measure
import Theorems.Thm_bernoulli_powerset_expectation_eq_product_measure_integral
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
Formal bridge from the Boolean product-measure Candes--Romberg bad-event tail
to the powerset `bernoulliEventProb` formulation used by the C21 leaf.
-/

namespace MatrixCompletion

open MeasureTheory
open scoped Classical BigOperators

private noncomputable def boolProcess {n1 n2 : ℕ} {ι : Type}
    (p : ℝ) (coeff : ι → Fin n1 → Fin n2 → ℝ)
    (a : ι) (ω : (Fin n1 × Fin n2) → Bool) : ℝ :=
  ∑ i : Fin n1, ∑ j : Fin n2,
    ((cond (ω (i, j)) (1 : ℝ) 0 - p) * coeff a i j)

private noncomputable def boolZ {n1 n2 : ℕ} {ι : Type} [Fintype ι] [Nonempty ι]
    (p : ℝ) (coeff : ι → Fin n1 → Fin n2 → ℝ)
    (ω : (Fin n1 × Fin n2) → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : ι => boolProcess p coeff a ω)

private noncomputable def boolZbar {n1 n2 : ℕ} {ι : Type} [Fintype ι] [Nonempty ι]
    (p : ℝ) (coeff : ι → Fin n1 → Fin n2 → ℝ)
    (ω : (Fin n1 × Fin n2) → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : ι => |boolProcess p coeff a ω|)

private noncomputable def powersetProcess {n1 n2 : ℕ} {ι : Type}
    (p : ℝ) (coeff : ι → Fin n1 → Fin n2 → ℝ)
    (a : ι) (Ω : Finset (Fin n1 × Fin n2)) : ℝ :=
  ∑ i : Fin n1, ∑ j : Fin n2,
    (((if (i, j) ∈ Ω then (1 : ℝ) else 0) - p) * coeff a i j)

private noncomputable def powersetZ {n1 n2 : ℕ} {ι : Type}
    [Fintype ι] [Nonempty ι]
    (p : ℝ) (coeff : ι → Fin n1 → Fin n2 → ℝ)
    (Ω : Finset (Fin n1 × Fin n2)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : ι => powersetProcess p coeff a Ω)

private noncomputable def powersetZbar {n1 n2 : ℕ} {ι : Type}
    [Fintype ι] [Nonempty ι]
    (p : ℝ) (coeff : ι → Fin n1 → Fin n2 → ℝ)
    (Ω : Finset (Fin n1 × Fin n2)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : ι => |powersetProcess p coeff a Ω|)

private noncomputable def sampleRatioNN (n1 n2 m : ℕ)
    (hp0 : 0 ≤ ((m : ℝ) / ((n1 : ℝ) * (n2 : ℝ)))) : NNReal :=
  ⟨((m : ℝ) / ((n1 : ℝ) * (n2 : ℝ))), hp0⟩

private lemma sampleRatioNN_coe (n1 n2 m : ℕ)
    (hp0 : 0 ≤ ((m : ℝ) / ((n1 : ℝ) * (n2 : ℝ)))) :
    (sampleRatioNN n1 n2 m hp0 : ℝ) =
      (m : ℝ) / ((n1 : ℝ) * (n2 : ℝ)) :=
  rfl

private lemma sampleRatioNN_le_one (n1 n2 m : ℕ)
    (hn1 : 0 < n1) (hn2 : 0 < n2) (hm : m ≤ n1 * n2) :
    sampleRatioNN n1 n2 m
        ((sample_ratio_between_zero_and_one n1 n2 m hn1 hn2 hm).1) ≤ 1 := by
  rw [← NNReal.coe_le_coe]
  exact (sample_ratio_between_zero_and_one n1 n2 m hn1 hn2 hm).2

private lemma varianceHyp_sampleRatioNN {n1 n2 m : ℕ} {ι : Type}
    (coeff : ι → Fin n1 → Fin n2 → ℝ) (sigmaSq : ℝ)
    (hp0 : 0 ≤ ((m : ℝ) / ((n1 : ℝ) * (n2 : ℝ)))) :
    (∀ a : ι,
      ∑ i : Fin n1, ∑ j : Fin n2,
        ((m : ℝ) / ((n1 : ℝ) * (n2 : ℝ))) *
          (1 - ((m : ℝ) / ((n1 : ℝ) * (n2 : ℝ)))) * (coeff a i j) ^ 2 ≤
            sigmaSq) →
    ∀ a : ι,
      ∑ i : Fin n1, ∑ j : Fin n2,
        (sampleRatioNN n1 n2 m hp0 : ℝ) *
          (1 - (sampleRatioNN n1 n2 m hp0 : ℝ)) *
            (coeff a i j) ^ 2 ≤ sigmaSq := by
  intro hvar a
  exact hvar a

private lemma powersetProcess_indicatorToFinset {n1 n2 : ℕ} {ι : Type}
    (p : ℝ) (coeff : ι → Fin n1 → Fin n2 → ℝ)
    (a : ι) (ω : (Fin n1 × Fin n2) → Bool) :
    powersetProcess p coeff a (indicatorToFinset ω) =
      boolProcess p coeff a ω := by
  classical
  unfold powersetProcess boolProcess indicatorToFinset
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  cases hω : ω (i, j) <;> simp [hω]

private lemma powersetZ_indicatorToFinset {n1 n2 : ℕ} {ι : Type}
    [Fintype ι] [Nonempty ι]
    (p : ℝ) (coeff : ι → Fin n1 → Fin n2 → ℝ)
    (ω : (Fin n1 × Fin n2) → Bool) :
    powersetZ p coeff (indicatorToFinset ω) =
      boolZ p coeff ω := by
  classical
  unfold powersetZ boolZ
  congr with a
  exact powersetProcess_indicatorToFinset p coeff a ω

private lemma powersetZbar_indicatorToFinset {n1 n2 : ℕ} {ι : Type}
    [Fintype ι] [Nonempty ι]
    (p : ℝ) (coeff : ι → Fin n1 → Fin n2 → ℝ)
    (ω : (Fin n1 × Fin n2) → Bool) :
    powersetZbar p coeff (indicatorToFinset ω) =
      boolZbar p coeff ω := by
  classical
  unfold powersetZbar boolZbar
  congr with a
  exact congrArg abs (powersetProcess_indicatorToFinset p coeff a ω)

private def productStatement : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ (n1 n2 : ℕ) (p : NNReal) (hp : p ≤ 1)
      (ι : Type) [Fintype ι] [Nonempty ι]
      (coeff : ι → Fin n1 → Fin n2 → ℝ) (B sigmaSq t : ℝ),
      0 < B → 0 ≤ sigmaSq → 0 ≤ t →
      (∀ a : ι, ∀ i : Fin n1, ∀ j : Fin n2, |coeff a i j| ≤ B) →
      (∀ a : ι,
        ∑ i : Fin n1, ∑ j : Fin n2,
          (p : ℝ) * (1 - (p : ℝ)) * (coeff a i j) ^ 2 ≤ sigmaSq) →
      (bernMeasure (n1 := n1) (n2 := n2) p hp).real
          {ω | ¬ |boolZ (p : ℝ) coeff ω -
                (∫ ω, boolZ (p : ℝ) coeff ω
                  ∂(bernMeasure (n1 := n1) (n2 := n2) p hp))| ≤ t} ≤
        3 * Real.exp
          (-(t / (K * B)) *
            Real.log
              (1 + (B * t) /
                (sigmaSq + B *
                  (∫ ω, boolZbar (p : ℝ) coeff ω
                    ∂(bernMeasure (n1 := n1) (n2 := n2) p hp)))))

private def powersetConclusion : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ (n1 n2 m : ℕ) (ι : Type) [Fintype ι] [Nonempty ι]
      (coeff : ι → Fin n1 → Fin n2 → ℝ) (B sigmaSq t : ℝ),
      0 < n1 → 0 < n2 → m ≤ n1 * n2 →
      0 < B → 0 ≤ sigmaSq → 0 ≤ t →
      (∀ a : ι, ∀ i : Fin n1, ∀ j : Fin n2, |coeff a i j| ≤ B) →
      (∀ a : ι,
        ∑ i : Fin n1, ∑ j : Fin n2,
          ((m : ℝ) / ((n1 : ℝ) * (n2 : ℝ))) *
            (1 - ((m : ℝ) / ((n1 : ℝ) * (n2 : ℝ)))) *
              (coeff a i j) ^ 2 ≤ sigmaSq) →
      let p : ℝ := (m : ℝ) / ((n1 : ℝ) * (n2 : ℝ))
      bernoulliEventProb p
          (fun Ω =>
            ¬ |powersetZ p coeff Ω -
                  bernoulliExpectation p (powersetZ p coeff)| ≤ t) ≤
        3 * Real.exp
          (-(t / (K * B)) *
            Real.log
              (1 + (B * t) /
                (sigmaSq + B * bernoulliExpectation p (powersetZbar p coeff))))

private theorem powersetBridgeFromProduct (hProduct : productStatement) :
    powersetConclusion := by
  rcases hProduct with ⟨K, hK, htail⟩
  refine ⟨K, hK, ?_⟩
  intro n1 n2 m ι _ _ coeff B sigmaSq t hn1 hn2 hm hB hsig ht hcoeff hvar
  let hpBounds := sample_ratio_between_zero_and_one n1 n2 m hn1 hn2 hm
  let pNN : NNReal := sampleRatioNN n1 n2 m hpBounds.1
  have hpNN : pNN ≤ 1 := sampleRatioNN_le_one n1 n2 m hn1 hn2 hm
  have hvarNN :
      ∀ a : ι,
        ∑ i : Fin n1, ∑ j : Fin n2,
          (pNN : ℝ) * (1 - (pNN : ℝ)) * (coeff a i j) ^ 2 ≤ sigmaSq := by
    simpa [pNN] using
      varianceHyp_sampleRatioNN (n1 := n1) (n2 := n2) (m := m)
        coeff sigmaSq hpBounds.1 hvar
  have htailNN :=
    htail n1 n2 pNN hpNN ι coeff B sigmaSq t hB hsig ht hcoeff hvarNN
  have hExpZ :
      bernoulliExpectation (pNN : ℝ) (powersetZ (pNN : ℝ) coeff) =
        ∫ ω, boolZ (pNN : ℝ) coeff ω
          ∂(bernMeasure (n1 := n1) (n2 := n2) pNN hpNN) := by
    rw [bernoulli_powerset_expectation_eq_product_measure_integral pNN hpNN
      (powersetZ (pNN : ℝ) coeff)]
    simp [powersetZ_indicatorToFinset]
  have hExpZbar :
      bernoulliExpectation (pNN : ℝ) (powersetZbar (pNN : ℝ) coeff) =
        ∫ ω, boolZbar (pNN : ℝ) coeff ω
          ∂(bernMeasure (n1 := n1) (n2 := n2) pNN hpNN) := by
    rw [bernoulli_powerset_expectation_eq_product_measure_integral pNN hpNN
      (powersetZbar (pNN : ℝ) coeff)]
    simp [powersetZbar_indicatorToFinset]
  have hProb :
      bernoulliEventProb (pNN : ℝ)
          (fun Ω =>
            ¬ |powersetZ (pNN : ℝ) coeff Ω -
                  bernoulliExpectation (pNN : ℝ)
                    (powersetZ (pNN : ℝ) coeff)| ≤ t) =
        (bernMeasure (n1 := n1) (n2 := n2) pNN hpNN).real
          {ω | ¬ |boolZ (pNN : ℝ) coeff ω -
                (∫ ω, boolZ (pNN : ℝ) coeff ω
                  ∂(bernMeasure (n1 := n1) (n2 := n2) pNN hpNN))| ≤ t} := by
    rw [bernoulli_powerset_event_prob_eq_product_measure pNN hpNN
      (fun Ω =>
        ¬ |powersetZ (pNN : ℝ) coeff Ω -
              bernoulliExpectation (pNN : ℝ)
                (powersetZ (pNN : ℝ) coeff)| ≤ t)]
    rw [hExpZ]
    simp [powersetZ_indicatorToFinset]
  dsimp [powersetConclusion]
  rw [← sampleRatioNN_coe n1 n2 m hpBounds.1]
  rw [hProb, hExpZbar]
  exact htailNN

end MatrixCompletion

open MatrixCompletion
open MeasureTheory
open scoped Classical BigOperators

theorem solution
    (hProduct :
      ∃ K : ℝ, 0 < K ∧
        ∀ (n1 n2 : ℕ) (p : NNReal) (hp : p ≤ 1)
          (ι : Type) [Fintype ι] [Nonempty ι]
          (coeff : ι → Fin n1 → Fin n2 → ℝ) (B sigmaSq t : ℝ),
          0 < B → 0 ≤ sigmaSq → 0 ≤ t →
          (∀ a : ι, ∀ i : Fin n1, ∀ j : Fin n2, |coeff a i j| ≤ B) →
          (∀ a : ι,
            ∑ i : Fin n1, ∑ j : Fin n2,
              (p : ℝ) * (1 - (p : ℝ)) * (coeff a i j) ^ 2 ≤ sigmaSq) →
          let boolProcess : ι → ((Fin n1 × Fin n2) → Bool) → ℝ :=
            fun a ω =>
              ∑ i : Fin n1, ∑ j : Fin n2,
                ((cond (ω (i, j)) (1 : ℝ) 0 - (p : ℝ)) * coeff a i j)
          let boolZ : ((Fin n1 × Fin n2) → Bool) → ℝ :=
            fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => boolProcess a ω)
          let boolZbar : ((Fin n1 × Fin n2) → Bool) → ℝ :=
            fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |boolProcess a ω|)
          (bernMeasure (n1 := n1) (n2 := n2) p hp).real
              {ω | ¬ |boolZ ω -
                    (∫ ω, boolZ ω ∂(bernMeasure (n1 := n1) (n2 := n2) p hp))| ≤ t} ≤
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq + B *
                      (∫ ω, boolZbar ω ∂(bernMeasure (n1 := n1) (n2 := n2) p hp)))))) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n1 n2 m : ℕ) (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → Fin n1 → Fin n2 → ℝ) (B sigmaSq t : ℝ),
        0 < n1 → 0 < n2 → m ≤ n1 * n2 →
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∀ i : Fin n1, ∀ j : Fin n2, |coeff a i j| ≤ B) →
        (∀ a : ι,
          ∑ i : Fin n1, ∑ j : Fin n2,
            ((m : ℝ) / ((n1 : ℝ) * (n2 : ℝ))) *
              (1 - ((m : ℝ) / ((n1 : ℝ) * (n2 : ℝ)))) *
                (coeff a i j) ^ 2 ≤ sigmaSq) →
        let p : ℝ := (m : ℝ) / ((n1 : ℝ) * (n2 : ℝ))
        let process : ι → Finset (Fin n1 × Fin n2) → ℝ :=
          fun a Ω =>
            ∑ i : Fin n1, ∑ j : Fin n2,
              (((if (i, j) ∈ Ω then (1 : ℝ) else 0) - p) * coeff a i j)
        let Z : Finset (Fin n1 × Fin n2) → ℝ :=
          fun Ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => process a Ω)
        let Zbar : Finset (Fin n1 × Fin n2) → ℝ :=
          fun Ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |process a Ω|)
        bernoulliEventProb p
            (fun Ω => ¬ |Z Ω - bernoulliExpectation p Z| ≤ t) ≤
          3 * Real.exp
            (-(t / (K * B)) *
              Real.log
                (1 + (B * t) /
                  (sigmaSq + B * bernoulliExpectation p Zbar))) := by
  change MatrixCompletion.productStatement at hProduct
  change MatrixCompletion.powersetConclusion
  exact MatrixCompletion.powersetBridgeFromProduct hProduct
