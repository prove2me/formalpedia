-- Prove2me | solution 1 for PrivPACLower.ICP.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-16T07:19:56.279963+00:00
-- url     : https://prove2.me/submissions/d9513171-e3a8-4370-a616-82063619c7aa

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Reductions

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

open PrivateUniformGen.Characterization

namespace PrivateGroup

private noncomputable def groupGeomSum (ε : ℝ) (r : ℕ) : ℝ :=
  ∑ s ∈ Finset.range r, Real.exp ((s : ℝ) * ε)

private lemma groupGeomSum_step (ε : ℝ) (r : ℕ) :
    1 + Real.exp ε * groupGeomSum ε r = groupGeomSum ε (r + 1) := by
  induction r with
  | zero => simp [groupGeomSum]
  | succ r ih =>
      simp only [groupGeomSum, Finset.sum_range_succ] at ih ⊢
      have hpow : Real.exp ε * Real.exp ((r : ℝ) * ε) =
          Real.exp (((r : ℝ) + 1) * ε) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        1 + Real.exp ε *
            (∑ s ∈ Finset.range r, Real.exp ((s : ℝ) * ε) + Real.exp ((r : ℝ) * ε)) =
            (1 + Real.exp ε * ∑ s ∈ Finset.range r, Real.exp ((s : ℝ) * ε)) +
              Real.exp ε * Real.exp ((r : ℝ) * ε) := by ring
        _ = (∑ s ∈ Finset.range r, Real.exp ((s : ℝ) * ε) + Real.exp ((r : ℝ) * ε)) +
              Real.exp (((r : ℝ) + 1) * ε) := by rw [ih, hpow]
        _ = ∑ s ∈ Finset.range r, Real.exp ((s : ℝ) * ε) + Real.exp ((r : ℝ) * ε) +
              Real.exp (((r + 1 : ℕ) : ℝ) * ε) := by
                simpa only [Nat.cast_add, Nat.cast_one]

private lemma groupUpdateBound {Z O : Type*} [MeasurableSpace O] {n : ℕ}
    (M : Mechanism Z O n) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ)
    (hM : IsDP M ε δ) (S : Fin n → Z) (i : Fin n) (v : Z)
    (E : Set O) (hE : MeasurableSet E) :
    (M S : Measure O).real E ≤
      Real.exp ε * (M (Function.update S i v) : Measure O).real E + δ := by
  by_cases hi : S i = v
  · have hu : Function.update S i v = S := by rw [← hi, Function.update_eq_self]
    rw [hu]
    have hexp : 1 ≤ Real.exp ε := Real.one_le_exp_iff.mpr hε.le
    have hp : 0 ≤ (M S : Measure O).real E := ENNReal.toReal_nonneg
    calc
      (M S : Measure O).real E = 1 * (M S : Measure O).real E := by ring
      _ ≤ Real.exp ε * (M S : Measure O).real E := mul_le_mul_of_nonneg_right hexp hp
      _ ≤ Real.exp ε * (M S : Measure O).real E + δ := le_add_of_nonneg_right hδ
  · have hN : Neighbors S (Function.update S i v) := by
      refine ⟨i, ?_, ?_⟩
      · simpa using hi
      · intro j hj
        simp [Function.update_of_ne hj]
    exact hM S (Function.update S i v) hN E hE

private lemma groupFinsetBound {Z O : Type*} [MeasurableSpace O] {n : ℕ}
    (M : Mechanism Z O n) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ)
    (hM : IsDP M ε δ) (s : Finset (Fin n)) (S S' : Fin n → Z)
    (hs : ∀ i ∉ s, S i = S' i) (E : Set O) (hE : MeasurableSet E) :
    (M S : Measure O).real E ≤
      Real.exp ((s.card : ℝ) * ε) * (M S' : Measure O).real E +
        δ * groupGeomSum ε s.card := by
  classical
  induction s using Finset.induction_on generalizing S with
  | empty =>
      have heq : S = S' := funext fun i => hs i (by simp)
      subst S'
      simp [groupGeomSum]
  | @insert i s hi ih =>
      have hs' : ∀ j ∉ s, Function.update S i (S' i) j = S' j := by
        intro j hj
        by_cases hji : j = i
        · subst j
          simp
        · rw [Function.update_of_ne hji]
          exact hs j (by simp [hj, hji])
      calc
        (M S : Measure O).real E ≤
            Real.exp ε * (M (Function.update S i (S' i)) : Measure O).real E + δ :=
          groupUpdateBound M ε δ hε hδ hM S i (S' i) E hE
        _ ≤ Real.exp ε *
            (Real.exp ((s.card : ℝ) * ε) * (M S' : Measure O).real E +
              δ * groupGeomSum ε s.card) + δ := by
          gcongr
          exact ih (Function.update S i (S' i)) hs'
        _ = Real.exp ((s.card : ℝ) * ε + ε) * (M S' : Measure O).real E +
              δ * groupGeomSum ε (s.card + 1) := by
          have hgeom : Real.exp ε * groupGeomSum ε s.card + 1 =
              groupGeomSum ε (s.card + 1) := by
            calc
              Real.exp ε * groupGeomSum ε s.card + 1 =
                  1 + Real.exp ε * groupGeomSum ε s.card := by ring
              _ = groupGeomSum ε (s.card + 1) := groupGeomSum_step ε s.card
          have hpow : Real.exp ε * Real.exp ((s.card : ℝ) * ε) =
              Real.exp ((s.card : ℝ) * ε + ε) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc
            Real.exp ε *
                (Real.exp ((s.card : ℝ) * ε) * (M S' : Measure O).real E +
                  δ * groupGeomSum ε s.card) + δ =
                (Real.exp ε * Real.exp ((s.card : ℝ) * ε)) *
                    (M S' : Measure O).real E +
                  δ * (Real.exp ε * groupGeomSum ε s.card + 1) := by ring
            _ = Real.exp ((s.card : ℝ) * ε + ε) * (M S' : Measure O).real E +
                  δ * groupGeomSum ε (s.card + 1) := by rw [hpow, hgeom]
        _ = Real.exp (((insert i s).card : ℝ) * ε) *
              (M S' : Measure O).real E + δ * groupGeomSum ε (insert i s).card := by
          rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
          congr 2 <;> ring

private lemma groupHammingBound {Z O : Type*} [MeasurableSpace O] {n : ℕ}
    (M : Mechanism Z O n) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ)
    (hM : IsDP M ε δ) (S S' : Fin n → Z) (r : ℕ)
    (hr : hamming S S' = r) (E : Set O) (hE : MeasurableSet E) :
    (M S : Measure O).real E ≤
      Real.exp ((r : ℝ) * ε) * (M S' : Measure O).real E +
        δ * groupGeomSum ε r := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i => S i ≠ S' i
  have hs : ∀ i ∉ s, S i = S' i := by simp [s]
  have hc : s.card = r := by
    have hcard : s.card = hamming S S' := by simp [s, hamming]
    exact hcard.trans hr
  simpa [hc] using groupFinsetBound M ε δ hε hδ hM s S S' hs E hE

private lemma groupGeomBound {ε : ℝ} (hε : 0 < ε) (d r : ℕ) (hd : d ≤ r) :
    groupGeomSum ε d ≤ (r : ℝ) * Real.exp (((r : ℝ) - 1) * ε) := by
  by_cases hr : r = 0
  · subst r
    have hd0 : d = 0 := Nat.eq_zero_of_le_zero hd
    subst d
    simp [groupGeomSum]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hterm : ∀ i ∈ Finset.range d,
        Real.exp ((i : ℝ) * ε) ≤ Real.exp (((r : ℝ) - 1) * ε) := by
      intro i hi
      have hlt : i < r := (Finset.mem_range.mp hi).trans_le hd
      have hsucc : i + 1 ≤ r := Nat.succ_le_of_lt hlt
      have hreal_succ : (i : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hsucc
      have hreal : (i : ℝ) ≤ (r : ℝ) - 1 := by linarith
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hreal hε.le)
    calc
      groupGeomSum ε d ≤
          ∑ i ∈ Finset.range d, Real.exp (((r : ℝ) - 1) * ε) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hterm i hi
      _ = (d : ℝ) * Real.exp (((r : ℝ) - 1) * ε) := by simp
      _ ≤ (r : ℝ) * Real.exp (((r : ℝ) - 1) * ε) := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd) (Real.exp_nonneg _)

private lemma groupHammingLooseBound {Z O : Type*} [MeasurableSpace O] {n : ℕ}
    (M : Mechanism Z O n) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ)
    (hM : IsDP M ε δ) (S S' : Fin n → Z) (r : ℕ)
    (hr : hamming S S' ≤ r) (E : Set O) (hE : MeasurableSet E) :
    (M S : Measure O).real E ≤
      Real.exp ((r : ℝ) * ε) * (M S' : Measure O).real E +
        (r : ℝ) * Real.exp (((r : ℝ) - 1) * ε) * δ := by
  let d := hamming S S'
  have hd : d ≤ r := hr
  have hExact := groupHammingBound M ε δ hε hδ hM S S' d rfl E hE
  have hExp : Real.exp ((d : ℝ) * ε) ≤ Real.exp ((r : ℝ) * ε) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd) hε.le
  have hGeom := groupGeomBound hε d r hd
  have hProb : 0 ≤ (M S' : Measure O).real E := ENNReal.toReal_nonneg
  calc
    (M S : Measure O).real E ≤
        Real.exp ((d : ℝ) * ε) * (M S' : Measure O).real E +
          δ * groupGeomSum ε d := hExact
    _ ≤ Real.exp ((r : ℝ) * ε) * (M S' : Measure O).real E +
          δ * ((r : ℝ) * Real.exp (((r : ℝ) - 1) * ε)) := by
          gcongr
    _ = Real.exp ((r : ℝ) * ε) * (M S' : Measure O).real E +
          (r : ℝ) * Real.exp (((r : ℝ) - 1) * ε) * δ := by ring

end PrivateGroup

open PrivateGroup

theorem solution {Z O : Type*} [MeasurableSpace O] {n : ℕ}
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ ∧ δ < 1)
    (M : Mechanism Z O n) (hM : IsDP M ε δ) :
    (∀ (S S' : Fin n → Z) (r : ℕ), hamming S S' = r →
      ∀ E : Set O, MeasurableSet E →
        (M S : Measure O).real E ≤ Real.exp ((r : ℝ)*ε) * (M S' : Measure O).real E +
          δ * ∑ s ∈ Finset.range r, Real.exp ((s : ℝ)*ε)) ∧
    (∀ (r : ℕ) (S S' : Fin n → Z), hamming S S' ≤ r →
      ∀ E : Set O, MeasurableSet E →
        (M S : Measure O).real E ≤ Real.exp ((r : ℝ)*ε) * (M S' : Measure O).real E +
          (r : ℝ) * Real.exp (((r : ℝ)-1)*ε) * δ) := by
  constructor
  · intro S S' r hr E hE
    simpa [groupGeomSum, mul_comm] using
      groupHammingBound M ε δ hε hδ.1 hM S S' r hr E hE
  · intro r S S' hr E hE
    exact groupHammingLooseBound M ε δ hε hδ.1 hM S S' r hr E hE

end PrivPACLower.ICP



open PrivateUniformGen.Characterization
open PrivPACLower.ICP

theorem solution {Z O : Type*} [MeasurableSpace O] {n : ℕ}
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ ∧ δ < 1)
    (M : Mechanism Z O n) (hM : IsDP M ε δ) :
    (∀ (S S' : Fin n → Z) (r : ℕ), hamming S S' = r →
      ∀ E : Set O, MeasurableSet E →
        (M S : Measure O).real E ≤ Real.exp ((r : ℝ)*ε) * (M S' : Measure O).real E +
          δ * ∑ s ∈ Finset.range r, Real.exp ((s : ℝ)*ε)) ∧
    (∀ (r : ℕ) (S S' : Fin n → Z), hamming S S' ≤ r →
      ∀ E : Set O, MeasurableSet E →
        (M S : Measure O).real E ≤ Real.exp ((r : ℝ)*ε) * (M S' : Measure O).real E +
          (r : ℝ) * Real.exp (((r : ℝ)-1)*ε) * δ) := by
  exact @PrivPACLower.ICP.solution Z O (inferInstance : MeasurableSpace O) n ε δ hε hδ M hM
