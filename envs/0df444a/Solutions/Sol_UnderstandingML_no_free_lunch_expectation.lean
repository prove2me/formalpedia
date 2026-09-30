-- Prove2me | solution 1 for UnderstandingML.no_free_lunch_expectation
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T13:35:12.108108+00:00
-- url     : https://prove2.me/submissions/c4915f4a-0087-48a1-91f2-d4818dbc5a38

import Definitions.Def_UnderstandingML_Framework
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

open MeasureTheory

namespace UnderstandingML.NFLExpectationAux

/-! ### Part 1: the finite combinatorial core -/

/-- Number of points of `Fin n` on which `h` and `g` disagree. -/
def errCount {n : ℕ} (h g : Fin n → Bool) : ℕ :=
  ∑ i, if h i = g i then 0 else 1

/-- Flipping the label of an unseen point: for `i` outside the range of `j`, exactly half of the
labelings `g` make the prediction at `i` wrong. -/
theorem two_mul_sum_flip {n m : ℕ} (Q : (Fin m → Fin n) → (Fin m → Bool) → Fin n → Bool)
    (j : Fin m → Fin n) (i : Fin n) (hi : i ∉ Set.range j) :
    2 * (∑ g : Fin n → Bool, if Q j (g ∘ j) i = g i then 0 else 1) = 2 ^ n := by
  classical
  let σ : (Fin n → Bool) ≃ (Fin n → Bool) :=
    { toFun := fun g => Function.update g i (!g i)
      invFun := fun g => Function.update g i (!g i)
      left_inv := fun g => by ext k; by_cases hk : k = i <;> simp [Function.update, hk]
      right_inv := fun g => by ext k; by_cases hk : k = i <;> simp [Function.update, hk] }
  have hcomp : ∀ g, σ g ∘ j = g ∘ j := by
    intro g; funext k
    have : j k ≠ i := fun h => hi ⟨k, h⟩
    simp [σ, Function.update, this]
  have hi' : ∀ g, σ g i = !g i := by intro g; simp [σ]
  have hsum : (∑ g : Fin n → Bool, if Q j (g ∘ j) i = g i then 0 else 1) =
      ∑ g : Fin n → Bool, if Q j (σ g ∘ j) i = σ g i then 0 else 1 :=
    (Equiv.sum_comp σ (fun g => if Q j (g ∘ j) i = g i then 0 else 1)).symm
  have hpt : ∀ g : Fin n → Bool, ((if Q j (g ∘ j) i = g i then 0 else 1) +
      (if Q j (σ g ∘ j) i = σ g i then 0 else 1) : ℕ) = 1 := by
    intro g; rw [hcomp, hi']
    cases Q j (g ∘ j) i <;> cases g i <;> simp
  calc 2 * (∑ g : Fin n → Bool, if Q j (g ∘ j) i = g i then 0 else 1)
      = ∑ g : Fin n → Bool, (((if Q j (g ∘ j) i = g i then 0 else 1) +
      (if Q j (σ g ∘ j) i = σ g i then 0 else 1)) : ℕ) := by
        rw [Finset.sum_add_distrib, ← hsum]; ring
    _ = 2 ^ n := by simp [hpt]

/-- Averaged over all labelings, the total error is large. -/
theorem sum_errCount_ge {n m : ℕ} (hnm : 2 * m < n)
    (Q : (Fin m → Fin n) → (Fin m → Bool) → Fin n → Bool) :
    2 ^ n * (n ^ m * n) ≤
      4 * ∑ g : Fin n → Bool, ∑ j : Fin m → Fin n, errCount (Q j (g ∘ j)) g := by
  classical
  have hj : ∀ j : Fin m → Fin n, 2 ^ n * (n - m) ≤
      2 * ∑ i, ∑ g : Fin n → Bool, if Q j (g ∘ j) i = g i then 0 else 1 := by
    intro j
    set U := Finset.univ \ Finset.univ.image j with hU
    have hcard : n - m ≤ U.card := by
      have h1 : (Finset.univ.image j).card ≤ m := by
        simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := j))
      rw [hU, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    have hsub : ∑ i ∈ U, ∑ g : Fin n → Bool, (if Q j (g ∘ j) i = g i then 0 else 1) ≤
        ∑ i, ∑ g : Fin n → Bool, if Q j (g ∘ j) i = g i then 0 else 1 :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hU2 : 2 * ∑ i ∈ U, ∑ g : Fin n → Bool, (if Q j (g ∘ j) i = g i then 0 else 1) =
        U.card * 2 ^ n := by
      rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl (g := fun _ => 2 ^ n)]
      · simp
      · intro i hi
        apply two_mul_sum_flip
        rintro ⟨k, rfl⟩
        simp [hU] at hi
    have := Nat.mul_le_mul_right (2 ^ n) hcard
    nlinarith
  have hswap : ∑ g : Fin n → Bool, ∑ j : Fin m → Fin n, errCount (Q j (g ∘ j)) g =
      ∑ j : Fin m → Fin n, ∑ i, ∑ g : Fin n → Bool, if Q j (g ∘ j) i = g i then 0 else 1 := by
    unfold errCount
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_comm]
  rw [hswap]
  have hsum : ∑ _j : Fin m → Fin n, 2 ^ n * (n - m) ≤
      ∑ j : Fin m → Fin n, 2 * ∑ i, ∑ g : Fin n → Bool, (if Q j (g ∘ j) i = g i then 0 else 1) :=
    Finset.sum_le_sum (fun j _ => hj j)
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    smul_eq_mul] at hsum
  have h2 : n ≤ 2 * (n - m) := by omega
  set T := ∑ j : Fin m → Fin n, ∑ i, ∑ g : Fin n → Bool, (if Q j (g ∘ j) i = g i then 0 else 1)
  have hsum' : 2 ^ n * (n ^ m * (n - m)) ≤ 2 * T := by
    rw [Finset.mul_sum]; exact hsum
  calc 2 ^ n * (n ^ m * n) ≤ 2 ^ n * (n ^ m * (2 * (n - m))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
    _ = 2 * (2 ^ n * (n ^ m * (n - m))) := by ring
    _ ≤ 2 * (2 * T) := Nat.mul_le_mul_left _ hsum'
    _ = 4 * T := by ring

/-- Some labeling has a large total error. -/
theorem exists_errCount_ge {n m : ℕ} (hnm : 2 * m < n)
    (Q : (Fin m → Fin n) → (Fin m → Bool) → Fin n → Bool) :
    ∃ g : Fin n → Bool, n ^ m * n ≤ 4 * ∑ j : Fin m → Fin n, errCount (Q j (g ∘ j)) g := by
  by_contra hcon
  push_neg at hcon
  have h1 := sum_errCount_ge hnm Q
  have h2 : ∑ g : Fin n → Bool, 4 * ∑ j : Fin m → Fin n, errCount (Q j (g ∘ j)) g <
      ∑ _g : Fin n → Bool, n ^ m * n :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun g _ => hcon g)
  rw [← Finset.mul_sum] at h2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, smul_eq_mul] at h2
  omega

/-! ### Part 2: finite sums of Dirac masses -/

theorem integral_sum_dirac {α ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (s : Finset ι) (c : ENNReal) (hc : c ≠ ⊤) (x : ι → α) (F : α → ℝ) :
    ∫ a, F a ∂(∑ i ∈ s, c • Measure.dirac (x i)) = ∑ i ∈ s, c.toReal * F (x i) := by
  rw [integral_finset_sum_measure]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_smul_measure, integral_dirac, smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure hc

theorem indicator_univ_pi_one {α : Type*} {m : ℕ} (s : Fin m → Set α) (y : Fin m → α) :
    (Set.univ.pi s).indicator (1 : (Fin m → α) → ENNReal) y =
      ∏ k, (s k).indicator (1 : α → ENNReal) (y k) := by
  classical
  by_cases h : y ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem h]
    rw [Finset.prod_eq_one]; · rfl
    intro k _; rw [Set.indicator_of_mem (h k (Set.mem_univ _))]; rfl
  · rw [Set.indicator_of_notMem h]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at h
    obtain ⟨k, hk⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ k) (Set.indicator_of_notMem hk _)).symm

theorem pi_sum_dirac {α ι : Type*} [MeasurableSpace α] [Fintype ι] {m : ℕ}
    (c : ENNReal) (hc : c ≠ ⊤) (x : ι → α) :
    Measure.pi (fun _ : Fin m => ∑ i, c • Measure.dirac (x i)) =
      ∑ j : Fin m → ι, c ^ m • Measure.dirac (fun k => x (j k)) := by
  classical
  haveI : IsFiniteMeasure (∑ i, c • Measure.dirac (x i)) := by
    constructor
    simp [Measure.coe_finset_sum, ENNReal.mul_lt_top, hc.lt_top]
  refine Measure.pi_eq (fun s hs => ?_)
  simp only [Measure.coe_finset_sum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  simp only [Measure.dirac_apply' _ (hs _)]
  exact indicator_univ_pi_one s _

/-- A domain with more than `2m` points contains `2m + 1` distinct points. -/
theorem nonempty_embedding_of_lt_card {X : Type*} {m : ℕ} (hm : (2 * m : ℕ∞) < ENat.card X) :
    Nonempty (Fin (2 * m + 1) ↪ X) := by
  rcases finite_or_infinite X with hX | hX
  · haveI := Fintype.ofFinite X
    rw [ENat.card_eq_coe_fintype_card] at hm
    have : 2 * m < Fintype.card X := by exact_mod_cast hm
    exact Function.Embedding.nonempty_of_card_le (by simpa using this)
  · exact ⟨Fin.valEmbedding.trans (Infinite.natEmbedding X)⟩

end UnderstandingML.NFLExpectationAux

open UnderstandingML UnderstandingML.NFLExpectationAux

theorem solution {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (A : Learner (X × Bool) (X → Bool)) (m : ℕ) (hm : (2 * m : ℕ∞) < ENat.card X) :
    ∃ D : Measure (X × Bool), IsProbabilityMeasure D ∧
      (∃ f : X → Bool, Measurable f ∧ risk loss01 D f = 0) ∧
      1 / 4 ≤ ∫ S, risk loss01 D (A m S) ∂(iidLaw D m) := by
  classical
  obtain ⟨e⟩ := nonempty_embedding_of_lt_card hm
  set n := 2 * m + 1 with hn
  have hn0 : (n : ENNReal) ≠ 0 := by simp [hn]
  set c : ENNReal := (n : ENNReal)⁻¹ with hc
  have hctop : c ≠ ⊤ := by simp [hc, hn]
  have hcreal : c.toReal = 1 / (n : ℝ) := by simp [hc]
  -- the uniform distribution on the labeled points `(e i, g i)`
  let P : (Fin n → Bool) → Measure (X × Bool) := fun g => ∑ i, c • Measure.dirac (e i, g i)
  -- the labeling function extending `g` by `false`
  let F : (Fin n → Bool) → X → Bool := fun g x =>
    decide (x ∈ (Finset.univ.filter (fun i => g i = true)).map e)
  have hF : ∀ g i, F g (e i) = g i := by
    intro g i
    cases hg : g i <;> simp [F, hg]
  have hFmeas : ∀ g, Measurable (F g) := by
    intro g
    refine measurable_to_countable' (fun b => ?_)
    have hfin : ((Finset.univ.filter (fun i => g i = true)).map e : Set X).Finite :=
      Finset.finite_toSet _
    cases b
    · have : F g ⁻¹' {false} = (((Finset.univ.filter (fun i => g i = true)).map e : Set X))ᶜ := by
        ext x; simp [F]
      rw [this]; exact hfin.measurableSet.compl
    · have : F g ⁻¹' {true} = (((Finset.univ.filter (fun i => g i = true)).map e : Set X)) := by
        ext x; simp [F]
      rw [this]; exact hfin.measurableSet
  have hprob : ∀ g, IsProbabilityMeasure (P g) := by
    intro g
    constructor
    simp only [P, Measure.coe_finset_sum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [hc]
    exact ENNReal.mul_inv_cancel hn0 (by simp)
  have hrisk : ∀ g (h : X → Bool), risk loss01 (P g) h =
      1 / (n : ℝ) * (errCount (fun i => h (e i)) g : ℝ) := by
    intro g h
    simp only [risk, P]
    rw [integral_sum_dirac _ c hctop, hcreal, ← Finset.mul_sum]
    congr 1
    simp [errCount, loss01]
  -- the learner's prediction on the points `e i`, as a function of the sample indices and labels
  let Q : (Fin m → Fin n) → (Fin m → Bool) → Fin n → Bool :=
    fun j b i => A m (fun k => (e (j k), b k)) (e i)
  obtain ⟨g, hg⟩ := exists_errCount_ge (show 2 * m < n by omega) Q
  refine ⟨P g, hprob g, ⟨F g, hFmeas g, ?_⟩, ?_⟩
  · rw [hrisk]
    simp [errCount, hF]
  · have hiid : iidLaw (P g) m =
        ∑ j : Fin m → Fin n, c ^ m • Measure.dirac (fun k => (e (j k), g (j k))) :=
      pi_sum_dirac c hctop (fun i => (e i, g i))
    rw [hiid, integral_sum_dirac _ _ (ENNReal.pow_ne_top hctop)]
    simp only [hrisk]
    have hQ : ∀ j : Fin m → Fin n,
        errCount (fun i => A m (fun k => (e (j k), g (j k))) (e i)) g = errCount (Q j (g ∘ j)) g :=
      fun j => rfl
    simp only [hQ]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hcm : (c ^ m).toReal = 1 / (n : ℝ) ^ m := by
      rw [ENNReal.toReal_pow, hcreal, one_div_pow]
    rw [hcm]
    have hg' : ((n ^ m * n : ℕ) : ℝ) ≤ 4 * ((∑ j : Fin m → Fin n, errCount (Q j (g ∘ j)) g : ℕ) : ℝ) := by
      exact_mod_cast hg
    push_cast at hg'
    have hnpos : (0 : ℝ) < n := by positivity
    have hnm : (0 : ℝ) < (n : ℝ) ^ m := by positivity
    rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, one_mul, div_div, le_div_iff₀ (by positivity)]
    linarith
