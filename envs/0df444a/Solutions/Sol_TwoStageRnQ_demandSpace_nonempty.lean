-- Prove2me | solution 1 for TwoStageRnQ.demandSpace_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T00:27:18.162907+00:00
-- url     : https://prove2.me/submissions/c8d1c5b7-e1ad-46ff-8953-3f0807e8a52a

import Definitions.Def_TwoStageRnQ_Model
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-!
# Nonemptiness of the demand space, part 1: Poisson weights and multinomial counts

Elementary facts used to build a two-sided Poisson process: the Poisson weights `poisW`,
their convolution identity, and the multinomial count of maps `Fin M → Fin K` with prescribed
fibre sizes.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal

noncomputable section

namespace TwoStageRnQ

namespace NE

lemma poisW_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ poisW x n := by
  unfold poisW; positivity

lemma poisW_zero (n : ℕ) : poisW 0 n = if n = 0 then 1 else 0 := by
  unfold poisW
  rcases n with _ | n
  · simp
  · simp

lemma poisW_conv (x y : ℝ) (k : ℕ) :
    ∑ a ∈ range (k + 1), poisW x a * poisW y (k - a) = poisW (x + y) k := by
  unfold poisW
  rw [add_pow, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  have hak : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [Nat.cast_choose ℝ hak, neg_add, Real.exp_add]
  have h1 : (a.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((k - a).factorial : ℝ) ≠ 0 := by positivity
  have h3 : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma ofReal_poisW_conv {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    ∑ a ∈ range (k + 1), ENNReal.ofReal (poisW x a) * ENNReal.ofReal (poisW y (k - a))
      = ENNReal.ofReal (poisW (x + y) k) := by
  rw [← poisW_conv, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ENNReal.ofReal_mul (poisW_nonneg hx a)]
  · intro a _; exact mul_nonneg (poisW_nonneg hx a) (poisW_nonneg hy _)

lemma hasSum_poisW {x : ℝ} (hx : 0 ≤ x) : HasSum (fun n => poisW x n) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp x).mul_left (Real.exp (-x))
  rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  have hf : (fun n => poisW x n) = (fun i => Real.exp (-x) * (x ^ i / (i.factorial : ℝ))) := by
    funext n; unfold poisW; ring
  rw [hf]; exact h

lemma tsum_ofReal_poisW {x : ℝ} (hx : 0 ≤ x) : ∑' n, ENNReal.ofReal (poisW x n) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (poisW_nonneg hx) (hasSum_poisW hx).summable,
    (hasSum_poisW hx).tsum_eq, ENNReal.ofReal_one]

/-- The Poisson law with mean `x`, as a measure on `ℕ`. -/
def poisM (x : ℝ) : Measure ℕ :=
  Measure.sum (fun n : ℕ => ENNReal.ofReal (poisW x n) • Measure.dirac n)

lemma poisM_singleton (x : ℝ) (m : ℕ) : poisM x {m} = ENNReal.ofReal (poisW x m) := by
  rw [poisM, Measure.sum_apply _ (measurableSet_singleton m)]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [tsum_eq_single m]
  · simp
  · intro n hn
    simp [Set.indicator, hn]

lemma isProbabilityMeasure_poisM {x : ℝ} (hx : 0 ≤ x) : IsProbabilityMeasure (poisM x) :=
  HasSum.isProbabilityMeasure_sum_dirac (fun n => poisW_nonneg hx n) (hasSum_poisW hx)

/-! ### Multinomial counts -/

/-- Fibre size of `σ` over `i`. -/
def cnt {M K : ℕ} (σ : Fin M → Fin K) (i : Fin K) : ℕ := (univ.filter (fun j => σ j = i)).card

lemma cnt_cons {M K : ℕ} (a : Fin K) (τ : Fin M → Fin K) (i : Fin K) :
    cnt (Fin.cons a τ : Fin (M + 1) → Fin K) i = (if a = i then 1 else 0) + cnt τ i := by
  unfold cnt
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

lemma sum_cnt {M K : ℕ} (σ : Fin M → Fin K) : ∑ i, cnt σ i = M := by
  unfold cnt
  have := Finset.card_eq_sum_card_fiberwise (f := σ) (s := univ) (t := univ)
    (fun _ _ => mem_univ _)
  simpa using this.symm

/-- The multinomial count: the number of maps `Fin M → Fin K` with fibre sizes `κ`, times
`∏ κᵢ!`, equals `M!`. -/
theorem card_cnt_mul (M K : ℕ) (κ : Fin K → ℕ) (hκ : ∑ i, κ i = M) :
    (univ.filter (fun σ : Fin M → Fin K => cnt σ = κ)).card * ∏ i, (κ i).factorial
      = M.factorial := by
  induction M generalizing κ with
  | zero =>
    have h0 : κ = 0 := by
      funext i; exact (Finset.sum_eq_zero_iff.mp hκ) i (mem_univ i)
    subst h0
    have : (univ.filter (fun σ : Fin 0 → Fin K => cnt σ = 0)) = univ := by
      apply Finset.filter_true_of_mem; intro σ _; funext i; simp [cnt]
    rw [this]; simp
  | succ M ih =>
    have hcard : (univ.filter (fun σ : Fin (M + 1) → Fin K => cnt σ = κ)).card
        = ∑ a : Fin K, (univ.filter (fun τ : Fin M → Fin K =>
            ∀ i, (if a = i then 1 else 0) + cnt τ i = κ i)).card := by
      rw [Finset.card_filter, ← (Fin.consEquiv (fun _ => Fin K)).sum_comp,
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      have e : (Fin.consEquiv (fun _ => Fin K)) (a, τ) = (Fin.cons a τ : Fin (M + 1) → Fin K) :=
        rfl
      rw [e]
      simp only [funext_iff, cnt_cons]
    have hterm : ∀ a : Fin K, (univ.filter (fun τ : Fin M → Fin K =>
        ∀ i, (if a = i then 1 else 0) + cnt τ i = κ i)).card * ∏ i, (κ i).factorial
          = κ a * M.factorial := by
      intro a
      by_cases ha : κ a = 0
      · have : (univ.filter (fun τ : Fin M → Fin K =>
            ∀ i, (if a = i then 1 else 0) + cnt τ i = κ i)) = ∅ := by
          apply Finset.filter_false_of_mem
          intro τ _ h
          have := h a
          simp [ha] at this
        rw [this, ha]; simp
      · set κ' := Function.update κ a (κ a - 1) with hκ'
        have hset : (univ.filter (fun τ : Fin M → Fin K =>
            ∀ i, (if a = i then 1 else 0) + cnt τ i = κ i))
              = univ.filter (fun τ : Fin M → Fin K => cnt τ = κ') := by
          apply Finset.filter_congr
          intro τ _
          constructor
          · intro h; funext i
            have hi := h i
            by_cases hai : i = a
            · subst hai; simp [hκ'] at hi ⊢; omega
            · simp [hκ', hai, Ne.symm hai] at hi ⊢; omega
          · intro h i
            by_cases hai : i = a
            · subst hai; simp [hκ', funext_iff] at h ⊢; have := h i; simp at this; omega
            · have := congrFun h i
              simp [hκ', hai, Ne.symm hai] at this ⊢; omega
        have hsum' : ∑ i, κ' i = M := by
          have e1 : ∑ i, κ' i = (κ a - 1) + ∑ x ∈ univ \ {a}, κ x := by
            rw [hκ', Finset.sum_update_of_mem (mem_univ a)]
          have e2 : ∑ i, κ i = κ a + ∑ x ∈ univ \ {a}, κ x := by
            rw [← Finset.sum_sdiff (s₁ := {a}) (s₂ := univ) (subset_univ _)]
            simp [add_comm]
          omega
        have hprod : ∏ i, (κ i).factorial = κ a * ∏ i, (κ' i).factorial := by
          have e1 : ∏ i, (κ' i).factorial
              = ∏ i, Function.update (fun j => (κ j).factorial) a (κ a - 1).factorial i := by
            refine Finset.prod_congr rfl (fun i _ => ?_)
            by_cases hai : i = a
            · subst hai; simp [hκ']
            · simp [hκ', hai]
          rw [e1, Finset.prod_update_of_mem (mem_univ a)]
          rw [← Finset.prod_sdiff (s₁ := {a}) (s₂ := univ) (f := fun j => (κ j).factorial)
            (subset_univ _)]
          rw [Finset.prod_singleton, ← Nat.mul_factorial_pred ha]
          ring
        rw [hset, hprod, ← ih κ' hsum']
        ring
    rw [hcard, Finset.sum_mul]
    simp_rw [hterm]
    rw [← Finset.sum_mul, hκ, Nat.factorial_succ]

end NE

end TwoStageRnQ

/-!
# Nonemptiness of the demand space, part 2: one cell

A cell is a Poisson number of points with i.i.d. uniform positions in `[0,1)`. For disjoint
measurable sets `A₁, …, A_L ⊆ ℝ`, the numbers of points in the `Aₗ` are independent Poisson
variables with means `x · |Aₗ|` (Poisson thinning).
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Classical

noncomputable section

namespace TwoStageRnQ

namespace NE

/-- The uniform law on `[0,1)`. -/
def unif : Measure ℝ := volume.restrict (Set.Ico (0 : ℝ) 1)

instance : IsProbabilityMeasure unif :=
  ⟨by simp [unif, Measure.restrict_apply_univ, Real.volume_Ico]⟩

/-- A cell: a number of points and a sequence of positions. -/
abbrev Cell := ℕ × (ℕ → ℝ)

/-- The law of a cell with rate `x`: Poisson number of points, i.i.d. uniform positions. -/
def cellMeasure (x : ℝ) : Measure Cell :=
  (poisM x).prod (Measure.infinitePi (fun _ : ℕ => unif))

lemma isProbabilityMeasure_cellMeasure {x : ℝ} (hx : 0 ≤ x) :
    IsProbabilityMeasure (cellMeasure x) := by
  haveI := isProbabilityMeasure_poisM hx
  unfold cellMeasure; infer_instance

/-- Number of points of the cell `c` lying in `B`. -/
def ccount (B : Set ℝ) (c : Cell) : ℕ :=
  ((range c.1).filter (fun j => c.2 j ∈ B)).card

lemma measurable_ccount {B : Set ℝ} (hB : MeasurableSet B) :
    Measurable (ccount B) := by
  apply measurable_from_prod_countable_right
  intro M
  simp only [ccount, Finset.card_filter]
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite ((measurable_pi_apply j) hB) measurable_const measurable_const

/-- Category of a position with respect to disjoint sets `A`: `l.succ` on `A l`, `0` elsewhere. -/
def catOf {L : ℕ} (A : Fin L → Set ℝ) (u : ℝ) : Fin (L + 1) :=
  if h : ∃ l, u ∈ A l then (Classical.choose h).succ else 0

lemma catOf_eq_succ {L : ℕ} {A : Fin L → Set ℝ}
    (hA : Pairwise (fun l l' => Disjoint (A l) (A l'))) (u : ℝ) (l : Fin L) :
    catOf A u = l.succ ↔ u ∈ A l := by
  unfold catOf
  constructor
  · intro h
    split_ifs at h with h'
    · have := Fin.succ_injective _ h
      rw [← this]; exact Classical.choose_spec h'
    · exact absurd h (Fin.succ_ne_zero l).symm
  · intro hu
    have h' : ∃ l, u ∈ A l := ⟨l, hu⟩
    rw [dif_pos h']
    congr 1
    by_contra hne
    exact Set.disjoint_left.mp (hA hne) (Classical.choose_spec h') hu

lemma catOf_eq_zero {L : ℕ} (A : Fin L → Set ℝ) (u : ℝ) :
    catOf A u = 0 ↔ ¬ ∃ l, u ∈ A l := by
  unfold catOf
  split_ifs with h
  · simp [h, Fin.succ_ne_zero]
  · simp [h]

lemma catOf_preimage_succ {L : ℕ} {A : Fin L → Set ℝ}
    (hA : Pairwise (fun l l' => Disjoint (A l) (A l'))) (l : Fin L) :
    catOf A ⁻¹' {l.succ} = A l := by
  ext u; simp [catOf_eq_succ hA]

lemma measurable_catOf {L : ℕ} {A : Fin L → Set ℝ}
    (hA : Pairwise (fun l l' => Disjoint (A l) (A l'))) (hAm : ∀ l, MeasurableSet (A l)) :
    Measurable (catOf A) := by
  apply measurable_to_countable'
  intro i
  refine Fin.cases ?_ (fun l => ?_) i
  · have : catOf A ⁻¹' {0} = (⋃ l, A l)ᶜ := by
      ext u; simp [catOf_eq_zero]
    rw [this]
    exact (MeasurableSet.iUnion hAm).compl
  · rw [catOf_preimage_succ hA]; exact hAm l

/-- Full count vector of a cell, by category. -/
def cv {L : ℕ} (A : Fin L → Set ℝ) (c : Cell) (i : Fin (L + 1)) : ℕ :=
  ccount (catOf A ⁻¹' {i}) c

lemma sum_cv {L : ℕ} (A : Fin L → Set ℝ) (c : Cell) : ∑ i, cv A c i = c.1 := by
  have := Finset.card_eq_sum_card_fiberwise (f := fun j => catOf A (c.2 j)) (s := range c.1)
    (t := univ) (fun _ _ => mem_univ _)
  simp only [card_range] at this
  rw [this]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [cv, ccount]

lemma measurableSet_cv {L : ℕ} {A : Fin L → Set ℝ}
    (hA : Pairwise (fun l l' => Disjoint (A l) (A l'))) (hAm : ∀ l, MeasurableSet (A l))
    (κ : Fin (L + 1) → ℕ) : MeasurableSet {c : Cell | cv A c = κ} := by
  have : {c : Cell | cv A c = κ} = ⋂ i, (ccount (catOf A ⁻¹' {i})) ⁻¹' {κ i} := by
    ext c; simp [cv, funext_iff]
  rw [this]
  exact MeasurableSet.iInter (fun i =>
    measurable_ccount ((measurable_catOf hA hAm) (measurableSet_singleton i))
      (measurableSet_singleton _))

/-- The real identity behind Poisson thinning. -/
lemma thinning_identity (x : ℝ) {K : ℕ} (q : Fin K → ℝ) (hq : ∑ i, q i = 1) (κ : Fin K → ℕ)
    (cF : ℕ) (hc : cF * ∏ i, (κ i).factorial = (∑ i, κ i).factorial) :
    poisW x (∑ i, κ i) * ((cF : ℝ) * ∏ i, q i ^ κ i) = ∏ i, poisW (x * q i) (κ i) := by
  unfold poisW
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, ← Real.exp_sum]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hc' : ((∑ i, κ i).factorial : ℝ) = (cF : ℝ) * ∏ i, ((κ i).factorial : ℝ) := by
    rw [← hc]; push_cast; ring
  have hsum : ∑ i, -(x * q i) = -x := by
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hq, mul_one]
  have hP : (∏ i, ((κ i).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by positivity)
  have hcF : (cF : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hc'
    exact (Nat.factorial_ne_zero (∑ i, κ i)) (by exact_mod_cast hc')
  rw [hsum, hc']
  field_simp

lemma thinning_ennreal (x : ℝ) (hx : 0 ≤ x) {K : ℕ} (ρ : Fin K → ℝ≥0∞) (hρ : ∀ i, ρ i ≠ ⊤)
    (hsum : ∑ i, ρ i = 1) (κ : Fin K → ℕ) (cF : ℕ)
    (hc : cF * ∏ i, (κ i).factorial = (∑ i, κ i).factorial) :
    ENNReal.ofReal (poisW x (∑ i, κ i)) * ((cF : ℝ≥0∞) * ∏ i, ρ i ^ κ i)
      = ∏ i, ENNReal.ofReal (poisW (x * (ρ i).toReal) (κ i)) := by
  obtain ⟨q, hqnn, rfl⟩ : ∃ q : Fin K → ℝ, (∀ i, 0 ≤ q i) ∧ ρ = fun i => ENNReal.ofReal (q i) :=
    ⟨fun i => (ρ i).toReal, fun i => ENNReal.toReal_nonneg,
      funext (fun i => (ENNReal.ofReal_toReal (hρ i)).symm)⟩
  have hq : ∑ i, q i = 1 := by
    have h2 := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_sum (fun i _ => hρ i)] at h2
    simpa [ENNReal.toReal_ofReal (hqnn _)] using h2
  simp only [ENNReal.toReal_ofReal (hqnn _)]
  rw [← ENNReal.ofReal_natCast cF,
    Finset.prod_congr rfl (fun i _ => (ENNReal.ofReal_pow (hqnn i) (κ i)).symm),
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => pow_nonneg (hqnn i) (κ i)),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg cF), ← ENNReal.ofReal_mul (poisW_nonneg hx _),
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => poisW_nonneg (mul_nonneg hx (hqnn i)) (κ i))]
  congr 1
  exact thinning_identity x q hq κ cF hc

/-- Measure of a box of positions: the first `M` positions have prescribed categories. -/
lemma infinitePi_box {L : ℕ} (A : Fin L → Set ℝ)
    (hcat : Measurable (catOf A)) (M : ℕ) (σ : Fin M → Fin (L + 1)) :
    Measure.infinitePi (fun _ : ℕ => unif)
        {u | ∀ j : Fin M, catOf A (u j) = σ j}
      = ∏ j : Fin M, unif (catOf A ⁻¹' {σ j}) := by
  have hset : {u : ℕ → ℝ | ∀ j : Fin M, catOf A (u j) = σ j}
      = Set.pi (↑(range M))
          (fun j => if h : j < M then catOf A ⁻¹' {σ ⟨j, h⟩} else Set.univ) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.coe_range, Set.mem_Iio]
    constructor
    · intro h j hj
      rw [dif_pos hj]; exact h ⟨j, hj⟩
    · intro h j
      have := h j.1 j.2
      rw [dif_pos j.2] at this
      exact this
  rw [hset, Measure.infinitePi_pi]
  · rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [dif_pos j.2]
  · intro j _
    split_ifs
    · exact hcat (measurableSet_singleton _)
    · exact MeasurableSet.univ

/-- Poisson thinning for one cell, all categories. -/
theorem cell_full (x : ℝ) (hx : 0 ≤ x) {L : ℕ} (A : Fin L → Set ℝ)
    (hA : Pairwise (fun l l' => Disjoint (A l) (A l'))) (hAm : ∀ l, MeasurableSet (A l))
    (κ : Fin (L + 1) → ℕ) :
    cellMeasure x {c | cv A c = κ}
      = ∏ i, ENNReal.ofReal (poisW (x * (unif (catOf A ⁻¹' {i})).toReal) (κ i)) := by
  have hcat := measurable_catOf hA hAm
  set M := ∑ i, κ i with hM
  set ψ : (ℕ → ℝ) → (Fin M → Fin (L + 1)) := fun u j => catOf A (u j) with hψ
  have hψm : Measurable ψ := by
    rw [hψ]; exact measurable_pi_lambda _ (fun j => hcat.comp (measurable_pi_apply _))
  set F := univ.filter (fun σ : Fin M → Fin (L + 1) => cnt σ = κ) with hF
  -- the cell set is a product set
  have hprod : {c : Cell | cv A c = κ} = ({M} : Set ℕ) ×ˢ (ψ ⁻¹' {σ | cnt σ = κ}) := by
    ext ⟨m, u⟩
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_singleton_iff, Set.mem_preimage]
    have key : ∀ i, cv A (M, u) i = cnt (ψ u) i := by
      intro i
      simp only [cv, ccount, cnt, hψ, Set.mem_preimage, Set.mem_singleton_iff,
        Finset.card_filter]
      exact (Fin.sum_univ_eq_sum_range (fun j => if catOf A (u j) = i then 1 else 0) M).symm
    constructor
    · intro h
      have hm : m = M := by
        have := sum_cv A (m, u); rw [h] at this; exact this.symm
      subst hm
      refine ⟨rfl, ?_⟩
      funext i; rw [← key i, h]
    · rintro ⟨hm, h⟩
      subst hm
      funext i; rw [key i, h]
  have hbox : ∀ σ : Fin M → Fin (L + 1),
      (Measure.infinitePi (fun _ : ℕ => unif)).map ψ {σ}
        = ∏ i, unif (catOf A ⁻¹' {i}) ^ cnt σ i := by
    intro σ
    rw [Measure.map_apply hψm (measurableSet_singleton σ)]
    have : ψ ⁻¹' {σ} = {u | ∀ j : Fin M, catOf A (u j) = σ j} := by
      ext u; simp [hψ, funext_iff]
    rw [this, infinitePi_box A hcat M σ]
    rw [← Finset.prod_fiberwise (s := univ) (g := σ)
      (f := fun j => unif (catOf A ⁻¹' {σ j}))]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Finset.prod_congr rfl (g := fun _ => unif (catOf A ⁻¹' {i}))
      (fun j hj => by rw [(Finset.mem_filter.mp hj).2])]
    rw [Finset.prod_const]
    rfl
  have hE : Measure.infinitePi (fun _ : ℕ => unif)
      (ψ ⁻¹' {σ | cnt σ = κ}) = (F.card : ℝ≥0∞) * ∏ i, unif (catOf A ⁻¹' {i}) ^ κ i := by
    rw [← Measure.map_apply hψm (Set.Finite.measurableSet (Set.toFinite _))]
    have hcoe : {σ : Fin M → Fin (L + 1) | cnt σ = κ} = ↑F := by
      rw [hF]; simp
    rw [hcoe, ← sum_measure_singleton]
    rw [Finset.sum_congr rfl (g := fun _ => ∏ i, unif (catOf A ⁻¹' {i}) ^ κ i)
      (fun σ hσ => by rw [hbox σ, (Finset.mem_filter.mp hσ).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hsum1 : ∑ i, unif (catOf A ⁻¹' {i}) = 1 := by
    rw [sum_measure_preimage_singleton _ (fun i _ => hcat (measurableSet_singleton i))]
    simp
  rw [hprod, cellMeasure, Measure.prod_prod, poisM_singleton, hE]
  exact thinning_ennreal x hx (fun i => unif (catOf A ⁻¹' {i})) (fun i => measure_ne_top _ _)
    hsum1 κ F.card (card_cnt_mul M (L + 1) κ hM.symm)

/-- Poisson thinning for one cell: counts in disjoint sets are independent Poisson. -/
theorem cell_marginal (x : ℝ) (hx : 0 ≤ x) {L : ℕ} (A : Fin L → Set ℝ)
    (hA : Pairwise (fun l l' => Disjoint (A l) (A l'))) (hAm : ∀ l, MeasurableSet (A l))
    (k : Fin L → ℕ) :
    cellMeasure x {c | ∀ l, ccount (A l) c = k l}
      = ∏ l, ENNReal.ofReal (poisW (x * (unif (A l)).toReal) (k l)) := by
  have hcv : ∀ c l, ccount (A l) c = cv A c l.succ := by
    intro c l; simp only [cv, catOf_preimage_succ hA]
  have hset : {c : Cell | ∀ l, ccount (A l) c = k l}
      = ⋃ a0 : ℕ, {c : Cell | cv A c = Fin.cons a0 k} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      refine ⟨cv A c 0, ?_⟩
      funext i
      refine Fin.cases ?_ (fun l => ?_) i
      · simp
      · simp [← hcv, h l]
    · rintro ⟨a0, h⟩ l
      rw [hcv, h]; simp
  rw [hset, measure_iUnion]
  · simp_rw [cell_full x hx A hA hAm, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_mul_right, tsum_ofReal_poisW (mul_nonneg hx ENNReal.toReal_nonneg), one_mul]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    rw [catOf_preimage_succ hA]
  · intro a b hab
    refine Set.disjoint_left.mpr (fun c hca hcb => hab ?_)
    have h1 := congrFun (hca.symm.trans hcb) 0
    simpa using h1
  · intro a0; exact measurableSet_cv hA hAm _

end NE

end TwoStageRnQ

/-!
# Nonemptiness of the demand space, part 3: the two-sided Poisson process

Cells indexed by `ℤ` are independent under the product law. The cell `n` carries the points
`n + u` (`u ∈ [0,1)`). Counts of points in disjoint intervals `(aₗ, bₗ]` are independent Poisson
variables with means `x (bₗ - aₗ)`.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Classical

noncomputable section

namespace TwoStageRnQ

namespace NE

/-- The sample space: one cell per integer. -/
abbrev Ωc := ℤ → Cell

/-- The product law of the cells. -/
def nuc (x : ℝ) : Measure Ωc := Measure.infinitePi (fun _ : ℤ => cellMeasure x)

lemma isProbabilityMeasure_nuc {x : ℝ} (hx : 0 ≤ x) : IsProbabilityMeasure (nuc x) := by
  haveI := isProbabilityMeasure_cellMeasure hx
  unfold nuc; infer_instance

/-- Positions `u ∈ [0,1)` in cell `n` whose point `n + u` lies in `A`. -/
def posSet (n : ℤ) (A : Set ℝ) : Set ℝ := {u | u ∈ Set.Ico (0 : ℝ) 1 ∧ (n : ℝ) + u ∈ A}

lemma measurableSet_posSet (n : ℤ) {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet (posSet n A) :=
  measurableSet_Ico.inter (measurable_const_add (n : ℝ) hA)

lemma posSet_disjoint (n : ℤ) {A B : Set ℝ} (h : Disjoint A B) :
    Disjoint (posSet n A) (posSet n B) :=
  Set.disjoint_left.mpr (fun _ hu hv => Set.disjoint_left.mp h hu.2 hv.2)

lemma unif_posSet (n : ℤ) {A : Set ℝ} (hA : MeasurableSet A) :
    unif (posSet n A) = volume (A ∩ Set.Ico (n : ℝ) (n + 1)) := by
  rw [unif, Measure.restrict_apply (measurableSet_posSet n hA)]
  have : posSet n A ∩ Set.Ico (0 : ℝ) 1
      = (fun u => (n : ℝ) + u) ⁻¹' (A ∩ Set.Ico (n : ℝ) (n + 1)) := by
    ext u
    simp only [posSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ico, Set.mem_preimage]
    constructor
    · rintro ⟨⟨⟨h0, h1⟩, hA⟩, _⟩; exact ⟨hA, by linarith, by linarith⟩
    · rintro ⟨hA, h0, h1⟩; exact ⟨⟨⟨by linarith, by linarith⟩, hA⟩, by linarith, by linarith⟩
  rw [this, measure_preimage_add]

/-- Poisson counts in disjoint sets, over a finite set of cells. -/
theorem global_law {x : ℝ} (hx : 0 ≤ x) {L : ℕ} (A : Fin L → Set ℝ)
    (hA : Pairwise (fun l l' => Disjoint (A l) (A l'))) (hAm : ∀ l, MeasurableSet (A l))
    (S : Finset ℤ) (k : Fin L → ℕ) :
    nuc x {ω | ∀ l, ∑ n ∈ S, ccount (posSet n (A l)) (ω n) = k l}
      = ∏ l, ENNReal.ofReal (poisW (x * ∑ n ∈ S, (unif (posSet n (A l))).toReal) (k l)) := by
  haveI := isProbabilityMeasure_cellMeasure hx
  haveI := isProbabilityMeasure_nuc hx
  have hAm' : ∀ n l, MeasurableSet (posSet n (A l)) := fun n l => measurableSet_posSet n (hAm l)
  induction S using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.sum_empty, mul_zero, poisW_zero]
    by_cases hk : ∀ l, k l = 0
    · have : {ω : Ωc | ∀ l, (0 : ℕ) = k l} = Set.univ := by
        ext ω; simp [hk]
      rw [this, measure_univ]
      symm; apply Finset.prod_eq_one; intro l _; simp [hk l]
    · push_neg at hk
      obtain ⟨l0, hl0⟩ := hk
      have : {ω : Ωc | ∀ l, (0 : ℕ) = k l} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall]
        exact ⟨l0, fun h => hl0 h.symm⟩
      rw [this, measure_empty]
      symm; apply Finset.prod_eq_zero (mem_univ l0); simp [hl0]
  | insert m S hm ih =>
    set X : Ωc → Fin L → ℕ := fun ω l => ∑ n ∈ S, ccount (posSet n (A l)) (ω n) with hX
    set Y : Ωc → Fin L → ℕ := fun ω l => ccount (posSet m (A l)) (ω m) with hY
    have hXm : Measurable X := by
      rw [hX]; refine measurable_pi_lambda _ (fun l => ?_)
      exact Finset.measurable_sum _
        (fun n _ => (measurable_ccount (hAm' n l)).comp (measurable_pi_apply n))
    have hYm : Measurable Y := by
      rw [hY]; refine measurable_pi_lambda _ (fun l => ?_)
      exact (measurable_ccount (hAm' m l)).comp (measurable_pi_apply m)
    -- independence of the cells in `S` and the cell `m`
    have hind : IndepFun X Y (nuc x) := by
      have h0 := (iIndepFun_infinitePi (P := fun _ : ℤ => cellMeasure x)
        (X := fun _ : ℤ => (id : Cell → Cell)) (fun _ => measurable_id)).indepFun_finset
        S {m} (Finset.disjoint_singleton_right.mpr hm) (fun i => measurable_pi_apply i)
      have hφ : Measurable (fun (v : S → Cell) (l : Fin L) =>
          ∑ n : S, ccount (posSet n (A l)) (v n)) := by
        refine measurable_pi_lambda _ (fun l => ?_)
        exact Finset.measurable_sum _
          (fun n _ => (measurable_ccount (hAm' n l)).comp (measurable_pi_apply n))
      have hψ : Measurable (fun (w : ({m} : Finset ℤ) → Cell) (l : Fin L) =>
          ccount (posSet m (A l)) (w ⟨m, mem_singleton_self m⟩)) := by
        refine measurable_pi_lambda _ (fun l => ?_)
        exact (measurable_ccount (hAm' m l)).comp (measurable_pi_apply _)
      have h1 := h0.comp hφ hψ
      have e1 : X = (fun (v : S → Cell) (l : Fin L) => ∑ n : S, ccount (posSet n (A l)) (v n))
          ∘ (fun ω (i : S) => id (ω i)) := by
        funext ω l
        simp only [hX, Function.comp_apply, id]
        exact (Finset.sum_coe_sort S (fun n => ccount (posSet n (A l)) (ω n))).symm
      have e2 : Y = (fun (w : ({m} : Finset ℤ) → Cell) (l : Fin L) =>
          ccount (posSet m (A l)) (w ⟨m, mem_singleton_self m⟩))
          ∘ (fun ω (i : ({m} : Finset ℤ)) => id (ω i)) := by
        funext ω l; rfl
      rw [e1, e2]
      exact h1
    -- decomposition according to the value of `X`
    have hset : {ω : Ωc | ∀ l, ∑ n ∈ insert m S, ccount (posSet n (A l)) (ω n) = k l}
        = ⋃ a ∈ Fintype.piFinset (fun l => range (k l + 1)),
            ({ω | X ω = a} ∩ {ω | Y ω = fun l => k l - a l}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop,
        Finset.sum_insert hm, Fintype.mem_piFinset, Finset.mem_range]
      constructor
      · intro h
        refine ⟨X ω, fun l => ?_, rfl, ?_⟩
        · have := h l; simp only [hX]; omega
        · funext l; have := h l; simp only [hX, hY]; omega
      · rintro ⟨a, ha, hXa, hYa⟩ l
        have h1 := congrFun hXa l
        have h2 := congrFun hYa l
        simp only [hX, hY] at h1 h2
        have := ha l
        omega
    rw [hset, measure_biUnion_finset]
    · have hterm : ∀ a ∈ Fintype.piFinset (fun l => range (k l + 1)),
          nuc x ({ω | X ω = a} ∩ {ω | Y ω = fun l => k l - a l})
            = (∏ l, ENNReal.ofReal (poisW (x * ∑ n ∈ S, (unif (posSet n (A l))).toReal) (a l)))
              * ∏ l, ENNReal.ofReal (poisW (x * (unif (posSet m (A l))).toReal) (k l - a l)) := by
        intro a _
        have hmi := hind.meas_inter (s := X ⁻¹' {a}) (t := Y ⁻¹' {fun l => k l - a l})
          ⟨{a}, measurableSet_singleton a, rfl⟩
          ⟨{fun l => k l - a l}, measurableSet_singleton _, rfl⟩
        rw [show ({ω | X ω = a} ∩ {ω | Y ω = fun l => k l - a l})
          = X ⁻¹' {a} ∩ Y ⁻¹' {fun l => k l - a l} from rfl, hmi]
        congr 1
        · have : X ⁻¹' {a}
              = {ω | ∀ l, ∑ n ∈ S, ccount (posSet n (A l)) (ω n) = a l} := by
            ext ω; simp [hX, funext_iff]
          rw [this, ih a]
        · have hpre : Y ⁻¹' {fun l => k l - a l}
              = (fun ω : Ωc => ω m) ⁻¹' {c | ∀ l, ccount (posSet m (A l)) c = k l - a l} := by
            ext ω; simp [hY, funext_iff]
          have hmeas : MeasurableSet {c : Cell | ∀ l, ccount (posSet m (A l)) c = k l - a l} := by
            have : {c : Cell | ∀ l, ccount (posSet m (A l)) c = k l - a l}
                = ⋂ l, ccount (posSet m (A l)) ⁻¹' {k l - a l} := by
              ext c; simp
            rw [this]
            exact MeasurableSet.iInter
              (fun l => measurable_ccount (hAm' m l) (measurableSet_singleton _))
          rw [hpre, ← Measure.map_apply (measurable_pi_apply m) hmeas, nuc,
            Measure.infinitePi_map_eval]
          exact cell_marginal x hx (fun l => posSet m (A l))
            (fun l l' h => posSet_disjoint m (hA h)) (hAm' m) _
      rw [Finset.sum_congr rfl hterm]
      have hconv : ∑ a ∈ Fintype.piFinset (fun l => range (k l + 1)),
          (∏ l, ENNReal.ofReal (poisW (x * ∑ n ∈ S, (unif (posSet n (A l))).toReal) (a l)))
            * ∏ l, ENNReal.ofReal (poisW (x * (unif (posSet m (A l))).toReal) (k l - a l))
          = ∏ l, ∑ j ∈ range (k l + 1),
              ENNReal.ofReal (poisW (x * ∑ n ∈ S, (unif (posSet n (A l))).toReal) j)
                * ENNReal.ofReal (poisW (x * (unif (posSet m (A l))).toReal) (k l - j)) := by
        rw [Finset.prod_univ_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.prod_mul_distrib]
      rw [hconv]
      refine Finset.prod_congr rfl (fun l _ => ?_)
      rw [ofReal_poisW_conv (mul_nonneg hx (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)))
        (mul_nonneg hx ENNReal.toReal_nonneg), Finset.sum_insert hm]
      congr 2
      ring
    · intro a _ a' _ hne
      exact Set.disjoint_left.mpr (fun ω h1 h2 => hne (h1.1.symm.trans h2.1))
    · intro a _
      exact (hXm (measurableSet_singleton a)).inter (hYm (measurableSet_singleton _))

/-! ### Interval counts -/

/-- Number of points in `(a, b]`. -/
def C (ω : Ωc) (a b : ℝ) : ℕ := ∑ n ∈ Icc ⌊a⌋ ⌊b⌋, ccount (posSet n (Set.Ioc a b)) (ω n)

lemma ccount_empty (c : Cell) : ccount ∅ c = 0 := by simp [ccount]

lemma posSet_Ioc_eq_empty {n : ℤ} {a b : ℝ} (hn : n ∉ Icc ⌊a⌋ ⌊b⌋) :
    posSet n (Set.Ioc a b) = ∅ := by
  ext u
  simp only [posSet, Set.mem_setOf_eq, Set.mem_Ico, Set.mem_Ioc, Set.mem_empty_iff_false,
    iff_false]
  rintro ⟨⟨h0, h1⟩, ha, hb⟩
  apply hn
  rw [Finset.mem_Icc]
  have hfl : ⌊(n : ℝ) + u⌋ = n := by
    rw [Int.floor_eq_iff]; constructor <;> linarith
  constructor
  · calc ⌊a⌋ ≤ ⌊(n : ℝ) + u⌋ := Int.floor_mono ha.le
      _ = n := hfl
  · calc n = ⌊(n : ℝ) + u⌋ := hfl.symm
      _ ≤ ⌊b⌋ := Int.floor_mono hb

lemma C_eq_sum {S : Finset ℤ} {a b : ℝ} (hS : Icc ⌊a⌋ ⌊b⌋ ⊆ S) (ω : Ωc) :
    ∑ n ∈ S, ccount (posSet n (Set.Ioc a b)) (ω n) = C ω a b := by
  unfold C
  symm
  apply Finset.sum_subset hS
  intro n _ hn
  rw [posSet_Ioc_eq_empty hn, ccount_empty]

lemma sum_unif_posSet {S : Finset ℤ} {a b : ℝ} (hab : a ≤ b) (hS : Icc ⌊a⌋ ⌊b⌋ ⊆ S) :
    ∑ n ∈ S, (unif (posSet n (Set.Ioc a b))).toReal = b - a := by
  rw [← ENNReal.toReal_sum (fun n _ => measure_ne_top _ _)]
  have h1 : ∑ n ∈ S, unif (posSet n (Set.Ioc a b))
      = volume (⋃ n ∈ S, (Set.Ioc a b ∩ Set.Ico (n : ℝ) (n + 1))) := by
    rw [measure_biUnion_finset]
    · exact Finset.sum_congr rfl (fun n _ => unif_posSet n measurableSet_Ioc)
    · intro n _ n' _ hne
      refine Set.disjoint_left.mpr (fun y hy hy' => hne ?_)
      have e1 : ⌊y⌋ = n := Int.floor_eq_iff.mpr hy.2
      have e2 : ⌊y⌋ = n' := Int.floor_eq_iff.mpr hy'.2
      exact e1.symm.trans e2
    · intro n _; exact measurableSet_Ioc.inter measurableSet_Ico
  have h2 : (⋃ n ∈ S, (Set.Ioc a b ∩ Set.Ico (n : ℝ) (n + 1))) = Set.Ioc a b := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    constructor
    · rintro ⟨n, _, hy, _⟩; exact hy
    · intro hy
      refine ⟨⌊y⌋, hS ?_, hy, Int.floor_le y, Int.lt_floor_add_one y⟩
      rw [Finset.mem_Icc]
      exact ⟨Int.floor_mono hy.1.le, Int.floor_mono hy.2⟩
  rw [h1, h2, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]

lemma measurable_C (a b : ℝ) : Measurable (fun ω : Ωc => C ω a b) :=
  Finset.measurable_sum _ (fun n _ =>
    (measurable_ccount (measurableSet_posSet n measurableSet_Ioc)).comp (measurable_pi_apply n))

/-- Counts in disjoint intervals are independent Poisson variables. -/
theorem interval_law {x : ℝ} (hx : 0 ≤ x) {L : ℕ} (a b : Fin L → ℝ) (hab : ∀ l, a l ≤ b l)
    (hd : Pairwise (fun l l' => Disjoint (Set.Ioc (a l) (b l)) (Set.Ioc (a l') (b l'))))
    (k : Fin L → ℕ) :
    nuc x {ω | ∀ l, C ω (a l) (b l) = k l}
      = ∏ l, ENNReal.ofReal (poisW (x * (b l - a l)) (k l)) := by
  set S : Finset ℤ := univ.biUnion (fun l => Icc ⌊a l⌋ ⌊b l⌋) with hSdef
  have hS : ∀ l, Icc ⌊a l⌋ ⌊b l⌋ ⊆ S := fun l =>
    Finset.subset_biUnion_of_mem (fun l => Icc ⌊a l⌋ ⌊b l⌋) (mem_univ l)
  have hset : {ω : Ωc | ∀ l, C ω (a l) (b l) = k l}
      = {ω | ∀ l, ∑ n ∈ S, ccount (posSet n (Set.Ioc (a l) (b l))) (ω n) = k l} := by
    ext ω
    exact forall_congr' (fun l => by rw [C_eq_sum (hS l)])
  rw [hset, global_law hx (fun l => Set.Ioc (a l) (b l)) hd (fun l => measurableSet_Ioc) S k]
  refine Finset.prod_congr rfl (fun l _ => ?_)
  rw [sum_unif_posSet (hab l) (hS l)]

lemma interval_law_one {x : ℝ} (hx : 0 ≤ x) {a b : ℝ} (hab : a ≤ b) (k : ℕ) :
    nuc x {ω | C ω a b = k} = ENNReal.ofReal (poisW (x * (b - a)) k) := by
  have := interval_law hx (L := 1) (fun _ => a) (fun _ => b) (fun _ => hab)
    (fun l l' h => absurd (Subsingleton.elim l l') h) (fun _ => k)
  simpa using this

/-- Counts in disjoint intervals are independent. -/
theorem iIndep_intervals {x : ℝ} (hx : 0 ≤ x) {L : ℕ} (a b : Fin L → ℝ) (hab : ∀ l, a l ≤ b l)
    (hd : Pairwise (fun l l' => Disjoint (Set.Ioc (a l) (b l)) (Set.Ioc (a l') (b l')))) :
    iIndepFun (fun l ω => C ω (a l) (b l)) (nuc x) := by
  haveI := isProbabilityMeasure_nuc hx
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun l => (measurable_C _ _).aemeasurable)]
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_pi_lambda _ (fun l => measurable_C _ _))
    (measurableSet_singleton k), ← Set.univ_pi_singleton k, Measure.pi_pi]
  have : (fun ω l => C ω (a l) (b l)) ⁻¹' Set.univ.pi (fun l => {k l})
      = {ω | ∀ l, C ω (a l) (b l) = k l} := by
    ext ω; simp
  rw [this, interval_law hx a b hab hd k]
  refine Finset.prod_congr rfl (fun l _ => ?_)
  rw [Measure.map_apply (measurable_C _ _) (measurableSet_singleton _)]
  exact (interval_law_one hx (hab l) (k l)).symm

end NE

end TwoStageRnQ

/-!
# Nonemptiness of the demand space, part 4: the demand process

The signed counter `N t` of the two-sided Poisson process (`N 0 = 0`), its natural filtration,
and the verification of every field of `DemandSpace`.
-/

open MeasureTheory ProbabilityTheory Filter Finset Topology
open scoped ENNReal NNReal Classical

noncomputable section

namespace TwoStageRnQ

namespace NE

lemma C_self (ω : Ωc) (a : ℝ) : C ω a a = 0 := by
  unfold C
  apply Finset.sum_eq_zero
  intro n _
  rw [Set.Ioc_self, show posSet n ∅ = ∅ by ext u; simp [posSet], ccount_empty]

lemma ccount_union {B1 B2 B : Set ℝ} (hd : Disjoint B1 B2) (hu : B1 ∪ B2 = B) (c : Cell) :
    ccount B1 c + ccount B2 c = ccount B c := by
  unfold ccount
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← hu]
  by_cases h1 : c.2 j ∈ B1
  · have h2 : c.2 j ∉ B2 := Set.disjoint_left.mp hd h1
    simp [h1, h2]
  · by_cases h2 : c.2 j ∈ B2 <;> simp [h1, h2]

lemma C_add (ω : Ωc) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    C ω a b + C ω b c = C ω a c := by
  have h1 : Icc ⌊a⌋ ⌊b⌋ ⊆ Icc ⌊a⌋ ⌊c⌋ := Finset.Icc_subset_Icc le_rfl (Int.floor_mono hbc)
  have h2 : Icc ⌊b⌋ ⌊c⌋ ⊆ Icc ⌊a⌋ ⌊c⌋ := Finset.Icc_subset_Icc (Int.floor_mono hab) le_rfl
  rw [← C_eq_sum h1, ← C_eq_sum h2, ← Finset.sum_add_distrib]
  unfold C
  refine Finset.sum_congr rfl (fun n _ => ?_)
  apply ccount_union
  · refine Set.disjoint_left.mpr (fun u hu hv => ?_)
    have := hu.2.2; have := hv.2.1; linarith
  · ext u
    simp only [posSet, Set.mem_union, Set.mem_setOf_eq, Set.mem_Ioc]
    constructor
    · rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩)
      · exact ⟨h0, h1, by linarith⟩
      · exact ⟨h0, by linarith, h2⟩
    · rintro ⟨h0, h1, h2⟩
      by_cases h : (n : ℝ) + u ≤ b
      · exact Or.inl ⟨h0, h1, h⟩
      · exact Or.inr ⟨h0, lt_of_not_ge h, h2⟩

/-- The signed demand counter: `N 0 = 0`, increments count the points. -/
def Nf (t : ℝ) (ω : Ωc) : ℤ := if 0 ≤ t then (C ω 0 t : ℤ) else -(C ω t 0 : ℤ)

lemma Nf_sub {s t : ℝ} (hst : s ≤ t) (ω : Ωc) : Nf t ω - Nf s ω = (C ω s t : ℤ) := by
  unfold Nf
  by_cases hs : 0 ≤ s
  · have ht : 0 ≤ t := hs.trans hst
    rw [if_pos ht, if_pos hs]
    have := C_add ω hs hst
    omega
  · push_neg at hs
    by_cases ht : 0 ≤ t
    · rw [if_pos ht, if_neg (not_le.mpr hs)]
      have := C_add ω hs.le ht
      omega
    · push_neg at ht
      rw [if_neg (not_le.mpr ht), if_neg (not_le.mpr hs)]
      have := C_add ω hst ht.le
      omega

lemma Nf_zero (ω : Ωc) : Nf 0 ω = 0 := by simp [Nf, C_self]

lemma Nf_eq (ω : Ωc) {q y : ℝ} (hq0 : q ≤ 0) (hqy : q ≤ y) :
    Nf y ω = (C ω q y : ℤ) - (C ω q 0 : ℤ) := by
  have h1 := Nf_sub hqy ω
  have h2 := Nf_sub hq0 ω
  rw [Nf_zero] at h2
  linarith

lemma measurable_Nf (t : ℝ) : Measurable (Nf t) := by
  unfold Nf
  by_cases ht : 0 ≤ t
  · simp only [if_pos ht]
    exact (measurable_of_countable (fun n : ℕ => (n : ℤ))).comp (measurable_C 0 t)
  · simp only [if_neg ht]
    exact (measurable_of_countable (fun n : ℕ => -(n : ℤ))).comp (measurable_C t 0)

/-- The natural filtration of the demand counter. -/
def Fseq (s : ℝ) : MeasurableSpace Ωc :=
  ⨆ (r : ℝ) (_ : r ≤ s), MeasurableSpace.comap (Nf r) (inferInstance : MeasurableSpace ℤ)

/-- The natural filtration, bundled. -/
def filt : Filtration ℝ (inferInstance : MeasurableSpace Ωc) where
  seq := Fseq
  mono' := fun _ _ hss' => iSup₂_mono' (fun r hr => ⟨r, hr.trans hss', le_rfl⟩)
  le' := fun _ => iSup₂_le (fun r _ => (measurable_Nf r).comap_le)

lemma Nf_adapted (t : ℝ) : Measurable[filt t] (Nf t) :=
  Measurable.of_comap_le
    (le_iSup₂ (f := fun r (_ : r ≤ t) => MeasurableSpace.comap (Nf r)
      (inferInstance : MeasurableSpace ℤ)) t le_rfl)

lemma Nf_mono (ω : Ωc) : Monotone (fun t => Nf t ω) := by
  intro s t hst
  show Nf s ω ≤ Nf t ω
  have := Nf_sub hst ω
  omega

lemma Nf_rcont (ω : Ωc) (t : ℝ) : ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → Nf s ω = Nf t ω := by
  set S0 : Finset ℤ := Icc ⌊t⌋ (⌊t⌋ + 1) with hS0
  have hev : ∀ᶠ s in 𝓝[≥] t, C ω t s = 0 := by
    have h1 : ∀ᶠ s in 𝓝[≥] t, s < t + 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
    have h3 : ∀ᶠ s in 𝓝[≥] t, ∀ n ∈ S0, ∀ j ∈ range (ω n).1,
        ¬ ((ω n).2 j ∈ posSet n (Set.Ioc t s)) := by
      rw [Filter.eventually_all_finset]
      intro n _
      rw [Filter.eventually_all_finset]
      intro j _
      by_cases hp : t < (n : ℝ) + (ω n).2 j
      · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hp)] with s hs
        rintro ⟨_, _, h2⟩
        exact absurd h2 (not_le.mpr hs)
      · exact Filter.Eventually.of_forall (fun s hmem => hp hmem.2.1)
    filter_upwards [h1, h3] with s hs1 hs3
    have hsub : Icc ⌊t⌋ ⌊s⌋ ⊆ S0 := by
      rw [hS0]
      refine Finset.Icc_subset_Icc le_rfl ?_
      have : ⌊s⌋ ≤ ⌊t + 1⌋ := Int.floor_mono hs1.le
      rwa [Int.floor_add_one] at this
    rw [← C_eq_sum hsub]
    apply Finset.sum_eq_zero
    intro n hn
    unfold ccount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hj
    exact hs3 n hn j hj
  obtain ⟨u, hu, hsub⟩ := (nhdsGE_basis_Ico t).eventually_iff.mp hev
  refine ⟨u - t, by linarith, fun s hts hs => ?_⟩
  have h := hsub ⟨hts, by linarith⟩
  have := Nf_sub hts ω
  rw [h] at this
  simp at this
  linarith

/-- The pullback of a product σ-algebra is below `m` when every coordinate is `m`-measurable. -/
lemma comap_pi_le {Ω ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] (F : Ω → ∀ i, X i)
    (m : MeasurableSpace Ω) (h : ∀ i, Measurable[m] (fun ω => F ω i)) :
    MeasurableSpace.comap F MeasurableSpace.pi ≤ m := by
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_le (fun i => ?_)
  rw [MeasurableSpace.comap_comp]
  exact (h i).comap_le

/-- Counts on the past of `s` are independent of the count on `(s, t]`. -/
theorem indep_past {x : ℝ} (hx : 0 ≤ x) {s t : ℝ} (hst : s ≤ t) (T : Finset ℝ) (hsT : s ∈ T)
    (hT : ∀ y ∈ T, y ≤ s) :
    Indep (MeasurableSpace.comap (fun ω (y : T) => C ω (T.min' ⟨s, hsT⟩) y)
        MeasurableSpace.pi)
      (MeasurableSpace.comap (fun ω => C ω s t) (inferInstance : MeasurableSpace ℕ)) (nuc x) := by
  haveI := isProbabilityMeasure_nuc hx
  set q0 := T.min' ⟨s, hsT⟩ with hq0
  have hm : 0 < T.card := Finset.card_pos.mpr ⟨s, hsT⟩
  set m := T.card with hmdef
  set e := T.orderEmbOfFin (k := m) rfl with he
  set e' : ℕ → ℝ := fun i => if h : i < m then e ⟨i, h⟩ else t with he'
  have he0 : e' 0 = q0 := by
    simp only [he', dif_pos hm, he, hq0]
    rw [Finset.orderEmbOfFin_zero rfl hm]
  have hmax : T.max' ⟨s, hsT⟩ = s :=
    le_antisymm (Finset.max'_le _ _ _ hT) (Finset.le_max' _ _ hsT)
  have helast : e' (m - 1) = s := by
    simp only [he', dif_pos (Nat.sub_lt hm Nat.one_pos), he]
    rw [Finset.orderEmbOfFin_last rfl hm]
    exact hmax
  have hem : e' m = t := by simp [he']
  have hmono : ∀ i j, i ≤ j → j ≤ m → e' i ≤ e' j := by
    intro i j hij hjm
    rcases Nat.lt_or_ge j m with hj | hj
    · have hi : i < m := lt_of_le_of_lt hij hj
      simp only [he', dif_pos hi, dif_pos hj]
      exact e.monotone (Fin.mk_le_mk.mpr hij)
    · have hjm' : j = m := le_antisymm hjm hj
      rcases Nat.lt_or_ge i m with hi | hi
      · rw [hjm', hem]
        simp only [he', dif_pos hi]
        exact (hT _ (Finset.orderEmbOfFin_mem T rfl _)).trans hst
      · have : i = m := le_antisymm (hij.trans hjm) hi
        rw [this, hjm']
  have hab : ∀ l : Fin m, e' l ≤ e' (l + 1) := fun l => hmono _ _ (Nat.le_succ _) l.2
  have hdisj : Pairwise (fun l l' : Fin m =>
      Disjoint (Set.Ioc (e' l) (e' (l + 1))) (Set.Ioc (e' l') (e' (l' + 1)))) := by
    intro l l' hne
    have hne' : l.1 ≠ l'.1 := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with h | h
    · have := hmono (l.1 + 1) l'.1 h (le_of_lt l'.2)
      exact Set.disjoint_left.mpr (fun y hy hy' => by
        have := hy.2; have := hy'.1; linarith)
    · have := hmono (l'.1 + 1) l.1 h (le_of_lt l.2)
      exact Set.disjoint_left.mpr (fun y hy hy' => by
        have := hy.1; have := hy'.2; linarith)
  have hD := iIndep_intervals hx (fun l : Fin m => e' l) (fun l => e' (l + 1)) hab hdisj
  set P : Finset (Fin m) := univ.filter (fun l : Fin m => l.1 < m - 1) with hP
  set lastF : Fin m := ⟨m - 1, Nat.sub_lt hm Nat.one_pos⟩ with hlastF
  have hPQ : Disjoint P {lastF} := by
    rw [Finset.disjoint_singleton_right, hP, Finset.mem_filter]
    intro h; simp [hlastF] at h
  have hIPQ := hD.indepFun_finset P {lastF} hPQ (fun l => measurable_C _ _)
  rw [IndepFun_iff_Indep] at hIPQ
  refine indep_of_indep_of_le hIPQ ?_ ?_
  · -- the past vector is a function of the counts indexed by `P`
    refine comap_pi_le _ _ (fun y => ?_)
    have hy : (y : ℝ) ∈ Set.range e := by
      rw [he, Finset.range_orderEmbOfFin]; exact y.2
    obtain ⟨j, hj⟩ := hy
    have hsum : ∀ i ≤ m, ∀ ω, C ω (e' 0) (e' i) = ∑ i' ∈ range i, C ω (e' i') (e' (i' + 1)) := by
      intro i
      induction i with
      | zero => intro _ ω; simp [C_self]
      | succ i ih =>
        intro hi ω
        rw [Finset.sum_range_succ, ← ih (Nat.le_of_succ_le hi) ω,
          C_add ω (hmono 0 i (Nat.zero_le _) (Nat.le_of_succ_le hi))
            (hmono i (i + 1) (Nat.le_succ _) hi)]
    have hfun : (fun ω => C ω q0 y) = fun ω => ∑ i' ∈ range j.1, C ω (e' i') (e' (i' + 1)) := by
      funext ω
      have hej : e' j.1 = y := by simp only [he', dif_pos j.2]; exact hj
      rw [← he0, ← hej, hsum j.1 (le_of_lt j.2) ω]
    rw [hfun]
    refine Finset.measurable_sum _ (fun i hi => ?_)
    have hiP : (⟨i, by have := Finset.mem_range.mp hi; omega⟩ : Fin m) ∈ P := by
      rw [hP, Finset.mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have h1 := Finset.mem_range.mp hi
      have h2 : j.1 ≤ m - 1 := Nat.le_sub_one_of_lt j.2
      show i < m - 1
      omega
    have hc : ∀ i' : P, Measurable[MeasurableSpace.comap
        (fun ω (i : P) => C ω (e' ((i : Fin m) : ℕ)) (e' (((i : Fin m) : ℕ) + 1)))
          MeasurableSpace.pi] (fun ω => C ω (e' ((i' : Fin m) : ℕ)) (e' (((i' : Fin m) : ℕ) + 1))) :=
      fun i' => (measurable_pi_apply (X := fun _ : P => ℕ) i').comp (comap_measurable _)
    exact hc ⟨⟨i, _⟩, hiP⟩
  · -- the future count is the last count
    apply Measurable.comap_le
    have hfun : (fun ω => C ω s t)
        = (fun v : ({lastF} : Finset (Fin m)) → ℕ => v ⟨lastF, mem_singleton_self _⟩)
          ∘ (fun ω (i : ({lastF} : Finset (Fin m))) => C ω (e' i) (e' (i + 1))) := by
      funext ω
      simp only [Function.comp_apply, hlastF]
      rw [helast, Nat.sub_add_cancel hm, hem]
    rw [hfun]
    exact (measurable_pi_apply _).comp (comap_measurable _)

/-- Increments after a nonnegative time are independent of the natural filtration. -/
theorem Nf_indep {x : ℝ} (hx : 0 ≤ x) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => Nf t ω - Nf s ω) (inferInstance : MeasurableSpace ℤ))
      (filt s) (nuc x) := by
  haveI := isProbabilityMeasure_nuc hx
  apply Indep.symm
  set G : Finset ℝ → MeasurableSpace Ωc := fun R =>
    MeasurableSpace.comap (fun ω (r : R) => Nf (min (r : ℝ) s) ω) MeasurableSpace.pi with hG
  have hFle : filt s ≤ ⨆ R, G R := by
    show Fseq s ≤ _
    refine iSup₂_le (fun r hr => ?_)
    refine le_iSup_of_le {r} ?_
    apply Measurable.comap_le
    have : Nf r = (fun v : ({r} : Finset ℝ) → ℤ => v ⟨r, mem_singleton_self r⟩)
        ∘ (fun ω (r' : ({r} : Finset ℝ)) => Nf (min (r' : ℝ) s) ω) := by
      funext ω; simp [min_eq_left hr]
    rw [this]; exact (measurable_pi_apply _).comp (comap_measurable _)
  refine indep_of_indep_of_le_left ?_ hFle
  have hincr_m : Measurable (fun ω => Nf t ω - Nf s ω) :=
    (measurable_of_countable (fun p : ℤ × ℤ => p.1 - p.2)).comp
      ((measurable_Nf t).prodMk (measurable_Nf s))
  refine indep_iSup_of_directed_le (fun R => ?_) (fun R => ?_) hincr_m.comap_le ?_
  · set T : Finset ℝ := insert s (insert 0 (R.image (fun r => min r s))) with hT
    have hsT : s ∈ T := mem_insert_self _ _
    have h0T : (0 : ℝ) ∈ T := mem_insert_of_mem (mem_insert_self _ _)
    have hTle : ∀ y ∈ T, y ≤ s := by
      intro y hy
      rw [hT, mem_insert, mem_insert, mem_image] at hy
      rcases hy with rfl | rfl | ⟨r, _, rfl⟩
      · exact le_rfl
      · exact hs
      · exact min_le_right _ _
    have hpast := indep_past hx hst T hsT hTle
    have hq0 : T.min' ⟨s, hsT⟩ ≤ 0 := Finset.min'_le T 0 h0T
    have hq0T : ∀ y ∈ T, T.min' ⟨s, hsT⟩ ≤ y := fun y hy => Finset.min'_le T y hy
    refine indep_of_indep_of_le hpast ?_ ?_
    · refine comap_pi_le _ _ (fun r => ?_)
      have hrT : min (r : ℝ) s ∈ T :=
        mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem _ r.2))
      have : (fun ω => Nf (min (r : ℝ) s) ω)
          = (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2)
            ∘ (fun ω => ((fun ω (y : T) => C ω (T.min' ⟨s, hsT⟩) y) ω ⟨min (r : ℝ) s, hrT⟩,
                (fun ω (y : T) => C ω (T.min' ⟨s, hsT⟩) y) ω ⟨0, h0T⟩)) := by
        funext ω
        simp only [Function.comp_apply]
        exact Nf_eq ω hq0 (hq0T _ hrT)
      have hc : ∀ y : T, Measurable[MeasurableSpace.comap
          (fun ω (y : T) => C ω (T.min' ⟨s, hsT⟩) y) MeasurableSpace.pi]
            (fun ω => C ω (T.min' ⟨s, hsT⟩) y) :=
        fun y => (measurable_pi_apply (X := fun _ : T => ℕ) y).comp (comap_measurable _)
      rw [this]
      exact (measurable_of_countable _).comp ((hc _).prodMk (hc _))
    · apply Measurable.comap_le
      have : (fun ω => Nf t ω - Nf s ω) = (fun n : ℕ => (n : ℤ)) ∘ (fun ω => C ω s t) := by
        funext ω; exact Nf_sub hst ω
      rw [this]
      exact (measurable_of_countable _).comp (comap_measurable _)
  · apply Measurable.comap_le
    exact measurable_pi_lambda _ (fun r => measurable_Nf _)
  · intro R1 R2
    refine ⟨R1 ∪ R2, ?_, ?_⟩
    · refine comap_pi_le _ _ (fun r => ?_)
      have : (fun ω => Nf (min (r : ℝ) s) ω)
          = (fun v : (R1 ∪ R2 : Finset ℝ) → ℤ => v ⟨r, mem_union_left _ r.2⟩)
            ∘ (fun ω (r' : (R1 ∪ R2 : Finset ℝ)) => Nf (min (r' : ℝ) s) ω) := rfl
      rw [this]; exact (measurable_pi_apply _).comp (comap_measurable _)
    · refine comap_pi_le _ _ (fun r => ?_)
      have : (fun ω => Nf (min (r : ℝ) s) ω)
          = (fun v : (R1 ∪ R2 : Finset ℝ) → ℤ => v ⟨r, mem_union_right _ r.2⟩)
            ∘ (fun ω (r' : (R1 ∪ R2 : Finset ℝ)) => Nf (min (r' : ℝ) s) ω) := rfl
      rw [this]; exact (measurable_pi_apply _).comp (comap_measurable _)

/-- The two-sided Poisson model is a demand space. -/
theorem demandSpace_nonempty' (P : Params) : Nonempty (DemandSpace P) :=
  ⟨{ Ω := Ωc
     mΩ := inferInstance
     ν := nuc P.lam
     prob := isProbabilityMeasure_nuc P.lam_nonneg
     𝓕 := filt
     N := Nf
     N_adapted := Nf_adapted
     N_mono := Nf_mono
     N_rcont := Nf_rcont
     N_law := fun s t hst k => by
       have : {ω : Ωc | Nf t ω - Nf s ω = (k : ℤ)} = {ω | C ω s t = k} := by
         ext ω; simp only [Set.mem_setOf_eq, Nf_sub hst ω, Nat.cast_inj]
       rw [this, interval_law_one P.lam_nonneg hst k]
     N_indep := fun s t hs hst => Nf_indep P.lam_nonneg hs hst }⟩

end NE

end TwoStageRnQ

namespace TwoStageRnQ

/-- The demand space is nonempty: the two-sided Poisson counter of rate `λ`
(Poisson number of uniform points in each unit cell, independent cells), with its natural
filtration, satisfies every requirement of `DemandSpace`. -/
theorem _root_.solution (P : Params) : Nonempty (DemandSpace P) :=
  NE.demandSpace_nonempty' P

end TwoStageRnQ
