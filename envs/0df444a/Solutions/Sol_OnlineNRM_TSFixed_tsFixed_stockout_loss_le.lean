-- Prove2me | solution 1 for OnlineNRM.TSFixed.tsFixed_stockout_loss_le
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-17T18:34:18.509852+00:00
-- url     : https://prove2.me/submissions/c07cb89b-c593-415a-badd-fdadc9c4965c

import Mathlib.Probability.Distributions.Bernoulli
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open OnlineNRM.TSFixed
open scoped OnlineNRM.TSFixed

universe u v

set_option maxHeartbeats 1200000

/-
The shortage branch permits throwing away the resource-free, positive-price
product. The two products have prices (0,1), consumption (1,0), inventory 1,
and equiprobable demands (0,1) and (2,1). The LP offers the first price surely.
The fulfilled demands are (0,1) and (1,0). Thus the loss is 1/2, while pjmax=0.

The auxiliary certificate works at arbitrary universe levels. The final solution
uses explicit level zero so applying it to the target determines both levels.
-/
namespace StockoutCounterexample

/-- The fair Bernoulli parameter, with its interval bounds checked explicitly. -/
noncomputable def half : unitInterval := ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

noncomputable def coin {α : Type*} [MeasurableSpace α] (x y : α) : Measure α :=
  bernoulliMeasure x y half

instance coin_probability {α : Type*} [MeasurableSpace α] (x y : α) :
    IsProbabilityMeasure (coin x y) := by
  unfold coin
  infer_instance

lemma integral_coin {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (x y : α) (f : α → ℝ) :
    (∫ z, f z ∂coin x y) = (f x + f y) / 2 := by
  calc
    (∫ z, f z ∂coin x y) =
        (half : ℝ) • f x + (1 - (half : ℝ)) • f y :=
      integral_bernoulliMeasure x y half f
    _ = (f x + f y) / 2 := by
      change (1 / 2 : ℝ) * f x + (1 - 1 / 2 : ℝ) * f y = (f x + f y) / 2
      ring

lemma ae_coin {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (x y : α) (Q : α → Prop) (hx : Q x) (hy : Q y) :
    ∀ᵐ z ∂coin x y, Q z := by
  unfold coin bernoulliMeasure
  apply ae_add_measure_iff.mpr
  constructor
  · exact Measure.ae_smul_measure
      (by simpa only [ae_dirac_eq, Filter.eventually_pure] using hx) _
  · exact Measure.ae_smul_measure
      (by simpa only [ae_dirac_eq, Filter.eventually_pure] using hy) _

lemma condProb_bot_eq {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (S : Set α) (hS : MeasurableSet S) :
    condProb ν ⊥ S = fun _ => (ν S).toReal := by
  classical
  unfold condProb
  rw [condExp_bot]
  have hi : (∫ z, S.indicator (fun _ => (1 : ℝ)) z ∂ν) = (ν S).toReal := by
    simpa only [measureReal_def, smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := ν) (1 : ℝ) hS)
  rw [hi]

def p (i : Fin 2) (_k : Fin 2) : ℝ := if i = 0 then 0 else 1
def a (i : Fin 2) (_j : Fin 1) : ℝ := if i = 0 then 1 else 0
def I (_j : Fin 1) : ℝ := 1
def dbar (i : Fin 2) : ℝ := if i = 0 then 2 else 1

def vec (b : Bool) (i : Fin 2) : ℝ :=
  if i = 0 then (if b then 2 else 0) else 1

def sat (b : Bool) (i : Fin 2) : ℝ :=
  if b then (if i = 0 then 1 else 0) else vec false i

noncomputable def q : Measure (Fin 2 → ℝ) := coin (vec false) (vec true)

instance q_probability : IsProbabilityMeasure q := by
  classical
  unfold q
  infer_instance

noncomputable def F : Kernel (PUnit.{u+1} × Fin 2) (Fin 2 → ℝ) :=
  Kernel.const _ q

instance F_markov : IsMarkovKernel F.{u} := by
  classical
  unfold F
  infer_instance

noncomputable def P : Measure (Bool × PUnit.{v+1}) :=
  coin (false, PUnit.unit) (true, PUnit.unit)

instance P_probability : IsProbabilityMeasure P.{v} := by
  classical
  unfold P
  infer_instance

def θ : (Bool × PUnit.{v+1}) → PUnit.{u+1} := fun _ => PUnit.unit
def θs : ℕ → (Bool × PUnit.{v+1}) → PUnit.{u+1} := fun _ _ => PUnit.unit
def A : ℕ → (Bool × PUnit.{v+1}) → Option (Fin 2) := fun _ _ => some 0
def D : ℕ → (Bool × PUnit.{v+1}) → Fin 2 → ℝ := fun _ ω => vec ω.1
def Dsat : ℕ → (Bool × PUnit.{v+1}) → Fin 2 → ℝ := fun _ ω => sat ω.1
def xsel : PUnit.{u+1} → Fin 2 → ℝ := fun _ k => if k = 0 then 1 else 0

lemma comap_θ :
    MeasurableSpace.comap (θ : (Bool × PUnit.{v+1}) → PUnit.{u+1}) inferInstance = ⊥ := by
  exact MeasurableSpace.comap_const (PUnit.unit : PUnit.{u+1})

lemma comap_θs (t : ℕ) :
    MeasurableSpace.comap (θs t : (Bool × PUnit.{v+1}) → PUnit.{u+1}) inferInstance = ⊥ := by
  exact MeasurableSpace.comap_const (PUnit.unit : PUnit.{u+1})

lemma comap_A (t : ℕ) :
    MeasurableSpace.comap (A t : (Bool × PUnit.{v+1}) → Option (Fin 2)) inferInstance = ⊥ := by
  exact MeasurableSpace.comap_const (some (0 : Fin 2))

lemma past_zero :
    pastSigma (θ : (Bool × PUnit.{v+1}) → PUnit.{u+1}) θs A D 0 = ⊥ := by
  simp only [pastSigma, comap_θ, Nat.not_lt_zero, iSup_false, iSup_bot, sup_bot_eq]

lemma hist_zero : histSigma (A : ℕ → (Bool × PUnit.{v+1}) → Option (Fin 2)) D 0 = ⊥ := by
  simp only [histSigma, Nat.not_lt_zero, iSup_false, iSup_bot]

lemma D_law : P.{v}.map (D 0) = q := by
  exact map_bernoulliMeasure (false, (PUnit.unit : PUnit.{v+1}))
    (true, PUnit.unit) (D 0) half

lemma hp : ∀ i k, 0 ≤ p i k := by
  classical
  intro i k
  unfold p
  split_ifs <;> norm_num

lemma ha : ∀ i j, 0 ≤ a i j := by
  classical
  intro i j
  unfold a
  split_ifs <;> norm_num

lemma hI : ∀ j, 0 ≤ I j := by
  classical
  intro j
  norm_num [I]

lemma bounded : ∀ (ρ : PUnit.{u+1}) (k : Fin 2),
    ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i) := by
  classical
  intro ρ k
  unfold F
  rw [Kernel.const_apply]
  unfold q
  apply ae_coin
  · intro i
    fin_cases i <;> norm_num [vec, dbar]
  · intro i
    fin_cases i <;> norm_num [vec, dbar]

lemma mean_F (ρ : PUnit.{u+1}) : meanDemand F ρ = (fun _ _ => 1) := by
  classical
  funext i k
  change (∫ x : Fin 2 → ℝ, x i ∂q) = 1
  rw [q, integral_coin]
  fin_cases i <;> norm_num [vec]

lemma optimal (ρ : PUnit.{u+1}) :
    IsLPOptimal p a (meanDemand F ρ) (fun j => I j / (1 : ℝ)) (xsel ρ) := by
  classical
  rw [mean_F]
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro j
      norm_num [a, I, xsel, Fin.sum_univ_two]
    · norm_num [xsel, Fin.sum_univ_two]
    · intro k
      fin_cases k <;> norm_num [xsel]
  · intro y hy
    have hys : y 0 + y 1 ≤ 1 := by
      simpa only [Fin.sum_univ_two] using hy.2.1
    simpa [lpObj, p, xsel, Fin.sum_univ_two] using hys

lemma run : IsTSFixedRun p a I F (Measure.dirac (PUnit.unit : PUnit.{u+1})) 1
    P.{v} θ θs A D Dsat xsel := by
  classical
  refine
    { measurable_θ := measurable_const
      measurable_θs := fun _ => measurable_const
      measurable_A := fun _ => measurable_const
      measurable_D := fun _ => measurable_of_finite _
      measurable_Dsat := fun _ => measurable_of_finite _
      measurable_xsel := measurable_const
      prior := ?_
      posterior_sample := ?_
      lp_optimal := ?_
      offer_price := ?_
      demand := ?_
      fulfilment := ?_ }
  · change P.{v}.map (fun _ : Bool × PUnit.{v+1} =>
      (PUnit.unit : PUnit.{u+1})) = Measure.dirac PUnit.unit
    rw [Measure.map_const]
    simp only [measure_univ, one_smul]
  · intro t ht C hC
    have ht0 : t = 0 := by omega
    subst t
    rw [past_zero, hist_zero]
    exact Filter.EventuallyEq.rfl
  · intro ρ
    simpa using optimal ρ
  · intro t ht k
    have ht0 : t = 0 := by omega
    subst t
    rw [past_zero, comap_θs, bot_sup_eq]
    rw [condProb_bot_eq P.{v} _ ((measurable_of_finite (A 0)) (measurableSet_singleton _))]
    apply Filter.Eventually.of_forall
    intro ω
    change (P.{v} ((fun _ : Bool × PUnit.{v+1} => some (0 : Fin 2)) ⁻¹'
      {some k})).toReal = (if k = 0 then 1 else 0)
    fin_cases k <;> norm_num
  · intro t ht B hB
    have ht0 : t = 0 := by omega
    subst t
    have hm : pastSigma (θ : (Bool × PUnit.{v+1}) → PUnit.{u+1}) θs A D 0 ⊔
        MeasurableSpace.comap (θs 0 : (Bool × PUnit.{v+1}) → PUnit.{u+1}) inferInstance ⊔
        MeasurableSpace.comap (A 0) inferInstance = ⊥ := by
      rw [past_zero, comap_θs, comap_A, bot_sup_eq, bot_sup_eq]
    rw [hm, condProb_bot_eq P.{v} _ ((measurable_of_finite (D 0)) hB)]
    apply Filter.Eventually.of_forall
    intro ω
    change (P.{v} (D 0 ⁻¹' B)).toReal = (q B).toReal
    have hmap := congrArg (fun ν : Measure (Fin 2 → ℝ) => ν B) D_law.{v}
    rw [Measure.map_apply (measurable_of_finite (D 0)) hB] at hmap
    exact congrArg ENNReal.toReal hmap
  · intro t ht
    have ht0 : t = 0 := by omega
    subst t
    apply Filter.Eventually.of_forall
    rintro ⟨b, z⟩
    cases b <;>
      norm_num [FulfilmentRule, D, Dsat, vec, sat, a, I, inventory,
        Fin.sum_univ_two, Fin.forall_fin_two] <;> rfl

lemma pjmax_zero (j : Fin 1) : pjmax p a j = 0 := by
  classical
  unfold pjmax
  split_ifs with h
  · apply Finset.sup'_eq_of_forall
    rintro ⟨i, k⟩ hik
    have hi : a i j ≠ 0 := (Finset.mem_filter.mp hik).2
    by_cases h0 : i = 0
    · simp [p, h0]
    · exact False.elim (hi (by simp [a, h0]))
  · rfl

lemma loss :
    (∫ ω, revenue p A D 1 ω ∂P.{v}) - (∫ ω, revenue p A Dsat 1 ω ∂P.{v}) =
      (1 : ℝ) / 2 := by
  classical
  norm_num [P, integral_coin, revenue, Fin.sum_univ_two, postedPrice,
    A, D, Dsat, vec, sat, p]

end StockoutCounterexample

/-- Negation of the entire target proposition, including both type parameters. -/
theorem stockout_loss_counterexample :
    ¬ (∀ {N M K T : ℕ} (hK : 2 ≤ K) (hT : 1 ≤ T)
      (p : Fin N → Fin K → ℝ) (a : Fin N → Fin M → ℝ) (I : Fin M → ℝ)
      (dbar : Fin N → ℝ)
      (hp : ∀ i k, 0 ≤ p i k) (ha : ∀ i j, 0 ≤ a i j) (hI : ∀ j, 0 ≤ I j)
      {Θ : Type u} [MeasurableSpace Θ] [StandardBorelSpace Θ]
      (μ₀ : Measure Θ) [IsProbabilityMeasure μ₀]
      (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
      (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
      {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (θ : Ω → Θ) (θs : ℕ → Ω → Θ) (A : ℕ → Ω → Option (Fin K))
      (D Dsat : ℕ → Ω → Fin N → ℝ) (xsel : Θ → Fin K → ℝ)
      (hrun : IsTSFixedRun p a I F μ₀ T P θ θs A D Dsat xsel),
      (∫ ω, revenue p A D T ω ∂P) - (∫ ω, revenue p A Dsat T ω ∂P) ≤
        37 * (∑ i : Fin N, ∑ j : Fin M, pjmax p a j * a i j * dbar i) *
          Real.sqrt ((T : ℝ) * K * Real.log K)) := by
  classical
  intro h
  have hb := h (N := 2) (M := 1) (K := 2) (T := 1) (by decide) (by decide)
    StockoutCounterexample.p StockoutCounterexample.a StockoutCounterexample.I
    StockoutCounterexample.dbar StockoutCounterexample.hp StockoutCounterexample.ha
    StockoutCounterexample.hI
    (Θ := PUnit.{u+1}) (Measure.dirac PUnit.unit)
    StockoutCounterexample.F StockoutCounterexample.bounded
    (Ω := Bool × PUnit.{v+1}) StockoutCounterexample.P
    StockoutCounterexample.θ StockoutCounterexample.θs StockoutCounterexample.A
    StockoutCounterexample.D StockoutCounterexample.Dsat StockoutCounterexample.xsel
    StockoutCounterexample.run
  rw [StockoutCounterexample.loss] at hb
  norm_num [StockoutCounterexample.pjmax_zero] at hb

/-- The full quantified target is false already for types in universe zero. -/
theorem solution :
    ¬ (∀ {N M K T : ℕ} (hK : 2 ≤ K) (hT : 1 ≤ T)
      (p : Fin N → Fin K → ℝ) (a : Fin N → Fin M → ℝ) (I : Fin M → ℝ)
      (dbar : Fin N → ℝ)
      (hp : ∀ i k, 0 ≤ p i k) (ha : ∀ i j, 0 ≤ a i j) (hI : ∀ j, 0 ≤ I j)
      {Θ : Type 0} [MeasurableSpace Θ] [StandardBorelSpace Θ]
      (μ₀ : Measure Θ) [IsProbabilityMeasure μ₀]
      (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
      (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
      {Ω : Type 0} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (θ : Ω → Θ) (θs : ℕ → Ω → Θ) (A : ℕ → Ω → Option (Fin K))
      (D Dsat : ℕ → Ω → Fin N → ℝ) (xsel : Θ → Fin K → ℝ)
      (hrun : IsTSFixedRun p a I F μ₀ T P θ θs A D Dsat xsel),
      (∫ ω, revenue p A D T ω ∂P) - (∫ ω, revenue p A Dsat T ω ∂P) ≤
        37 * (∑ i : Fin N, ∑ j : Fin M, pjmax p a j * a i j * dbar i) *
          Real.sqrt ((T : ℝ) * K * Real.log K)) := by
  exact stockout_loss_counterexample.{0, 0}
