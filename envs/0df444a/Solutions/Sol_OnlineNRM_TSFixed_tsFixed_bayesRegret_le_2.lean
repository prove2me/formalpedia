-- Prove2me | solution 2 for OnlineNRM.TSFixed.tsFixed_bayesRegret_le
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-17T18:53:42.128887+00:00
-- url     : https://prove2.me/submissions/70f54301-949c-4bd0-977e-d7b8423fab74

import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

/-
There are 2048 resource-consuming products of price zero and one product
of price one which uses no resources. Each period selects one of the
zero-price products uniformly and demands two units of it. Each resource
has inventory one. The additional, unused resource has inventory zero.
Every period is a shortage, so zero fulfilment satisfies the exact rule:
the unused resource is already exhausted. The LP nevertheless has value one.
-/
namespace RootCounterexample

abbrev Outcome := Fin 1024 → Fin 2048

def p (i : Fin 2049) (_k : Fin 2) : ℝ := if i = 0 then 1 else 0
def a (i j : Fin 2049) : ℝ := if i = j ∧ j ≠ 0 then 1 else 0
def I (j : Fin 2049) : ℝ := if j = 0 then 0 else 1
def dbar (i : Fin 2049) : ℝ := if i = 0 then 1 else 2

def vec (r : Fin 2048) (i : Fin 2049) : ℝ :=
  if i = 0 then 1 else if i = r.succ then 2 else 0

noncomputable def uniform : Measure (Fin 2048) :=
  (PMF.uniformOfFintype (Fin 2048)).toMeasure

instance uniform_probability : IsProbabilityMeasure uniform := by
  unfold uniform
  infer_instance

noncomputable def q : Measure (Fin 2049 → ℝ) := uniform.map vec

instance q_probability : IsProbabilityMeasure q :=
  Measure.isProbabilityMeasure_map (measurable_of_finite vec).aemeasurable

noncomputable def F : Kernel (Unit × Fin 2) (Fin 2049 → ℝ) := Kernel.const _ q

instance F_markov : IsMarkovKernel F := by
  unfold F
  infer_instance

noncomputable def P : Measure Outcome := Measure.pi (fun _ : Fin 1024 => uniform)

instance P_probability : IsProbabilityMeasure P := by
  unfold P
  infer_instance

def θ : Outcome → Unit := fun _ => ()
def θs : ℕ → Outcome → Unit := fun _ _ => ()
def A : ℕ → Outcome → Option (Fin 2) := fun _ _ => some 0
def index (t : ℕ) : Fin 1024 := ⟨t % 1024, Nat.mod_lt _ (by decide)⟩
def D (t : ℕ) (ω : Outcome) : Fin 2049 → ℝ := vec (ω (index t))
def Dsat : ℕ → Outcome → Fin 2049 → ℝ := fun _ _ _ => 0
def xsel : Unit → Fin 2 → ℝ := fun _ k => if k = 0 then 1 else 0
def X (u : Fin 1024) (ω : Outcome) : Fin 2049 → ℝ := vec (ω u)

lemma hp : ∀ i k, 0 ≤ p i k := by
  intro i k
  unfold p
  split_ifs <;> norm_num

lemma ha : ∀ i j, 0 ≤ a i j := by
  intro i j
  unfold a
  split_ifs <;> norm_num

lemma hI : ∀ j, 0 ≤ I j := by
  intro j
  unfold I
  split_ifs <;> norm_num

lemma vec_bounds (r : Fin 2048) (i : Fin 2049) :
    vec r i ∈ Set.Icc 0 (dbar i) := by
  unfold vec dbar
  split_ifs <;> norm_num

lemma bounded : ∀ (ρ : Unit) (k : Fin 2),
    ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i) := by
  intro ρ k
  change ∀ᵐ x ∂uniform.map vec, ∀ i, x i ∈ Set.Icc 0 (dbar i)
  have hr := ae_map_mem_range vec (Set.finite_range vec).measurableSet uniform
  filter_upwards [hr] with x hx
  obtain ⟨r, rfl⟩ := hx
  exact vec_bounds r

lemma mean_F (ρ : Unit) :
    meanDemand F ρ = fun i _ => if i = 0 then 1 else (1 : ℝ) / 1024 := by
  funext i k
  change (∫ x : Fin 2049 → ℝ, x i ∂uniform.map vec) = _
  rw [integral_map (measurable_of_finite vec).aemeasurable
    (measurable_pi_apply i).aestronglyMeasurable]
  rw [uniform, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat, smul_eq_mul]
  refine Fin.cases ?_ (fun j => ?_) i
  · norm_num [vec]
  · norm_num [vec, Fin.succ_ne_zero, Fin.succ_inj, eq_comm, mul_ite]

lemma consumption_left (v : Fin 2049 → ℝ) (j : Fin 2049) :
    (∑ i : Fin 2049, a i j * v i) = if j = 0 then 0 else v j := by
  classical
  by_cases hj : j = 0
  · simp [a, hj]
  · simp [a, hj, ite_mul]

lemma consumption_right (v : Fin 2049 → ℝ) (j : Fin 2049) :
    (∑ i : Fin 2049, v i * a i j) = if j = 0 then 0 else v j := by
  simpa only [mul_comm] using consumption_left v j

lemma priced_sum (v : Fin 2049 → ℝ) (k : Fin 2) :
    (∑ i : Fin 2049, p i k * v i) = v 0 := by
  classical
  simp [p, ite_mul]

lemma objective (ρ : Unit) (y : Fin 2 → ℝ) :
    lpObj p (meanDemand F ρ) y = y 0 + y 1 := by
  classical
  have hc (k : Fin 2) : (∑ i : Fin 2049, p i k * meanDemand F ρ i k) = 1 := by
    calc
      (∑ i : Fin 2049, p i k * meanDemand F ρ i k) = meanDemand F ρ 0 k :=
        priced_sum (fun i => meanDemand F ρ i k) k
      _ = 1 := by
        rw [mean_F]
        norm_num
  simp only [lpObj, hc, one_mul, Fin.sum_univ_two]

lemma optimal (ρ : Unit) :
    IsLPOptimal p a (meanDemand F ρ) (fun j => I j / (1024 : ℝ)) (xsel ρ) := by
  classical
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro j
      simp only [consumption_left]
      rw [mean_F]
      by_cases hj : j = 0 <;>
        norm_num [I, xsel, hj, Fin.sum_univ_two]
    · norm_num [xsel, Fin.sum_univ_two]
    · intro k
      unfold xsel
      split_ifs <;> norm_num
  · intro y hy
    rw [objective, objective]
    have hys : y 0 + y 1 ≤ 1 := by
      simpa only [Fin.sum_univ_two] using hy.2.1
    simpa [xsel] using hys

lemma opt_value (ρ : Unit) :
    lpOpt p a (meanDemand F ρ) (fun j => I j / (1024 : ℝ)) = 1 := by
  classical
  have hx : lpObj p (meanDemand F ρ) (xsel ρ) = 1 := by
    norm_num [objective, xsel]
  have hmem : (1 : ℝ) ∈ lpObj p (meanDemand F ρ) ''
      {y | lpFeasible a (meanDemand F ρ) (fun j => I j / (1024 : ℝ)) y} :=
    ⟨xsel ρ, (optimal ρ).1, hx⟩
  have hbound : ∀ z ∈ lpObj p (meanDemand F ρ) ''
      {y | lpFeasible a (meanDemand F ρ) (fun j => I j / (1024 : ℝ)) y}, z ≤ 1 := by
    rintro z ⟨y, hy, rfl⟩
    simpa only [hx] using (optimal ρ).2 y hy
  exact le_antisymm (csSup_le ⟨1, hmem⟩ hbound) (le_csSup ⟨1, hbound⟩ hmem)

lemma D_eq_X (t : ℕ) (ht : t < 1024) : D t = X ⟨t, ht⟩ := by
  have he : index t = (⟨t, ht⟩ : Fin 1024) := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt ht
  funext ω i
  change vec (ω (index t)) i = vec (ω ⟨t, ht⟩) i
  rw [he]

lemma measurable_D (t : ℕ) : Measurable (D t) :=
  (measurable_of_finite vec).comp (measurable_pi_apply (index t))

lemma measurable_X (u : Fin 1024) : Measurable (X u) :=
  (measurable_of_finite vec).comp (measurable_pi_apply u)

lemma independent_X : iIndepFun X P := by
  exact iIndepFun_pi (X := fun _ : Fin 1024 => vec)
    (fun _ => (measurable_of_finite vec).aemeasurable)

lemma X_law (u : Fin 1024) : P.map (X u) = q := by
  change P.map (vec ∘ Function.eval u) = uniform.map vec
  rw [← Measure.map_map (measurable_of_finite vec) (measurable_pi_apply u)]
  congr 1
  exact (measurePreserving_eval (fun _ : Fin 1024 => uniform) u).map_eq

lemma hist_le (t : ℕ) : histSigma A D t ≤ (inferInstance : MeasurableSpace Outcome) := by
  unfold histSigma
  exact iSup_le fun s => iSup_le fun _ =>
    sup_le measurable_const.comap_le (measurable_D s).comap_le

lemma comap_θ : MeasurableSpace.comap θ inferInstance = ⊥ :=
  MeasurableSpace.comap_const ()

lemma comap_θs (t : ℕ) : MeasurableSpace.comap (θs t) inferInstance = ⊥ :=
  MeasurableSpace.comap_const ()

lemma comap_A (t : ℕ) : MeasurableSpace.comap (A t) inferInstance = ⊥ :=
  MeasurableSpace.comap_const (some (0 : Fin 2))

lemma past_eq_hist (t : ℕ) : pastSigma θ θs A D t = histSigma A D t := by
  simp only [pastSigma, histSigma, comap_θ, comap_θs, bot_sup_eq]

lemma before_le (t : ℕ) (ht : t < 1024) :
    histSigma A D t ≤
      ⨆ u : Fin 1024, ⨆ (_ : u.val < t), MeasurableSpace.comap (X u) inferInstance := by
  unfold histSigma
  refine iSup_le fun s => iSup_le fun hs => ?_
  have hsT : s < 1024 := lt_trans hs ht
  rw [show A s = fun _ : Outcome => some (0 : Fin 2) from rfl,
    MeasurableSpace.comap_const, bot_sup_eq, D_eq_X s hsT]
  exact le_iSup_of_le ⟨s, hsT⟩ (le_iSup_of_le hs le_rfl)

lemma demand_independent (t : ℕ) (ht : t < 1024) :
    Indep (MeasurableSpace.comap (D t) inferInstance) (histSigma A D t) P := by
  have hd : Disjoint ({(⟨t, ht⟩ : Fin 1024)} : Set (Fin 1024)) {u | u.val < t} := by
    apply Set.disjoint_left.mpr
    intro u hu hlt
    have he : u = (⟨t, ht⟩ : Fin 1024) := Set.mem_singleton_iff.mp hu
    subst u
    exact (lt_irrefl t) hlt
  have hi := indep_iSup_of_disjoint (fun u => (measurable_X u).comap_le)
    independent_X.iIndep hd
  have hi' : Indep (MeasurableSpace.comap (X ⟨t, ht⟩) inferInstance)
      (⨆ u : Fin 1024, ⨆ (_ : u.val < t),
        MeasurableSpace.comap (X u) inferInstance) P := by
    simpa only [iSup_singleton, Set.mem_setOf_eq] using hi
  rw [D_eq_X t ht]
  exact indep_of_indep_of_le_right hi' (before_le t ht)

lemma demand_condProb (t : ℕ) (ht : t < 1024)
    (B : Set (Fin 2049 → ℝ)) (hB : MeasurableSet B) :
    condProb P (histSigma A D t) (D t ⁻¹' B) =ᵐ[P] fun _ => (q B).toReal := by
  have hme : MeasurableSet[MeasurableSpace.comap (D t) inferInstance] (D t ⁻¹' B) :=
    (comap_measurable (D t)) hB
  have hf : StronglyMeasurable[MeasurableSpace.comap (D t) inferInstance]
      ((D t ⁻¹' B).indicator (fun _ : Outcome => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator hme
  have hc := condExp_indep_eq (measurable_D t).comap_le (hist_le t)
    hf (demand_independent t ht)
  have hmass : P (D t ⁻¹' B) = q B := by
    rw [← Measure.map_apply (measurable_D t) hB, D_eq_X t ht, X_law]
  have hint : (∫ ω, (D t ⁻¹' B).indicator (fun _ : Outcome => (1 : ℝ)) ω ∂P) =
      (q B).toReal := by
    simpa only [measureReal_def, hmass, smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := P) (1 : ℝ) ((measurable_D t) hB))
  simpa only [condProb, hint] using hc

open scoped Classical in
lemma condProb_const_event (t : ℕ)
    {β : Type*} (c : β) (C : Set β) :
    condProb P (histSigma A D t) ((fun _ : Outcome => c) ⁻¹' C) =
      fun _ => if c ∈ C then (1 : ℝ) else 0 := by
  classical
  have he : ((fun _ : Outcome => c) ⁻¹' C).indicator (fun _ => (1 : ℝ)) =
      fun _ => if c ∈ C then (1 : ℝ) else 0 := by
    funext ω
    by_cases h : c ∈ C <;> simp [h]
  unfold condProb
  rw [he, condExp_const (hist_le t)]

lemma inventory_eq (t : ℕ) (ω : Outcome) (j : Fin 2049) :
    inventory a I Dsat t ω j = I j := by
  induction t with
  | zero => rfl
  | succ t ih => simp [inventory, Dsat, ih]

lemma fulfilment (t : ℕ) (ω : Outcome) : FulfilmentRule a I D Dsat t ω := by
  classical
  have hn : ¬ ∀ j : Fin 2049,
      ∑ i : Fin 2049, D t ω i * a i j ≤ inventory a I Dsat t ω j := by
    intro h
    have hbad := h (ω (index t)).succ
    rw [consumption_right, inventory_eq] at hbad
    norm_num [D, vec, I, Fin.succ_ne_zero] at hbad
  rw [FulfilmentRule, if_neg hn]
  refine ⟨?_, ?_, ⟨0, ?_⟩⟩
  · intro i
    exact ⟨le_rfl, (vec_bounds (ω (index t)) i).1⟩
  · intro j
    rw [inventory_eq]
    exact hI j
  · simp [inventory_eq, I]

lemma run : IsTSFixedRun p a I F (Measure.dirac ()) 1024 P θ θs A D Dsat xsel := by
  classical
  refine
    { measurable_θ := measurable_const
      measurable_θs := fun _ => measurable_const
      measurable_A := fun _ => measurable_const
      measurable_D := measurable_D
      measurable_Dsat := fun _ => measurable_const
      measurable_xsel := measurable_const
      prior := ?_
      posterior_sample := ?_
      lp_optimal := optimal
      offer_price := ?_
      demand := ?_
      fulfilment := fun t _ => Filter.Eventually.of_forall (fulfilment t) }
  · change P.map (fun _ : Outcome => ()) = Measure.dirac ()
    rw [Measure.map_const]
    simp only [measure_univ, one_smul]
  · intro t ht C hC
    rw [past_eq_hist]
    exact Filter.EventuallyEq.rfl
  · intro t ht k
    rw [past_eq_hist, comap_θs, sup_bot_eq]
    rw [show A t = fun _ : Outcome => some (0 : Fin 2) from rfl,
      condProb_const_event t]
    apply Filter.Eventually.of_forall
    intro ω
    simp [xsel, eq_comm]
  · intro t ht B hB
    rw [past_eq_hist, comap_θs, comap_A, sup_bot_eq, sup_bot_eq]
    simpa only [θ, A, demandLaw, F, Kernel.const_apply] using demand_condProb t ht B hB

lemma pmax_eq : pmax p dbar = 1 := by
  classical
  unfold pmax
  split_ifs with h
  · apply Finset.sup'_eq_of_forall
    intro k hk
    exact (priced_sum dbar k).trans (by norm_num [dbar])
  · exact False.elim (h ⟨0, Finset.mem_univ _⟩)

lemma pjmax_eq (j : Fin 2049) : pjmax p a j = 0 := by
  classical
  unfold pjmax
  split_ifs with h
  · apply Finset.sup'_eq_of_forall
    rintro ⟨i, k⟩ hik
    have hai : a i j ≠ 0 := (Finset.mem_filter.mp hik).2
    have hij : i = j ∧ j ≠ 0 := by
      by_contra hh
      exact hai (by simp [a, hh])
    have hi : i ≠ 0 := by simpa only [hij.1] using hij.2
    simp [p, hi]
  · rfl

lemma regret_eq : lpBayesRegret p a I F 1024 P θ A Dsat = 1024 := by
  simp [lpBayesRegret, opt_value, revenue, Dsat]

lemma numerical_contradiction :
    ¬ (1024 : ℝ) ≤ 18 * Real.sqrt ((1024 : ℝ) * 2 * Real.log 2) := by
  have hl : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hs : Real.sqrt ((1024 : ℝ) * 2 * Real.log 2) < 50 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 50)).2
    nlinarith
  linarith

end RootCounterexample

/-- Negation of the whole target proposition, including all hypotheses. -/
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
      lpBayesRegret p a I F T P θ A Dsat ≤
        (18 * pmax p dbar + 37 * ∑ i : Fin N, ∑ j : Fin M,
          pjmax p a j * a i j * dbar i) *
          Real.sqrt ((T : ℝ) * K * Real.log K)) := by
  classical
  intro h
  have hb := h (N := 2049) (M := 2049) (K := 2) (T := 1024)
    (by decide) (by decide) RootCounterexample.p RootCounterexample.a
    RootCounterexample.I RootCounterexample.dbar RootCounterexample.hp
    RootCounterexample.ha RootCounterexample.hI
    (Θ := Unit) (Measure.dirac ()) RootCounterexample.F RootCounterexample.bounded
    (Ω := RootCounterexample.Outcome) RootCounterexample.P RootCounterexample.θ
    RootCounterexample.θs RootCounterexample.A RootCounterexample.D
    RootCounterexample.Dsat RootCounterexample.xsel RootCounterexample.run
  rw [RootCounterexample.regret_eq, RootCounterexample.pmax_eq] at hb
  simp only [RootCounterexample.pjmax_eq, zero_mul, Finset.sum_const_zero,
    mul_zero, add_zero, mul_one, Nat.cast_ofNat] at hb
  exact RootCounterexample.numerical_contradiction hb
