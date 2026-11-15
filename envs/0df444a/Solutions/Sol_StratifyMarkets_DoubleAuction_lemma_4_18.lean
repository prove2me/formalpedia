-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.lemma_4_18
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:50:22.860187+00:00
-- url     : https://prove2.me/submissions/a7afc293-1c22-4fb3-a8c1-85cc3a7e9339

import Definitions.Def_StratifyMarkets_DoubleAuction_Prices
import Definitions.Def_StratifyMarkets_DoubleAuction_Submarket
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Mathlib
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_17
import Theorems.Thm_StratifyMarkets_DoubleAuction_theorem_3_1
import Theorems.Thm_StratifyMarkets_DoubleAuction_theorem_4_2

set_option autoImplicit false

-- Solutions.StratifyMarketsSubintervals
section
open MeasureTheory Set
namespace StratifyMarkets.DoubleAuction

theorem buyer_threshold {n m : ℕ} (I : DAInstance n m) {p b : ℝ} (hp : p ≤ b)
    (h : 1 / 4 ≤ I.expBuyersIn p b) : ∃ t ∈ Icc p b, I.expBuyersIn t b = 1 / 4 := by
  have hc : ContinuousOn (fun t => I.expBuyersIn t b) (Icc p b) := by
    apply continuousOn_finsetSum
    intro i _
    let := I.isProb_B i
    let := I.noAtoms_B i
    let μ := (I.μB i).restrict (Iic b)
    have H : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici p) μ := (integrable_const 1).integrableOn
    simpa [μ, setIntegral_one_eq_measureReal, measureReal_def, Measure.restrict_apply,
      Ici_inter_Iic] using (H.continuousOn_Ici_primitive_Ici.mono Icc_subset_Ici_self)
  have hz : I.expBuyersIn b b = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    let := I.noAtoms_B i
    simp
  apply isPreconnected_Icc.intermediate_value (right_mem_Icc.mpr hp) (left_mem_Icc.mpr hp) hc
  exact ⟨by simp [hz], h⟩

theorem seller_threshold {n m : ℕ} (I : DAInstance n m) {a p : ℝ} (hp : a ≤ p)
    (h : 1 / 4 ≤ I.expSellersIn a p) : ∃ t ∈ Icc a p, I.expSellersIn a t = 1 / 4 := by
  have hc : ContinuousOn (fun t => I.expSellersIn a t) (Icc a p) := by
    apply continuousOn_finsetSum
    intro j _
    let := I.isProb_S j
    let := I.noAtoms_S j
    have H : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc a p) (I.μS j) :=
      (integrable_const 1).integrableOn
    simpa [setIntegral_one_eq_measureReal, measureReal_def] using
      intervalIntegral.continuousOn_primitive_Icc H
  have hz : I.expSellersIn a a = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    let := I.noAtoms_S j
    simp
  apply isPreconnected_Icc.intermediate_value (left_mem_Icc.mpr hp) (right_mem_Icc.mpr hp) hc
  exact ⟨by simp [hz], h⟩


theorem buyer_forward_threshold {n m : ℕ} (I : DAInstance n m) {a p : ℝ} (hp : a ≤ p)
    (h : 1 / 4 ≤ I.expBuyersIn a p) : ∃ t ∈ Icc a p, I.expBuyersIn a t = 1 / 4 := by
  have hc : ContinuousOn (fun t => I.expBuyersIn a t) (Icc a p) := by
    apply continuousOn_finsetSum
    intro j _
    let := I.isProb_B j
    let := I.noAtoms_B j
    have H : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc a p) (I.μB j) :=
      (integrable_const 1).integrableOn
    simpa [setIntegral_one_eq_measureReal, measureReal_def] using
      intervalIntegral.continuousOn_primitive_Icc H
  have hz : I.expBuyersIn a a = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    let := I.noAtoms_B j
    simp
  apply isPreconnected_Icc.intermediate_value (left_mem_Icc.mpr hp) (right_mem_Icc.mpr hp) hc
  exact ⟨by simp [hz], h⟩


theorem seller_backward_threshold {n m : ℕ} (I : DAInstance n m) {p b : ℝ} (hp : p ≤ b)
    (h : 1 / 4 ≤ I.expSellersIn p b) : ∃ t ∈ Icc p b, I.expSellersIn t b = 1 / 4 := by
  have hc : ContinuousOn (fun t => I.expSellersIn t b) (Icc p b) := by
    apply continuousOn_finsetSum
    intro i _
    let := I.isProb_S i
    let := I.noAtoms_S i
    let μ := (I.μS i).restrict (Iic b)
    have H : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici p) μ := (integrable_const 1).integrableOn
    simpa [μ, setIntegral_one_eq_measureReal, measureReal_def, Measure.restrict_apply,
      Ici_inter_Iic] using (H.continuousOn_Ici_primitive_Ici.mono Icc_subset_Ici_self)
  have hz : I.expSellersIn b b = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    let := I.noAtoms_S i
    simp
  apply isPreconnected_Icc.intermediate_value (right_mem_Icc.mpr hp) (left_mem_Icc.mpr hp) hc
  exact ⟨by simp [hz], h⟩

noncomputable def single_submarket (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) (hap : a ≤ p) (hpb : p ≤ b) : Stratification where
  N := 1
  one_le_N := le_rfl
  m := fun i => if i = 0 then a else b
  p := fun _ => p
  zero_le_m := by simpa using ha
  m_le_one := by simpa using hb
  m_strictMono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  p_mem := by intro i; fin_cases i; simpa using And.intro hap hpb

theorem single_submarket_gains {n m : ℕ} (I : DAInstance n m)
    (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hap : a ≤ p) (hpb : p ≤ b) :
    I.strat (single_submarket a b p ha hab hb hap hpb) = I.worstRationedIn a p b := by
  change (∑ k : Fin 1, I.worstRationedIn (if k.castSucc = 0 then a else b) p
    (if k.succ = 0 then a else b)) = I.worstRationedIn a p b
  rw [Fin.sum_univ_one]
  simp

end StratifyMarkets.DoubleAuction
end

-- Solutions.StratifyMarketsBandPartition
section
open Set MeasureTheory StratifyMarkets.DoubleAuction
namespace StratifyMarkets.BandPartition

/-- The final matched pair also applies whenever a single price separates both
threshold bands with at most a quarter expected agents on each intervening side. -/
theorem single_pair {n m : ℕ} (I : DAInstance n m) {a b tB tS q : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hB : I.IsBuyerThreshold a b tB) (hS : I.IsSellerThreshold a b tS)
    (hSq : tS ≤ q) (hqB : q ≤ tB)
    (buyers : I.expBuyersIn q tB ≤ 1/4) (sellers : I.expSellersIn tS q ≤ 1/4) :
    ∃ σ : Stratification, σ.m 0 = a ∧ σ.m (Fin.last σ.N) = b ∧
      3/128 * I.oneTrade a b tB tS ≤ I.strat σ := by
  let left := hS.1.1.trans hSq
  let right := hqB.trans hB.1.2
  refine ⟨single_submarket a b q ha hab hb left right,by change (if (0:Fin 2) = 0 then a else b) = a; simp,
    by change (if Fin.last 1 = 0 then a else b) = b; simp,?_⟩
  rw [single_submarket_gains]
  exact lemma_4_17 I a b tB tS q ha hab hb hB hS (hSq.trans hqB) hSq hqB buyers sellers

/-- Atomless interval masses add exactly even with shared closed endpoints. -/
theorem adjacent_mass (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    μ.real (Icc a c) = μ.real (Icc a b) + μ.real (Icc b c) := by
  have eq : Icc a c = Icc a b ∪ Ioc b c := by
    ext x
    simp only [mem_Icc,mem_Ioc,mem_union]
    constructor
    · rintro ⟨h1,h2⟩
      by_cases h : x ≤ b
      · exact Or.inl ⟨h1,h⟩
      · exact Or.inr ⟨lt_of_not_ge h,h2⟩
    · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
      · exact ⟨h1,h2.trans hbc⟩
      · exact ⟨hab.trans h1.le,h2⟩
  have dis : Disjoint (Icc a b) (Ioc b c) := disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hx.2) hy.1)
  rw [eq,measureReal_union dis measurableSet_Ioc]
  exact congrArg (fun x => μ.real (Icc a b) + ENNReal.toReal x) (measure_congr Ioc_ae_eq_Icc)

theorem buyer_add {n m : ℕ} (I : DAInstance n m) {a b c : ℝ} (ab : a ≤ b) (bc : b ≤ c) :
    I.expBuyersIn a c = I.expBuyersIn a b + I.expBuyersIn b c := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ i, NullSingletonClass (I.μB i) := I.noAtoms_B
  unfold DAInstance.expBuyersIn
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => adjacent_mass (I.μB i) ab bc

theorem seller_add {n m : ℕ} (I : DAInstance n m) {a b c : ℝ} (ab : a ≤ b) (bc : b ≤ c) :
    I.expSellersIn a c = I.expSellersIn a b + I.expSellersIn b c := by
  let : ∀ i, IsProbabilityMeasure (I.μS i) := I.isProb_S
  let : ∀ i, NullSingletonClass (I.μS i) := I.noAtoms_S
  unfold DAInstance.expSellersIn
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => adjacent_mass (I.μS i) ab bc



theorem buyer_mono {n m : ℕ} (I : DAInstance n m) {a b c d : ℝ}
    (ca : c ≤ a) (bd : b ≤ d) : I.expBuyersIn a b ≤ I.expBuyersIn c d := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  exact Finset.sum_le_sum fun i _ => measureReal_mono (μ := I.μB i) (Icc_subset_Icc ca bd)

theorem seller_mono {n m : ℕ} (I : DAInstance n m) {a b c d : ℝ}
    (ca : c ≤ a) (bd : b ≤ d) : I.expSellersIn a b ≤ I.expSellersIn c d := by
  let : ∀ i, IsProbabilityMeasure (I.μS i) := I.isProb_S
  exact Finset.sum_le_sum fun i _ => measureReal_mono (μ := I.μS i) (Icc_subset_Icc ca bd)

structure Band where
  sl : ℝ
  sh : ℝ
  q : ℝ
  bl : ℝ
  bh : ℝ
  order : sl ≤ sh ∧ sh ≤ q ∧ q ≤ bl ∧ bl ≤ bh

def Band.correct {n m : ℕ} (I : DAInstance n m) (z : Band) : Prop :=
  I.expSellersIn z.sl z.sh = 1/4 ∧ I.expBuyersIn z.bl z.bh = 1/4 ∧
  I.expSellersIn z.sh z.q ≤ 1/4 ∧ I.expBuyersIn z.q z.bl ≤ 1/4

/-- Every recursive call starts with a fresh quarter-mass seller band. The
previous buyer's right endpoint supplies a lower bound for the next buyer band.
When this crosses the terminal buyer threshold the construction terminates. -/
inductive Path {n m : ℕ} (I : DAInstance n m) (tB b : ℝ) : ℝ → ℝ → ℝ → List Band → Prop
  | stop {s t prev : ℝ} (z : Band) (hs : z.sl = s) (ht : z.sh = t)
      (hB : z.bl = tB) (hb : z.bh = b) (hc : z.correct I) : Path I tB b s t prev [z]
  | step {s t prev next : ℝ} {zs : List Band} (z : Band) (hs : z.sl = s) (ht : z.sh = t)
      (ps : prev ≤ z.bl) (advance : t ≤ next) (ub : z.bh ≤ b) (hc : z.correct I)
      (rest : Path I tB b next z.bl z.bh zs) : Path I tB b s t prev (z :: zs)

theorem buyer_same {n m : ℕ} (I : DAInstance n m) (q : ℝ) : I.expBuyersIn q q = 0 := by
  let : ∀ i, NullSingletonClass (I.μB i) := I.noAtoms_B
  apply Finset.sum_eq_zero
  intro i _
  simp

theorem seller_same {n m : ℕ} (I : DAInstance n m) (q : ℝ) : I.expSellersIn q q = 0 := by
  let : ∀ i, NullSingletonClass (I.μS i) := I.noAtoms_S
  apply Finset.sum_eq_zero
  intro i _
  simp

/-- Construct all matched bands. Each nonterminal step removes at least one
quarter of expected seller mass, giving an explicit finite recursion bound. -/
theorem build_path {n m : ℕ} (I : DAInstance n m) {tB b : ℝ} (bb : tB ≤ b)
    (massB : I.expBuyersIn tB b = 1/4) (fuel : ℕ) :
    ∀ {s t prev : ℝ}, s ≤ t → t ≤ tB → I.expSellersIn s t = 1/4 →
    t ≤ prev → I.expBuyersIn t prev ≤ 1/4 → I.expSellersIn t tB ≤ (fuel:ℝ)/4 →
    ∃ xs, Path I tB b s t prev xs := by
  induction fuel with
  | zero =>
    intro s t prev st ttB massS tprev cap fuel
    let z : Band := ⟨s,t,tB,tB,b,st,ttB,le_rfl,bb⟩
    refine ⟨[z],.stop z rfl rfl rfl rfl ⟨massS,massB,?_,?_⟩⟩
    · change I.expSellersIn t tB ≤ 1/4
      norm_num at fuel
      linarith
    · change I.expBuyersIn tB tB ≤ 1/4
      rw [buyer_same]; norm_num
  | succ d ih =>
    intro s t prev st ttB massS tprev cap fuel
    by_cases small : I.expSellersIn t tB ≤ 1/4
    · let z : Band := ⟨s,t,tB,tB,b,st,ttB,le_rfl,bb⟩
      refine ⟨[z],.stop z rfl rfl rfl rfl ⟨massS,massB,small,?_⟩⟩
      change I.expBuyersIn tB tB ≤ 1/4
      rw [buyer_same]; norm_num
    obtain ⟨q,⟨tq,qtB⟩,quarter⟩ := seller_threshold I ttB (le_of_not_ge small)
    by_cases final : I.expBuyersIn q tB ≤ 1/4
    · let z : Band := ⟨s,t,q,tB,b,st,tq,qtB,bb⟩
      exact ⟨[z],.stop z rfl rfl rfl rfl ⟨massS,massB,quarter.le,final⟩⟩
    have prevB : prev ≤ tB := by
      by_contra hh
      exact final ((buyer_mono I tq (le_of_not_ge hh)).trans cap)
    let l := max q prev
    have ql : q ≤ l := le_max_left _ _
    have pl : prev ≤ l := le_max_right _ _
    have lB : l ≤ tB := max_le qtB prevB
    have gap : I.expBuyersIn q l ≤ 1/4 := by
      rcases le_total prev q with h|h
      · rw [show l = q from max_eq_left h,buyer_same]; norm_num
      · rw [show l = prev from max_eq_right h]
        exact (buyer_mono I tq le_rfl).trans cap
    obtain ⟨u,⟨lu,ub⟩,buyer⟩ := buyer_forward_threshold I (lB.trans bb)
      (massB ▸ buyer_mono I lB (le_rfl (a := b)))
    obtain ⟨next,⟨tn,nl⟩,seller⟩ := seller_backward_threshold I (tq.trans ql)
      (quarter ▸ seller_mono I (le_rfl (a := t)) ql)
    have drop := seller_add I (tq.trans ql) lB
    have growth := seller_mono I (le_rfl (a := t)) ql
    have rest : I.expSellersIn l tB ≤ (d:ℝ)/4 := by
      rw [Nat.cast_succ] at fuel
      linarith
    obtain ⟨xs,path⟩ := ih nl lB seller lu buyer.le rest
    let z : Band := ⟨s,t,q,l,u,st,tq,ql,lu⟩
    exact ⟨z::xs,.step z rfl rfl pl tn ub ⟨massS,buyer,quarter.le,gap⟩ path⟩

end StratifyMarkets.BandPartition
end

-- Solutions.StratifyMarketsParticipation
section
open MeasureTheory Set StratifyMarkets.DoubleAuction

namespace StratifyMarkets.Participation

def eligible {k : ℕ} (s : Set ℝ) [DecidablePred (· ∈ s)] (x : Fin k → ℝ) :=
  Finset.univ.filter (fun i => x i ∈ s)

theorem count_measurable {k : ℕ} (s : Set ℝ) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    Measurable (fun x : Fin k → ℝ => ((eligible s x).card : ℝ)) := by
  have h (x : Fin k → ℝ) : ((eligible s x).card : ℝ) = ∑ i, s.indicator (fun _ => (1:ℝ)) (x i) := by
    simp only [Set.indicator,eligible,Finset.sum_boole]
  simp_rw [h]
  exact Finset.measurable_sum _ fun i _ => (measurable_const.indicator hs).comp (measurable_pi_apply i)

theorem count_median_bounds {k : ℕ} (μ : Fin k → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Set ℝ) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    (1/2 : ENNReal) ≤ Measure.pi μ {x | (∑ i, (μ i s).toReal) - 1 < ((eligible s x).card : ℝ)} ∧
    (1/2 : ENNReal) ≤ Measure.pi μ {x | ((eligible s x).card : ℝ) < (∑ i, (μ i s).toReal) + 1} := by
  classical
  let f := fun x => s.indicator (fun _ : ℝ => (1:ℝ)) x
  have hf : Measurable f := measurable_const.indicator hs
  have hber (i : Fin k) : ∀ᵐ x ∂Measure.pi μ, f (x i) = 0 ∨ f (x i) = 1 := by
    apply Filter.Eventually.of_forall
    intro x
    by_cases h : x i ∈ s <;> simp [f, Set.indicator, h]
  have hpi := ProbabilityTheory.iIndepFun_pi (μ := μ) (X := fun _ => f) (fun _ => hf.aemeasurable)
  have htail := (theorem_4_2 (Measure.pi μ) k (fun i x => f (x i))
    (fun i => hf.comp (measurable_pi_apply i)) hber hpi).2
  have sum_eq (x : Fin k → ℝ) : ∑ i, f (x i) = ((eligible s x).card : ℝ) := by
    simp only [f,Set.indicator,eligible,Finset.sum_boole]
  have hint (i : Fin k) : Integrable (fun x : Fin k → ℝ => f (x i)) (Measure.pi μ) :=
    ((measurePreserving_eval μ i).integrable_comp hf.aestronglyMeasurable).mpr
      ((integrable_const (1:ℝ)).indicator hs)
  have eint (i : Fin k) : (∫ x, f (x i) ∂Measure.pi μ) = (μ i s).toReal := by
    have eq := (measurePreserving_eval μ i).map_eq
    calc
      _ = ∫ y, f y ∂(Measure.pi μ).map (Function.eval i) :=
        (integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable).symm
      _ = _ := by rw [eq]; simp [f, integral_indicator hs, measureReal_def]
  rw [integral_finsetSum _ (fun i _ => hint i)] at htail
  simpa only [eint,sum_eq] using htail

theorem gains_integrable_sets {n m : ℕ} (I : DAInstance n m) (A B : Set ℝ)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Integrable (fun x => worstRationedGains (eligible A x.1) (eligible B x.2) x.1 x.2) I.law := by
  classical
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  let : IsProbabilityMeasure I.law := by unfold DAInstance.law; infer_instance
  let mask := fun (x : (Fin n → ℝ) × (Fin m → ℝ)) =>
    ((fun i => decide (x.1 i ∈ A)),(fun j => decide (x.2 j ∈ B)))
  have hmask : Measurable mask := by
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro i
      apply measurable_to_bool
      simpa [Set.preimage] using ((measurable_pi_apply i).comp measurable_fst) hA
    · apply measurable_pi_iff.mpr
      intro j
      apply measurable_to_bool
      simpa [Set.preimage] using ((measurable_pi_apply j).comp measurable_snd) hB
  let g := fun z : ((Fin n → ℝ) × (Fin m → ℝ)) × ((Fin n → Bool) × (Fin m → Bool)) =>
    worstRationedGains (Finset.univ.filter (fun i => z.2.1 i)) (Finset.univ.filter (fun j => z.2.2 j))
      z.1.1 z.1.2
  have hg : Measurable g := by
    apply measurable_from_prod_countable_left
    intro masks
    let bs := Finset.univ.filter (fun i => masks.1 i)
    let ss := Finset.univ.filter (fun j => masks.2 j)
    let opts := bs.powersetCard (min bs.card ss.card) ×ˢ ss.powersetCard (min bs.card ss.card)
    have hn : opts.Nonempty := (Finset.powersetCard_nonempty.mpr (min_le_left _ _)).product
      (Finset.powersetCard_nonempty.mpr (min_le_right _ _))
    let f := fun (T : Finset (Fin n) × Finset (Fin m)) (x : (Fin n → ℝ) × (Fin m → ℝ)) =>
      ∑ i ∈ T.1, x.1 i - ∑ j ∈ T.2, x.2 j
    have hfn (T) : Measurable (f T) := by
      apply Measurable.sub
      · exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_fst
      · exact Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).comp measurable_snd
    have heq : (fun x => g (x,masks)) = opts.inf' hn f := by
      funext x
      exact (Finset.inf'_apply hn f x).symm
    rw [heq]
    exact Finset.measurable_sup' (α := ℝᵒᵈ) hn fun T _ => hfn T
  have HM : Measurable (fun x : (Fin n → ℝ) × (Fin m → ℝ) => worstRationedGains (eligible A x.1) (eligible B x.2) x.1 x.2) := by
    simpa only [Function.comp_def, id_eq, g, mask, eligible, decide_eq_true_eq] using
      hg.comp (measurable_id.prodMk hmask)
  have buyer_support (i : Fin n) : ∀ᵐ x ∂I.law, x.1 i ∈ Icc (0 : ℝ) 1 :=
    (measurePreserving_fst (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μB i).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_B i)))
  have seller_support (j : Fin m) : ∀ᵐ x ∂I.law, x.2 j ∈ Icc (0 : ℝ) 1 :=
    (measurePreserving_snd (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μS j).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_S j)))
  apply Integrable.of_bound HM.aestronglyMeasurable ((n:ℝ)+m)
  filter_upwards [ae_all_iff.mpr buyer_support, ae_all_iff.mpr seller_support] with x hx hy
  unfold worstRationedGains
  let bs := eligible A x.1
  let ss := eligible B x.2
  have nonempty : ((bs.powersetCard (min bs.card ss.card)) ×ˢ ss.powersetCard (min bs.card ss.card)).Nonempty :=
    (Finset.powersetCard_nonempty.mpr (min_le_left _ _)).product (Finset.powersetCard_nonempty.mpr (min_le_right _ _))
  obtain ⟨pair,_,h⟩ := Finset.exists_mem_eq_inf' nonempty (fun T => ∑ i ∈ T.1, x.1 i - ∑ j ∈ T.2, x.2 j)
  change ‖Finset.inf' _ nonempty (fun T => ∑ i ∈ T.1, x.1 i - ∑ j ∈ T.2, x.2 j)‖ ≤ _
  rw [h,Real.norm_eq_abs,abs_le]
  have h1 : (∑ i ∈ pair.1, x.1 i) ≤ n := by
    calc _ ≤ ∑ _i ∈ pair.1, (1:ℝ) := Finset.sum_le_sum fun i _ => (hx i).2
         _ ≤ _ := by simpa using (show (pair.1.card:ℝ) ≤ n by exact_mod_cast (show pair.1.card ≤ n by simpa using Finset.card_le_univ pair.1))
  have h2 : (∑ j ∈ pair.2, x.2 j) ≤ m := by
    calc _ ≤ ∑ _j ∈ pair.2, (1:ℝ) := Finset.sum_le_sum fun j _ => (hy j).2
         _ ≤ _ := by simpa using (show (pair.2.card:ℝ) ≤ m by exact_mod_cast (show pair.2.card ≤ m by simpa using Finset.card_le_univ pair.2))
  have h3 := Finset.sum_nonneg (s := pair.1) (fun i _ => (hx i).1)
  have h4 := Finset.sum_nonneg (s := pair.2) (fun j _ => (hy j).1)
  constructor <;> linarith

theorem gains_integrable {n m : ℕ} (I : DAInstance n m) (q : ℝ) :
    Integrable (fun x => worstRationedGains (eligible (Ici q) x.1) (eligible (Iic q) x.2) x.1 x.2) I.law :=
  gains_integrable_sets I _ _ measurableSet_Ici measurableSet_Iic

theorem nonneg_gains {n m : ℕ} (v : Fin n → ℝ) (c : Fin m → ℝ) (q : ℝ) :
    0 ≤ worstRationedGains (eligible (Ici q) v) (eligible (Iic q) c) v c := by
  apply Finset.le_inf'
  intro T hT
  obtain ⟨hB,hS⟩ := Finset.mem_product.mp hT
  obtain ⟨inB,cB⟩ := Finset.mem_powersetCard.mp hB
  obtain ⟨inS,cS⟩ := Finset.mem_powersetCard.mp hS
  have sc : (∑ j ∈ T.2, c j) ≤ ∑ _j ∈ T.2, q := Finset.sum_le_sum fun j hj => (Finset.mem_filter.mp (inS hj)).2
  have vb : (∑ _i ∈ T.1, q) ≤ ∑ i ∈ T.1, v i := Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp (inB hi)).2
  exact sub_nonneg.mpr (sc.trans ((by simp [cB,cS] : (∑ _j ∈ T.2, q) ≤ ∑ _i ∈ T.1, q).trans vb))

/-- The leave-one-out comparison behind (4.10) whenever expected demand
is at least one unit below expected supply. Each side is an independent
heterogeneous family; removing one eligible-side coordinate is allowed. -/
theorem extra_participant_wins {k l : ℕ}
    (μ : Fin k → Measure ℝ) (ν : Fin l → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (s t : Set ℝ) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (gap : (∑ i, (μ i s).toReal) + 2 ≤ ∑ j, (ν j t).toReal) :
    (1/4 : ℝ) ≤ (((Measure.pi μ).prod (Measure.pi ν))
      {x | (eligible s x.1).card < (eligible t x.2).card}).toReal := by
  let B := {x : Fin k → ℝ | ((eligible s x).card : ℝ) < (∑ i, (μ i s).toReal) + 1}
  let S := {y : Fin l → ℝ | (∑ j, (ν j t).toReal) - 1 < ((eligible t y).card : ℝ)}
  have b := ENNReal.toReal_mono (measure_ne_top _ _) (count_median_bounds μ s hs).2
  have c := ENNReal.toReal_mono (measure_ne_top _ _) (count_median_bounds ν t ht).1
  change (1/2 : ENNReal).toReal ≤ ((Measure.pi μ) B).toReal at b
  change (1/2 : ENNReal).toReal ≤ ((Measure.pi ν) S).toReal at c
  norm_num at b c
  have subset : B ×ˢ S ⊆ {x | (eligible s x.1).card < (eligible t x.2).card} := by
    intro x hx
    obtain ⟨h1,h2⟩ := hx
    change ((eligible s x.1).card : ℝ) < (∑ i, (μ i s).toReal) + 1 at h1
    change (∑ j, (ν j t).toReal) - 1 < ((eligible t x.2).card : ℝ) at h2
    exact_mod_cast (show ((eligible s x.1).card : ℝ) < ((eligible t x.2).card : ℝ) by linarith)
  have h := measureReal_mono (μ := (Measure.pi μ).prod (Measure.pi ν)) subset
  apply le_trans _ h
  rw [measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
  nlinarith [mul_nonneg (sub_nonneg.mpr b) (sub_nonneg.mpr c)]

end StratifyMarkets.Participation
end

-- Solutions.StratifyMarketsSuperAgents
section
open MeasureTheory Set
namespace StratifyMarkets.DoubleAuction

theorem vmax_meas {n : ℕ} [NeZero n] : Measurable (vmax (n := n)) := by
  have h := Finset.measurable_sup' Finset.univ_nonempty
    (fun i _ => measurable_pi_apply (X := fun _ : Fin n => ℝ) i)
  have heq : vmax (n := n) = Finset.univ.sup' Finset.univ_nonempty
      (fun i (v : Fin n → ℝ) => v i) := by
    funext v
    exact (Finset.sup'_apply Finset.univ_nonempty (fun i (w : Fin n → ℝ) => w i) v).symm
  rw [heq]
  exact h

theorem cmin_meas {m : ℕ} [NeZero m] : Measurable (cmin (m := m)) := by
  have h := Finset.measurable_sup' (α := ℝᵒᵈ) Finset.univ_nonempty
    (fun i _ => measurable_pi_apply (X := fun _ : Fin m => ℝᵒᵈ) i)
  have heq : cmin (m := m) = Finset.univ.inf' Finset.univ_nonempty
      (fun i (c : Fin m → ℝ) => c i) := by
    funext c
    exact (Finset.inf'_apply Finset.univ_nonempty (fun i (w : Fin m → ℝ) => w i) c).symm
  rw [heq]
  exact h

private theorem extremum_law {k : ℕ} (μ : Fin k → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)]
    (hn : ∀ j, NullSingletonClass (μ j)) (hs : ∀ j, μ j (Icc 0 1) = 1)
    (f : (Fin k → ℝ) → ℝ) (hf : Measurable f) (attains : ∀ x, ∃ j, f x = x j) :
    IsProbabilityMeasure ((Measure.pi μ).map f) ∧ NullSingletonClass ((Measure.pi μ).map f) ∧
      (Measure.pi μ).map f (Icc 0 1) = 1 := by
  let : IsProbabilityMeasure ((Measure.pi μ).map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  refine ⟨inferInstance, ⟨fun r => ?_⟩, ?_⟩
  · rw [Measure.map_apply hf (measurableSet_singleton _)]
    have coord (i : Fin k) : ∀ᵐ x ∂Measure.pi μ, x i ≠ r :=
      (measurePreserving_eval μ i).quasiMeasurePreserving.ae (by
        let := hn i
        exact (μ i).ae_ne r)
    have null : ∀ᵐ x ∂Measure.pi μ, f x ≠ r := by
      filter_upwards [ae_all_iff.mpr coord] with x hx
      obtain ⟨i,hi⟩ := attains x
      exact hi ▸ hx i
    exact compl_mem_ae_iff.mp null
  · rw [Measure.map_apply hf measurableSet_Icc]
    apply (mem_ae_iff_prob_eq_one (hf measurableSet_Icc)).mp
    have coord (i : Fin k) : ∀ᵐ x ∂Measure.pi μ, x i ∈ Icc (0 : ℝ) 1 :=
      (measurePreserving_eval μ i).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (hs i))
    filter_upwards [ae_all_iff.mpr coord] with x hx
    obtain ⟨i,hi⟩ := attains x
    change f x ∈ Icc 0 1
    rw [hi]
    exact hx i

/-- The extrema in the double-auction profile define an admissible atomless
bilateral instance; the buyer and seller are sampled independently. -/
noncomputable def superAgents {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) : BTInstance := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ i, IsProbabilityMeasure (I.μS i) := I.isProb_S
  have hB := extremum_law I.μB I.noAtoms_B I.support_B vmax vmax_meas (fun x => by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
    exact ⟨i,hi⟩)
  have hS := extremum_law I.μS I.noAtoms_S I.support_S cmin cmin_meas (fun x => by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty x
    exact ⟨i,hi⟩)
  exact ⟨_, _, hB.1, hS.1, hB.2.1, hS.2.1, hB.2.2, hS.2.2⟩

private theorem super_integral {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m)
    (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
    ∫ x, f x ∂(superAgents I).law = ∫ x, f (cmin x.2, vmax x.1) ∂I.law := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  change (∫ x, f x ∂(((Measure.pi I.μS).map cmin).prod ((Measure.pi I.μB).map vmax))) = _
  rw [Measure.map_prod_map _ _ cmin_meas vmax_meas, integral_map (cmin_meas.prodMap vmax_meas).aemeasurable hf.aestronglyMeasurable]
  have swap : MeasurePreserving (MeasurableEquiv.prodComm : _ ≃ᵐ _)
      ((Measure.pi I.μB).prod (Measure.pi I.μS)) ((Measure.pi I.μS).prod (Measure.pi I.μB)) :=
    Measure.measurePreserving_swap
  exact (swap.integral_comp' (fun z => f ((Prod.map cmin vmax) z))).symm

theorem superAgents_first_best {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) :
    (superAgents I).FB = ∫ x, max (vmax x.1 - cmin x.2) 0 ∂I.law :=
  super_integral I (fun x => max (x.2-x.1) 0) (by fun_prop)

theorem superAgents_strat {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) (σ : Stratification) :
    (superAgents I).strat σ = ∑ k : Fin σ.N, I.superFP (σ.m k.castSucc) (σ.p k) (σ.m k.succ) := by
  apply Finset.sum_congr rfl
  intro k _
  apply super_integral
  apply Measurable.ite
  · exact (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
        ((measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const)))
  · exact measurable_snd.sub measurable_fst
  · exact measurable_const

/-- Equation (4.35) transports the bilateral theorem to the exact super-agent
integrals of the double auction. -/
theorem superAgents_bilateral_guarantee {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) :
    ∃ σ : Stratification, 1/(12*Real.exp 1) * (∫ x, max (vmax x.1-cmin x.2) 0 ∂I.law) ≤
      ∑ k : Fin σ.N, I.superFP (σ.m k.castSucc) (σ.p k) (σ.m k.succ) := by
  obtain ⟨σ,hσ⟩ := theorem_3_1 (superAgents I)
  exact ⟨σ, by simpa only [superAgents_first_best, superAgents_strat] using hσ⟩

end StratifyMarkets.DoubleAuction
end

-- Solutions.StratifyMarketsScarcity
section
open MeasureTheory Set StratifyMarkets.Participation

namespace StratifyMarkets.Scarcity

/-- The no-other-participant factor is at least one minus the total marginal participation. -/
theorem product_failure {ι : Type*} (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1) (s : Finset ι) :
    1 - ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1-u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s h ih =>
    rw [Finset.prod_insert h, Finset.sum_insert h]
    have e := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hu1 i))
    nlinarith [mul_nonneg (hu i) (Finset.sum_nonneg (s := s) fun j _ => hu j)]

noncomputable def others {n : ℕ} (s : Set ℝ) (i : Fin n) : Set (Fin n → ℝ) :=
  univ.pi (Function.update (fun _ : Fin n => sᶜ) i univ)

theorem mem_others {n : ℕ} {s : Set ℝ} {i : Fin n} {x : Fin n → ℝ} :
    x ∈ others s i ↔ ∀ j, j ≠ i → x j ∉ s := by
  classical
  simp [others, Set.mem_pi,Function.update_apply]

theorem measurable_others {n : ℕ} {s : Set ℝ} (hs : MeasurableSet s) (i : Fin n) :
    MeasurableSet (others s i) := by
  classical
  apply MeasurableSet.univ_pi
  intro j
  by_cases eq : j = i <;> simp [eq,hs.compl]

theorem isolated_factor {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Set ℝ) (hs : MeasurableSet s) (i : Fin n) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, (others s i).indicator (fun y => f (y i)) x ∂Measure.pi μ) =
      (∏ j ∈ Finset.univ.erase i, (1 - (μ j).real s)) * ∫ y, f y ∂μ i := by
  classical
  let A := Function.update (fun _ : Fin n => sᶜ) i univ
  let ν := fun j => (μ j).restrict (A j)
  rw [integral_indicator (measurable_others hs i)]
  unfold others
  rw [Measure.restrict_pi_pi]
  change (∫ x, f (Function.eval i x) ∂Measure.pi ν) = _
  rw [← integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable, Measure.pi_map_eval, integral_smul_measure]
  have ei : ν i = μ i := by simp [ν,A]
  rw [ei]
  simp only [ENNReal.toReal_prod, smul_eq_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have ne := (Finset.mem_erase.mp hj).1
  simp [ν,A,Function.update_of_ne ne, ← measureReal_def, measureReal_compl hs]

/-- Equation (A.7) for an arbitrary nonnegative coordinate weight. The index
itself is unconstrained in the box, which also handles zero eligibility mass. -/
theorem isolated_integral {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Set ℝ) (hs : MeasurableSet s) (cap : (∑ j, (μ j).real s) ≤ 1/4)
    (i : Fin n) (f : ℝ → ℝ) (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) :
    3/4 * (∫ y, f y ∂μ i) ≤ ∫ x, (others s i).indicator (fun y => f (y i)) x ∂Measure.pi μ := by
  classical
  rw [isolated_factor μ s hs i f hf]
  apply mul_le_mul_of_nonneg_right _ (integral_nonneg hn)
  have total := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i (Finset.univ : Finset (Fin n)))
    (fun j _ _ => measureReal_nonneg (μ := μ j) (s := s))
  have low := product_failure (fun j => (μ j).real s) (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one)
    (Finset.univ.erase i)
  linarith


/-- Weighted surplus when a participant is the unique eligible coordinate. -/
noncomputable def uniqueWeight {n : ℕ} (s : Set ℝ) (f : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (others s i).indicator (fun y => f (y i)) x

theorem unique_integral {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Set ℝ) (hs : MeasurableSet s) (cap : (∑ j, (μ j).real s) ≤ 1/4)
    (f : ℝ → ℝ) (hf : Measurable f) (hi : ∀ i, Integrable f (μ i)) (hn : ∀ x, 0 ≤ f x) :
    Integrable (uniqueWeight s f) (Measure.pi μ) ∧
      3/4 * (∑ i, ∫ y, f y ∂μ i) ≤ ∫ x, uniqueWeight s f x ∂Measure.pi μ := by
  have h (i) : Integrable ((others s i).indicator (fun y => f (y i))) (Measure.pi μ) :=
    (((measurePreserving_eval μ i).integrable_comp hf.aestronglyMeasurable).mpr (hi i)).indicator (measurable_others hs i)
  refine ⟨integrable_finsetSum _ (fun i _ => h i), ?_⟩
  unfold uniqueWeight
  rw [integral_finsetSum _ (fun i _ => h i), Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => isolated_integral μ s hs cap i f hf hn

theorem unique_le_alloc {n : ℕ} {s : Set ℝ} [DecidablePred (· ∈ s)] (x : Fin n → ℝ)
    (f : ℝ → ℝ) (outside : ∀ y, y ∉ s → f y = 0) (hn : ∀ y, 0 ≤ f y)
    (T : Finset (Fin n)) (sub : T ⊆ eligible s x) (pos : (eligible s x).Nonempty → T.Nonempty) :
    uniqueWeight s f x ≤ ∑ i ∈ T, f (x i) := by
  classical
  have eq : (∑ i ∈ T, f (x i)) = ∑ i, if i ∈ T then f (x i) else 0 := by
    rw [← Finset.sum_filter]
    simp
  rw [eq,uniqueWeight]
  apply Finset.sum_le_sum
  intro i _
  by_cases e : x i ∈ s
  · by_cases iso : x ∈ others s i
    · have mem : i ∈ eligible s x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,e⟩
      obtain ⟨j,hj⟩ := pos ⟨i,mem⟩
      have eq : j = i := by
        by_contra hji
        exact mem_others.mp iso j hji (Finset.mem_filter.mp (sub hj)).2
      have hi : i ∈ T := eq ▸ hj
      simp [iso,hi]
    · by_cases hi : i ∈ T <;> simp [iso,hi,hn]
  · simp [Set.indicator,outside _ e]

theorem bounded_band {μ : Measure ℝ} [IsProbabilityMeasure μ] {lo hi : ℝ} (hh : lo ≤ hi) :
    Integrable ((Icc lo hi).indicator (fun y => y-lo)) μ ∧ Integrable ((Icc lo hi).indicator (fun y => hi-y)) μ := by
  constructor
  · apply Integrable.of_bound ((measurable_id.sub measurable_const).indicator measurableSet_Icc).aestronglyMeasurable (hi-lo)
    filter_upwards with y
    by_cases h : y ∈ Icc lo hi
    · rw [Set.indicator_of_mem h]
      change ‖y-lo‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr h.1)]
      exact sub_le_sub_right h.2 _
    · simp [h,sub_nonneg.mpr hh]
  · apply Integrable.of_bound ((measurable_const.sub measurable_id).indicator measurableSet_Icc).aestronglyMeasurable (hi-lo)
    filter_upwards with y
    by_cases h : y ∈ Icc lo hi
    · rw [Set.indicator_of_mem h]
      change ‖hi-y‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr h.2)]
      exact sub_le_sub_left h.1 _
    · simp [h,sub_nonneg.mpr hh]

noncomputable def oneEvent {n : ℕ} (s : Set ℝ) [DecidablePred (· ∈ s)] : Set (Fin n → ℝ) :=
  {x | (eligible s x).card = 1}

theorem one_meas {n : ℕ} {s : Set ℝ} [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    MeasurableSet (oneEvent (n := n) s) := by
  have card (x : Fin n → ℝ) : ((eligible s x).card : ℝ) = ∑ i, s.indicator (fun _ => (1:ℝ)) (x i) := by
    simp only [Set.indicator,eligible,Finset.sum_boole]
  have hm : Measurable (fun x : Fin n → ℝ => ((eligible s x).card : ℝ)) := by
    simp_rw [card]
    exact Finset.measurable_sum _ fun i _ => (measurable_const.indicator hs).comp (measurable_pi_apply i)
  have eq : oneEvent (n := n) s = (fun x : Fin n → ℝ => ((eligible s x).card : ℝ)) ⁻¹' {1} := by
    ext x
    change (eligible s x).card = 1 ↔ ((eligible s x).card : ℝ) = 1
    norm_cast
  rw [eq]
  exact hm (measurableSet_singleton _)

/-- If there is one eligible coordinate the isolated weight is its weight;
on all other profiles the isolated weight vanishes. -/
theorem unique_eq {n : ℕ} (s : Set ℝ) [DecidablePred (· ∈ s)] (f : ℝ → ℝ)
    (out : ∀ y, y ∉ s → f y = 0) (x : Fin n → ℝ) :
    uniqueWeight s f x = (oneEvent s).indicator (fun y => ∑ i ∈ eligible s y, f (y i)) x := by
  classical
  by_cases h : x ∈ oneEvent s
  · rw [Set.indicator_of_mem h]
    obtain ⟨j,ej⟩ := Finset.card_eq_one.mp h
    have iso : x ∈ others s j := by
      apply mem_others.mpr
      intro k ne hk
      have H : k ∈ eligible s x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩
      simpa [ej,ne] using H
    rw [ej,Finset.sum_singleton,uniqueWeight,Finset.sum_eq_single j,Set.indicator_of_mem iso]
    · intro k _ ne
      have hn : x k ∉ s := mem_others.mp iso k ne
      simp [Set.indicator,out _ hn]
    · simp
  · rw [Set.indicator_of_notMem h,uniqueWeight]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : x i ∈ s
    · apply Set.indicator_of_notMem
      intro iso
      apply h
      apply Finset.card_eq_one.mpr
      refine ⟨i,?_⟩
      ext j
      by_cases eq : j = i
      · simp [eligible,eq,hi]
      · simp [eligible,eq,mem_others.mp iso j eq]
    · simp [Set.indicator,out _ hi]

theorem one_probability {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Set ℝ) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) (mass : (∑ i, (μ i).real s) = 1/4) :
    3/16 ≤ (Measure.pi μ).real (oneEvent s) ∧ (Measure.pi μ).real (oneEvent s) ≤ 1/4 := by
  let f := s.indicator (fun _ => (1:ℝ))
  have f0 (y) (hy : y ∉ s) : f y = 0 := Set.indicator_of_notMem hy _
  have iden (x : Fin n → ℝ) : uniqueWeight s f x = (oneEvent s).indicator (fun _ => (1:ℝ)) x := by
    rw [unique_eq s f f0]
    by_cases h : x ∈ oneEvent s
    · obtain ⟨j,ej⟩ := Finset.card_eq_one.mp h
      have hj : x j ∈ s := (Finset.mem_filter.mp (ej ▸ Finset.mem_singleton_self j : j ∈ eligible s x)).2
      simp [h,ej,f,hj]
    · simp [h]
  have hu := (unique_integral μ s hs mass.le f (measurable_const.indicator hs)
    (fun _ => (integrable_const _).indicator hs) (fun y => Set.indicator_nonneg (fun _ _ => zero_le_one) y)).2
  simp_rw [iden] at hu
  simp only [f,integral_indicator hs, integral_indicator (one_meas hs),setIntegral_one_eq_measureReal,mass] at hu
  refine ⟨by linarith,?_⟩
  have sub : oneEvent (n := n) s ⊆ ⋃ i : Fin n, Function.eval i ⁻¹' s := by
    intro x h
    have hm : (eligible s x).Nonempty := Finset.card_pos.mp (show 0 < (eligible s x).card by rw [show (eligible s x).card = 1 from h]; decide)
    obtain ⟨j,hj⟩ := hm
    exact Set.mem_iUnion.mpr ⟨j,(Finset.mem_filter.mp hj).2⟩
  have u := (measureReal_mono (μ := Measure.pi μ) sub).trans (measureReal_iUnion_fintype_le _)
  apply u.trans_eq
  rw [← mass]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg ENNReal.toReal ((measurePreserving_eval μ i).measure_preimage hs.nullMeasurableSet)

/-- Adding a middle band of mass at most one quarter preserves at least
two thirds of each isolated-coordinate surplus (equations 4.28–4.32). -/
theorem middle_comparison {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) (sub : s ⊆ t)
    (cap : (∑ j, (μ j).real s) ≤ 1/4) (mid : (∑ j, (μ j).real (t \ s)) ≤ 1/4)
    (i : Fin n) (f : ℝ → ℝ) (hf : Measurable f) (hn : ∀ y, 0 ≤ f y) :
    2/3 * (∫ x, (others s i).indicator (fun y => f (y i)) x ∂Measure.pi μ) ≤
      ∫ x, (others t i).indicator (fun y => f (y i)) x ∂Measure.pi μ := by
  classical
  let u := fun j => (μ j).real (t \ s) / (1 - (μ j).real s)
  have den (j) : (3/4:ℝ) ≤ 1-(μ j).real s := by
    have H := Finset.single_le_sum (f := fun k => (μ k).real s) (fun _ _ => measureReal_nonneg) (Finset.mem_univ j)
    linarith
  have un (j) : 0 ≤ u j := div_nonneg measureReal_nonneg (by linarith only [den j])
  have ub (j) : u j ≤ 4/3 * (μ j).real (t \ s) := by
    apply (div_le_iff₀ (by linarith only [den j] : 0 < 1-(μ j).real s)).mpr
    nlinarith [mul_le_mul_of_nonneg_left (den j) (measureReal_nonneg (μ := μ j) (s := t \ s))]
  have total := Finset.sum_le_sum (s := Finset.univ) fun j _ => ub j
  rw [← Finset.mul_sum] at total
  have total' : (∑ j, u j) ≤ 1/3 := by linarith only [total,mid]
  have u1 (j) : u j ≤ 1 := by
    have H := Finset.single_le_sum (f := u) (fun k _ => un k) (Finset.mem_univ j)
    linarith
  have rest := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i (Finset.univ : Finset (Fin n))) (fun j _ _ => un j)
  have good := product_failure u un u1 (Finset.univ.erase i)
  have der (j) : 1-(μ j).real t = (1-(μ j).real s)*(1-u j) := by
    have hpos : 0 < 1-(μ j).real s := by linarith only [den j]
    dsimp only [u]
    rw [measureReal_sdiff sub hs]
    field_simp
    ring
  rw [isolated_factor μ s hs i f hf,isolated_factor μ t ht i f hf]
  simp_rw [der]
  rw [Finset.prod_mul_distrib, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (integral_nonneg hn)
  rw [mul_comm (2/3:ℝ)]
  exact mul_le_mul_of_nonneg_left (by linarith only [good,rest,total']) (Finset.prod_nonneg fun j _ => sub_nonneg.mpr measureReal_le_one)

theorem unique_comparison {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) (sub : s ⊆ t)
    (cap : (∑ j, (μ j).real s) ≤ 1/4) (mid : (∑ j, (μ j).real (t \ s)) ≤ 1/4)
    (f : ℝ → ℝ) (hf : Measurable f) (hi : ∀ i, Integrable f (μ i)) (hn : ∀ y, 0 ≤ f y) :
    Integrable (uniqueWeight t f) (Measure.pi μ) ∧
      2/3 * (∫ x, uniqueWeight s f x ∂Measure.pi μ) ≤ ∫ x, uniqueWeight t f x ∂Measure.pi μ := by
  have int {A : Set ℝ} (hA : MeasurableSet A) (i) : Integrable ((others A i).indicator (fun y => f (y i))) (Measure.pi μ) :=
    (((measurePreserving_eval μ i).integrable_comp hf.aestronglyMeasurable).mpr (hi i)).indicator (measurable_others hA i)
  refine ⟨integrable_finsetSum _ (fun i _ => int ht i), ?_⟩
  unfold uniqueWeight
  rw [integral_finsetSum _ (fun i _ => int hs i),integral_finsetSum _ (fun i _ => int ht i),Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => middle_comparison μ s t hs ht sub cap mid i f hf hn

open StratifyMarkets.DoubleAuction

/-- The numerator in the definition of one trade splits at any intermediate price. -/
theorem one_trade_numerator {n m : ℕ} (I : DAInstance n m) (a b tB tS q : ℝ)
    (hB : tB ≤ b) (hS : a ≤ tS) (hq1 : tS ≤ q) (hq2 : q ≤ tB) :
    let B := Icc tB b
    let S := Icc a tS
    let f := B.indicator (fun y => y-q)
    let g := S.indicator (fun y => q-y)
    let μ := Measure.pi I.μB
    let ν := Measure.pi I.μS
    I.oneTrade a b tB tS * (μ.real (oneEvent B) * ν.real (oneEvent S)) =
      (∫ x, uniqueWeight B f x ∂μ)*ν.real (oneEvent S) + μ.real (oneEvent B)*(∫ y, uniqueWeight S g y ∂ν) := by
  classical
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  let B := Icc tB b
  let S := Icc a tS
  let μ := Measure.pi I.μB
  let ν := Measure.pi I.μS
  let EB := oneEvent (n := n) B
  let ES := oneEvent (n := m) S
  let f := B.indicator (fun y => y-q)
  let g := S.indicator (fun y => q-y)
  let U : (Fin n → ℝ) → ℝ := uniqueWeight B f
  let V : (Fin m → ℝ) → ℝ := uniqueWeight S g
  let LB := EB.indicator (fun _ => (1:ℝ))
  let LS := ES.indicator (fun _ => (1:ℝ))
  have ub (i) : Integrable f (I.μB i) := by
    have x : Integrable ((Icc q b).indicator (fun y => y-q)) (I.μB i) := (bounded_band (hq2.trans hB)).1
    have H := x.indicator (s := B) measurableSet_Icc
    have inB : B ⊆ Icc q b := Icc_subset_Icc_left hq2
    simpa only [indicator_indicator,inter_eq_self_of_subset_left inB] using H
  have us (j) : Integrable g (I.μS j) := by
    have x : Integrable ((Icc a q).indicator (fun y => q-y)) (I.μS j) := (bounded_band (hS.trans hq1)).2
    have H := x.indicator (s := S) measurableSet_Icc
    have inS : S ⊆ Icc a q := Icc_subset_Icc_right hq1
    simpa only [indicator_indicator,inter_eq_self_of_subset_left inS] using H
  have iU : Integrable U μ := integrable_finsetSum _ fun i _ =>
    (((measurePreserving_eval I.μB i).integrable_comp ((measurable_id.sub measurable_const).indicator measurableSet_Icc).aestronglyMeasurable).mpr (ub i)).indicator (measurable_others measurableSet_Icc i)
  have iV : Integrable V ν := integrable_finsetSum _ fun j _ =>
    (((measurePreserving_eval I.μS j).integrable_comp ((measurable_const.sub measurable_id).indicator measurableSet_Icc).aestronglyMeasurable).mpr (us j)).indicator (measurable_others measurableSet_Icc j)
  have mB : MeasurableSet EB := one_meas measurableSet_Icc
  have mS : MeasurableSet ES := one_meas measurableSet_Icc
  have lb : Integrable LB μ := (integrable_const _).indicator mB
  have ls : Integrable LS ν := (integrable_const _).indicator mS
  have eB : (∫ x, LB x ∂μ) = μ.real EB := by simp [LB,integral_indicator mB]
  have eS : (∫ y, LS y ∂ν) = ν.real ES := by simp [LS,integral_indicator mS]
  let pay := fun z : (Fin n → ℝ) × (Fin m → ℝ) => if (inRange tB b z.1).card = 1 ∧ (inRange a tS z.2).card = 1
    then ∑ i ∈ inRange tB b z.1, ∑ j ∈ inRange a tS z.2, (z.1 i - z.2 j) else 0
  have decomp (z : (Fin n → ℝ) × (Fin m → ℝ)) : pay z = U z.1 * LS z.2 + LB z.1 * V z.2 := by
    change (if (eligible B z.1).card = 1 ∧ (eligible S z.2).card = 1 then ∑ i ∈ eligible B z.1, ∑ j ∈ eligible S z.2, (z.1 i - z.2 j) else 0) = _
    dsimp only [U,V]
    rw [unique_eq B f (fun _ h => Set.indicator_of_notMem h _),unique_eq S g (fun _ h => Set.indicator_of_notMem h _)]
    by_cases bH : z.1 ∈ EB <;> by_cases sH : z.2 ∈ ES
    · obtain ⟨i,hi⟩ := Finset.card_eq_one.mp bH
      obtain ⟨j,hj⟩ := Finset.card_eq_one.mp sH
      have bi : z.1 i ∈ B := (Finset.mem_filter.mp (hi ▸ Finset.mem_singleton_self i : i ∈ eligible B z.1)).2
      have sj : z.2 j ∈ S := (Finset.mem_filter.mp (hj ▸ Finset.mem_singleton_self j : j ∈ eligible S z.2)).2
      change z.1 ∈ oneEvent B at bH
      change z.2 ∈ oneEvent S at sH
      simp [hi,hj,LB,LS,EB,ES,bH,sH,f,g,bi,sj]
    all_goals
      have no : ¬((eligible B z.1).card = 1 ∧ (eligible S z.2).card = 1) := by
        intro H
        first | exact bH H.1 | exact sH H.2
      rw [if_neg no]
      dsimp only [LB,LS]
      simp [EB,ES] at bH sH ⊢ <;> simp [Set.indicator,bH,sH]
  have den : (I.law {x | (inRange tB b x.1).card = 1 ∧ (inRange a tS x.2).card = 1}).toReal = μ.real EB * ν.real ES := by
    change ((μ.prod ν) (EB ×ˢ ES)).toReal = _
    rw [Measure.prod_prod,ENNReal.toReal_mul]; rfl
  have N : (∫ z, pay z ∂I.law) = (∫ x, U x ∂μ)*ν.real ES + μ.real EB*(∫ y, V y ∂ν) := by
    simp_rw [decomp]
    change (∫ z, _ ∂μ.prod ν) = _
    rw [integral_add (iU.mul_prod ls) (lb.mul_prod iV),integral_prod_mul,integral_prod_mul,eB,eS]
  change I.oneTrade a b tB tS * (μ.real EB*ν.real ES) = _
  rw [← N]; unfold DAInstance.oneTrade
  rw [den]
  change (∫ z, pay z ∂I.law) / _ * _ = ∫ z, pay z ∂I.law
  by_cases h : μ.real EB * ν.real ES = 0
  · have hnull : I.law (EB ×ˢ ES) = 0 := by
      have : (I.law (EB ×ˢ ES)).toReal = 0 := den.trans h
      exact (ENNReal.toReal_eq_zero_iff _).mp this |>.resolve_right (by unfold DAInstance.law; exact measure_ne_top _ _)
    have zae : ∀ᵐ z ∂I.law, z ∉ EB ×ˢ ES := compl_mem_ae_iff.mpr hnull
    have nil : ∫ z, pay z ∂I.law = 0 := integral_eq_zero_of_ae (zae.mono (fun z hz => by
      have no : ¬((inRange tB b z.1).card = 1 ∧ (inRange a tS z.2).card = 1) := hz
      simp [pay,no]))
    rw [nil]; simp
  · exact div_mul_cancel₀ _ h

end StratifyMarkets.Scarcity
end

-- Solutions.StratifyMarketsBandMeans
section
open MeasureTheory Set StratifyMarkets.Participation StratifyMarkets.Scarcity StratifyMarkets.DoubleAuction
namespace StratifyMarkets.BandMeans

/-- The sum of values in the band on the event of a unique participant. -/
noncomputable def singleValue {n : ℕ} (lo hi : ℝ) (x : Fin n → ℝ) : ℝ :=
  (oneEvent (Icc lo hi)).indicator (fun y => ∑ i ∈ eligible (Icc lo hi) y, y i) x

noncomputable def mean {n : ℕ} (μ : Measure (Fin n → ℝ)) (lo hi : ℝ) : ℝ :=
  (∫ x, singleValue lo hi x ∂μ) / μ.real (oneEvent (Icc lo hi))

theorem value_bounds {n : ℕ} (lo hi : ℝ) (x : Fin n → ℝ) :
    (oneEvent (Icc lo hi)).indicator (fun _ => lo) x ≤ singleValue lo hi x ∧
    singleValue lo hi x ≤ (oneEvent (Icc lo hi)).indicator (fun _ => hi) x := by
  classical
  by_cases h : x ∈ oneEvent (Icc lo hi)
  · obtain ⟨i,hi'⟩ := Finset.card_eq_one.mp h
    have mem : i ∈ eligible (Icc lo hi) x := hi' ▸ Finset.mem_singleton_self i
    simpa [singleValue,h,hi'] using (Finset.mem_filter.mp mem).2
  · simp [singleValue,h]

theorem integral_bounds {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hh : lo ≤ hi) :
    Integrable (singleValue (n := n) lo hi) μ ∧
    lo * μ.real (oneEvent (Icc lo hi)) ≤ ∫ x, singleValue lo hi x ∂μ ∧
    (∫ x, singleValue lo hi x ∂μ) ≤ hi * μ.real (oneEvent (Icc lo hi)) := by
  classical
  let E := oneEvent (n := n) (Icc lo hi)
  have hE : MeasurableSet E := one_meas measurableSet_Icc
  have meas : Measurable (singleValue (n := n) lo hi) := by
    unfold singleValue
    apply Measurable.indicator _ hE
    have eq : (fun y : Fin n → ℝ => ∑ i ∈ eligible (Icc lo hi) y, y i) =
        fun y => ∑ i, (Icc lo hi).indicator id (y i) := by
      funext y
      simp only [eligible,Finset.sum_filter,Set.indicator,id_eq]
    rw [eq]
    exact Finset.measurable_sum _ fun i _ => (measurable_id.indicator measurableSet_Icc).comp (measurable_pi_apply i)
  have int : Integrable (singleValue (n := n) lo hi) μ := by
    apply Integrable.of_bound meas.aestronglyMeasurable hi
    filter_upwards with x
    obtain ⟨L,U⟩ := value_bounds lo hi x
    have nn := (Set.indicator_nonneg (s := E) (fun _ _ => hlo) x).trans L
    rw [Real.norm_eq_abs,abs_of_nonneg nn]
    exact U.trans (by by_cases h : x ∈ E <;> simp [E] at h ⊢ <;> simp [h,hlo.trans hh])
  have compute (v : ℝ) : (∫ x, E.indicator (fun _ => v) x ∂μ) = v * μ.real E := by
    simp [integral_indicator hE,setIntegral_const,smul_eq_mul,mul_comm,measureReal_def]
  refine ⟨int,?_,?_⟩
  · rw [← compute]
    exact integral_mono ((integrable_const _).indicator hE) int fun x => (value_bounds lo hi x).1
  · rw [← compute]
    exact integral_mono int ((integrable_const _).indicator hE) fun x => (value_bounds lo hi x).2

theorem mean_mem {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hh : lo ≤ hi) (pos : 0 < μ.real (oneEvent (Icc lo hi))) :
    mean μ lo hi ∈ Icc lo hi := by
  obtain ⟨_,low,up⟩ := integral_bounds μ hlo hh
  exact ⟨(le_div_iff₀ pos).mpr low, (div_le_iff₀ pos).mpr up⟩

/-- Independence turns the two-sided one-trade benchmark into a difference
of one-sided means. This allows gains from consecutive matched bands to telescope. -/
theorem oneTrade_eq {n m : ℕ} (I : DAInstance n m) {a b tB tS : ℝ} (ha : 0 ≤ a)
    (htB : I.IsBuyerThreshold a b tB) (htS : I.IsSellerThreshold a b tS) :
    I.oneTrade a b tB tS = mean (Measure.pi I.μB) tB b - mean (Measure.pi I.μS) a tS := by
  classical
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  let μ := Measure.pi I.μB
  let ν := Measure.pi I.μS
  let B := oneEvent (n := n) (Icc tB b)
  let S := oneEvent (n := m) (Icc a tS)
  let lb := B.indicator (fun _ => (1:ℝ))
  let ls := S.indicator (fun _ => (1:ℝ))
  have eb : MeasurableSet B := one_meas measurableSet_Icc
  have es : MeasurableSet S := one_meas measurableSet_Icc
  have lbint : Integrable lb μ := (integrable_const _).indicator eb
  have lsint : Integrable ls ν := (integrable_const _).indicator es
  have ib := (integral_bounds μ (ha.trans htB.1.1) htB.1.2).1
  have is' := (integral_bounds ν ha htS.1.1).1
  have bp : 0 < μ.real B := lt_of_lt_of_le (by norm_num : (0:ℝ) < 3/16)
    (one_probability I.μB (Icc tB b) measurableSet_Icc htB.2).1
  have sp : 0 < ν.real S := lt_of_lt_of_le (by norm_num : (0:ℝ) < 3/16)
    (one_probability I.μS (Icc a tS) measurableSet_Icc htS.2).1
  have decomp (z : (Fin n → ℝ) × (Fin m → ℝ)) :
      (if (inRange tB b z.1).card = 1 ∧ (inRange a tS z.2).card = 1 then
        ∑ i ∈ inRange tB b z.1, ∑ j ∈ inRange a tS z.2, (z.1 i - z.2 j) else 0) =
        singleValue tB b z.1 * ls z.2 - lb z.1 * singleValue a tS z.2 := by
    change (if (eligible (Icc tB b) z.1).card = 1 ∧ (eligible (Icc a tS) z.2).card = 1 then ∑ i ∈ eligible (Icc tB b) z.1, ∑ j ∈ eligible (Icc a tS) z.2, (z.1 i - z.2 j) else 0) = _
    by_cases h : z.1 ∈ B <;> by_cases k : z.2 ∈ S
    · obtain ⟨i,ei⟩ := Finset.card_eq_one.mp h
      obtain ⟨j,ej⟩ := Finset.card_eq_one.mp k
      simp [h,k,ei,ej,lb,ls,singleValue,show z.1 ∈ oneEvent (Icc tB b) from h,show z.2 ∈ oneEvent (Icc a tS) from k]
    all_goals
      have no : ¬((eligible (Icc tB b) z.1).card = 1 ∧ (eligible (Icc a tS) z.2).card = 1) := by
        intro H
        first | exact h H.1 | exact k H.2
      rw [if_neg no]
      dsimp only [lb,ls,singleValue,B,S] at h k ⊢
      simp [h,k]
  have den : (I.law {z | (inRange tB b z.1).card = 1 ∧ (inRange a tS z.2).card = 1}).toReal = μ.real B * ν.real S := by
    change ((μ.prod ν) (B ×ˢ S)).toReal = _
    simp [measureReal_def]
  rw [DAInstance.oneTrade,den]
  simp_rw [decomp]
  change (∫ z, singleValue tB b z.1 * ls z.2 - lb z.1 * singleValue a tS z.2 ∂μ.prod ν) / _ = _
  rw [integral_sub (ib.mul_prod lsint) (lbint.mul_prod is'),integral_prod_mul,integral_prod_mul]
  have evb : (∫ x, lb x ∂μ) = μ.real B := by simp [lb,integral_indicator eb]
  have evs : (∫ x, ls x ∂ν) = ν.real S := by simp [ls,integral_indicator es]
  rw [evb,evs]
  change _ = (∫ x, singleValue tB b x ∂μ) / μ.real B - (∫ x, singleValue a tS x ∂ν) / ν.real S
  field_simp [bp.ne',sp.ne']

end StratifyMarkets.BandMeans
end

-- Solutions.StratifyMarketsRefinements
section
open MeasureTheory Set
namespace StratifyMarkets.DoubleAuction.Stratification

/-- The shared boundary belongs to both adjacent pieces. The membership rule
uses the left piece's copy at exactly the join. -/
def edge (σ ρ : Stratification) (i : Fin (σ.N + ρ.N + 1)) : ℝ :=
  if h : i.val ≤ σ.N then σ.m ⟨i.val, by omega⟩ else ρ.m ⟨i.val - σ.N, by omega⟩

def tagPrice (σ ρ : Stratification) : Fin (σ.N + ρ.N) → ℝ :=
  Fin.addCases (motive := fun _ => ℝ) σ.p ρ.p

theorem left_edges (σ ρ : Stratification) (k : Fin σ.N) :
    edge σ ρ (k.castAdd ρ.N).castSucc = σ.m k.castSucc ∧
    edge σ ρ (k.castAdd ρ.N).succ = σ.m k.succ := by
  have h₁ : k.val ≤ σ.N := k.isLt.le
  have h₂ : k.val + 1 ≤ σ.N := k.isLt
  simp [edge, h₁, h₂]
  exact ⟨rfl,rfl⟩

theorem right_edges (σ ρ : Stratification) (join : σ.m (Fin.last σ.N) = ρ.m 0)
    (k : Fin ρ.N) :
    edge σ ρ (k.natAdd σ.N).castSucc = ρ.m k.castSucc ∧
    edge σ ρ (k.natAdd σ.N).succ = ρ.m k.succ := by
  have positive : ¬ σ.N + k.val + 1 ≤ σ.N := by omega
  constructor
  · by_cases h : k.val = 0
    · have hzero : k.castSucc = 0 := Fin.ext h
      rw [hzero, ← join]
      simp [edge, h]
      rfl
    · have hh : ¬σ.N + k.val ≤ σ.N := by omega
      simp [edge, hh]
      rfl
  · simp [edge, Nat.add_assoc]
    rfl

noncomputable def concatenate (σ ρ : Stratification) (join : σ.m (Fin.last σ.N) = ρ.m 0) :
    Stratification where
  N := σ.N + ρ.N
  one_le_N := by have := σ.one_le_N; omega
  m := edge σ ρ
  p := tagPrice σ ρ
  zero_le_m := by simpa [edge] using σ.zero_le_m
  m_le_one := by
    have h : ¬σ.N + ρ.N ≤ σ.N := by have := ρ.one_le_N; omega
    simp [edge, h]
    exact ρ.m_le_one
  m_strictMono := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    refine Fin.addCases (motive := fun k => edge σ ρ k.castSucc < edge σ ρ k.succ) ?_ ?_ i
    · intro k
      rw [(left_edges σ ρ k).1, (left_edges σ ρ k).2]
      exact σ.m_strictMono k.castSucc_lt_succ
    · intro k
      rw [(right_edges σ ρ join k).1, (right_edges σ ρ join k).2]
      exact ρ.m_strictMono k.castSucc_lt_succ
  p_mem := by
    intro i
    refine Fin.addCases (motive := fun k => edge σ ρ k.castSucc ≤ tagPrice σ ρ k ∧
      tagPrice σ ρ k ≤ edge σ ρ k.succ) ?_ ?_ i
    · intro k
      rw [(left_edges σ ρ k).1, (left_edges σ ρ k).2]
      simpa [tagPrice] using σ.p_mem k
    · intro k
      rw [(right_edges σ ρ join k).1, (right_edges σ ρ join k).2]
      simpa [tagPrice] using ρ.p_mem k

theorem concatenate_start (σ ρ : Stratification) (join) :
    (concatenate σ ρ join).m 0 = σ.m 0 := by simp [concatenate, edge]

theorem concatenate_end (σ ρ : Stratification) (join) :
    (concatenate σ ρ join).m (Fin.last (concatenate σ ρ join).N) = ρ.m (Fin.last ρ.N) := by
  have h : ¬σ.N + ρ.N ≤ σ.N := by have := ρ.one_le_N; omega
  simp [concatenate, edge, h]
  rfl

theorem concatenate_gains {n m : ℕ} (I : DAInstance n m) (σ ρ : Stratification) (join) :
    I.strat (concatenate σ ρ join) = I.strat σ + I.strat ρ := by
  change (∑ k : Fin (σ.N + ρ.N), I.worstRationedIn (edge σ ρ k.castSucc)
    (tagPrice σ ρ k) (edge σ ρ k.succ)) = _
  rw [Fin.sum_univ_add]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro k _
    rw [(left_edges σ ρ k).1, (left_edges σ ρ k).2]
    simp [tagPrice]
  · apply Finset.sum_congr rfl
    intro k _
    rw [(right_edges σ ρ join k).1, (right_edges σ ρ join k).2]
    simp [tagPrice]

/-- Glue all pieces of a nonempty partition, preserving the interval ends
and adding their gains exactly. The number of pieces is arbitrary. -/
theorem assemble_chain {n m : ℕ} (I : DAInstance n m) (d : ℕ)
    (pieces : Fin (d+1) → Stratification)
    (join : ∀ i : Fin d, (pieces i.castSucc).m (Fin.last (pieces i.castSucc).N) =
      (pieces i.succ).m 0) :
    ∃ σ : Stratification, σ.m 0 = (pieces 0).m 0 ∧
      σ.m (Fin.last σ.N) = (pieces (Fin.last d)).m (Fin.last (pieces (Fin.last d)).N) ∧
      I.strat σ = ∑ i, I.strat (pieces i) := by
  induction d with
  | zero => exact ⟨pieces 0,rfl,rfl,by rw [Fin.sum_univ_one]⟩
  | succ d ih =>
    let pref : Fin (d+1) → Stratification := fun i => pieces i.castSucc
    have chain (i : Fin d) : (pref i.castSucc).m (Fin.last (pref i.castSucc).N) =
        (pref i.succ).m 0 := join i.castSucc
    obtain ⟨σ,hl,hr,hg⟩ := ih pref chain
    let last := pieces (Fin.last (d+1))
    have j : σ.m (Fin.last σ.N) = last.m 0 := hr.trans (join (Fin.last d))
    refine ⟨concatenate σ last j, (concatenate_start _ _ _).trans hl, concatenate_end _ _ _, ?_⟩
    rw [concatenate_gains, hg, Fin.sum_univ_castSucc (fun i : Fin (d+2) => I.strat (pieces i))]

theorem assemble_refinements {n m : ℕ} (I : DAInstance n m) (base : Stratification)
    (pieces : Fin base.N → Stratification)
    (left : ∀ i, (pieces i).m 0 = base.m i.castSucc)
    (right : ∀ i, (pieces i).m (Fin.last (pieces i).N) = base.m i.succ) :
    ∃ σ : Stratification, I.strat σ = ∑ i, I.strat (pieces i) := by
  obtain ⟨N,hN,edges,prices,first,last,strict,valid⟩ := base
  cases N with
  | zero => omega
  | succ d =>
    have join (i : Fin d) : (pieces i.castSucc).m (Fin.last (pieces i.castSucc).N) =
        (pieces i.succ).m 0 := (right i.castSucc).trans (left i.succ).symm
    obtain ⟨σ,_,_,h⟩ := assemble_chain I d pieces join
    exact ⟨σ,h⟩

end StratifyMarkets.DoubleAuction.Stratification
end

-- Solutions.StratifyMarketsBandCapture
section
open Set MeasureTheory StratifyMarkets.DoubleAuction StratifyMarkets.BandMeans
namespace StratifyMarkets.BandPartition

theorem path_edges {n m : ℕ} {I : DAInstance n m} {tB b s t prev : ℝ}
    {xs : List Band} (P : Path I tB b s t prev xs) :
    (∀ z ∈ xs, z.correct I ∧ s ≤ z.sl ∧ z.bh ≤ b) ∧
    xs.IsChain (fun z w => z.sl ≤ w.sl) := by
  induction P with
  | stop z hs ht hB hb hc =>
    exact ⟨by simpa [hs,hb] using (show z.correct I ∧ s ≤ s ∧ b ≤ b from ⟨hc,le_rfl,le_rfl⟩),by simp⟩
  | step z hs ht ps adv ub hc rest ih =>
    obtain ⟨all,chain⟩ := ih
    have start := (hs ▸ z.order.1).trans (ht ▸ adv)
    constructor
    · intro w hw
      rcases List.mem_cons.mp hw with e|mem
      · subst w; exact ⟨hc,hs.ge,ub⟩
      · obtain ⟨c,low,high⟩ := all w mem
        exact ⟨c,start.trans low,high⟩
    · apply List.isChain_cons.mpr
      refine ⟨?_,chain⟩
      intro w hw
      exact hs.le.trans (start.trans (all w (List.mem_of_mem_head? hw)).2.1)

noncomputable def gain {n m : ℕ} (I : DAInstance n m) (z : Band) := I.oneTrade z.sl z.bh z.bl z.sh

theorem telescope {n m : ℕ} {I : DAInstance n m} {tB b s t prev : ℝ} {xs : List Band}
    (P : Path I tB b s t prev xs) (nonneg : 0 ≤ s) (bb : tB ≤ b) (massB : I.expBuyersIn tB b = 1/4) :
    mean (Measure.pi I.μB) tB b - mean (Measure.pi I.μS) s t ≤ (xs.map (gain I)).sum := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  induction P with
  | stop z hs ht hB hb hc =>
    have h := z.order
    have e := oneTrade_eq I (show 0 ≤ z.sl from hs ▸ nonneg)
      (show I.IsBuyerThreshold z.sl z.bh z.bl from ⟨⟨h.1.trans (h.2.1.trans h.2.2.1),h.2.2.2⟩,hc.2.1⟩)
      (show I.IsSellerThreshold z.sl z.bh z.sh from ⟨⟨h.1,h.2.1.trans (h.2.2.1.trans h.2.2.2)⟩,hc.1⟩)
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    change _ ≤ I.oneTrade _ _ _ _
    rw [e,hs,ht,hB,hb]
  | @step s t prev next zs z hs ht ps adv ub hc rest ih =>
    have h := z.order
    have zpos : 0 ≤ z.sl := hs ▸ nonneg
    have e := oneTrade_eq I zpos
      (show I.IsBuyerThreshold z.sl z.bh z.bl from ⟨⟨h.1.trans (h.2.1.trans h.2.2.1),h.2.2.2⟩,hc.2.1⟩)
      (show I.IsSellerThreshold z.sl z.bh z.sh from ⟨⟨h.1,h.2.1.trans (h.2.2.1.trans h.2.2.2)⟩,hc.1⟩)
    have npos : 0 ≤ next := zpos.trans (h.1.trans (ht.trans_le adv))
    have nr : next ≤ z.bl ∧ I.expSellersIn next z.bl = 1/4 := by
      cases rest with
      | stop w a d _ _ wc | step w a d _ _ _ wc _ =>
        exact ⟨a ▸ d ▸ w.order.1,a ▸ d ▸ wc.1⟩
    have bpos := lt_of_lt_of_le (by norm_num : (0:ℝ) < 3/16)
      (StratifyMarkets.Scarcity.one_probability I.μB (Icc z.bl z.bh) measurableSet_Icc hc.2.1).1
    have spos := lt_of_lt_of_le (by norm_num : (0:ℝ) < 3/16)
      (StratifyMarkets.Scarcity.one_probability I.μS (Icc next z.bl) measurableSet_Icc nr.2).1
    have bu := (mean_mem (Measure.pi I.μB) (zpos.trans (h.1.trans (h.2.1.trans h.2.2.1))) h.2.2.2 bpos).1
    have se := (mean_mem (Measure.pi I.μS) npos nr.1 spos).2
    have rel := ih npos
    change _ ≤ I.oneTrade z.sl z.bh z.bl z.sh + (zs.map (gain I)).sum
    rw [e,hs,ht]
    linarith


def color : List Band → List Band
  | a::_::_::_::xs => a::color xs
  | [] => []
  | [a] => [a]
  | [a,_] => [a]
  | [a,_,_] => [a]

private theorem color_head (a : Band) (xs : List Band) :
    color (a::xs) = a::color xs.tail.tail.tail := by
  cases xs with
  | nil => rfl
  | cons b ys => cases ys with
    | nil => rfl
    | cons c zs => cases zs <;> rfl

theorem color_sub (xs : List Band) : ∀ z ∈ color xs, z ∈ xs := by
  match xs with
  | [] => simp [color]
  | [a] => simp [color]
  | [a,b] => simp [color]
  | [a,b,c] => simp [color]
  | a::b::c::d::xs =>
    intro z hz
    rcases List.mem_cons.mp hz with eq|mem
    · simp [eq]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (color_sub xs z mem))))
termination_by xs.length

def EndpointOrder (z w : Band) : Prop := z.bh ≤ w.sl

theorem color_order {n m : ℕ} {I : DAInstance n m} {tB b s t prev : ℝ} {xs : List Band}
    (P : Path I tB b s t prev xs) : (color xs).IsChain EndpointOrder := by
  match xs with
  | [] => simp [color]
  | [a] => simp [color]
  | [a,c] => simp [color]
  | [a,c,d] => simp [color]
  | [a,c,d,e] => simp [color]
  | a::c::d::e::f::xs =>
    cases P with | step _ _ _ _ _ _ _ p2 =>
      cases p2 with | step _ _ _ price2 _ _ _ p3 =>
        cases p3 with | step _ _ _ price3 _ _ _ p4 =>
          cases p4 with | step _ _ _ _ advance4 _ _ p5 =>
            have ordered := color_order p5
            have endpt : a.bh ≤ f.sl := by
              cases p5 with
              | stop _ fl _ _ _ _ | step _ fl _ _ _ _ _ _ =>
                exact price2.trans (c.order.2.2.2.trans (price3.trans (advance4.trans fl.ge)))
            change (a :: color (f::xs)).IsChain _
            rw [color_head]
            apply List.isChain_cons_cons.mpr
            rw [← color_head]
            exact ⟨endpt,ordered⟩
termination_by xs.length

theorem tail_orders {n m : ℕ} {I : DAInstance n m} {tB b s t prev : ℝ} {xs : List Band}
    (P : Path I tB b s t prev xs) (d : ℕ) : (color (xs.drop d)).IsChain EndpointOrder := by
  induction d generalizing s t prev xs with
  | zero => simpa using color_order P
  | succ d ih =>
    cases P with
    | stop z _ _ _ _ _ => simp [color]
    | step z _ _ _ _ _ _ rest => simpa using ih rest

theorem color_sum (f : Band → ℝ) (xs : List Band) :
    (xs.map f).sum = ((color xs).map f).sum + ((color xs.tail).map f).sum +
      ((color xs.tail.tail).map f).sum + ((color xs.tail.tail.tail).map f).sum := by
  induction xs with
  | nil => simp [color]
  | cons a xs ih =>
    rw [color_head]
    simp only [List.tail_cons,List.map_cons,List.sum_cons] at *
    linarith


theorem submarket_nonneg {n m : ℕ} (I : DAInstance n m) (a p b : ℝ) :
    0 ≤ I.worstRationedIn a p b := by
  apply integral_nonneg
  intro x
  apply Finset.le_inf'
  intro T hT
  obtain ⟨hB,hS⟩ := Finset.mem_product.mp hT
  obtain ⟨inB,cB⟩ := Finset.mem_powersetCard.mp hB
  obtain ⟨inS,cS⟩ := Finset.mem_powersetCard.mp hS
  have sc : (∑ j ∈ T.2, x.2 j) ≤ ∑ _j ∈ T.2, p := Finset.sum_le_sum fun j hj => (Finset.mem_filter.mp (inS hj)).2.2
  have vb : (∑ _i ∈ T.1, p) ≤ ∑ i ∈ T.1, x.1 i := Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp (inB hi)).2.1
  exact sub_nonneg.mpr (sc.trans ((by simp [cB,cS] : (∑ _j ∈ T.2, p) ≤ ∑ _i ∈ T.1, p).trans vb))

private theorem strat_nn {n m : ℕ} (I : DAInstance n m) (σ : Stratification) : 0 ≤ I.strat σ :=
  Finset.sum_nonneg fun _ _ => submarket_nonneg I _ _ _

private theorem fill_left {n m : ℕ} (I : DAInstance n m) (σ : Stratification) {a : ℝ} (ha : 0 ≤ a)
    (l : a ≤ σ.m 0) : ∃ ρ : Stratification, ρ.m 0 = a ∧
      ρ.m (Fin.last ρ.N) = σ.m (Fin.last σ.N) ∧ I.strat σ ≤ I.strat ρ := by
  rcases l.eq_or_lt with eql|gap
  · exact ⟨σ,eql.symm,rfl,le_rfl⟩
  · have u : σ.m 0 ≤ 1 := (σ.m_strictMono.monotone (Fin.zero_le _)).trans σ.m_le_one
    let filler := single_submarket a (σ.m 0) a ha gap u le_rfl gap.le
    have j : filler.m (Fin.last filler.N) = σ.m 0 := by rfl
    refine ⟨filler.concatenate σ j,filler.concatenate_start σ j,filler.concatenate_end σ j,?_⟩
    rw [filler.concatenate_gains I]
    linarith [strat_nn I filler]

private theorem fill_right {n m : ℕ} (I : DAInstance n m) (σ : Stratification) {b : ℝ} (hb : b ≤ 1)
    (u : σ.m (Fin.last σ.N) ≤ b) : ∃ ρ : Stratification, ρ.m 0 = σ.m 0 ∧
      ρ.m (Fin.last ρ.N) = b ∧ I.strat σ ≤ I.strat ρ := by
  rcases u.eq_or_lt with eq|gap
  · exact ⟨σ,rfl,eq,le_rfl⟩
  · let l := σ.m (Fin.last σ.N)
    have hl : 0 ≤ l := σ.zero_le_m.trans (σ.m_strictMono.monotone (Fin.zero_le _))
    let filler := single_submarket l b l hl gap hb le_rfl gap.le
    have j : σ.m (Fin.last σ.N) = filler.m 0 := rfl
    refine ⟨σ.concatenate filler j,σ.concatenate_start filler j,σ.concatenate_end filler j,?_⟩
    rw [σ.concatenate_gains I]
    linarith [strat_nn I filler]

theorem gather {n m : ℕ} (I : DAInstance n m) (xs : List Band) {a b : ℝ}
    (ha : 0 ≤ a) (ab : a < b) (hb : b ≤ 1) (chain : xs.IsChain EndpointOrder)
    (bounds : ∀ z ∈ xs, z.correct I ∧ a ≤ z.sl ∧ z.bh ≤ b) :
    ∃ σ : Stratification, σ.m 0 = a ∧ σ.m (Fin.last σ.N) = b ∧
      3/128 * (xs.map (gain I)).sum ≤ I.strat σ := by
  cases xs with
  | nil =>
    let ρ := single_submarket a b a ha ab hb le_rfl ab.le
    exact ⟨ρ,rfl,rfl,by simpa using strat_nn I ρ⟩
  | cons z xs =>
    obtain ⟨hc,lo,hi⟩ := bounds z List.mem_cons_self
    have h := z.order
    have sellerWidth : z.sl < z.sh := by
      refine lt_of_le_of_ne h.1 ?_
      intro eq
      have H := hc.1
      rw [eq,seller_same] at H
      norm_num at H
    have zz : z.sl < z.bh := sellerWidth.trans_le (h.2.1.trans (h.2.2.1.trans h.2.2.2))
    obtain ⟨one,hl,hr,hg⟩ := single_pair I (ha.trans lo) zz (hi.trans hb)
      (show I.IsBuyerThreshold z.sl z.bh z.bl from ⟨⟨h.1.trans (h.2.1.trans h.2.2.1),h.2.2.2⟩,hc.2.1⟩)
      (show I.IsSellerThreshold z.sl z.bh z.sh from ⟨⟨h.1,h.2.1.trans (h.2.2.1.trans h.2.2.2)⟩,hc.1⟩)
      h.2.1 h.2.2.1 hc.2.2.2 hc.2.2.1
    obtain ⟨left,la,lr,lg⟩ := fill_left I one ha (hl ▸ lo)
    have first : 3/128 * gain I z ≤ I.strat left := hg.trans lg
    have last := lr.trans hr
    cases xs with
    | nil =>
      obtain ⟨ρ,ρa,ρb,ρg⟩ := fill_right I left hb (last ▸ hi)
      exact ⟨ρ,ρa.trans la,ρb,by simpa using first.trans ρg⟩
    | cons w ws =>
      have sep := (List.isChain_cons_cons.mp chain).1
      have asc : (w::ws).Pairwise (fun u v : Band => u.sl ≤ v.sl) := by
        apply List.isChain_iff_pairwise.mp
        apply (List.isChain_cons_cons.mp chain).2.imp
        intro x y xy
        exact x.order.1.trans (x.order.2.1.trans (x.order.2.2.1.trans (x.order.2.2.2.trans xy)))
      have next (v) (hv : v ∈ w::ws) : v.correct I ∧ z.bh ≤ v.sl ∧ v.bh ≤ b := by
        obtain ⟨vc,_,vb⟩ := bounds v (List.mem_cons_of_mem z hv)
        rcases List.mem_cons.mp hv with eq|mem
        · exact ⟨vc,eq ▸ sep,vb⟩
        · exact ⟨vc,sep.trans ((List.pairwise_cons.mp asc).1 v mem),vb⟩
      have W := next w List.mem_cons_self
      have wwidth : w.sl < w.sh := by
        refine lt_of_le_of_ne w.order.1 ?_
        intro eq
        have H := W.1.1
        rw [eq,seller_same] at H
        norm_num at H
      have upper : z.bh < b := W.2.1.trans_lt (wwidth.trans_le
        (w.order.2.1.trans (w.order.2.2.1.trans (w.order.2.2.2.trans W.2.2))))
      obtain ⟨right,rl,rr,rg⟩ := gather I (w::ws) ((ha.trans lo).trans zz.le) upper hb
        (List.isChain_cons_cons.mp chain).2 next
      have join := last.trans rl.symm
      refine ⟨left.concatenate right join,(left.concatenate_start right join).trans la,
        (left.concatenate_end right join).trans rr,?_⟩
      rw [Stratification.concatenate_gains]
      change 3/128 * (gain I z + ((w::ws).map (gain I)).sum) ≤ _
      linarith
termination_by xs.length

end StratifyMarkets.BandPartition
end

-- Solutions.Sol_StratifyMarkets_DoubleAuction_lemma_4_18
section
open MeasureTheory Set StratifyMarkets.DoubleAuction StratifyMarkets.BandMeans StratifyMarkets.BandPartition

theorem solution {n m : ℕ} (I : DAInstance n m) (a b tB tS : ℝ)
    (ha : 0 ≤ a) (ab : a < b) (hb : b ≤ 1)
    (hB : I.IsBuyerThreshold a b tB) (hS : I.IsSellerThreshold a b tS) (hSB : tS ≤ tB) :
    ∃ σ : Stratification, σ.m 0 = a ∧ σ.m (Fin.last σ.N) = b ∧
      3 / 512 * I.oneTrade a b tB tS ≤ I.strat σ := by
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  have bound : I.expSellersIn tS tB ≤ (4*m : ℕ)/ (4:ℝ) := by
    have upper : I.expSellersIn tS tB ≤ ∑ _ : Fin m, (1:ℝ) :=
      Finset.sum_le_sum fun j _ => measureReal_le_one (μ := I.μS j)
    simpa using upper
  obtain ⟨xs,P⟩ := build_path I hB.1.2 hB.2 (4*m) (s := a) (t := tS) (prev := tS)
    hS.1.1 hSB hS.2 le_rfl (by rw [buyer_same]; norm_num) bound
  have members := (path_edges P).1
  have bench := telescope P ha hB.1.2 hB.2
  rw [← oneTrade_eq I ha hB hS] at bench
  have capture (d : ℕ) : ∃ σ : Stratification, σ.m 0 = a ∧ σ.m (Fin.last σ.N) = b ∧
      3/128 * (((color (xs.drop d)).map (gain I)).sum) ≤ I.strat σ := by
    apply gather I _ ha ab hb (tail_orders P d)
    intro z hz
    exact members z (List.mem_of_mem_drop (color_sub _ z hz))
  obtain ⟨σ0,l0,r0,g0⟩ := capture 0
  obtain ⟨σ1,l1,r1,g1⟩ := capture 1
  obtain ⟨σ2,l2,r2,g2⟩ := capture 2
  obtain ⟨σ3,l3,r3,g3⟩ := capture 3
  have total := color_sum (gain I) xs
  have drop1 : xs.drop 1 = xs.tail := by cases xs <;> rfl
  have drop2 : xs.drop 2 = xs.tail.tail := by
    cases xs with | nil => rfl | cons y ys => cases ys <;> rfl
  have drop3 : xs.drop 3 = xs.tail.tail.tail := by
    cases xs with
    | nil => rfl
    | cons y ys => cases ys with
      | nil => rfl
      | cons w ws => cases ws <;> rfl
  rw [List.drop_zero] at g0
  rw [drop1] at g1
  rw [drop2] at g2
  rw [drop3] at g3
  have atLeast : 3/512 * I.oneTrade a b tB tS ≤ I.strat σ0 ∨
      3/512 * I.oneTrade a b tB tS ≤ I.strat σ1 ∨
      3/512 * I.oneTrade a b tB tS ≤ I.strat σ2 ∨ 3/512 * I.oneTrade a b tB tS ≤ I.strat σ3 := by
    by_contra! h
    obtain ⟨h0,h1,h2,h3⟩ := h
    linarith
  rcases atLeast with h|h|h|h
  · exact ⟨σ0,l0,r0,h⟩
  · exact ⟨σ1,l1,r1,h⟩
  · exact ⟨σ2,l2,r2,h⟩
  · exact ⟨σ3,l3,r3,h⟩
end
