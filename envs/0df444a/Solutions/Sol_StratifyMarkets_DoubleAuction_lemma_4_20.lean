-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.lemma_4_20
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:55:34.171603+00:00
-- url     : https://prove2.me/submissions/1219b32a-41a5-4332-b5bf-119949f4be1a

import Definitions.Def_StratifyMarkets_DoubleAuction_Prices
import Definitions.Def_StratifyMarkets_DoubleAuction_Submarket
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Mathlib
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_14
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_15
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_16
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_18
import Theorems.Thm_StratifyMarkets_DoubleAuction_theorem_3_1

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

-- Solutions.StratifyMarketsFewTrades
section
open MeasureTheory Set
namespace StratifyMarkets.DoubleAuction

/-- Equation (4.39), in one original submarket. The local refinement covers
the same endpoints and captures 3/512 of the bilateral super-agent surplus. -/
theorem refine_super_submarket {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m)
    (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hap : a ≤ p) (hpb : p ≤ b) :
    ∃ σ : Stratification, σ.m 0 = a ∧ σ.m (Fin.last σ.N) = b ∧
      3 / 512 * I.superFP a p b ≤ I.strat σ := by
  have nonneg : 0 ≤ I.superFP a p b := by
    apply integral_nonneg
    intro x
    change 0 ≤ (if _ then _ else (0:ℝ))
    split_ifs with H
    · exact sub_nonneg.mpr (H.2.1.trans H.2.2.1)
    · exact le_rfl
  have use_price (h : ∃ q ∈ Icc a b, 1/7 * I.superFP a p b ≤ I.worstRationedIn a q b) :
      ∃ σ : Stratification, σ.m 0 = a ∧ σ.m (Fin.last σ.N) = b ∧
        3/512 * I.superFP a p b ≤ I.strat σ := by
    obtain ⟨q,hq,hw⟩ := h
    refine ⟨single_submarket a b q ha hab hb hq.1 hq.2, by rfl, by rfl, ?_⟩
    rw [single_submarket_gains]
    linarith
  by_cases low : I.expBuyersIn a b ≤ 1/4 ∨ I.expSellersIn a b ≤ 1/4
  · exact use_price (lemma_4_14 I a b p ha hab hb hap hpb low)
  have hB : 1/4 ≤ I.expBuyersIn a b := le_of_not_ge fun h => low (Or.inl h)
  have hS : 1/4 ≤ I.expSellersIn a b := le_of_not_ge fun h => low (Or.inr h)
  obtain ⟨tB,hBt,hBq⟩ := buyer_threshold I hab.le hB
  obtain ⟨tS,hSt,hSq⟩ := seller_threshold I hab.le hS
  have hbt : I.IsBuyerThreshold a b tB := ⟨hBt,hBq⟩
  have hst : I.IsSellerThreshold a b tS := ⟨hSt,hSq⟩
  rcases lt_or_ge tB tS with h | h
  · exact use_price (lemma_4_15 I a b p tB tS ha hab hb hap hpb hbt hst h)
  · have hcomp := lemma_4_16 I a b p tB tS ha hab hb hap hpb hbt hst h
    obtain ⟨σ,hl,hr,hw⟩ := lemma_4_18 I a b tB tS ha hab hb hbt hst h
    exact ⟨σ,hl,hr,by linarith⟩

/-- The realized comparison underlying equation (4.34). -/
theorem few_trades_super_bound {n m : ℕ} [NeZero n] [NeZero m]
    (v : Fin n → ℝ) (c : Fin m → ℝ) :
    (if tau v c ≤ 5 then realizedFB v c else 0) ≤ 5 * max (vmax v - cmin c) 0 := by
  have hp : 0 ≤ max (vmax v - cmin c) 0 := le_max_right _ _
  split_ifs with h
  · have count : tau v c ≤ min n m := by
      apply Finset.sup_le
      intro i hi
      exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    calc
      realizedFB v c ≤ ∑ _i ∈ Finset.range (tau v c), max (vmax v - cmin c) 0 := by
        apply Finset.sum_le_sum
        intro i hi
        have hmin := (Finset.mem_range.mp hi).trans_le count
        have hv : i < (valuesDesc v).length := by simpa [valuesDesc] using hmin.trans_le (min_le_left _ _)
        have hc : i < (costsAsc c).length := by simpa [costsAsc] using hmin.trans_le (min_le_right _ _)
        rw [List.getD_eq_getElem _ _ hv, List.getD_eq_getElem _ _ hc]
        have hvm := List.mem_mergeSort.mp (List.getElem_mem (l := valuesDesc v) hv)
        have hcm := List.mem_mergeSort.mp (List.getElem_mem (l := costsAsc c) hc)
        obtain ⟨j,hj⟩ := (List.mem_ofFn' _ _).mp hvm
        obtain ⟨k,hk⟩ := (List.mem_ofFn' _ _).mp hcm
        rw [← hj, ← hk]
        apply le_trans _ (le_max_left _ _)
        exact sub_le_sub (Finset.le_sup' v (Finset.mem_univ j)) (Finset.inf'_le c (Finset.mem_univ k))
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right (show (tau v c : ℝ) ≤ 5 by exact_mod_cast h) hp
  · positivity

end StratifyMarkets.DoubleAuction
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

-- Solutions.StratifyMarketsBalancedLaw
section
open MeasureTheory Set
namespace StratifyMarkets.DoubleAuction

/-- Equation (4.1) defines the same expected count for all balanced prices,
even when some marginal CDFs are constant on a nonempty interval. -/
theorem balanced_count_unique {n m : ℕ} (I : DAInstance n m) {p q : ℝ}
    (hp : I.IsBalancedPrice p) (hq : I.IsBalancedPrice q) : I.expB p = I.expB q := by
  have hB : Antitone I.expB := by
    intro x y h
    apply Finset.sum_le_sum
    intro i _
    let := I.isProb_B i
    exact measureReal_mono (Ici_subset_Ici.mpr h)
  have hS : Monotone I.expS := by
    intro x y h
    apply Finset.sum_le_sum
    intro j _
    let := I.isProb_S j
    exact measureReal_mono (Iic_subset_Iic.mpr h)
  rcases le_total p q with h | h
  · exact le_antisymm (hp.2.le.trans ((hS h).trans hq.2.ge)) (hB h)
  · exact le_antisymm (hB h) (hq.2.le.trans ((hS h).trans hp.2.ge))

/-- A global price and the same price in the whole unit interval trade with
identical eligible sets almost surely under the product law. -/
theorem whole_submarket_eq {n m : ℕ} (I : DAInstance n m) (p : ℝ) :
    I.worstRationedIn 0 p 1 = I.worstRationed p := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  have B (i : Fin n) : ∀ᵐ x ∂I.law, x.1 i ∈ Icc (0 : ℝ) 1 := by
    have h : Icc (0 : ℝ) 1 ∈ ae (I.μB i) :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_B i)
    exact (measurePreserving_fst (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μB i).quasiMeasurePreserving.ae h)
  have S (j : Fin m) : ∀ᵐ x ∂I.law, x.2 j ∈ Icc (0 : ℝ) 1 := by
    have h : Icc (0 : ℝ) 1 ∈ ae (I.μS j) :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_S j)
    exact (measurePreserving_snd (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μS j).quasiMeasurePreserving.ae h)
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr B, ae_all_iff.mpr S] with x hx hy
  congr 1
  · ext i
    simp [Finset.mem_filter, (hx i).2]
  · ext j
    simp [Finset.mem_filter, (hy j).1]

/-- Every summand of the efficient matching is positive because the list of
seller costs increases while the list of buyer values decreases. -/
theorem realizedFB_nonnegative {n m : ℕ} (v : Fin n → ℝ) (c : Fin m → ℝ) :
    0 ≤ realizedFB v c := by
  apply Finset.sum_nonneg
  intro i hi
  have hit : i < tau v c := Finset.mem_range.mp hi
  obtain ⟨j, hj, hij⟩ := Finset.lt_sup_iff.mp hit
  obtain ⟨jr, hjgain⟩ := Finset.mem_filter.mp hj
  have jmin := Finset.mem_range.mp jr
  change i < j+1 at hij
  have jv : j < (valuesDesc v).length := by simpa [valuesDesc] using (lt_of_lt_of_le jmin (min_le_left n m))
  have js : j < (costsAsc c).length := by simpa [costsAsc] using (lt_of_lt_of_le jmin (min_le_right n m))
  have ig : i ≤ j := Nat.le_of_lt_succ hij
  change (costsAsc c).getD j 0 < (valuesDesc v).getD j 0 at hjgain
  apply sub_nonneg.mpr
  rcases eq_or_lt_of_le ig with rfl | hl
  · exact hjgain.le
  have cv := List.pairwise_iff_getElem.mp (List.pairwise_mergeSort' (· ≥ ·) (List.ofFn v))
    i j (ig.trans_lt jv) jv hl
  have cc := List.pairwise_iff_getElem.mp (List.pairwise_mergeSort' (· ≤ ·) (List.ofFn c))
    i j (ig.trans_lt js) js hl
  simp only [List.getD_eq_getElem _ _ jv, List.getD_eq_getElem _ _ js] at hjgain
  rw [List.getD_eq_getElem _ _ (ig.trans_lt js), List.getD_eq_getElem _ _ (ig.trans_lt jv)]
  exact cc.trans (hjgain.le.trans cv)

end StratifyMarkets.DoubleAuction
end

-- Solutions.StratifyMarketsFirstBest
section
open MeasureTheory Set
namespace StratifyMarkets.DoubleAuction

private theorem sorted_coordinate_measurable {k : ℕ} (r : ℝ → ℝ → Bool)
    (hr : ∀ i j : Fin k, Measurable fun v : Fin k → ℝ => r (v i) (v j))
    (t : ℕ) :
    Measurable fun v : Fin k → ℝ => ((List.ofFn v).mergeSort r).getD t 0 := by
  let table := fun (v : Fin k → ℝ) (i j : Fin k) => r (v i) (v j)
  have htable : Measurable table :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => hr i j
  let indices := List.ofFn (id : Fin k → Fin k)
  let entry := fun (z : (Fin k → ℝ) × (Fin k → Fin k → Bool)) =>
    (((indices.mergeSort z.2).map z.1)[t]?).getD 0
  have hentry : Measurable entry := by
    apply measurable_from_prod_countable_left
    intro order
    simp only [entry, List.getElem?_map]
    cases (indices.mergeSort order)[t]? with
    | none => exact measurable_const
    | some i => exact measurable_pi_apply i
  have hmap (v : Fin k → ℝ) :
      (indices.mergeSort (table v)).map v = (List.ofFn v).mergeSort r := by
    simpa [indices, List.map_ofFn] using
      (List.map_mergeSort (f := v) (l := indices) (r := table v) (s := r)
        (fun _ _ _ _ => rfl))
  simpa only [Function.comp_def, id_eq, entry, hmap, List.getD_eq_getElem?_getD] using
    hentry.comp (measurable_id.prodMk htable)

theorem measurable_trade_cut {n m : ℕ} (r : ℕ) :
    MeasurableSet {x : (Fin n → ℝ) × (Fin m → ℝ) | r < tau x.1 x.2} := by
  have value (i : ℕ) : Measurable fun v : Fin n → ℝ => (valuesDesc v).getD i 0 :=
    sorted_coordinate_measurable (fun a b => decide (b ≤ a)) (fun a b => measurable_to_bool (by
      simpa [Set.preimage] using
        (measurableSet_le (f := fun v : Fin n → ℝ => v b) (g := fun v => v a)
          (measurable_pi_apply b) (measurable_pi_apply a)))) i
  have cost (i : ℕ) : Measurable fun c : Fin m → ℝ => (costsAsc c).getD i 0 :=
    sorted_coordinate_measurable (fun a b => decide (a ≤ b)) (fun a b => measurable_to_bool (by
      simpa [Set.preimage] using
        (measurableSet_le (f := fun c : Fin m → ℝ => c a) (g := fun c => c b)
          (measurable_pi_apply a) (measurable_pi_apply b)))) i
  let trades := fun i => {x : (Fin n → ℝ) × (Fin m → ℝ) |
    (costsAsc x.2).getD i 0 < (valuesDesc x.1).getD i 0}
  have h : {x : (Fin n → ℝ) × (Fin m → ℝ) | r < tau x.1 x.2} =
      ⋃ i : ℕ, ⋃ (_ : i < min n m ∧ r < i + 1), trades i := by
    ext x
    simp [tau, Finset.lt_sup_iff, trades]
    aesop
  rw [h]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ =>
    measurableSet_lt ((cost i).comp measurable_snd) ((value i).comp measurable_fst)


theorem integrable_first_best {n m : ℕ} (I : DAInstance n m) :
    Integrable (fun x : (Fin n → ℝ) × (Fin m → ℝ) => realizedFB x.1 x.2) I.law := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  let : IsProbabilityMeasure I.law := by unfold DAInstance.law; infer_instance
  have count (v : Fin n → ℝ) (c : Fin m → ℝ) : tau v c ≤ min n m := by
    apply Finset.sup_le
    intro i hi
    exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hv (i : ℕ) : Measurable fun v : Fin n → ℝ => (valuesDesc v).getD i 0 :=
    sorted_coordinate_measurable (fun a b => decide (b ≤ a)) (fun a b => measurable_to_bool (by
      simpa [Set.preimage] using (measurableSet_le (f := fun v : Fin n → ℝ => v b)
        (g := fun v => v a) (measurable_pi_apply b) (measurable_pi_apply a)))) i
  have hc (i : ℕ) : Measurable fun c : Fin m → ℝ => (costsAsc c).getD i 0 :=
    sorted_coordinate_measurable (fun a b => decide (a ≤ b)) (fun a b => measurable_to_bool (by
      simpa [Set.preimage] using (measurableSet_le (f := fun c : Fin m → ℝ => c a)
        (g := fun c => c b) (measurable_pi_apply a) (measurable_pi_apply b)))) i
  have hmeas : Measurable (fun x : (Fin n → ℝ) × (Fin m → ℝ) => realizedFB x.1 x.2) := by
    have expand (v : Fin n → ℝ) (c : Fin m → ℝ) :
        realizedFB v c = ∑ i ∈ Finset.range (min n m), if i < tau v c then
          (valuesDesc v).getD i 0 - (costsAsc c).getD i 0 else 0 := by
      rw [← Finset.sum_filter]
      unfold realizedFB
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => ⟨h.trans_le (count v c), h⟩, fun h => h.2⟩
    simp_rw [expand]
    exact Finset.measurable_sum _ fun i _ => Measurable.ite (measurable_trade_cut i)
      (((hv i).comp measurable_fst).sub ((hc i).comp measurable_snd)) measurable_const
  have B (i : Fin n) : ∀ᵐ x ∂I.law, x.1 i ∈ Icc (0 : ℝ) 1 :=
    (measurePreserving_fst (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μB i).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_B i)))
  have S (j : Fin m) : ∀ᵐ x ∂I.law, x.2 j ∈ Icc (0 : ℝ) 1 :=
    (measurePreserving_snd (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μS j).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_S j)))
  apply Integrable.of_bound hmeas.aestronglyMeasurable (min n m : ℕ)
  filter_upwards [ae_all_iff.mpr B, ae_all_iff.mpr S] with x hx hy
  rw [Real.norm_eq_abs, abs_of_nonneg (realizedFB_nonnegative _ _)]
  have entry {k : ℕ} (w : Fin k → ℝ) (r : ℝ → ℝ → Bool) (h : ∀ j, w j ∈ Icc (0 : ℝ) 1)
      (i : ℕ) (hi : i < k) : ((List.ofFn w).mergeSort r).getD i 0 ∈ Icc (0 : ℝ) 1 := by
    have hil : i < ((List.ofFn w).mergeSort r).length := by simpa using hi
    rw [List.getD_eq_getElem _ _ hil]
    have mem := List.getElem_mem (l := (List.ofFn w).mergeSort r) hil
    have orig := List.mem_mergeSort.mp mem
    obtain ⟨j,hj⟩ := (List.mem_ofFn' _ _).mp orig
    rw [← hj]
    exact h j
  calc
    realizedFB x.1 x.2 ≤ ∑ _i ∈ Finset.range (tau x.1 x.2), (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := (Finset.mem_range.mp hi).trans_le (count x.1 x.2)
      have hb := (entry x.1 (fun a b => decide (b ≤ a)) hx i (h.trans_le (min_le_left _ _))).2
      have hs := (entry x.2 (fun a b => decide (a ≤ b)) hy i (h.trans_le (min_le_right _ _))).1
      change (valuesDesc x.1).getD i 0 ≤ 1 at hb
      change 0 ≤ (costsAsc x.2).getD i 0 at hs
      linarith
    _ ≤ _ := by simpa using (show (tau x.1 x.2 : ℝ) ≤ (min n m : ℕ) by exact_mod_cast count x.1 x.2)

theorem sorted_positive_sum {k : ℕ} (w : Fin k → ℝ) (r : ℝ → ℝ → Bool)
    (φ : ℝ → ℝ) (hφ : ∀ a, 0 ≤ φ a) {t : ℕ} (ht : t ≤ k) :
    (∑ i ∈ Finset.range t, φ (((List.ofFn w).mergeSort r).getD i 0)) ≤ ∑ i, φ (w i) := by
  let l := (List.ofFn w).mergeSort r
  have len : l.length = k := by simp [l]
  have hperm := (List.mergeSort_perm (List.ofFn w) r).map φ
  calc
    _ ≤ ∑ i ∈ Finset.range l.length, φ (l.getD i 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (ht.trans_eq len.symm)) (fun i _ _ => hφ _)
    _ = (l.map φ).sum := by
      rw [← Fin.sum_univ_eq_sum_range]
      rw [← List.sum_ofFn]
      congr 1
      rw [← List.ofFn_getElem_eq_map]
      apply congrArg List.ofFn
      funext i
      rw [List.getD_eq_getElem _ _ i.isLt]
    _ = ((List.ofFn w).map φ).sum := hperm.sum_eq
    _ = ∑ i, φ (w i) := by simp [List.map_ofFn, List.sum_ofFn]

theorem realized_surplus {n m : ℕ} (v : Fin n → ℝ) (c : Fin m → ℝ) (t : ℝ) :
    realizedFB v c ≤ ∑ i, max (v i - t) 0 + ∑ j, max (t - c j) 0 := by
  have H : tau v c ≤ min n m := by
    apply Finset.sup_le
    intro i hi
    exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  calc
    _ ≤ ∑ i ∈ Finset.range (tau v c), (max ((valuesDesc v).getD i 0 - t) 0 + max (t - (costsAsc c).getD i 0) 0) := by
      apply Finset.sum_le_sum
      intro i _
      linarith only [le_max_left ((valuesDesc v).getD i 0 - t) 0, le_max_left (t - (costsAsc c).getD i 0) 0]
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (sorted_positive_sum v (fun a b => decide (b ≤ a)) (fun x => max (x-t) 0)
        (fun _ => le_max_right _ _) (H.trans (min_le_left _ _)))
        (sorted_positive_sum c (fun a b => decide (a ≤ b)) (fun x => max (t-x) 0)
          (fun _ => le_max_right _ _) (H.trans (min_le_right _ _)))

end StratifyMarkets.DoubleAuction
end

-- Solutions.Sol_StratifyMarkets_DoubleAuction_lemma_4_20
section
open MeasureTheory Set StratifyMarkets.DoubleAuction

private theorem five_trade_integral {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) :
    I.FBtauLe5 ≤ 5 * (superAgents I).FB := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  let : IsProbabilityMeasure I.law := by unfold DAInstance.law; infer_instance
  have masked : Integrable (fun x => if tau x.1 x.2 ≤ 5 then realizedFB x.1 x.2 else 0) I.law := by
    have h := (integrable_first_best I).indicator (measurable_trade_cut 5 (n := n) (m := m)).compl
    apply h.congr
    filter_upwards with x
    simp [Set.indicator, not_lt]
  let g := fun x : (Fin n → ℝ) × (Fin m → ℝ) => max (vmax x.1 - cmin x.2) 0
  have hmeas : Measurable g := ((vmax_meas.comp measurable_fst).sub
    (cmin_meas.comp measurable_snd)).max measurable_const
  have b (i : Fin n) : ∀ᵐ x ∂I.law, x.1 i ∈ Icc (0 : ℝ) 1 :=
    (measurePreserving_fst (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μB i).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_B i)))
  have s (j : Fin m) : ∀ᵐ x ∂I.law, x.2 j ∈ Icc (0 : ℝ) 1 :=
    (measurePreserving_snd (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μS j).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_S j)))
  have hg : Integrable g I.law := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards [ae_all_iff.mpr b, ae_all_iff.mpr s] with x hx hy
    obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x.1
    obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty x.2
    change ‖max (vmax x.1 - cmin x.2) 0‖ ≤ 1
    change vmax x.1 = x.1 i at hi
    change cmin x.2 = x.2 j at hj
    rw [hi,hj,Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [(hx i).2, (hy j).1]) zero_le_one
  rw [superAgents_first_best, ← integral_const_mul]
  exact integral_mono masked (hg.const_mul 5) (fun x => few_trades_super_bound x.1 x.2)

private theorem empty_side {n m : ℕ} (I : DAInstance n m) (empty : n = 0 ∨ m = 0) :
    ∃ σ : Stratification, 1 / (10240 * Real.exp 1) * I.FBtauLe5 ≤ I.strat σ := by
  have hm : min n m = 0 := by rcases empty with h | h <;> simp [h]
  have hzero : I.FBtauLe5 = 0 := by
    simp [DAInstance.FBtauLe5,realizedFB,tau,hm]
  let σ : Stratification := {
    N := 1, one_le_N := le_rfl, m := fun k => (k.val : ℝ), p := fun _ => 0,
    zero_le_m := by norm_num, m_le_one := by norm_num [Fin.last],
    m_strictMono := fun _ _ h => Nat.cast_lt.mpr h,
    p_mem := by intro i; fin_cases i; norm_num }
  refine ⟨σ, ?_⟩
  rw [hzero,mul_zero]
  apply Finset.sum_nonneg
  intro i _
  apply integral_nonneg
  intro x
  dsimp only
  unfold worstRationedGains
  apply Finset.le_inf'
  intro pair hpair
  obtain ⟨hB,hS⟩ := Finset.mem_product.mp hpair
  obtain ⟨_,hBc⟩ := Finset.mem_powersetCard.mp hB
  obtain ⟨_,hSc⟩ := Finset.mem_powersetCard.mp hS
  rcases empty with h | h
  · subst n
    simp at hBc hSc
    simp [hBc,hSc]
  · subst m
    simp at hBc hSc
    simp [hBc,hSc]

theorem solution {n m : ℕ} (I : DAInstance n m) :
    ∃ σ : Stratification, 1 / (10240 * Real.exp 1) * I.FBtauLe5 ≤ I.strat σ := by
  by_cases empty : n = 0 ∨ m = 0
  · exact empty_side I empty
  have : NeZero n := ⟨fun h => empty (Or.inl h)⟩
  have : NeZero m := ⟨fun h => empty (Or.inr h)⟩
  obtain ⟨σ,hσ⟩ := theorem_3_1 (superAgents I)
  rw [superAgents_strat] at hσ
  have local_refine (k : Fin σ.N) := refine_super_submarket I (σ.m k.castSucc) (σ.m k.succ) (σ.p k)
    (σ.zero_le_m.trans (σ.m_strictMono.monotone (Fin.zero_le _))) (σ.m_strictMono k.castSucc_lt_succ)
    ((σ.m_strictMono.monotone (Fin.le_last _)).trans σ.m_le_one) (σ.p_mem k).1 (σ.p_mem k).2
  choose pieces hleft hright hgain using local_refine
  obtain ⟨ρ,hρ⟩ := Stratification.assemble_refinements I σ pieces hleft hright
  refine ⟨ρ, ?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hgain k)
  rw [← Finset.mul_sum, ← hρ] at hsum
  have lower : (superAgents I).FB / (12 * Real.exp 1) ≤
      ∑ k : Fin σ.N, I.superFP (σ.m k.castSucc) (σ.p k) (σ.m k.succ) := by
    simpa only [one_div_mul_eq_div] using hσ
  have hτ := five_trade_integral I
  rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
  have he := (div_le_iff₀ (by positivity)).mp lower
  calc I.FBtauLe5 ≤ 5 * (superAgents I).FB := hτ
    _ ≤ 5 * ((∑ k : Fin σ.N, I.superFP (σ.m k.castSucc) (σ.p k) (σ.m k.succ)) * (12 * Real.exp 1)) :=
      mul_le_mul_of_nonneg_left he (by norm_num)
    _ ≤ I.strat ρ * (10240 * Real.exp 1) := by
      have step := mul_le_mul_of_nonneg_right hsum (show 0 ≤ 10240 * Real.exp 1 by positivity)
      linarith only [step]
end
