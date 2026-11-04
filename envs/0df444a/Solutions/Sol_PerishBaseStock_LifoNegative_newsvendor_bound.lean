-- Prove2me | solution 1 for PerishBaseStock.LifoNegative.newsvendor_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T18:40:39.919585+00:00
-- url     : https://prove2.me/submissions/b270111e-187c-4265-9e48-d7756062b039

import Definitions.Def_PerishBaseStock_LifoNegative_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open CappedBaseStock LostSalesOrderUpTo.Asymptotic

namespace LifoNegSol
open PerishBaseStock.LifoNegative

variable {m : ℕ}

lemma stockLevel_zero (x : PerishBaseStock.Lifetime.State m) : stockLevel x 0 = 0 := by
  simp [stockLevel]

lemma stockLevel_of_ge (x : PerishBaseStock.Lifetime.State m) (i : ℕ) (hi : m ≤ i) :
    stockLevel x i = 0 := by
  unfold stockLevel; rw [dif_neg]; omega

lemma level_of_lt (x : PerishBaseStock.Lifetime.State m) (q : ℝ≥0) (i : ℕ) (hi : i < m) :
    level x q i = stockLevel x i := by
  simp [level, hi]

lemma level_m (x : PerishBaseStock.Lifetime.State m) (q : ℝ≥0) :
    level x q m = orderUpTo x q := by
  simp [level]

lemma stockLevel_lifoStep (x : PerishBaseStock.Lifetime.State m) (q D : ℝ≥0) (i : ℕ)
    (h0 : 0 < i) (hi : i < m) :
    stockLevel (lifoStep x q D) i =
      min (max (orderUpTo x q - (D : ℝ)) 0) (level x q (i + 1)) - outdating x q D := by
  unfold stockLevel
  rw [dif_pos ⟨h0, hi⟩]
  simp only [lifoStep]
  congr 3
  omega

/-- Key identity: `x_{t+1,j-1} + o_t = min{(x_{t,m}-D)⁺, x_{t,j}}` for `1 ≤ j ≤ m`. -/
lemma level_lifoStep_add_outdating (x : PerishBaseStock.Lifetime.State m) (q D q' : ℝ≥0)
    (j : ℕ) (h1 : 1 ≤ j) (hj : j ≤ m) :
    level (lifoStep x q D) q' (j - 1) + outdating x q D =
      min (max (orderUpTo x q - (D : ℝ)) 0) (level x q j) := by
  rw [level_of_lt _ _ _ (by omega)]
  rcases Nat.eq_or_lt_of_le h1 with h | h
  · subst h
    simp [stockLevel_zero, outdating]
  · rw [stockLevel_lifoStep _ _ _ _ (by omega) (by omega)]
    have : j - 1 + 1 = j := by omega
    rw [this]; ring


lemma stockLevel_empty (i : ℕ) : stockLevel (PerishBaseStock.Lifetime.emptyState m) i = 0 := by
  unfold stockLevel; split_ifs <;> rfl

/-- Invariant of the base-stock trajectory. -/
def BSInv (S : ℝ≥0) (x : PerishBaseStock.Lifetime.State m) : Prop :=
  (∀ i j, i ≤ j → j < m → stockLevel x i ≤ stockLevel x j) ∧ stockLevel x (m - 1) ≤ S

lemma bsInv_empty (S : ℝ≥0) : BSInv S (PerishBaseStock.Lifetime.emptyState m) := by
  refine ⟨fun i j _ _ => by simp [stockLevel_empty], by simp [stockLevel_empty]⟩

lemma BSInv.nonneg {S : ℝ≥0} {x : PerishBaseStock.Lifetime.State m} (h : BSInv S x) (i : ℕ) :
    0 ≤ stockLevel x i := by
  by_cases hi : i < m
  · have := h.1 0 i (Nat.zero_le _) hi
    rwa [stockLevel_zero] at this
  · rw [stockLevel_of_ge _ _ (by omega)]

lemma BSInv.orderUpTo_eq {S : ℝ≥0} {x : PerishBaseStock.Lifetime.State m} (h : BSInv S x)
    (t : ℕ) : orderUpTo x (baseStockOrder S t x) = S := by
  unfold orderUpTo baseStockOrder
  rw [Real.coe_toNNReal _ (by linarith [h.2])]
  ring

lemma BSInv.level_mono {S : ℝ≥0} {x : PerishBaseStock.Lifetime.State m} (h : BSInv S x)
    (hm : 1 ≤ m) (t : ℕ) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m) :
    level x (baseStockOrder S t x) i ≤ level x (baseStockOrder S t x) j := by
  rcases Nat.lt_or_ge j m with hjm | hjm
  · rw [level_of_lt _ _ _ hjm, level_of_lt _ _ _ (by omega)]
    exact h.1 i j hij hjm
  · have hjm' : j = m := le_antisymm hj hjm
    rw [hjm', level_m, h.orderUpTo_eq]
    rcases Nat.lt_or_ge i m with him | him
    · rw [level_of_lt _ _ _ him]
      exact (h.1 i (m - 1) (by omega) (by omega)).trans h.2
    · have : i = m := le_antisymm (hij.trans hj) him
      rw [this, level_m, h.orderUpTo_eq]

lemma BSInv.level_nonneg {S : ℝ≥0} {x : PerishBaseStock.Lifetime.State m} (h : BSInv S x)
    (t : ℕ) (i : ℕ) : 0 ≤ level x (baseStockOrder S t x) i := by
  unfold level
  split_ifs
  · exact h.nonneg i
  · rw [h.orderUpTo_eq]; exact S.2

lemma BSInv.outdating_nonneg {S : ℝ≥0} {x : PerishBaseStock.Lifetime.State m} (h : BSInv S x)
    (t : ℕ) (D : ℝ≥0) : 0 ≤ outdating x (baseStockOrder S t x) D := by
  unfold outdating
  exact le_min (le_max_right _ _) (h.level_nonneg t 1)

lemma BSInv.outdating_le {S : ℝ≥0} {x : PerishBaseStock.Lifetime.State m} (h : BSInv S x)
    (t : ℕ) (D : ℝ≥0) : outdating x (baseStockOrder S t x) D ≤ max ((S : ℝ) - D) 0 := by
  unfold outdating
  rw [h.orderUpTo_eq]
  exact min_le_left _ _

lemma BSInv.step {S : ℝ≥0} {x : PerishBaseStock.Lifetime.State m} (h : BSInv S x)
    (hm : 2 ≤ m) (t : ℕ) (D : ℝ≥0) :
    BSInv S (lifoStep x (baseStockOrder S t x) D) := by
  have hmono := fun {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m) => h.level_mono (by omega) t hij hj
  have hU := h.orderUpTo_eq t
  refine ⟨fun i j hij hj => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · subst hi0
      rw [stockLevel_zero]
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0; rw [stockLevel_zero]
      · rw [stockLevel_lifoStep _ _ _ _ hj0 hj, sub_nonneg]
        unfold outdating
        exact min_le_min_left _ (hmono (by omega) (by omega))
    · rw [stockLevel_lifoStep _ _ _ _ hi0 (by omega), stockLevel_lifoStep _ _ _ _ (by omega) hj]
      exact sub_le_sub_right (min_le_min_left _ (hmono (by omega) (by omega))) _
  · rw [stockLevel_lifoStep _ _ _ _ (by omega) (by omega)]
    have h1 := h.outdating_nonneg t D
    have h2 : min (max (orderUpTo x (baseStockOrder S t x) - (D : ℝ)) 0)
        (level x (baseStockOrder S t x) (m - 1 + 1)) ≤ max ((S : ℝ) - D) 0 := by
      rw [hU]; exact min_le_left _ _
    have h3 : max ((S : ℝ) - D) 0 ≤ S := max_le (by linarith [D.2]) S.2
    linarith

lemma bsInv_run (S : ℝ≥0) (hm : 2 ≤ m) (d : DemandPath) :
    ∀ t, BSInv S (run (baseStockOrder (m := m) S) d t) := by
  intro t
  induction t with
  | zero => exact bsInv_empty S
  | succ t ih => exact ih.step hm t (d t)


section window
variable (S : ℝ≥0) (d : DemandPath)

/-- Window bound: if all demands in `t, …, t+k-1` are at most `S - δ`, then
`x_{t+k, m-k} + Σ_{j<k} o_{t+j} ≥ δ`. -/
lemma window_aux (hm : 2 ≤ m) (δ : ℝ) (hδ : δ ≤ S) (t : ℕ) :
    ∀ k ≤ m, (∀ j < k, (d (t + j) : ℝ) ≤ S - δ) →
      δ ≤ level (run (baseStockOrder (m := m) S) d (t + k))
            (baseStockOrder S (t + k) (run (baseStockOrder (m := m) S) d (t + k))) (m - k) +
        ∑ j ∈ Finset.range k, outdating (run (baseStockOrder (m := m) S) d (t + j))
            (baseStockOrder S (t + j) (run (baseStockOrder (m := m) S) d (t + j))) (d (t + j)) := by
  intro k
  induction k with
  | zero =>
    intro _ _
    simp only [Nat.sub_zero, Finset.range_zero, Finset.sum_empty, add_zero, Nat.add_zero]
    rw [level_m, (bsInv_run S hm d t).orderUpTo_eq]
    exact hδ
  | succ k ih =>
    intro hk hd
    have ihk := ih (by omega) (fun j hj => hd j (by omega))
    set x := run (baseStockOrder (m := m) S) d (t + k)
    have hinv : BSInv S x := bsInv_run S hm d (t + k)
    have hrun : run (baseStockOrder (m := m) S) d (t + (k + 1)) =
        lifoStep x (baseStockOrder S (t + k) x) (d (t + k)) := by
      rw [← add_assoc]; rfl
    have key := level_lifoStep_add_outdating x (baseStockOrder S (t + k) x) (d (t + k))
      (baseStockOrder S (t + (k + 1)) (run (baseStockOrder (m := m) S) d (t + (k + 1))))
      (m - k) (by omega) (by omega)
    rw [← hrun, hinv.orderUpTo_eq] at key
    have hmk : m - k - 1 = m - (k + 1) := by omega
    rw [hmk] at key
    rw [Finset.sum_range_succ]
    have hsum : 0 ≤ ∑ j ∈ Finset.range k, outdating (run (baseStockOrder (m := m) S) d (t + j))
        (baseStockOrder S (t + j) (run (baseStockOrder (m := m) S) d (t + j))) (d (t + j)) :=
      Finset.sum_nonneg fun j _ => (bsInv_run S hm d (t + j)).outdating_nonneg _ _
    have hdk := hd k (by omega)
    have ha : δ ≤ max ((S : ℝ) - d (t + k)) 0 := le_max_of_le_left (by linarith)
    have := min_le_iff.mp (le_refl (min (max ((S : ℝ) - d (t + k)) 0)
      (level x (baseStockOrder S (t + k) x) (m - k))))
    rcases le_total (max ((S : ℝ) - d (t + k)) 0) (level x (baseStockOrder S (t + k) x) (m - k))
      with h | h
    · rw [min_eq_left h] at key; linarith
    · rw [min_eq_right h] at key; linarith

lemma window (hm : 2 ≤ m) (δ : ℝ) (hδ : δ ≤ S) (t : ℕ)
    (hd : ∀ j < m, (d (t + j) : ℝ) ≤ S - δ) :
    δ ≤ ∑ j ∈ Finset.range m, outdating (run (baseStockOrder (m := m) S) d (t + j))
            (baseStockOrder S (t + j) (run (baseStockOrder (m := m) S) d (t + j))) (d (t + j)) := by
  have := window_aux S d hm δ hδ t m le_rfl hd
  rwa [Nat.sub_self, level_of_lt _ _ _ (by omega), stockLevel_zero, zero_add] at this

end window

end LifoNegSol

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open CappedBaseStock LostSalesOrderUpTo.Asymptotic

namespace LifoNegSol
open PerishBaseStock.LifoNegative

variable {m : ℕ}

lemma continuous_stockLevel (i : ℕ) :
    Continuous (fun x : PerishBaseStock.Lifetime.State m => stockLevel x i) := by
  unfold stockLevel
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma continuous_orderUpTo :
    Continuous (fun p : PerishBaseStock.Lifetime.State m × ℝ≥0 => orderUpTo p.1 p.2) := by
  unfold orderUpTo
  exact ((continuous_stockLevel _).comp continuous_fst).add
    (NNReal.continuous_coe.comp continuous_snd)

lemma continuous_level (i : ℕ) :
    Continuous (fun p : PerishBaseStock.Lifetime.State m × ℝ≥0 => level p.1 p.2 i) := by
  unfold level
  split_ifs
  · exact (continuous_stockLevel _).comp continuous_fst
  · exact continuous_orderUpTo

lemma continuous_outdating :
    Continuous (fun p : PerishBaseStock.Lifetime.State m × ℝ≥0 × ℝ≥0 =>
      outdating p.1 p.2.1 p.2.2) := by
  unfold outdating
  have h1 : Continuous (fun p : PerishBaseStock.Lifetime.State m × ℝ≥0 × ℝ≥0 =>
      orderUpTo p.1 p.2.1) :=
    continuous_orderUpTo.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have h2 : Continuous (fun p : PerishBaseStock.Lifetime.State m × ℝ≥0 × ℝ≥0 =>
      level p.1 p.2.1 1) :=
    (continuous_level 1).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have h3 : Continuous (fun p : PerishBaseStock.Lifetime.State m × ℝ≥0 × ℝ≥0 =>
      ((p.2.2 : ℝ≥0) : ℝ)) := NNReal.continuous_coe.comp (continuous_snd.comp continuous_snd)
  exact ((h1.sub h3).max continuous_const).min h2

lemma continuous_lifoStep :
    Continuous (fun p : PerishBaseStock.Lifetime.State m × ℝ≥0 × ℝ≥0 =>
      lifoStep p.1 p.2.1 p.2.2) := by
  unfold lifoStep
  refine continuous_pi fun i => ?_
  have h1 : Continuous (fun p : PerishBaseStock.Lifetime.State m × ℝ≥0 × ℝ≥0 =>
      orderUpTo p.1 p.2.1) :=
    continuous_orderUpTo.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have h2 : Continuous (fun p : PerishBaseStock.Lifetime.State m × ℝ≥0 × ℝ≥0 =>
      level p.1 p.2.1 (i.val + 2)) :=
    (continuous_level _).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have h3 : Continuous (fun p : PerishBaseStock.Lifetime.State m × ℝ≥0 × ℝ≥0 =>
      ((p.2.2 : ℝ≥0) : ℝ)) := NNReal.continuous_coe.comp (continuous_snd.comp continuous_snd)
  exact (((h1.sub h3).max continuous_const).min h2).sub continuous_outdating

lemma measurable_run (φ : OrderRule m) (hφ : ∀ t, Measurable (φ t)) :
    ∀ t, Measurable (fun d : DemandPath => run φ d t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hs : Measurable (fun p : PerishBaseStock.Lifetime.State m × ℝ≥0 × ℝ≥0 =>
      lifoStep p.1 p.2.1 p.2.2) := continuous_lifoStep.measurable
    exact hs.comp (ih.prodMk (((hφ t).comp ih).prodMk (measurable_pi_apply t)))

lemma measurable_outdating_run (φ : OrderRule m) (hφ : ∀ t, Measurable (φ t)) (t : ℕ) :
    Measurable (fun d : DemandPath => outdating (run φ d t) (φ t (run φ d t)) (d t)) := by
  have ih := measurable_run φ hφ t
  exact continuous_outdating.measurable.comp
    (ih.prodMk (((hφ t).comp ih).prodMk (measurable_pi_apply t)))

lemma measurable_baseStockOrder (S : ℝ≥0) (t : ℕ) :
    Measurable (baseStockOrder (m := m) S t) := by
  unfold baseStockOrder
  exact (continuous_real_toNNReal.comp
    (continuous_const.sub (continuous_stockLevel _))).measurable

/-! ### Demand facts -/

section demand
variable (P : DemandLaw)

lemma lowerSupport_bdd (hD : 0 < PerishBaseStock.Outdating.lowerSupport P) :
    BddBelow {x : ℝ | 0 < PerishBaseStock.Outdating.cdf P x} ∧
      {x : ℝ | 0 < PerishBaseStock.Outdating.cdf P x}.Nonempty := by
  unfold PerishBaseStock.Outdating.lowerSupport at hD
  constructor
  · by_contra hb
    rw [Real.sInf_of_not_bddBelow hb] at hD
    exact lt_irrefl _ hD
  · by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sInf_empty] at hD
    exact lt_irrefl _ hD

lemma cdf_eq_zero (hD : 0 < PerishBaseStock.Outdating.lowerSupport P) (x : ℝ)
    (hx : x < PerishBaseStock.Outdating.lowerSupport P) :
    P.law {d : ℝ≥0 | (d : ℝ) ≤ x} = 0 := by
  by_contra hne
  have hpos : 0 < PerishBaseStock.Outdating.cdf P x := pos_iff_ne_zero.mpr hne
  have := csInf_le (lowerSupport_bdd P hD).1 hpos
  unfold PerishBaseStock.Outdating.lowerSupport at hx
  linarith

lemma ae_ge_lowerSupport (hD : 0 < PerishBaseStock.Outdating.lowerSupport P) :
    ∀ᵐ x : ℝ≥0 ∂P.law, PerishBaseStock.Outdating.lowerSupport P ≤ (x : ℝ) := by
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ n : ℕ,
    {d : ℝ≥0 | (d : ℝ) ≤ PerishBaseStock.Outdating.lowerSupport P - 1 / ((n : ℝ) + 1)})
  · intro d hd
    simp only [Set.mem_ofPred_eq, not_le] at hd
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hd)
    exact Set.mem_iUnion.mpr ⟨n, by simp only [Set.mem_ofPred_eq]; linarith⟩
  · exact measure_iUnion_null fun n => cdf_eq_zero P hD _ (by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)

lemma cdf_pos (hD : 0 < PerishBaseStock.Outdating.lowerSupport P) (x : ℝ)
    (hx : PerishBaseStock.Outdating.lowerSupport P < x) :
    0 < P.law {d : ℝ≥0 | (d : ℝ) ≤ x} := by
  obtain ⟨a, ha, hax⟩ := exists_lt_of_csInf_lt (lowerSupport_bdd P hD).2 hx
  refine lt_of_lt_of_le ha (measure_mono fun d hd => ?_)
  simp only [Set.mem_ofPred_eq] at hd ⊢
  linarith

lemma mp_eval (t : ℕ) :
    MeasurePreserving (fun d : DemandPath => d t) (demandPathLaw P) P.law :=
  measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) t

lemma ae_path_ge (hD : 0 < PerishBaseStock.Outdating.lowerSupport P) :
    ∀ᵐ d ∂demandPathLaw P, ∀ t, PerishBaseStock.Outdating.lowerSupport P ≤ ((d t : ℝ≥0) : ℝ) := by
  rw [ae_all_iff]
  intro t
  have h := ae_ge_lowerSupport P hD
  rw [← (mp_eval P t).map_eq] at h
  exact ae_of_ae_map (mp_eval P t).measurable.aemeasurable h

lemma lintegral_eval (t : ℕ) (f : ℝ≥0 → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ d, f (d t) ∂demandPathLaw P = ∫⁻ x, f x ∂P.law :=
  (mp_eval P t).lintegral_comp hf

lemma integrable_holding (s : ℝ) : Integrable (fun x : ℝ≥0 => max (s - (x : ℝ)) 0) P.law := by
  refine Integrable.mono' (integrable_const (|s|)) ?_ ?_
  · exact (Measurable.max (measurable_const.sub measurable_coe_nnreal_real) measurable_const).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [le_abs_self s, x.2]) (abs_nonneg s)

lemma integrable_shortfall (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun x : ℝ≥0 => max ((x : ℝ) - s) 0) P.law := by
  refine Integrable.mono' P.finiteMean ?_ ?_
  · exact (Measurable.max (measurable_coe_nnreal_real.sub measurable_const) measurable_const).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) x.2

/-- The expected newsvendor cost as a lower integral. -/
lemma lintegral_nv (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (s : ℝ≥0) :
    ∫⁻ x, (ENNReal.ofReal (h * max ((s : ℝ) - (x : ℝ)) 0) +
        ENNReal.ofReal (p * max ((x : ℝ) - s) 0)) ∂P.law =
      ENNReal.ofReal (backorderCost P.law h p s) := by
  have hi1 := (integrable_holding P s).const_mul h
  have hi2 := (integrable_shortfall P s s.2).const_mul p
  have : (fun x : ℝ≥0 => ENNReal.ofReal (h * max ((s : ℝ) - (x : ℝ)) 0) +
        ENNReal.ofReal (p * max ((x : ℝ) - s) 0)) =
      fun x : ℝ≥0 => ENNReal.ofReal (h * max ((s : ℝ) - (x : ℝ)) 0 + p * max ((x : ℝ) - s) 0) := by
    funext x
    rw [ENNReal.ofReal_add (mul_nonneg hh (le_max_right _ _)) (mul_nonneg hp (le_max_right _ _))]
  have hi : Integrable (fun x : ℝ≥0 => h * max ((s : ℝ) - (x : ℝ)) 0 + p * max ((x : ℝ) - s) 0)
      P.law := hi1.add hi2
  rw [this, ← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun x => add_nonneg (mul_nonneg hh (le_max_right _ _))
      (mul_nonneg hp (le_max_right _ _)))]
  congr 1
  rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul]
  rfl

lemma path_cylinder (t : ℕ) (r : ℝ) :
    demandPathLaw P {d : DemandPath | ∀ k < m, ((d (t + k) : ℝ≥0) : ℝ) ≤ r} =
      (P.law {x : ℝ≥0 | (x : ℝ) ≤ r}) ^ m := by
  have hset : {d : DemandPath | ∀ k < m, ((d (t + k) : ℝ≥0) : ℝ) ≤ r} =
      Set.pi (↑(Finset.image (fun k => t + k) (Finset.range m)))
        (fun _ => {x : ℝ≥0 | (x : ℝ) ≤ r}) := by
    ext d
    simp
  rw [hset, demandPathLaw, Measure.infinitePi_pi]
  · rw [Finset.prod_const, Finset.card_image_of_injective _ (add_right_injective t),
      Finset.card_range]
  · intro i _
    exact measurableSet_le measurable_coe_nnreal_real measurable_const

end demand

end LifoNegSol

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open CappedBaseStock LostSalesOrderUpTo.Asymptotic

namespace LifoNegSol
open PerishBaseStock.LifoNegative

/-- Cesàro upper bound. -/
lemma limsup_cesaro_le (u : ℕ → ℝ≥0∞) (A : ℝ≥0∞)
    (h : ∀ T : ℕ, ∑ t ∈ Finset.range (T + 1), u t ≤ A * ((T : ℝ≥0∞) + 1)) :
    limsup (fun T : ℕ => (∑ t ∈ Finset.range (T + 1), u t) / ((T : ℝ≥0∞) + 1)) atTop ≤ A :=
  limsup_le_of_le (h := Eventually.of_forall fun T => ENNReal.div_le_of_le_mul (h T))

lemma sum_range_mul_split (u : ℕ → ℝ≥0∞) (m : ℕ) : ∀ n : ℕ,
    ∑ t ∈ Finset.range (n * m), u t =
      ∑ w ∈ Finset.range n, ∑ k ∈ Finset.range m, u (w * m + k) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, show (n + 1) * m = n * m + m by ring, Finset.sum_range_add]

variable (P : DemandLaw)

/-- Outdating of the base-stock trajectory in period `t`. -/
noncomputable def bsOut (m : ℕ) (S : ℝ≥0) (t : ℕ) (d : DemandPath) : ℝ :=
  outdating (run (baseStockOrder (m := m) S) d t)
    (baseStockOrder S t (run (baseStockOrder (m := m) S) d t)) (d t)

lemma bs_costAt (c : Params) (hm : 2 ≤ c.m) (S : ℝ≥0) (d : DemandPath) (t : ℕ) :
    costAt c (baseStockOrder S) d t =
      (ENNReal.ofReal (c.h * max ((S : ℝ) - (d t : ℝ)) 0) +
        ENNReal.ofReal (c.p * max ((d t : ℝ) - S) 0)) +
      ENNReal.ofReal (c.θ * bsOut c.m S t d) := by
  unfold costAt PerishBaseStock.LifoNegative.periodCost bsOut
  rw [(bsInv_run S hm d t).orderUpTo_eq]

lemma measurable_nvTerm (h p : ℝ) (s : ℝ) :
    Measurable (fun x : ℝ≥0 => ENNReal.ofReal (h * max (s - (x : ℝ)) 0) +
      ENNReal.ofReal (p * max ((x : ℝ) - s) 0)) := by
  refine Measurable.add (f := fun x : ℝ≥0 => ENNReal.ofReal (h * max (s - (x : ℝ)) 0))
    (g := fun x : ℝ≥0 => ENNReal.ofReal (p * max ((x : ℝ) - s) 0)) ?_ ?_
  · exact (measurable_const.mul ((measurable_const.sub measurable_coe_nnreal_real).max
      measurable_const)).ennreal_ofReal
  · exact (measurable_const.mul ((measurable_coe_nnreal_real.sub measurable_const).max
      measurable_const)).ennreal_ofReal

lemma window_cost (c : Params) (hm : 2 ≤ c.m) (S : ℝ≥0) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ S)
    (t0 : ℕ) :
    (c.m : ℝ≥0∞) * ENNReal.ofReal (backorderCost P.law c.h c.p S) +
      ENNReal.ofReal c.θ * ENNReal.ofReal δ * (P.law {x : ℝ≥0 | (x : ℝ) ≤ S - δ}) ^ c.m ≤
    ∑ k ∈ Finset.range c.m, ∫⁻ d, costAt c (baseStockOrder S) d (t0 + k) ∂demandPathLaw P := by
  have hφ := measurable_baseStockOrder (m := c.m) S
  have hmo : ∀ t, Measurable (fun d => ENNReal.ofReal (c.θ * bsOut c.m S t d)) := fun t =>
    ((measurable_outdating_run _ hφ t).const_mul c.θ).ennreal_ofReal
  have hsplit : ∀ k, ∫⁻ d, costAt c (baseStockOrder S) d (t0 + k) ∂demandPathLaw P =
      ENNReal.ofReal (backorderCost P.law c.h c.p S) +
        ∫⁻ d, ENNReal.ofReal (c.θ * bsOut c.m S (t0 + k) d) ∂demandPathLaw P := by
    intro k
    simp_rw [bs_costAt c hm S _ (t0 + k)]
    rw [lintegral_add_right _ (hmo (t0 + k))]
    congr 1
    rw [lintegral_eval P (t0 + k) _ (measurable_nvTerm c.h c.p S)]
    exact lintegral_nv P c.h c.p c.h_pos.le c.p_pos.le S
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  gcongr
  rw [← lintegral_finsetSum _ (fun k _ => hmo (t0 + k))]
  set B : Set DemandPath := {d | ∀ k < c.m, ((d (t0 + k) : ℝ≥0) : ℝ) ≤ S - δ} with hB
  have hBm : MeasurableSet B := by
    simp only [hB, Set.setOf_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_le (measurable_coe_nnreal_real.comp (measurable_pi_apply _)) measurable_const
  calc ENNReal.ofReal c.θ * ENNReal.ofReal δ * (P.law {x : ℝ≥0 | (x : ℝ) ≤ S - δ}) ^ c.m
      = ∫⁻ d, B.indicator (fun _ => ENNReal.ofReal c.θ * ENNReal.ofReal δ) d ∂demandPathLaw P := by
        rw [lintegral_indicator_const hBm, hB, path_cylinder]
    _ ≤ _ := by
        apply lintegral_mono
        intro d
        by_cases hd : d ∈ B
        · rw [Set.indicator_of_mem hd]
          have hw : δ ≤ ∑ k ∈ Finset.range c.m, bsOut c.m S (t0 + k) d := window S d hm δ hδ t0 hd
          show ENNReal.ofReal c.θ * ENNReal.ofReal δ ≤
            ∑ k ∈ Finset.range c.m, ENNReal.ofReal (c.θ * bsOut c.m S (t0 + k) d)
          rw [← ENNReal.ofReal_mul c.θ_nonneg,
            ← ENNReal.ofReal_sum_of_nonneg (f := fun k => c.θ * bsOut c.m S (t0 + k) d)
              (fun k _ => mul_nonneg c.θ_nonneg
              ((bsInv_run S hm d (t0 + k)).outdating_nonneg _ _))]
          apply ENNReal.ofReal_le_ofReal
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left hw c.θ_nonneg
        · rw [Set.indicator_of_notMem hd]; exact bot_le

/-- Lower bound on the base-stock cost:
`C(S) ≥ N(S) + θ δ F(S-δ)^m / m`. -/
lemma bs_lower (c : Params) (hm : 2 ≤ c.m) (S : ℝ≥0) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ S) :
    ENNReal.ofReal (backorderCost P.law c.h c.p S) +
      ENNReal.ofReal c.θ * ENNReal.ofReal δ * (P.law {x : ℝ≥0 | (x : ℝ) ≤ S - δ}) ^ c.m /
        (c.m : ℝ≥0∞) ≤ PerishBaseStock.LifoNegative.baseStockCost P c S := by
  set N := ENNReal.ofReal (backorderCost P.law c.h c.p S)
  set K := ENNReal.ofReal c.θ * ENNReal.ofReal δ * (P.law {x : ℝ≥0 | (x : ℝ) ≤ S - δ}) ^ c.m
  unfold PerishBaseStock.LifoNegative.baseStockCost longRunCost
  apply le_limsup_of_frequently_le'
  rw [frequently_atTop]
  intro a
  refine ⟨(a + 1) * c.m - 1, by
    have : a + 1 ≤ (a + 1) * c.m := Nat.le_mul_of_pos_right _ (by omega)
    omega, ?_⟩
  have hT : (a + 1) * c.m - 1 + 1 = (a + 1) * c.m := by
    have : 1 ≤ (a + 1) * c.m := by nlinarith
    omega
  have hcast : (((a + 1) * c.m - 1 : ℕ) : ℝ≥0∞) + 1 = ((a + 1 : ℕ) : ℝ≥0∞) * (c.m : ℝ≥0∞) := by
    rw [← Nat.cast_mul, ← hT]; push_cast; ring
  rw [hT, hcast, sum_range_mul_split]
  have hm0 : (c.m : ℝ≥0∞) ≠ 0 := by
    have : c.m ≠ 0 := by omega
    exact_mod_cast this
  rw [ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero a) hm0))
    (Or.inl (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)))]
  calc (N + K / (c.m : ℝ≥0∞)) * (((a + 1 : ℕ) : ℝ≥0∞) * (c.m : ℝ≥0∞))
      = ∑ w ∈ Finset.range (a + 1), ((c.m : ℝ≥0∞) * N + K) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have : K / (c.m : ℝ≥0∞) * (c.m : ℝ≥0∞) = K :=
          ENNReal.div_mul_cancel hm0 (ENNReal.natCast_ne_top _)
        calc (N + K / (c.m : ℝ≥0∞)) * (((a + 1 : ℕ) : ℝ≥0∞) * (c.m : ℝ≥0∞))
            = ((a + 1 : ℕ) : ℝ≥0∞) * ((c.m : ℝ≥0∞) * N + K / (c.m : ℝ≥0∞) * (c.m : ℝ≥0∞)) := by
              ring
          _ = _ := by rw [this]
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro w _
        exact window_cost P c hm S δ hδ0 hδ (w * c.m)

/-- With `S = 0` nothing is ever stocked: `C(0) = N(0)`. -/
lemma bs_zero_le (c : Params) (hm : 2 ≤ c.m) :
    PerishBaseStock.LifoNegative.baseStockCost P c 0 ≤ ENNReal.ofReal (backorderCost P.law c.h c.p 0) := by
  unfold PerishBaseStock.LifoNegative.baseStockCost longRunCost
  apply limsup_cesaro_le
  intro T
  have he : ∀ t, ∫⁻ d, costAt c (baseStockOrder 0) d t ∂demandPathLaw P =
      ENNReal.ofReal (backorderCost P.law c.h c.p 0) := by
    intro t
    have : ∀ d, costAt c (baseStockOrder 0) d t =
        ENNReal.ofReal (c.h * max (((0 : ℝ≥0) : ℝ) - (d t : ℝ)) 0) +
          ENNReal.ofReal (c.p * max ((d t : ℝ) - ((0 : ℝ≥0) : ℝ)) 0) := by
      intro d
      rw [bs_costAt c hm 0 d t]
      have h1 := (bsInv_run (0 : ℝ≥0) hm d t).outdating_nonneg t (d t)
      have h2 := (bsInv_run (0 : ℝ≥0) hm d t).outdating_le t (d t)
      have h3 : max (((0 : ℝ≥0) : ℝ) - (d t : ℝ)) 0 = 0 := by
        apply max_eq_right; simp
      have h4 : bsOut c.m 0 t d = 0 := by
        unfold bsOut; linarith
      rw [h4, mul_zero, ENNReal.ofReal_zero, add_zero]
    simp_rw [this]
    rw [lintegral_eval P t _ (measurable_nvTerm c.h c.p _)]
    exact lintegral_nv P c.h c.p c.h_pos.le c.p_pos.le 0
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  push_cast
  exact le_rfl

end LifoNegSol

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open CappedBaseStock LostSalesOrderUpTo.Asymptotic

namespace LifoNegSol
open PerishBaseStock.LifoNegative

/-- A two-periodic policy: order `S'` in even periods, base-stock `L` in odd periods. -/
noncomputable def cycOrder (m : ℕ) (L S' : ℝ≥0) : OrderRule m := fun t x =>
  if t % 2 = 0 then S' else Real.toNNReal ((L : ℝ) - stockLevel x (m - 1))

lemma measurable_cycOrder (m : ℕ) (L S' : ℝ≥0) (t : ℕ) : Measurable (cycOrder m L S' t) := by
  unfold cycOrder
  by_cases ht : t % 2 = 0
  · simp only [ht, if_true]; exact measurable_const
  · simp only [ht, if_false]
    exact (continuous_real_toNNReal.comp
      (continuous_const.sub (continuous_stockLevel _))).measurable

variable {m : ℕ}

lemma stockLevel_nonneg_of_bd (L : ℝ≥0) (x : PerishBaseStock.Lifetime.State m)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ L) (i : ℕ) : 0 ≤ stockLevel x i ∧ stockLevel x i ≤ L := by
  unfold stockLevel
  split_ifs
  · exact hx _
  · exact ⟨le_rfl, L.2⟩

lemma stockLevel_of_zero (x : PerishBaseStock.Lifetime.State m)
    (hx : ∀ i, x i = 0) (i : ℕ) : stockLevel x i = 0 := by
  unfold stockLevel
  split_ifs
  · exact hx _
  · rfl

lemma even_step (hm : 2 ≤ m) (L S' : ℝ≥0) (x : PerishBaseStock.Lifetime.State m)
    (hx : ∀ i, x i = 0) (D : ℝ≥0) (hD : (S' : ℝ) - D ≤ L) :
    orderUpTo x S' = S' ∧ outdating x S' D = 0 ∧
      ∀ i, 0 ≤ lifoStep x S' D i ∧ lifoStep x S' D i ≤ L := by
  have hU : orderUpTo x S' = S' := by
    unfold orderUpTo; rw [stockLevel_of_zero x hx]; ring
  have hO : outdating x S' D = 0 := by
    unfold outdating
    rw [level_of_lt _ _ _ (by omega), stockLevel_of_zero x hx]
    exact min_eq_right (le_max_right _ _)
  refine ⟨hU, hO, fun i => ?_⟩
  unfold lifoStep
  rw [hO, sub_zero, hU]
  have hl : 0 ≤ level x S' (i.val + 2) := by
    unfold level
    split_ifs
    · rw [stockLevel_of_zero x hx]
    · rw [hU]; exact S'.2
  refine ⟨le_min (le_max_right _ _) hl, (min_le_left _ _).trans (max_le hD L.2)⟩

lemma odd_step (hm : 2 ≤ m) (L : ℝ≥0) (x : PerishBaseStock.Lifetime.State m)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ L) (D : ℝ≥0) (hD : (L : ℝ) ≤ D) :
    orderUpTo x (Real.toNNReal ((L : ℝ) - stockLevel x (m - 1))) = L ∧
      outdating x (Real.toNNReal ((L : ℝ) - stockLevel x (m - 1))) D = 0 ∧
      ∀ i, lifoStep x (Real.toNNReal ((L : ℝ) - stockLevel x (m - 1))) D i = 0 := by
  set q := Real.toNNReal ((L : ℝ) - stockLevel x (m - 1))
  have hb := stockLevel_nonneg_of_bd L x hx
  have hU : orderUpTo x q = L := by
    unfold orderUpTo
    rw [Real.coe_toNNReal _ (by linarith [(hb (m - 1)).2])]; ring
  have ha : max (orderUpTo x q - (D : ℝ)) 0 = 0 := by
    rw [hU]; exact max_eq_right (by linarith)
  have hO : outdating x q D = 0 := by
    unfold outdating
    rw [ha, level_of_lt _ _ _ (by omega)]
    exact min_eq_left (hb 1).1
  refine ⟨hU, hO, fun i => ?_⟩
  unfold lifoStep
  rw [hO, sub_zero, ha]
  apply min_eq_left
  unfold level
  split_ifs
  · exact (hb _).1
  · rw [hU]; exact L.2

lemma cyc_run (hm : 2 ≤ m) (L S' : ℝ≥0) (hS' : (S' : ℝ) ≤ 2 * L) (d : DemandPath)
    (hd : ∀ t, (L : ℝ) ≤ d t) :
    ∀ t, (t % 2 = 0 → ∀ i, run (cycOrder m L S') d t i = 0) ∧
      (t % 2 = 1 → ∀ i, 0 ≤ run (cycOrder m L S') d t i ∧ run (cycOrder m L S') d t i ≤ L) := by
  intro t
  induction t with
  | zero => exact ⟨fun _ _ => rfl, fun h => by simp at h⟩
  | succ t ih =>
    have hrun : run (cycOrder m L S') d (t + 1) =
        lifoStep (run (cycOrder m L S') d t) (cycOrder m L S' t (run (cycOrder m L S') d t))
          (d t) := rfl
    rcases Nat.mod_two_eq_zero_or_one t with ht | ht
    · have hq : cycOrder m L S' t (run (cycOrder m L S') d t) = S' := by
        simp [cycOrder, ht]
      rw [hrun, hq]
      have := even_step hm L S' _ (ih.1 ht) (d t) (by linarith [hd t])
      exact ⟨fun h => by omega, fun _ => this.2.2⟩
    · have hq : cycOrder m L S' t (run (cycOrder m L S') d t) =
          Real.toNNReal ((L : ℝ) - stockLevel (run (cycOrder m L S') d t) (m - 1)) := by
        simp [cycOrder, ht]
      rw [hrun, hq]
      have := odd_step hm L _ (ih.2 ht) (d t) (hd t)
      exact ⟨fun _ => this.2.2, fun h => by omega⟩

lemma cyc_costAt (c : Params) (hm : 2 ≤ c.m) (L S' : ℝ≥0) (hS' : (S' : ℝ) ≤ 2 * L)
    (d : DemandPath) (hd : ∀ t, (L : ℝ) ≤ d t) (t : ℕ) :
    costAt c (cycOrder c.m L S') d t =
      ENNReal.ofReal (c.h * max (((if t % 2 = 0 then S' else L : ℝ≥0) : ℝ) - (d t : ℝ)) 0) +
        ENNReal.ofReal (c.p * max ((d t : ℝ) - ((if t % 2 = 0 then S' else L : ℝ≥0) : ℝ)) 0) := by
  have hr := cyc_run hm L S' hS' d hd t
  unfold costAt PerishBaseStock.LifoNegative.periodCost
  rcases Nat.mod_two_eq_zero_or_one t with ht | ht
  · have hq : cycOrder c.m L S' t (run (cycOrder c.m L S') d t) = S' := by
      simp [cycOrder, ht]
    have := even_step hm L S' _ (hr.1 ht) (d t) (by linarith [hd t])
    rw [hq, this.1, this.2.1]
    simp [ht]
  · have hq : cycOrder c.m L S' t (run (cycOrder c.m L S') d t) =
        Real.toNNReal ((L : ℝ) - stockLevel (run (cycOrder c.m L S') d t) (c.m - 1)) := by
      simp [cycOrder, ht]
    have := odd_step hm L _ (hr.2 ht) (d t) (hd t)
    rw [hq, this.1, this.2.1]
    simp [ht]

lemma alt_sum (x y : ℝ) (hxy : x ≤ y) (n : ℕ) :
    ∑ t ∈ Finset.range n, (if t % 2 = 0 then x else y) ≤ n * ((x + y) / 2) := by
  have key : ∀ k : ℕ, ∑ t ∈ Finset.range (2 * k), (if t % 2 = 0 then x else y) = k * (x + y) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have h1 : (2 * k) % 2 = 0 := by omega
      have h2 : (2 * k + 1) % 2 = 1 := by omega
      simp only [h1, h2, if_true, one_ne_zero, if_false]
      push_cast; ring
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [key]; push_cast; linarith
  · rw [Finset.sum_range_succ, key]
    have h1 : (2 * k) % 2 = 0 := by omega
    simp only [h1, if_true]
    push_cast; nlinarith

variable (P : DemandLaw)

lemma cyc_cost_le (c : Params) (hm : 2 ≤ c.m) (L S' : ℝ≥0) (hS' : (S' : ℝ) ≤ 2 * L)
    (hL : (L : ℝ) = PerishBaseStock.Outdating.lowerSupport P)
    (hD : 0 < PerishBaseStock.Outdating.lowerSupport P)
    (hle : backorderCost P.law c.h c.p S' ≤ backorderCost P.law c.h c.p L) :
    longRunCost P c (cycOrder c.m L S') ≤
      ENNReal.ofReal ((backorderCost P.law c.h c.p S' + backorderCost P.law c.h c.p L) / 2) := by
  set x := backorderCost P.law c.h c.p S'
  set y := backorderCost P.law c.h c.p L
  have hae : ∀ᵐ d ∂demandPathLaw P, ∀ t, (L : ℝ) ≤ d t := by
    filter_upwards [ae_path_ge P hD] with d hd
    intro t; rw [hL]; exact hd t
  have he : ∀ t, ∫⁻ d, costAt c (cycOrder c.m L S') d t ∂demandPathLaw P =
      ENNReal.ofReal (if t % 2 = 0 then x else y) := by
    intro t
    rw [lintegral_congr_ae (hae.mono fun d hd => cyc_costAt c hm L S' hS' d hd t)]
    rw [lintegral_eval P t _ (measurable_nvTerm c.h c.p _),
      lintegral_nv P c.h c.p c.h_pos.le c.p_pos.le]
    split_ifs <;> rfl
  have hx0 : 0 ≤ x := by
    unfold x backorderCost expectedHolding expectedShortfall
    have := c.h_pos; have := c.p_pos
    have h1 : 0 ≤ ∫ d : ℝ≥0, max ((S' : ℝ) - (d : ℝ)) 0 ∂P.law :=
      integral_nonneg fun _ => le_max_right _ _
    have h2 : 0 ≤ ∫ d : ℝ≥0, max ((d : ℝ) - (S' : ℝ)) 0 ∂P.law :=
      integral_nonneg fun _ => le_max_right _ _
    positivity
  unfold longRunCost
  apply limsup_cesaro_le
  intro T
  simp_rw [he]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => by split_ifs <;> linarith)]
  have hA : 0 ≤ (x + y) / 2 := by linarith
  calc ENNReal.ofReal (∑ t ∈ Finset.range (T + 1), if t % 2 = 0 then x else y)
      ≤ ENNReal.ofReal (((T + 1 : ℕ) : ℝ) * ((x + y) / 2)) :=
        ENNReal.ofReal_le_ofReal (alt_sum x y hle (T + 1))
    _ = ENNReal.ofReal ((x + y) / 2) * ((T : ℝ≥0∞) + 1) := by
        rw [mul_comm, ENNReal.ofReal_mul hA, ENNReal.ofReal_natCast]
        push_cast; ring

end LifoNegSol

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open CappedBaseStock LostSalesOrderUpTo.Asymptotic

namespace LifoNegSol
open PerishBaseStock.LifoNegative

variable (P : DemandLaw)

lemma nv_integral (h p : ℝ) (s : ℝ≥0) :
    backorderCost P.law h p s =
      ∫ x : ℝ≥0, (h * max ((s : ℝ) - (x : ℝ)) 0 + p * max ((x : ℝ) - s) 0) ∂P.law := by
  unfold backorderCost expectedHolding expectedShortfall
  rw [integral_add ((integrable_holding P s).const_mul h)
    ((integrable_shortfall P s s.2).const_mul p), integral_const_mul, integral_const_mul]

lemma integral_lin (p : ℝ) (s : ℝ) :
    ∫ x : ℝ≥0, p * ((x : ℝ) - s) ∂P.law = p * (mean P - s) := by
  rw [integral_const_mul, integral_sub P.finiteMean (integrable_const _), integral_const]
  simp [mean]

lemma integrable_lin (p : ℝ) (s : ℝ) :
    Integrable (fun x : ℝ≥0 => p * ((x : ℝ) - s)) P.law :=
  (P.finiteMean.sub (integrable_const s)).const_mul p

lemma integrable_g (h p : ℝ) (s : ℝ≥0) :
    Integrable (fun x : ℝ≥0 => h * max ((s : ℝ) - (x : ℝ)) 0 + p * max ((x : ℝ) - s) 0) P.law :=
  ((integrable_holding P s).const_mul h).add ((integrable_shortfall P s s.2).const_mul p)

lemma nv_ge (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (s : ℝ≥0) :
    p * (mean P - s) ≤ backorderCost P.law h p s := by
  rw [nv_integral, ← integral_lin]
  apply integral_mono (integrable_lin P p s) (integrable_g P h p s)
  intro x
  have h1 : 0 ≤ h * max ((s : ℝ) - (x : ℝ)) 0 := mul_nonneg hh (le_max_right _ _)
  have h2 : p * ((x : ℝ) - s) ≤ p * max ((x : ℝ) - s) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hp
  linarith

lemma nv_lower (h p : ℝ) (L : ℝ≥0) (hL : (L : ℝ) = PerishBaseStock.Outdating.lowerSupport P)
    (hD : 0 < PerishBaseStock.Outdating.lowerSupport P) :
    backorderCost P.law h p L = p * (mean P - PerishBaseStock.Outdating.lowerSupport P) := by
  rw [nv_integral, ← hL, ← integral_lin]
  apply integral_congr_ae
  filter_upwards [ae_ge_lowerSupport P hD] with x hx
  rw [← hL] at hx
  rw [max_eq_right (by linarith), max_eq_left (by linarith)]
  ring

lemma nv_strict (h p : ℝ) (hh : 0 < h) (hp : 0 < p) (L S' : ℝ≥0)
    (hL : (L : ℝ) = PerishBaseStock.Outdating.lowerSupport P)
    (hD : 0 < PerishBaseStock.Outdating.lowerSupport P) (h1 : (L : ℝ) < S')
    (h2 : S' < newsvendorLevel P.law h p) :
    backorderCost P.law h p S' < backorderCost P.law h p L := by
  have hF : P.law (Set.Iic S') < ENNReal.ofReal (p / (p + h)) := by
    have := notMem_of_lt_csInf h2 (OrderBot.bddBelow _)
    simp only [Set.mem_ofPred_eq, not_le] at this
    exact this
  have hr : (P.law (Set.Iic S')).toReal < p / (p + h) := ENNReal.toReal_lt_of_lt_ofReal hF
  have hr' : (h + p) * (P.law (Set.Iic S')).toReal < p := by
    rw [lt_div_iff₀ (by linarith)] at hr; linarith
  set ind : ℝ≥0 → ℝ := (Set.Iic S').indicator (fun _ => (1 : ℝ))
  have hind : Integrable ind P.law := (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  have hint : ∫ x, ind x ∂P.law = (P.law (Set.Iic S')).toReal := by
    rw [integral_indicator measurableSet_Iic, setIntegral_const]
    simp [Measure.real]
  set g : ℝ≥0 → ℝ := fun x => h * max ((L : ℝ) - (x : ℝ)) 0 + p * max ((x : ℝ) - L) 0
  have hle : ∫ x : ℝ≥0, (h * max ((S' : ℝ) - (x : ℝ)) 0 + p * max ((x : ℝ) - S') 0) ∂P.law ≤
      ∫ x, (g x + ((S' : ℝ) - L) * (h + p) * ind x - ((S' : ℝ) - L) * p) ∂P.law := by
    apply integral_mono_ae (integrable_g P h p S')
      (((integrable_g P h p L).add (hind.const_mul _)).sub (integrable_const _))
    filter_upwards [ae_ge_lowerSupport P hD] with x hx
    rw [← hL] at hx
    simp only [Pi.add_apply, Pi.sub_apply, g, ind]
    by_cases hxS : x ≤ S'
    · have hxS' : (x : ℝ) ≤ S' := hxS
      rw [Set.indicator_of_mem (show x ∈ Set.Iic S' from hxS)]
      rw [max_eq_left (by linarith), max_eq_right (by linarith : (x : ℝ) - S' ≤ 0),
        max_eq_right (by linarith : (L : ℝ) - x ≤ 0), max_eq_left (by linarith : (0 : ℝ) ≤ x - L)]
      nlinarith
    · have hxS' : (S' : ℝ) < x := lt_of_not_ge (fun h' => hxS (by exact_mod_cast h'))
      rw [Set.indicator_of_notMem (show x ∉ Set.Iic S' from hxS)]
      rw [max_eq_right (by linarith : (S' : ℝ) - x ≤ 0), max_eq_left (by linarith : (0 : ℝ) ≤ x - S'),
        max_eq_right (by linarith : (L : ℝ) - x ≤ 0), max_eq_left (by linarith : (0 : ℝ) ≤ x - L)]
      nlinarith
  have hg : Integrable g P.law := integrable_g P h p L
  have hi1 : Integrable (fun x => g x + ((S' : ℝ) - L) * (h + p) * ind x) P.law :=
    hg.add (hind.const_mul _)
  rw [integral_sub hi1 (integrable_const _), integral_add hg (hind.const_mul _),
    integral_const_mul, hint, integral_const] at hle
  simp only [probReal_univ, one_smul] at hle
  rw [nv_integral P h p S', nv_integral P h p L]
  have : ((S' : ℝ) - L) * (h + p) * (P.law (Set.Iic S')).toReal - ((S' : ℝ) - L) * p < 0 := by
    have hpos : 0 < (S' : ℝ) - L := by linarith
    nlinarith
  linarith

/-! ### Monotonicity in `θ` -/

lemma mono_costAt (c : Params) (φ : OrderRule c.m) (d : DemandPath) (t : ℕ) {θ θ' : ℝ≥0}
    (hθ : θ ≤ θ') : costAt (c.withTheta θ) φ d t ≤ costAt (c.withTheta θ') φ d t := by
  unfold costAt PerishBaseStock.LifoNegative.periodCost
  apply add_le_add_right
  simp only [Params.withTheta]
  by_cases ho : 0 ≤ outdating (run φ d t) (φ t (run φ d t)) (d t)
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by exact_mod_cast hθ) ho)
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (NNReal.coe_nonneg θ)
      (le_of_not_ge ho))]
    exact bot_le

lemma mono_longRun (c : Params) (φ : OrderRule c.m) {θ θ' : ℝ≥0} (hθ : θ ≤ θ') :
    longRunCost P (c.withTheta θ) φ ≤ longRunCost P (c.withTheta θ') φ := by
  unfold longRunCost
  apply limsup_le_limsup (Eventually.of_forall fun T => ?_)
  exact ENNReal.div_le_div_right (Finset.sum_le_sum fun t _ =>
    lintegral_mono fun d => mono_costAt c φ d t hθ) _

/-! ### Lower bound on the best base-stock cost -/

lemma best_lower (c : Params) (hm : 2 ≤ c.m) (hD : 0 < PerishBaseStock.Outdating.lowerSupport P)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ θ₀ : ℝ≥0, ENNReal.ofReal (c.p * (mean P - PerishBaseStock.Outdating.lowerSupport P) - ε) ≤
      bestBaseStockCost P (c.withTheta θ₀) := by
  set Dl := PerishBaseStock.Outdating.lowerSupport P
  set η := ε / c.p with hη
  have hηpos : 0 < η := div_pos hε c.p_pos
  have hpη : c.p * η = ε := by rw [hη, mul_div_cancel₀ _ c.p_pos.ne']
  set δ := η / 2 with hδ
  have hδpos : 0 < δ := by positivity
  set q0 := P.law {x : ℝ≥0 | (x : ℝ) ≤ Dl + δ}
  have hq0 : 0 < q0 := cdf_pos P hD _ (by linarith)
  set K0 := ENNReal.ofReal δ * q0 ^ c.m / (c.m : ℝ≥0∞)
  have hK0 : K0 ≠ 0 := by
    apply ne_of_gt
    rw [ENNReal.div_pos_iff]
    exact ⟨mul_ne_zero (ENNReal.ofReal_pos.2 hδpos).ne' (pow_ne_zero _ hq0.ne'),
      ENNReal.natCast_ne_top _⟩
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hK0
    (ENNReal.ofReal_ne_top (r := c.p * (mean P - Dl)))
  refine ⟨(n : ℝ≥0), le_iInf fun S => ?_⟩
  have hm' : 2 ≤ (c.withTheta (n : ℝ≥0)).m := hm
  by_cases hS : (S : ℝ) ≤ Dl + η
  · have hb := bs_lower P (c.withTheta (n : ℝ≥0)) hm' S 0 le_rfl S.2
    refine le_trans ?_ (le_trans le_self_add hb)
    apply ENNReal.ofReal_le_ofReal
    have := nv_ge P c.h c.p c.h_pos.le c.p_pos.le S
    have h3 : c.p * (mean P - Dl) - ε ≤ c.p * (mean P - S) := by
      rw [← hpη]; nlinarith [c.p_pos]
    exact h3.trans this
  · push Not at hS
    have hδS : δ ≤ (S : ℝ) := by linarith
    have hb := bs_lower P (c.withTheta (n : ℝ≥0)) hm' S δ hδpos.le hδS
    refine le_trans ?_ (le_trans le_add_self hb)
    have hq : q0 ≤ P.law {x : ℝ≥0 | (x : ℝ) ≤ S - δ} :=
      measure_mono fun x hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢; linarith
    calc ENNReal.ofReal (c.p * (mean P - Dl) - ε) ≤ ENNReal.ofReal (c.p * (mean P - Dl)) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ (n : ℝ≥0∞) * K0 := hn.le
      _ ≤ _ := by
          have hθ : ENNReal.ofReal (c.withTheta (n : ℝ≥0)).θ = (n : ℝ≥0∞) := by
            show ENNReal.ofReal ((n : ℝ≥0) : ℝ) = _
            rw [NNReal.coe_natCast, ENNReal.ofReal_natCast]
          rw [hθ]
          simp only [K0]
          rw [mul_div_assoc', ← mul_assoc]
          show _ ≤ (n : ℝ≥0∞) * ENNReal.ofReal δ * P.law {x : ℝ≥0 | (x : ℝ) ≤ S - δ} ^ c.m /
            (c.m : ℝ≥0∞)
          gcongr

end LifoNegSol


open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open CappedBaseStock LostSalesOrderUpTo.Asymptotic

namespace LifoNegSol
open PerishBaseStock.LifoNegative

variable (P : DemandLaw)

/-- `C_θ(D̲) ≤ N(D̲)`: with base-stock level `D̲` nothing ever outdates (a.s.). -/
lemma bs_lower_level_le (c : Params) (hm : 2 ≤ c.m) (L : ℝ≥0)
    (hL : (L : ℝ) = PerishBaseStock.Outdating.lowerSupport P)
    (hD : 0 < PerishBaseStock.Outdating.lowerSupport P) :
    PerishBaseStock.LifoNegative.baseStockCost P c L ≤
      ENNReal.ofReal (backorderCost P.law c.h c.p L) := by
  unfold PerishBaseStock.LifoNegative.baseStockCost longRunCost
  apply limsup_cesaro_le
  intro T
  have hae : ∀ᵐ d ∂demandPathLaw P, ∀ t, (L : ℝ) ≤ d t := by
    filter_upwards [ae_path_ge P hD] with d hd
    intro t; rw [hL]; exact hd t
  have he : ∀ t, ∫⁻ d, costAt c (baseStockOrder L) d t ∂demandPathLaw P =
      ENNReal.ofReal (backorderCost P.law c.h c.p L) := by
    intro t
    have : ∀ᵐ d ∂demandPathLaw P, costAt c (baseStockOrder L) d t =
        ENNReal.ofReal (c.h * max ((L : ℝ) - (d t : ℝ)) 0) +
          ENNReal.ofReal (c.p * max ((d t : ℝ) - L) 0) := by
      filter_upwards [hae] with d hd
      rw [bs_costAt c hm L d t]
      have h1 := (bsInv_run L hm d t).outdating_nonneg t (d t)
      have h2 := (bsInv_run L hm d t).outdating_le t (d t)
      have h3 : max ((L : ℝ) - (d t : ℝ)) 0 = 0 := max_eq_right (by linarith [hd t])
      have h4 : bsOut c.m L t d = 0 := by
        unfold bsOut; linarith
      rw [h4, mul_zero, ENNReal.ofReal_zero, add_zero]
    rw [lintegral_congr_ae this, lintegral_eval P t _ (measurable_nvTerm c.h c.p _)]
    exact lintegral_nv P c.h c.p c.h_pos.le c.p_pos.le L
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  push_cast
  exact le_rfl

/-- `N(S) ≤ N(S'') + h (S - S'')` for `S'' ≤ S`. -/
lemma nv_lip (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (S'' S : ℝ≥0) (hle : S'' ≤ S) :
    backorderCost P.law h p S ≤ backorderCost P.law h p S'' + h * ((S : ℝ) - S'') := by
  rw [nv_integral, nv_integral]
  have hle' : (S'' : ℝ) ≤ S := hle
  have hc : ∫ x : ℝ≥0, (h * max ((S'' : ℝ) - (x : ℝ)) 0 + p * max ((x : ℝ) - S'') 0 +
      h * ((S : ℝ) - S'')) ∂P.law =
      ∫ x : ℝ≥0, (h * max ((S'' : ℝ) - (x : ℝ)) 0 + p * max ((x : ℝ) - S'') 0) ∂P.law +
        h * ((S : ℝ) - S'') := by
    rw [integral_add (integrable_g P h p S'') (integrable_const _), integral_const]
    simp
  rw [← hc]
  apply integral_mono (integrable_g P h p S) ((integrable_g P h p S'').add (integrable_const _))
  intro x
  simp only [Pi.add_apply]
  have a1 : max ((S : ℝ) - x) 0 ≤ max ((S'' : ℝ) - x) 0 + ((S : ℝ) - S'') := by
    rcases le_total ((S : ℝ) - x) 0 with h0 | h0
    · rw [max_eq_right h0]; have := le_max_right ((S'' : ℝ) - x) 0; linarith
    · rw [max_eq_left h0]; have := le_max_left ((S'' : ℝ) - x) 0; linarith
  have a2 : max ((x : ℝ) - S) 0 ≤ max ((x : ℝ) - S'') 0 :=
    max_le_max (by linarith) le_rfl
  nlinarith [mul_le_mul_of_nonneg_left a1 hh, mul_le_mul_of_nonneg_left a2 hp]

/-- The single-period bound `N(S) ≤ p(E[D] - D̲)` on `[D̲, S^NP]`. -/
lemma nv_bound (h p : ℝ) (hh : 0 < h) (hp : 0 < p) (L S : ℝ≥0)
    (hL : (L : ℝ) = PerishBaseStock.Outdating.lowerSupport P)
    (hD : 0 < PerishBaseStock.Outdating.lowerSupport P) (h1 : L ≤ S)
    (h2 : S ≤ newsvendorLevel P.law h p) :
    backorderCost P.law h p S ≤ p * (mean P - PerishBaseStock.Outdating.lowerSupport P) := by
  have hy := nv_lower P h p L hL hD
  rcases eq_or_lt_of_le h1 with heq | hlt
  · rw [← heq, hy]
  by_contra hcon
  push Not at hcon
  set e := backorderCost P.law h p S - p * (mean P - PerishBaseStock.Outdating.lowerSupport P)
  have he : 0 < e := by simp only [e]; linarith
  have hlt' : (L : ℝ) < S := hlt
  set r : ℝ := max (((L : ℝ) + S) / 2) ((S : ℝ) - e / (2 * h))
  have hr1 : (L : ℝ) < r := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hr2 : r < S := by
    have : 0 < e / (2 * h) := by positivity
    exact max_lt (by linarith) (by linarith)
  set S'' : ℝ≥0 := ⟨r, by linarith [L.2]⟩
  have hS''S : S'' ≤ S := hr2.le
  have hstrict := nv_strict P h p hh hp L S'' hL hD hr1 (lt_of_lt_of_le hr2 h2)
  have hlip := nv_lip P h p hh.le hp.le S'' S hS''S
  have hgap : h * ((S : ℝ) - r) ≤ e / 2 := by
    have : (S : ℝ) - e / (2 * h) ≤ r := le_max_right _ _
    have h' : h * ((S : ℝ) - r) ≤ h * (e / (2 * h)) := mul_le_mul_of_nonneg_left (by linarith) hh.le
    calc h * ((S : ℝ) - r) ≤ h * (e / (2 * h)) := h'
      _ = e / 2 := by field_simp
  rw [hy] at hstrict
  have : backorderCost P.law h p S ≤ backorderCost P.law h p S'' + h * ((S : ℝ) - r) := hlip
  simp only [e] at he hgap
  linarith

end LifoNegSol

open LifoNegSol PerishBaseStock.LifoNegative in
theorem solution (P : DemandLaw) (c : Params) (S : ℝ≥0)
    (hm : 2 ≤ c.m)
    (hNP : PerishBaseStock.Outdating.lowerSupport P < (newsvendorLevel P.law c.h c.p : ℝ))
    (hD : 0 < PerishBaseStock.Outdating.lowerSupport P)
    (hS₁ : PerishBaseStock.Outdating.lowerSupport P ≤ (S : ℝ))
    (hS₂ : (S : ℝ) ≤ min (newsvendorLevel P.law c.h c.p : ℝ) ((c.m : ℝ) * PerishBaseStock.Outdating.lowerSupport P)) :
    backorderCost P.law c.h c.p S ≤ c.p * (mean P - PerishBaseStock.Outdating.lowerSupport P) := by
  set L : ℝ≥0 := ⟨PerishBaseStock.Outdating.lowerSupport P, hD.le⟩
  exact nv_bound P c.h c.p c.h_pos c.p_pos L S rfl hD hS₁
    (by have := (le_min_iff.mp hS₂).1; exact_mod_cast this)

