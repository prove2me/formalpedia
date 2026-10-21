-- Prove2me | solution 1 for StochIneqPO.Monotone.theorem6
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T15:39:10.654358+00:00
-- url     : https://prove2.me/submissions/49163a9a-7466-42a0-b39e-1a8ea297e697

/-
SPDX-License-Identifier: Apache-2.0
Full native monotone random-elements convergence theorem.
Mathematical source: Kamae, Krengel and O'Brien, Stochastic Inequalities
on Partially Ordered Spaces, Annals of Probability5(1977),899–912,
Theorem6 and condition(17), printed908–909.
Fresh compact-order oscillation, genuine probability-Cauchy completion,
weak/tight measure bridges, regular sandwich and explicit typewriter
counterexample proofs. All native definitions and hypotheses are unchanged.
No accepted proof implementation is copied.
-/
import Mathlib
import Definitions.Def_StochIneqPO_Monotone_Regular17
import Definitions.Def_StochIneqPO_Monotone_ConvergenceModes

-- BEGIN Foundation
open MeasureTheory Filter Set Topology
open StochIneqPO.Monotone

namespace MonotoneConvergenceProof

def CauchyInProbability {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ,
    ∀ m ≥ N, ∀ n ≥ N,
      μ {ω | ε ≤ dist (X m ω) (X n ω)} ≤ ENNReal.ofReal δ

end MonotoneConvergenceProof
-- END Foundation

-- BEGIN CompactOrder
open MeasureTheory Filter Set Topology

namespace MonotoneConvergenceProof

variable {E : Type*} [MetricSpace E] [PartialOrder E] [OrderClosedTopology E]

theorem compact_order_oscillation (x : ℕ → E) (hx : Monotone x)
    {K : Set E} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N, x i ∈ K → x j ∈ K → dist (x i) (x j) < ε := by
  classical
  by_contra! h
  choose i hi j hj hKi hKj hd using h
  obtain ⟨z, _, φ, hφ, hz⟩ := (hK.prod hK).isSeqCompact
    (fun n => show (x (i n), x (j n)) ∈ K ×ˢ K from ⟨hKi n, hKj n⟩)
  have ha : Tendsto (fun n => x (i (φ n))) atTop (𝓝 z.1) :=
    (continuous_fst.tendsto z).comp hz
  have hb : Tendsto (fun n => x (j (φ n))) atTop (𝓝 z.2) :=
    (continuous_snd.tendsto z).comp hz
  have hia (k : ℕ) : x k ≤ z.1 := by
    apply ge_of_tendsto ha
    filter_upwards [eventually_ge_atTop k] with n hn
    exact hx (hn.trans ((hφ.id_le n).trans (hi (φ n))))
  have hib (k : ℕ) : x k ≤ z.2 := by
    apply ge_of_tendsto hb
    filter_upwards [eventually_ge_atTop k] with n hn
    exact hx (hn.trans ((hφ.id_le n).trans (hj (φ n))))
  have heq : z.1 = z.2 := le_antisymm
    (le_of_tendsto' ha (fun n => hib (i (φ n))))
    (le_of_tendsto' hb (fun n => hia (j (φ n))))
  have hdist : ε ≤ dist z.1 z.2 := ge_of_tendsto' (ha.dist hb) (fun n => hd (φ n))
  rw [heq, dist_self] at hdist
  exact (not_le_of_gt hε) hdist

end MonotoneConvergenceProof
-- END CompactOrder

-- BEGIN TightCauchy
open MeasureTheory Filter Set Topology
open StochIneqPO.Monotone
open scoped ENNReal

namespace MonotoneConvergenceProof

variable {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E]
  [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]

def tailOscillation (X : ℕ → Ω → E) (K : Set E) (ε : ℝ) (N : ℕ) : Set Ω :=
  {ω | ∃ i ≥ N, ∃ j ≥ N, X i ω ∈ K ∧ X j ω ∈ K ∧ ε ≤ dist (X i ω) (X j ω)}

omit [PartialOrder E] [OrderClosedTopology E] in
theorem measurable_tailOscillation [SecondCountableTopology E] {X : ℕ → Ω → E} (hX : ∀ i, Measurable (X i))
    {K : Set E} (hK : IsCompact K) (ε : ℝ) (N : ℕ) :
    MeasurableSet (tailOscillation X K ε N) := by
  unfold tailOscillation
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion; intro i
  by_cases hi : N ≤ i
  · simp only [hi, true_and, ofPred_exists]
    apply MeasurableSet.iUnion; intro j
    by_cases hj : N ≤ j
    · simp only [hj, true_and]
      exact ((hK.isClosed.measurableSet.preimage (hX i)).inter
        ((hK.isClosed.measurableSet.preimage (hX j)).inter
          (measurableSet_le measurable_const ((hX i).dist (hX j)))))
    · simp [hj]
  · simp [hi]

omit [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
  [PartialOrder E] [OrderClosedTopology E] in

theorem tailOscillation_antitone (X : ℕ → Ω → E) (K : Set E) (ε : ℝ) :
    Antitone (tailOscillation X K ε) := by
  intro n m hnm ω hω
  rcases hω with ⟨i, hi, j, hj, hKi, hKj, hd⟩
  exact ⟨i, hnm.trans hi, j, hnm.trans hj, hKi, hKj, hd⟩

omit [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] in
theorem tailOscillation_iInter {X : ℕ → Ω → E}
    (hm : ∀ ω, Monotone fun n => X n ω) {K : Set E} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) : (⋂ N, tailOscillation X K ε N) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro ω hω
  obtain ⟨N, hN⟩ := compact_order_oscillation (fun n => X n ω) (hm ω) hK hε
  rcases mem_iInter.mp hω N with ⟨i, hi, j, hj, hKi, hKj, hd⟩
  exact (not_le_of_gt (hN i hi j hj hKi hKj)) hd

theorem tight_cauchy [SecondCountableTopology E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ i, Measurable (X i))
    (hm : ∀ ω, Monotone fun n => X n ω) (htight : LawsTight μ X) :
    CauchyInProbability μ X := by
  intro ε hε δ hδ
  have hthird : 0 < δ / 3 := by positivity
  obtain ⟨K, hK, hmass⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    htight (ENNReal.ofReal (δ / 3)) (by positivity)
  have hout (n : ℕ) : μ {ω | X n ω ∉ K} ≤ ENNReal.ofReal (δ / 3) := by
    have h := hmass (μ.map (X n)) (mem_range_self n)
    rw [Measure.map_apply (hX n) hK.isClosed.measurableSet.compl] at h
    exact h
  have hlim : Tendsto (fun N => μ (tailOscillation X K ε N)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop
      (fun N => (measurable_tailOscillation hX hK ε N).nullMeasurableSet)
      (tailOscillation_antitone X K ε) ⟨0, measure_ne_top μ _⟩
    simpa only [tailOscillation_iInter hm hK hε, measure_empty, Function.comp_def] using h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const (by positivity :
    (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 3)))
  refine ⟨N, ?_⟩
  intro m hmN n hnN
  have hsub : {ω | ε ≤ dist (X m ω) (X n ω)} ⊆
      (tailOscillation X K ε N ∪ {ω | X m ω ∉ K}) ∪ {ω | X n ω ∉ K} := by
    intro ω hd
    by_cases hmK : X m ω ∈ K
    · by_cases hnK : X n ω ∈ K
      · exact Or.inl (Or.inl ⟨m, hmN, n, hnN, hmK, hnK, hd⟩)
      · exact Or.inr hnK
    · exact Or.inl (Or.inr hmK)
  calc
    μ {ω | ε ≤ dist (X m ω) (X n ω)} ≤
        μ ((tailOscillation X K ε N ∪ {ω | X m ω ∉ K}) ∪ {ω | X n ω ∉ K}) :=
      measure_mono hsub
    _ ≤ (μ (tailOscillation X K ε N) + μ {ω | X m ω ∉ K}) + μ {ω | X n ω ∉ K} :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3)) + ENNReal.ofReal (δ / 3) :=
      add_le_add (add_le_add (hN N le_rfl).le (hout m)) (hout n)
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add hthird.le hthird.le,
        ← ENNReal.ofReal_add (add_nonneg hthird.le hthird.le) hthird.le]
      congr 1
      ring

end MonotoneConvergenceProof
-- END TightCauchy

-- BEGIN ModeBridges
open MeasureTheory ProbabilityTheory Filter Set Topology
open StochIneqPO.Monotone

namespace MonotoneConvergenceProof

variable {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
  [MeasurableSpace E] [BorelSpace E]

theorem probability_weak (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n))
    (h : ConvergesInProbability μ X) : LawsConvergeWeakly μ X := by
  obtain ⟨Y, hY, hlim⟩ := h
  have hd := hlim.tendstoInDistribution (fun n => (hX n).aemeasurable)
  exact ⟨⟨μ.map Y, Measure.isProbabilityMeasure_map hY.aemeasurable⟩,
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hd.tendsto⟩

theorem weak_tight [CompleteSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n))
    (h : LawsConvergeWeakly μ X) : LawsTight μ X := by
  obtain ⟨P, hP⟩ := h
  let Q : ℕ → ProbabilityMeasure E := fun n =>
    ⟨μ.map (X n), Measure.isProbabilityMeasure_map (hX n).aemeasurable⟩
  have hlim : Tendsto Q atTop (𝓝 P) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hP
  have hc : IsCompact (closure (range Q)) :=
    hlim.isCompact_insert_range.of_isClosed_subset isClosed_closure
      (closure_minimal (subset_insert P (range Q)) hlim.isCompact_insert_range.isClosed)
  have ht := isTightMeasureSet_of_isCompact_closure hc
  have heq : {((q : ProbabilityMeasure E) : Measure E) | q ∈ range Q} =
      range (fun n => μ.map (X n)) := by
    ext ν
    constructor
    · rintro ⟨q, ⟨n, rfl⟩, rfl⟩
      exact mem_range_self n
    · rintro ⟨n, rfl⟩
      exact ⟨Q n, mem_range_self n, rfl⟩
  rw [heq] at ht
  exact ht

theorem almostSure_probability [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n))
    (h : ConvergesAS μ X) : ConvergesInProbability μ X := by
  obtain ⟨Y, hY⟩ := h
  obtain ⟨Z, hZ, hz⟩ := measurable_limit_of_tendsto_metrizable_ae
    (fun n => (hX n).aemeasurable) (hY.mono fun ω hω => ⟨Y ω, hω⟩)
  exact ⟨Z, hZ, tendstoInMeasure_of_tendsto_ae
    (fun n => (hX n).aestronglyMeasurable) hz⟩

end MonotoneConvergenceProof
-- END ModeBridges

-- BEGIN ProbabilityCompletion
open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace MonotoneConvergenceProof

private def thresholdSeq (N : ℕ → ℕ) : ℕ → ℕ
  | 0 => N 0
  | n + 1 => max (thresholdSeq N n + 1) (N (n + 1))

private theorem thresholdSeq_ge (N : ℕ → ℕ) (n : ℕ) : N n ≤ thresholdSeq N n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

private theorem thresholdSeq_strictMono (N : ℕ → ℕ) : StrictMono (thresholdSeq N) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

theorem cauchy_limit_of_subsequence {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (hC : CauchyInProbability μ X)
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop) (Y : Ω → E)
    (hY : TendstoInMeasure μ (fun n => X (r n)) atTop Y) :
    TendstoInMeasure μ X atTop Y := by
  rw [tendstoInMeasure_iff_dist] at hY ⊢
  intro ε hε
  apply ENNReal.tendsto_atTop_zero.mpr
  intro δ hδ
  by_cases htop : δ = ∞
  · subst δ
    exact ⟨0, fun _ _ => le_top⟩
  have hd : 0 < δ.toReal / 2 := half_pos (ENNReal.toReal_pos hδ.ne' htop)
  obtain ⟨N, hN⟩ := hC (ε / 2) (half_pos hε) (δ.toReal / 2) hd
  have he : ∀ᶠ j in atTop,
      μ {ω | ε / 2 ≤ dist (X (r j) ω) (Y ω)} < ENNReal.ofReal (δ.toReal / 2) :=
    (tendsto_order.1 (hY (ε / 2) (half_pos hε))).2 _ (ENNReal.ofReal_pos.mpr hd)
  obtain ⟨j, hj, hjN⟩ := (he.and (hr.eventually (eventually_ge_atTop N))).exists
  refine ⟨N, fun n hn => ?_⟩
  calc
    μ {ω | ε ≤ dist (X n ω) (Y ω)} ≤
        μ ({ω | ε / 2 ≤ dist (X n ω) (X (r j) ω)} ∪
          {ω | ε / 2 ≤ dist (X (r j) ω) (Y ω)}) := by
      apply measure_mono
      intro ω hω
      by_contra h
      simp only [mem_union, mem_ofPred_eq, not_or, not_le] at h
      have h1 := h.1
      have h2 := h.2
      have := dist_triangle (X n ω) (X (r j) ω) (Y ω)
      change ε ≤ dist (X n ω) (Y ω) at hω
      linarith
    _ ≤ μ {ω | ε / 2 ≤ dist (X n ω) (X (r j) ω)} +
        μ {ω | ε / 2 ≤ dist (X (r j) ω) (Y ω)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ.toReal / 2) + ENNReal.ofReal (δ.toReal / 2) :=
      add_le_add (hN n hn (r j) hjN) hj.le
    _ = δ := by
      rw [← ENNReal.ofReal_add hd.le hd.le]
      convert ENNReal.ofReal_toReal htop using 1; ring

theorem cauchy_measurable_limit {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → E)
    (hX : ∀ n, Measurable (X n)) (hC : CauchyInProbability μ X) :
    ∃ Y : Ω → E, Measurable Y ∧ TendstoInMeasure μ X atTop Y := by
  classical
  have hp (n : ℕ) : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) _
  choose N hN using fun n => hC ((1 / 2 : ℝ) ^ n) (hp n) ((1 / 2 : ℝ) ^ n) (hp n)
  let r := thresholdSeq N
  have hr : StrictMono r := thresholdSeq_strictMono N
  let B : ℕ → Set Ω := fun n =>
    {ω | (1 / 2 : ℝ) ^ n ≤ dist (X (r n) ω) (X (r (n + 1)) ω)}
  have hb (n : ℕ) : μ (B n) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    have hn := hN n (r n) (thresholdSeq_ge N n) (r (n + 1))
      ((thresholdSeq_ge N n).trans (hr.monotone (Nat.le_succ n)))
    have hcast : ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = (2 : ℝ≥0∞)⁻¹ ^ n := by
      rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    exact hn.trans_eq hcast

  have hs : (∑' n, μ (B n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hb)
    norm_num [ENNReal.tsum_geometric]
  have hae : ∀ᵐ ω ∂μ, ∃ y : E, Tendsto (fun n => X (r n) ω) atTop (𝓝 y) := by
    filter_upwards [ae_eventually_notMem hs] with ω hω
    obtain ⟨K, hK⟩ := eventually_atTop.1 hω
    have hc : CauchySeq (fun n => X (r (n + K)) ω) := by
      apply cauchySeq_of_dist_le_of_summable (fun n => (1 / 2 : ℝ) ^ (n + K))
      · intro n
        have hh := hK (n + K) (Nat.le_add_left _ _)
        have hh' : dist (X (r (n + K)) ω) (X (r (n + K + 1)) ω) <
            (1 / 2 : ℝ) ^ (n + K) := by simpa only [B, mem_ofPred_eq, not_le] using hh
        simpa only [Nat.succ_eq_add_one, Nat.add_right_comm] using hh'.le
      · simpa only [pow_add] using
          (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_right
            ((1 / 2 : ℝ) ^ K)
    exact cauchySeq_tendsto_of_complete ((cauchySeq_shift K).1 hc)
  obtain ⟨Y, hY, hlim⟩ := measurable_limit_of_tendsto_metrizable_ae
    (fun n => (hX (r n)).aemeasurable) hae
  refine ⟨Y, hY, cauchy_limit_of_subsequence μ X hC r hr.tendsto_atTop Y ?_⟩
  exact tendstoInMeasure_of_tendsto_ae (fun n => (hX (r n)).aestronglyMeasurable) hlim

end MonotoneConvergenceProof
-- END ProbabilityCompletion

-- BEGIN Regular
open MeasureTheory Filter Set Topology
open StochIneqPO.Monotone

namespace MonotoneConvergenceProof

theorem regular_subsequence {E : Type*} [TopologicalSpace E] [PartialOrder E]
    (h17 : Regular17 E) (u : ℕ → E) (hu : Monotone u)
    (r : ℕ → ℕ) (hr : StrictMono r) (z : E)
    (hz : Tendsto (fun n => u (r n)) atTop (𝓝 z)) : Tendsto u atTop (𝓝 z) := by
  classical
  by_contra hn
  obtain ⟨U, hU, hbad⟩ := not_tendsto_iff_exists_frequently_notMem.1 hn
  have hb : ∀ n : ℕ, ∃ k ≥ n, u k ∉ U := frequently_atTop.1 hbad
  choose b hb hbu using hb
  let a : ℕ → ℕ := Nat.rec 0 (fun _ i => max (i + 1) (b (r i) + 1))
  have has (n : ℕ) : a (n + 1) = max (a n + 1) (b (r (a n)) + 1) := rfl
  have ha : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [has]
    exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  have hs : ∀ n, u (r (a n)) ≤ u (b (r (a n))) ∧
      u (b (r (a n))) ≤ u (r (a (n + 1))) := by
    intro n
    refine ⟨hu (hb _), hu ?_⟩
    have hh : b (r (a n)) < a (n + 1) := by
      rw [has]
      exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)
    exact hh.le.trans (hr.id_le _)
  have hy := h17 (fun n => u (r (a n))) (fun n => u (b (r (a n)))) z hs
    (hz.comp ha.tendsto_atTop)
  obtain ⟨n, hn⟩ := (hy.eventually hU).exists
  exact hbu _ hn

theorem regular_ae {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [PartialOrder E]
    (h17 : Regular17 E) (μ : Measure Ω) (X : ℕ → Ω → E)
    (hX : ∀ n, Measurable (X n)) (hmono : ∀ ω, Monotone fun n => X n ω)
    (Y : Ω → E) (hY : Measurable Y) (hXY : TendstoInMeasure μ X atTop Y) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) := by
  have _ := hX
  have _ := hY
  obtain ⟨r, hr, hlim⟩ := hXY.exists_seq_tendsto_ae
  filter_upwards [hlim] with ω hω
  exact regular_subsequence h17 (fun n => X n ω) (hmono ω) r hr (Y ω) hω

end MonotoneConvergenceProof
-- END Regular

-- BEGIN Typewriter
open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace MonotoneConvergenceProof

noncomputable def typewriterLaw : Measure ℝ := volume.restrict (Ico 0 1)

instance typewriterLaw_probability : IsProbabilityMeasure typewriterLaw where
  measure_univ := by simp [typewriterLaw, Real.volume_Ico]

def typewriterEvent (n : ℕ) : Set ℝ :=
  let k := (Nat.unpair n).1
  let j := (Nat.unpair n).2
  if j ≤ k then Ico ((j : ℝ) / (k + 1)) ((j + 1 : ℝ) / (k + 1)) else ∅

theorem typewriterEvent_pair (k j : ℕ) :
    typewriterEvent (Nat.pair k j) =
      if j ≤ k then Ico ((j : ℝ) / (k + 1)) ((j + 1 : ℝ) / (k + 1)) else ∅ := by
  simp [typewriterEvent]

theorem typewriterEvent_measurable (n : ℕ) : MeasurableSet (typewriterEvent n) := by
  dsimp only [typewriterEvent]
  split_ifs
  · exact measurableSet_Ico
  · exact MeasurableSet.empty

theorem typewriter_measure_bound (k j : ℕ) :
    typewriterLaw (typewriterEvent (Nat.pair k j)) ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
  rw [typewriterEvent_pair]
  split_ifs
  · calc
      typewriterLaw (Ico ((j : ℝ) / (k + 1)) ((j + 1 : ℝ) / (k + 1))) ≤
          volume (Ico ((j : ℝ) / (k + 1)) ((j + 1 : ℝ) / (k + 1))) :=
        Measure.restrict_apply_le _ _
      _ = ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
        rw [Real.volume_Ico]
        congr 1
        ring
  · simp

theorem typewriter_measure_tendsto :
    Tendsto (fun n => typewriterLaw (typewriterEvent n)) atTop (𝓝 0) := by
  apply ENNReal.tendsto_atTop_zero.mpr
  intro δ hδ
  by_cases htop : δ = ∞
  · subst δ
    exact ⟨0, fun _ _ => le_top⟩
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt (ENNReal.toReal_pos hδ.ne' htop)
  refine ⟨(K + 1) ^ 2, fun n hn => ?_⟩
  let k := (Nat.unpair n).1
  let j := (Nat.unpair n).2
  have hpair : Nat.pair k j = n := Nat.pair_unpair n
  by_cases hj : j ≤ k
  · have hk : K ≤ k := by
      by_contra h
      have hlt : k < K := Nat.lt_of_not_ge h
      have hb := Nat.pair_lt_max_add_one_sq k j
      rw [max_eq_left hj, hpair] at hb
      nlinarith
    calc
      typewriterLaw (typewriterEvent n) ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
        rw [← hpair]
        exact typewriter_measure_bound k j
      _ ≤ ENNReal.ofReal (1 / ((K : ℝ) + 1)) := by
        apply ENNReal.ofReal_le_ofReal
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right hk 1
      _ ≤ δ := by
        rw [← ENNReal.ofReal_toReal htop]
        exact ENNReal.ofReal_le_ofReal hK.le
  · have he : typewriterEvent n = ∅ := by
      rw [← hpair, typewriterEvent_pair, if_neg hj]
    simp [he]

theorem typewriter_recurrent (ω : ℝ) (hω : ω ∈ Ico (0 : ℝ) 1) :
    ∀ N : ℕ, ∃ n ≥ N, ω ∈ typewriterEvent n := by
  intro N
  let j : ℕ := ⌊((N : ℝ) + 1) * ω⌋₊
  have hnonneg : 0 ≤ ((N : ℝ) + 1) * ω := mul_nonneg (by positivity) hω.1
  have hj : j ≤ N := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt hnonneg).2
    push_cast
    nlinarith [hω.2]
  refine ⟨Nat.pair N j, Nat.left_le_pair N j, ?_⟩
  rw [typewriterEvent_pair, if_pos hj]
  constructor
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < N + 1)).2
    simpa only [j, mul_comm] using Nat.floor_le hnonneg
  · apply (lt_div_iff₀ (by positivity : (0 : ℝ) < N + 1)).2
    simpa only [j, mul_comm] using Nat.lt_floor_add_one (((N : ℝ) + 1) * ω)

theorem typewriter_ae_recurrent :
    ∀ᵐ ω ∂typewriterLaw, ∀ N : ℕ, ∃ n ≥ N, ω ∈ typewriterEvent n := by
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ico] with ω hω
  exact typewriter_recurrent ω hω

end MonotoneConvergenceProof
-- END Typewriter

-- BEGIN Counterexample
open MeasureTheory Filter Set Topology
open StochIneqPO.Monotone
open scoped ENNReal NNReal Classical

namespace MonotoneConvergenceProof

noncomputable def alternatingRun {E : Type*} (x y : ℕ → E) (n : ℕ) (ω : ℝ) : E :=
  if n % 2 = 0 then x (n / 2)
  else if ω ∈ typewriterEvent (n / 2) then y (n / 2) else x (n / 2)

theorem alternatingRun_even {E : Type*} (x y : ℕ → E) (n : ℕ) (ω : ℝ) :
    alternatingRun x y (2 * n) ω = x n := by
  simp [alternatingRun]

theorem alternatingRun_odd {E : Type*} (x y : ℕ → E) (n : ℕ) (ω : ℝ) :
    alternatingRun x y (2 * n + 1) ω =
      if ω ∈ typewriterEvent n then y n else x n := by
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp [alternatingRun, hdiv]

theorem alternatingRun_measurable {E : Type*} [MeasurableSpace E] (x y : ℕ → E) (n : ℕ) :
    Measurable (alternatingRun x y n) := by
  unfold alternatingRun
  split_ifs with h
  · exact measurable_const
  · exact Measurable.ite (typewriterEvent_measurable _) measurable_const measurable_const

theorem alternatingRun_monotone {E : Type*} [PartialOrder E] (x y : ℕ → E)
    (hs : ∀ n, x n ≤ y n ∧ y n ≤ x (n + 1)) (ω : ℝ) :
    Monotone fun n => alternatingRun x y n ω := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n % 2 = 0
  · have he : n = 2 * (n / 2) := by omega
    nth_rw 1 [he]
    rw [alternatingRun_even]
    have he' : n + 1 = 2 * (n / 2) + 1 := by omega
    rw [he', alternatingRun_odd]
    split_ifs
    · exact (hs _).1
    · exact le_rfl
  · have he : n = 2 * (n / 2) + 1 := by omega
    nth_rw 1 [he]
    rw [alternatingRun_odd]
    have he' : n + 1 = 2 * (n / 2 + 1) := by omega
    rw [he', alternatingRun_even]
    split_ifs
    · exact (hs _).2
    · exact (hs _).1.trans (hs _).2

theorem alternatingRun_probability {E : Type*} [MetricSpace E] (x y : ℕ → E) (z : E)
    (hx : Tendsto x atTop (𝓝 z)) :
    TendstoInMeasure typewriterLaw (alternatingRun x y) atTop (fun _ => z) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hdiv : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    exact eventually_atTop.2 ⟨2 * N, fun n hn => by omega⟩
  have hx' : ∀ᶠ n in atTop, dist (x (n / 2)) z < ε :=
    hdiv.eventually ((Metric.tendsto_nhds.1 hx) ε hε)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (typewriter_measure_tendsto.comp hdiv) (Eventually.of_forall fun _ => zero_le)
  filter_upwards [hx'] with n hn
  apply measure_mono
  intro ω hω
  by_contra hnot
  have he : alternatingRun x y n ω = x (n / 2) := by
    simp [alternatingRun, hnot]
  change ε ≤ dist (alternatingRun x y n ω) z at hω
  rw [he] at hω
  exact hn.not_ge hω

theorem alternatingRun_not_as {E : Type*} [MetricSpace E] (x y : ℕ → E) (z : E)
    (hx : Tendsto x atTop (𝓝 z)) (ε : ℝ) (hε : 0 < ε)
    (hy : ∀ n, ε ≤ dist (y n) z) :
    ¬ ConvergesAS typewriterLaw (alternatingRun x y) := by
  rintro ⟨Y, hY⟩
  have heven : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    exact eventually_atTop.2 ⟨N, fun n hn => by omega⟩
  have hfalse : ∀ᵐ ω ∂typewriterLaw, False := by
    filter_upwards [hY, typewriter_ae_recurrent] with ω hω hrec
    have he : Tendsto x atTop (𝓝 (Y ω)) := by
      simpa only [Function.comp_def, alternatingRun_even] using hω.comp heven
    have hval : Y ω = z := tendsto_nhds_unique he hx
    rw [hval] at hω
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hω) ε hε
    obtain ⟨n, hn, hmem⟩ := hrec N
    have hb := hN (2 * n + 1) (by omega)
    rw [alternatingRun_odd, if_pos hmem] at hb
    exact hb.not_ge (hy n)
  simpa using (ae_iff.mp hfalse)

theorem counterexample_of_not_regular {E : Type*} [MetricSpace E]
    [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E] (h17 : ¬ Regular17 E) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
      ∃ X : ℕ → Ω → E, (∀ i, Measurable (X i)) ∧ (∀ ω, Monotone fun i => X i ω) ∧
        (∃ z : E, TendstoInMeasure μ X atTop (fun _ => z)) ∧ ¬ ConvergesAS μ X := by
  classical
  simp only [Regular17, not_forall] at h17
  obtain ⟨x, y, z, hs, hx, hy⟩ := h17
  have hxm : Monotone x := monotone_nat_of_le_succ fun n => (hs n).1.trans (hs n).2
  rw [Metric.tendsto_atTop] at hy
  push Not at hy
  obtain ⟨ε, hε, hbad⟩ := hy
  obtain ⟨r, hr, hdist⟩ := extraction_of_frequently_atTop
    (frequently_atTop.2 hbad)
  have hsr : ∀ n, x (r n) ≤ y (r n) ∧ y (r n) ≤ x (r (n + 1)) := by
    intro n
    refine ⟨(hs _).1, (hs _).2.trans (hxm ?_)⟩
    exact Nat.succ_le_of_lt (hr (Nat.lt_succ_self n))
  refine ⟨ℝ, inferInstance, typewriterLaw, inferInstance,
    alternatingRun (fun n => x (r n)) (fun n => y (r n)),
    alternatingRun_measurable _ _, alternatingRun_monotone _ _ hsr,
    ⟨z, alternatingRun_probability _ _ z (hx.comp hr.tendsto_atTop)⟩, ?_⟩
  exact alternatingRun_not_as _ _ z (hx.comp hr.tendsto_atTop) ε hε hdist

end MonotoneConvergenceProof
-- END Counterexample

-- BEGIN NativeRoot
namespace StochIneqPO.Monotone

open MeasureTheory

universe u

theorem theorem6 {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E] :
    (∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → E), (∀ i, Measurable (X i)) → (∀ ω, Monotone fun i => X i ω) →
        List.TFAE [LawsTight μ X, LawsConvergeWeakly μ X, ConvergesInProbability μ X]) ∧
    (Regular17 E ↔
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → E), (∀ i, Measurable (X i)) → (∀ ω, Monotone fun i => X i ω) →
        (ConvergesAS μ X ↔ ConvergesInProbability μ X)) := by
  constructor
  · intro Ω _ μ _ X hX hm
    tfae_have 1 → 3 := fun ht =>
      MonotoneConvergenceProof.cauchy_measurable_limit μ X hX
        (MonotoneConvergenceProof.tight_cauchy μ X hX hm ht)
    tfae_have 3 → 2 := MonotoneConvergenceProof.probability_weak μ X hX
    tfae_have 2 → 1 := MonotoneConvergenceProof.weak_tight μ X hX
    tfae_finish
  · constructor
    · intro h17 Ω _ μ _ X hX hm
      constructor
      · exact MonotoneConvergenceProof.almostSure_probability μ X hX
      · rintro ⟨Y, hY, hXY⟩
        exact ⟨Y, MonotoneConvergenceProof.regular_ae h17 μ X hX hm Y hY hXY⟩
    · intro h
      by_contra h17
      obtain ⟨Ω, mΩ, μ, hμ, X, hX, hm, ⟨z, hz⟩, hnot⟩ :=
        MonotoneConvergenceProof.counterexample_of_not_regular h17
      let : MeasurableSpace Ω := mΩ
      let : IsProbabilityMeasure μ := hμ
      exact hnot ((h Ω μ X hX hm).mpr ⟨fun _ => z, measurable_const, hz⟩)

end StochIneqPO.Monotone
-- END NativeRoot

open MeasureTheory StochIneqPO.Monotone

universe u

theorem solution {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E] :
    (∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → E), (∀ i, Measurable (X i)) → (∀ ω, Monotone fun i => X i ω) →
        List.TFAE [LawsTight μ X, LawsConvergeWeakly μ X, ConvergesInProbability μ X]) ∧
    (Regular17 E ↔
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → E), (∀ i, Measurable (X i)) → (∀ ω, Monotone fun i => X i ω) →
        (ConvergesAS μ X ↔ ConvergesInProbability μ X)) :=
  StochIneqPO.Monotone.theorem6 (E := E)
