-- Prove2me | solution 1 for OWMR.ss_poisson_upper
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T06:36:59.700408+00:00
-- url     : https://prove2.me/submissions/b79ab2fb-0dd6-4f97-bb18-e160d4b30faa

import Theorems.Thm_OWMR_ss_renewal_reward
import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Order.Filter.ENNReal
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
Finite-horizon upper bound for an `(s,S)` process started at a stopping time.

Let `ρ` be the law of the demand, `U` its renewal measure, and `g*` the long-run average cost of
the `(s,S)` policy (`s ≤ S`). The relative value
`V(y) = ∫_{[0,y-s)} (f(y-z) - g*) U(dz)` (plus `K` above `S` when `s = S`) is bounded on every
half-line `(-∞, M']`, and by the renewal equation `U = δ₀ + ρ * U` it satisfies the Poisson
inequality `K 1{x ≤ s, x < S} + f(post x) + 𝔼 V(post x - D) ≤ g* + V(x)`, with equality when
`s < S` (then `g* = (K + ∫_{[0,S-s)} f(S-z) U(dz)) / U[0,S-s)` by `ss_renewal_reward`, so that
`V(S) = -K`). For `s = S`, `g* = f(S) + K ℙ(D > 0)` directly. Along a process that follows the
rule from a stopping time on, with a start position at most `M`, the potential
`V(X_t) + C` (after the start) and `2C` (before) telescopes, using that the period-`t` demand is
independent of the history, which gives `𝔼 ∑_{t<T} cost_t ≤ T g* + 2C`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR

/-- Splitting off the first demand: `ρ^{⊗(T+1)} ≅ ρ ⊗ ρ^{⊗T}`. -/
private lemma lintegral_pi_succ (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (T : ℕ)
    {F : ℝ≥0 × (Fin T → ℝ≥0) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F (z 0, Fin.tail z) ∂(Measure.pi fun _ : Fin (T + 1) => ρ)
      = ∫⁻ y, ∫⁻ z', F (y, z') ∂(Measure.pi fun _ : Fin T => ρ) ∂ρ := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (T + 1) => ρ) 0
  have key : ∫⁻ z, F (z 0, Fin.tail z) ∂(Measure.pi fun _ : Fin (T + 1) => ρ)
      = ∫⁻ z, F (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T + 1) => ℝ≥0) 0 z)
          ∂(Measure.pi fun _ : Fin (T + 1) => ρ) := by
    refine lintegral_congr fun z => ?_
    simp [MeasurableEquiv.piFinSuccAbove_apply]
  rw [key, hmp.lintegral_comp hF, lintegral_prod _ hF.aemeasurable]

/-! ### The renewal equation for `U` -/

private lemma measurable_psum (k : ℕ) : Measurable (fun z : Fin k → ℝ≥0 => ∑ j, (z j : ℝ)) :=
  Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real

private lemma lintegral_law_zero (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] {F : ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ x, F x ∂((Measure.pi fun _ : Fin 0 => ρ).map fun z => ∑ j, (z j : ℝ)) = F 0 := by
  rw [lintegral_map hF (measurable_psum 0)]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, lintegral_const, measure_univ, mul_one]

private lemma lintegral_law_succ (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (n : ℕ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂((Measure.pi fun _ : Fin (n + 1) => ρ).map fun z => ∑ j, (z j : ℝ))
      = ∫⁻ y, ∫⁻ x, F ((y : ℝ) + x)
          ∂((Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ)) ∂ρ := by
  rw [lintegral_map hF (measurable_psum _)]
  have hG : Measurable fun q : ℝ≥0 × (Fin n → ℝ≥0) => F ((q.1 : ℝ) + ∑ j, (q.2 j : ℝ)) :=
    hF.comp (measurable_fst.coe_nnreal_real.add (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp measurable_snd).coe_nnreal_real))
  have key : ∫⁻ z, F (∑ j, (z j : ℝ)) ∂(Measure.pi fun _ : Fin (n + 1) => ρ)
      = ∫⁻ z, F (((z 0 : ℝ≥0) : ℝ) + ∑ j, ((Fin.tail z j : ℝ≥0) : ℝ))
          ∂(Measure.pi fun _ : Fin (n + 1) => ρ) := by
    refine lintegral_congr fun z => ?_
    simp [Fin.sum_univ_succ, Fin.tail]
  rw [key, lintegral_pi_succ ρ n hG]
  refine lintegral_congr fun y => ?_
  rw [lintegral_map (f := fun x => F ((y : ℝ) + x)) (hF.comp (measurable_const_add _))
    (measurable_psum n)]

/-- `U = δ₀ + ρ * U`. -/
private lemma renewal_decomp (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] {F : ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ u, F u ∂(renewalMeasure ρ)
      = F 0 + ∫⁻ y, ∫⁻ u, F ((y : ℝ) + u) ∂(renewalMeasure ρ) ∂ρ := by
  have hU : ∀ g : ℝ → ℝ≥0∞, ∫⁻ x, g x ∂(renewalMeasure ρ)
      = ∑' n : ℕ, ∫⁻ x, g x ∂((Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ)) :=
    fun g => lintegral_sum_measure g _
  have hmeas : ∀ n : ℕ, Measurable fun y : ℝ≥0 => ∫⁻ x, F ((y : ℝ) + x)
      ∂((Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ)) := fun n =>
    Measurable.lintegral_prod_right' (f := fun q : ℝ≥0 × ℝ => F ((q.1 : ℝ) + q.2))
      (hF.comp (measurable_fst.coe_nnreal_real.add measurable_snd))
  rw [hU F, tsum_eq_zero_add' ENNReal.summable, lintegral_law_zero ρ hF]
  congr 1
  simp_rw [lintegral_law_succ ρ _ hF]
  rw [← lintegral_tsum fun n => (hmeas n).aemeasurable]
  refine lintegral_congr fun y => ?_
  rw [hU (fun x => F ((y : ℝ) + x))]

private lemma renewal_Iio_zero (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] :
    renewalMeasure ρ (Set.Iio 0) = 0 := by
  unfold renewalMeasure
  rw [Measure.sum_apply _ measurableSet_Iio]
  refine ENNReal.tsum_eq_zero.2 fun n => ?_
  rw [Measure.map_apply (measurable_psum n) measurableSet_Iio]
  have : (fun z : Fin n → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Iio 0 = ∅ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
    exact Finset.sum_nonneg fun j _ => (z j).2
  rw [this, measure_empty]

private lemma one_le_renewal (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) (hw : 0 < w) :
    1 ≤ renewalMeasure ρ (Set.Ico 0 w) := by
  unfold renewalMeasure
  refine le_trans ?_ (Measure.le_iff'.1 (Measure.le_sum _ 0) _)
  rw [Measure.map_apply (measurable_psum 0) measurableSet_Ico]
  have : (fun z : Fin 0 → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w = Set.univ := by
    ext z
    simp [hw]
  rw [this, measure_univ]

/-- Renewal equation for `x ↦ ∫_{[0, w-x)} G(x+u) U(du)`, for `0 ≤ x < w`. -/
private lemma renewal_window (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) {G : ℝ → ℝ≥0∞}
    (hG : Measurable G) (x : ℝ) (hx0 : 0 ≤ x) (hxw : x < w) :
    ∫⁻ u in Set.Ico 0 (w - x), G (x + u) ∂(renewalMeasure ρ)
      = G x + ∫⁻ y, ∫⁻ u in Set.Ico 0 (w - (x + y)), G ((x + y) + u) ∂(renewalMeasure ρ) ∂ρ := by
  have hae : ∀ᵐ u ∂(renewalMeasure ρ), 0 ≤ u := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (renewal_Iio_zero ρ)] with u hu
    simpa using hu
  rw [← lintegral_indicator measurableSet_Ico,
    renewal_decomp ρ (F := (Set.Ico 0 (w - x)).indicator fun u => G (x + u))
      ((hG.comp (measurable_const_add x)).indicator measurableSet_Ico),
    Set.indicator_of_mem (Set.mem_Ico.2 ⟨le_rfl, by linarith⟩), add_zero]
  congr 1
  refine lintegral_congr fun y => ?_
  rw [← lintegral_indicator measurableSet_Ico]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with u hu
  have hy := NNReal.coe_nonneg y
  by_cases h : u < w - (x + y)
  · rw [Set.indicator_of_mem (Set.mem_Ico.2 ⟨by linarith, by linarith⟩),
      Set.indicator_of_mem (Set.mem_Ico.2 ⟨hu, h⟩), add_assoc]
  · rw [Set.indicator_of_notMem (fun h' => h (by linarith [(Set.mem_Ico.1 h').2])),
      Set.indicator_of_notMem (fun h' => h (Set.mem_Ico.1 h').2)]


section coord

variable {α : Type} [MeasurableSpace α] [Zero α]

private lemma measurable_padHist' (N : ℕ) : Measurable (padHist N : (Fin N → α) → ℕ → α) := by
  refine measurable_pi_lambda _ fun t => ?_
  by_cases h : t < N
  · simp only [padHist, dif_pos h]
    exact measurable_pi_apply _
  · simp only [padHist, dif_neg h]
    exact measurable_const

omit [MeasurableSpace α] in
private lemma padHist_insertNth_lt {M : ℕ} (i : Fin (M + 1)) (a b : α) (z : Fin M → α) (s : ℕ)
    (hs : s < i.val) :
    padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z) s
      = padHist (M + 1) (Fin.insertNth (α := fun _ => α) i b z) s := by
  have hsM : s < M + 1 := lt_trans hs i.2
  have hsM' : s < M := lt_of_lt_of_le hs (Nat.lt_succ_iff.1 i.2)
  simp only [padHist, dif_pos hsM]
  have he : (⟨s, hsM⟩ : Fin (M + 1)) = i.succAbove ⟨s, hsM'⟩ := by
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · simp [Fin.lt_def, hs]
  rw [he, Fin.insertNth_apply_succAbove (α := fun _ => α),
    Fin.insertNth_apply_succAbove (α := fun _ => α)]

omit [MeasurableSpace α] in
private lemma padHist_insertNth_self {M : ℕ} (i : Fin (M + 1)) (a : α) (z : Fin M → α) :
    padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z) i.val = a := by
  simp only [padHist, dif_pos i.2]
  exact Fin.insertNth_apply_same (α := fun _ => α) i a z

/-- The `t`-th demand is independent of anything depending on the demands before `t`. -/
private lemma lintegral_coord (μ : Measure α) [IsProbabilityMeasure μ]
    (N t : ℕ) (ht : t < N) (Φ : (ℕ → α) → α → ℝ≥0∞)
    (hΦ : Measurable fun p : (ℕ → α) × α => Φ p.1 p.2)
    (hdep : ∀ (d d' : ℕ → α) (a : α), (∀ s < t, d s = d' s) → Φ d a = Φ d' a) :
    ∫⁻ z, Φ (padHist N z) (padHist N z t) ∂(Measure.pi fun _ : Fin N => μ)
      = ∫⁻ z, ∫⁻ a, Φ (padHist N z) a ∂μ ∂(Measure.pi fun _ : Fin N => μ) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hD : Measurable fun z : Fin (M + 1) → α => padHist (M + 1) z := measurable_padHist' _
  set i : Fin (M + 1) := ⟨t, ht⟩ with hi
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => μ) i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => α) i with he
  have hsymm : ∀ p : α × (Fin M → α), e.symm p = Fin.insertNth (α := fun _ => α) i p.1 p.2 :=
    fun p => rfl
  have key : ∀ F : (Fin (M + 1) → α) → ℝ≥0∞,
      ∫⁻ z, F z ∂(Measure.pi fun _ : Fin (M + 1) => μ)
        = ∫⁻ p, F (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin M => μ)) := by
    intro F
    rw [← hmp.lintegral_comp_emb e.measurableEmbedding]
    simp only [MeasurableEquiv.symm_apply_apply]
  have hind : ∀ (a b : α) (z : Fin M → α) (c : α),
      Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z)) c
        = Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i b z)) c := by
    intro a b z c
    exact hdep _ _ c fun s hs => padHist_insertNth_lt i a b z s (by simpa [hi] using hs)
  have hins : Measurable fun p : α × (Fin M → α) => Fin.insertNth (α := fun _ => α) i p.1 p.2 :=
    e.symm.measurable
  have hG : Measurable fun p : α × (Fin M → α) =>
      Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i p.1 p.2)) p.1 :=
    hΦ.comp ((hD.comp hins).prodMk measurable_fst)
  rw [key, key]
  simp only [hsymm]
  have hl : ∀ p : α × (Fin M → α),
      padHist (M + 1) (Fin.insertNth (α := fun _ => α) i p.1 p.2) t = p.1 :=
    fun p => padHist_insertNth_self i p.1 p.2
  simp only [hl]
  rw [lintegral_prod_symm _ hG.aemeasurable]
  have hc : ∀ (a : α) (z : Fin M → α),
      ∫⁻ c, Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z)) c ∂μ
        = ∫⁻ c, Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i c z)) c ∂μ := fun a z =>
    lintegral_congr fun c => hind a c z c
  simp only [hc]
  have hH : Measurable fun z : Fin M → α =>
      ∫⁻ c, Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i c z)) c ∂μ :=
    Measurable.lintegral_prod_right' (f := fun p : (Fin M → α) × α =>
      Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i p.2 p.1)) p.2)
      (hΦ.comp ((hD.comp (hins.comp (measurable_snd.prodMk measurable_fst))).prodMk measurable_snd))
  have hprod := lintegral_prod (μ := μ) (ν := Measure.pi fun _ : Fin M => μ)
    (fun p : α × (Fin M → α) =>
      ∫⁻ c, Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i c p.2)) c ∂μ)
    (hH.comp measurable_snd).aemeasurable
  rw [hprod]
  simp only [lintegral_const, measure_univ, mul_one]

end coord

/-! ### The base-stock case `s = S` -/

private lemma ssPre_SS_le (S : ℝ) (d : ℕ → ℝ≥0) : ∀ t, ssPre S S d t ≤ S
  | 0 => le_rfl
  | t + 1 => by
    show (if ssPre S S d t ≤ S then S else ssPre S S d t) - (d t : ℝ) ≤ S
    rw [if_pos (ssPre_SS_le S d t)]
    linarith [NNReal.coe_nonneg (d t)]

private lemma ssPeriodCost_SS (f : ℝ → ℝ) (K S : ℝ) (d : ℕ → ℝ≥0) (t : ℕ) :
    ssPeriodCost f K S S d t
      = (if t = 0 then 0 else K * (if 0 < d (t - 1) then 1 else 0)) + f S := by
  unfold ssPeriodCost ssPost
  rw [if_pos (ssPre_SS_le S d t)]
  cases t with
  | zero => simp [ssPre]
  | succ t =>
    have h : ssPre S S d (t + 1) = S - (d t : ℝ) := by
      show (if ssPre S S d t ≤ S then S else ssPre S S d t) - (d t : ℝ) = _
      rw [if_pos (ssPre_SS_le S d t)]
    rw [h, if_neg (Nat.succ_ne_zero t), add_tsub_cancel_right]
    congr 2
    by_cases hd : 0 < d t
    · have : (0 : ℝ) < (d t : ℝ) := by exact_mod_cast hd
      rw [if_pos ⟨by linarith, by linarith⟩, if_pos hd]
    · have : (d t : ℝ) = 0 := by
        have := le_antisymm (not_lt.1 hd) zero_le
        exact_mod_cast this
      rw [if_neg (by rw [this]; simp), if_neg hd]

/-- The long-run average cost of the base-stock policy `(S,S)`. -/
private lemma ss_avg_SS (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ) (hf0 : ∀ y, 0 ≤ f y)
    (K S : ℝ) (hK : 0 ≤ K) :
    ssAvgCost ρ f K S S = ENNReal.ofReal (f S + K * (ρ (Set.Ioi 0)).toReal) := by
  set r := (ρ (Set.Ioi 0)).toReal with hr
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hint : ∫ a, (K * (if 0 < a then 1 else 0) + f S) ∂ρ = K * r + f S := by
    have h1 : (fun a : ℝ≥0 => K * (if 0 < a then (1 : ℝ) else 0) + f S)
        = fun a => K * (Set.Ioi (0 : ℝ≥0)).indicator 1 a + f S := by
      funext a
      by_cases ha : 0 < a
      · simp [Set.indicator_of_mem (show a ∈ Set.Ioi 0 from ha), ha]
      · simp [Set.indicator_of_notMem (show a ∉ Set.Ioi 0 from ha), ha]
    have hi1 : Integrable ((Set.Ioi (0 : ℝ≥0)).indicator (1 : ℝ≥0 → ℝ)) ρ :=
      (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
    rw [h1, integral_add (f := fun a => K * (Set.Ioi (0 : ℝ≥0)).indicator (1 : ℝ≥0 → ℝ) a)
      (hi1.const_mul K) (integrable_const _), integral_const_mul,
      integral_indicator_one measurableSet_Ioi, integral_const, probReal_univ, one_smul,
      measureReal_def]
  have hE : ∀ T t, t < T →
      ∫⁻ z, ENNReal.ofReal (ssPeriodCost f K S S (padHist T z) t) ∂(Measure.pi fun _ : Fin T => ρ)
        = ENNReal.ofReal ((if t = 0 then 0 else K * r) + f S) := by
    intro T t ht
    simp_rw [ssPeriodCost_SS]
    rcases t with _ | t
    · simp
    · have hcoord : ∀ z : Fin T → ℝ≥0, padHist T z t = z ⟨t, by omega⟩ := fun z => by
        simp [padHist, show t < T by omega]
      simp only [Nat.succ_ne_zero, if_false, add_tsub_cancel_right, hcoord]
      have hmp := measurePreserving_eval (fun _ : Fin T => ρ) (⟨t, by omega⟩ : Fin T)
      have hm : Measurable fun a : ℝ≥0 => ENNReal.ofReal (K * (if 0 < a then 1 else 0) + f S) :=
        ENNReal.measurable_ofReal.comp ((measurable_const.mul (Measurable.ite measurableSet_Ioi
          measurable_const measurable_const)).add measurable_const)
      rw [hmp.lintegral_comp hm, ← ofReal_integral_eq_lintegral_ofReal, hint]
      · refine Integrable.of_bound (C := K + f S) ((measurable_const.mul (Measurable.ite
          (measurableSet_lt measurable_const measurable_id) measurable_const
          measurable_const)).add measurable_const).aestronglyMeasurable (ae_of_all _ fun a => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by have := hf0 S; split_ifs <;> nlinarith)]
        split_ifs <;> linarith
      · exact ae_of_all _ fun a => by
          simp only [Pi.zero_apply]; have := hf0 S; split_ifs <;> nlinarith
  have havg : ∀ T : ℕ, ((T + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∫⁻ z, ∑ t ∈ Finset.range (T + 1),
      ENNReal.ofReal (ssPeriodCost f K S S (padHist (T + 1) z) t) ∂(Measure.pi fun _ : Fin (T + 1) => ρ)
        = ENNReal.ofReal (f S + K * r * ((T : ℝ) / ((T : ℝ) + 1))) := by
    intro T
    rw [lintegral_finsetSum]
    · rw [Finset.sum_congr rfl fun t ht => hE (T + 1) t (Finset.mem_range.1 ht),
        ← ENNReal.ofReal_sum_of_nonneg (fun t _ => by have := hf0 S; split_ifs <;> nlinarith)]
      have hsum : ∑ t ∈ Finset.range (T + 1), ((if t = 0 then 0 else K * r) + f S)
          = (T : ℝ) * (K * r) + ((T : ℝ) + 1) * f S := by
        rw [Finset.sum_range_succ']
        simp only [Nat.succ_ne_zero, if_false, if_true, zero_add, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      rw [hsum]
      have hT : (0 : ℝ) < (T : ℝ) + 1 := by positivity
      rw [show ((T + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((T : ℝ) + 1) by
          rw [← ENNReal.ofReal_natCast]; push_cast; rfl,
        ← ENNReal.ofReal_inv_of_pos hT, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring
    · intro t _
      exact ENNReal.measurable_ofReal.comp (by
        have hp := measurable_padHist' (α := ℝ≥0) (T + 1)
        simp_rw [ssPeriodCost_SS]
        refine Measurable.add ?_ measurable_const
        split_ifs
        · exact measurable_const
        · exact measurable_const.mul (Measurable.ite
            (measurableSet_lt measurable_const ((measurable_pi_apply (t - 1)).comp hp))
            measurable_const measurable_const))
  have hlim : Tendsto (fun T : ℕ => ENNReal.ofReal (f S + K * r * ((T : ℝ) / ((T : ℝ) + 1))))
      atTop (𝓝 (ENNReal.ofReal (f S + K * r))) := by
    refine ENNReal.tendsto_ofReal ?_
    have := (tendsto_natCast_div_add_atTop (1 : ℝ)).const_mul (K * r)
    simpa using this.const_add (f S)
  unfold ssAvgCost
  refine Tendsto.limsup_eq ?_
  rw [← tendsto_add_atTop_iff_nat 1]
  refine hlim.congr fun T => ?_
  rw [havg T]

/-! ### The relative value function -/

private lemma poisson_fn (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ y, 0 ≤ f y) (K s S M' : ℝ) (hK : 0 ≤ K)
    (hsS : s ≤ S) (hSM : S ≤ M') :
    ∃ (gv : ℝ) (V : ℝ → ℝ) (CV : ℝ), ssAvgCost ρ f K s S = ENNReal.ofReal gv ∧ 0 ≤ gv ∧
      Measurable V ∧ 0 ≤ CV ∧
      (∀ y ≤ M', |V y| ≤ CV) ∧ (∀ y, Integrable (fun d : ℝ≥0 => V (y - d)) ρ) ∧
      ∀ x, K * (if x ≤ s ∧ x < S then 1 else 0) + f (if x ≤ s then S else x)
        + ∫ d, V ((if x ≤ s then S else x) - d) ∂ρ ≤ gv + V x := by
  have hSF : SFinite (renewalMeasure ρ) := by unfold renewalMeasure; infer_instance
  have hfm : Measurable f := hf.measurable
  have hUfin : ∀ w, renewalMeasure ρ (Set.Ico 0 w) ≠ ∞ := fun w =>
    (renewalMeasure_Ico_lt_top ρ hρ w).ne
  set Λ : ℝ → ℝ≥0∞ := fun y => ∫⁻ z in Set.Ico 0 (y - s), ENNReal.ofReal (f (y - z))
    ∂(renewalMeasure ρ) with hΛ
  set Nw : ℝ → ℝ≥0∞ := fun y => renewalMeasure ρ (Set.Ico 0 (y - s)) with hNw
  have hΛm : Measurable Λ := by
    have : Λ = fun y => ∫⁻ z, ({p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 < p.1 - s}.indicator
        (fun p => ENNReal.ofReal (f (p.1 - p.2)))) (y, z) ∂(renewalMeasure ρ) := by
      funext y
      rw [hΛ]
      simp only
      rw [← lintegral_indicator measurableSet_Ico]
      rfl
    rw [this]
    refine Measurable.lintegral_prod_right' (Measurable.indicator ?_ ?_)
    · exact ENNReal.measurable_ofReal.comp (hfm.comp (measurable_fst.sub measurable_snd))
    · exact (measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd (measurable_fst.sub measurable_const))
  have hNm : Measurable Nw := by
    have : Nw = fun y => ∫⁻ z, ({p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 < p.1 - s}.indicator 1) (y, z)
        ∂(renewalMeasure ρ) := by
      funext y
      rw [hNw]
      simp only
      rw [← lintegral_indicator_one measurableSet_Ico]
      rfl
    rw [this]
    refine Measurable.lintegral_prod_right' (Measurable.indicator measurable_const ?_)
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.sub measurable_const))
  have hCbd : ∀ y, ∃ C, 0 ≤ C ∧ ∀ x ∈ Set.Icc s y, f x ≤ C := fun y => by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := s) (b := y)).exists_bound_of_continuousOn
      hf.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
    have h1 : |f x| ≤ C := by simpa [Real.norm_eq_abs] using hC x hx
    exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
  have hNle : ∀ y y', y' ≤ y → Nw y' ≤ Nw y := fun y y' h =>
    measure_mono (Set.Ico_subset_Ico_right (by linarith))
  have hΛle : ∀ y y' C, y' ≤ y → (∀ x ∈ Set.Icc s y, f x ≤ C) → 0 ≤ C →
      Λ y' ≤ ENNReal.ofReal C * Nw y := by
    intro y y' C hy hC hC0
    calc Λ y' ≤ ∫⁻ _z in Set.Ico 0 (y' - s), ENNReal.ofReal C ∂(renewalMeasure ρ) := by
          refine setLIntegral_mono' measurableSet_Ico fun z hz => ENNReal.ofReal_le_ofReal ?_
          exact hC _ ⟨by linarith [hz.2], by linarith [hz.1]⟩
      _ = ENNReal.ofReal C * Nw y' := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal C * Nw y := by gcongr; exact hNle y y' hy
  have hNfin : ∀ y, Nw y ≠ ∞ := fun y => hUfin _
  have hΛfin : ∀ y, Λ y ≠ ∞ := fun y => by
    obtain ⟨C, hC0, hC⟩ := hCbd y
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hNfin y))
      (hΛle y y C le_rfl hC hC0)
  have hΛ0 : ∀ y, y ≤ s → Λ y = 0 := fun y hy => by
    have he : Set.Ico (0 : ℝ) (y - s) = ∅ := Set.Ico_eq_empty (by linarith)
    simp only [hΛ, he, Measure.restrict_empty, lintegral_zero_measure]
  have hN0 : ∀ y, y ≤ s → Nw y = 0 := fun y hy => by
    have he : Set.Ico (0 : ℝ) (y - s) = ∅ := Set.Ico_eq_empty (by linarith)
    simp only [hNw, he, measure_empty]
  -- renewal equations
  have hΛeq : ∀ y, s < y → Λ y = ENNReal.ofReal (f y) + ∫⁻ d, Λ (y - d) ∂ρ := by
    intro y hy
    have hG : Measurable fun z : ℝ => ENNReal.ofReal (f (y - z)) :=
      ENNReal.measurable_ofReal.comp (hfm.comp (measurable_const.sub measurable_id))
    have h := renewal_window ρ (y - s) hG 0 le_rfl (by linarith)
    simp only [sub_zero, zero_add] at h
    simp only [hΛ]
    rw [h]
    congr 1
    refine lintegral_congr fun d => ?_
    rw [show y - (d : ℝ) - s = y - s - d by ring]
    refine lintegral_congr fun u => ?_
    rw [show y - ((d : ℝ) + u) = y - d - u by ring]
  have hNeq : ∀ y, s < y → Nw y = 1 + ∫⁻ d, Nw (y - d) ∂ρ := by
    intro y hy
    have h := renewal_window ρ (y - s) (G := fun _ => (1 : ℝ≥0∞)) measurable_const 0 le_rfl
      (by linarith)
    simp only [sub_zero, zero_add, setLIntegral_one] at h
    simp only [hNw]
    rw [h]
    congr 1
    refine lintegral_congr fun d => ?_
    rw [show y - (d : ℝ) - s = y - s - d by ring]
  have hiΛ : ∀ y, Integrable (fun d : ℝ≥0 => (Λ (y - d)).toReal) ρ := by
    intro y
    obtain ⟨C, hC0, hC⟩ := hCbd y
    refine Integrable.of_bound (hΛm.comp (measurable_const.sub
      measurable_coe_nnreal_real)).ennreal_toReal.aestronglyMeasurable (C * (Nw y).toReal)
      (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hNfin y))
      (hΛle y (y - d) C (by linarith [NNReal.coe_nonneg d]) hC hC0)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0] at this
  have hiN : ∀ y, Integrable (fun d : ℝ≥0 => (Nw (y - d)).toReal) ρ := by
    intro y
    refine Integrable.of_bound (hNm.comp (measurable_const.sub
      measurable_coe_nnreal_real)).ennreal_toReal.aestronglyMeasurable (Nw y).toReal
      (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono (hNfin y) (hNle y (y - d) (by linarith [NNReal.coe_nonneg d]))
  have hInt : ∀ y, (∫ x in Set.Ico 0 (y - s), f (y - x) ∂(renewalMeasure ρ)) = (Λ y).toReal := by
    intro y
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => f (y - x)) (ae_of_all _ fun x => hf0 _)
      (hfm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable]
  -- the average cost
  set gv : ℝ := if s < S then (K + (Λ S).toReal) / (Nw S).toReal
    else f S + K * (ρ (Set.Ioi 0)).toReal with hgvdef
  have hgv : ssAvgCost ρ f K s S = ENNReal.ofReal gv := by
    by_cases h : s < S
    · rw [hgvdef, if_pos h, ss_renewal_reward ρ hρ f hfm hf0 K s S hK h, hInt S]
      obtain ⟨C, hC0, hC⟩ := hCbd S
      exact ⟨C, hC⟩
    · have hs : s = S := le_antisymm hsS (not_lt.1 h)
      rw [hgvdef, if_neg h, hs]
      exact ss_avg_SS ρ f hf0 K S hK
  have hgv0 : 0 ≤ gv := by
    rw [hgvdef]
    split_ifs
    · exact div_nonneg (add_nonneg hK ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
    · exact add_nonneg (hf0 S) (mul_nonneg hK ENNReal.toReal_nonneg)
  -- the relative value
  set W : ℝ → ℝ := fun y => (Λ y).toReal - gv * (Nw y).toReal with hWdef
  have hWm : Measurable W := hΛm.ennreal_toReal.sub (measurable_const.mul hNm.ennreal_toReal)
  have hW0 : ∀ y, y ≤ s → W y = 0 := fun y hy => by
    simp only [hWdef, hΛ0 y hy, hN0 y hy, ENNReal.toReal_zero, mul_zero, sub_zero]
  have hiW : ∀ y, Integrable (fun d : ℝ≥0 => W (y - d)) ρ := fun y =>
    (hiΛ y).sub ((hiN y).const_mul gv)
  have hWeq : ∀ y, s < y → W y = f y - gv + ∫ d, W (y - d) ∂ρ := by
    intro y hy
    have hΛm' : Measurable fun d : ℝ≥0 => Λ (y - d) :=
      hΛm.comp (measurable_const.sub measurable_coe_nnreal_real)
    have hNm' : Measurable fun d : ℝ≥0 => Nw (y - d) :=
      hNm.comp (measurable_const.sub measurable_coe_nnreal_real)
    have hΛint : (∫⁻ d, Λ (y - d) ∂ρ).toReal = ∫ d, (Λ (y - d)).toReal ∂ρ :=
      (integral_toReal hΛm'.aemeasurable (ae_of_all _ fun d => (hΛfin _).lt_top)).symm
    have hNint : (∫⁻ d, Nw (y - d) ∂ρ).toReal = ∫ d, (Nw (y - d)).toReal ∂ρ :=
      (integral_toReal hNm'.aemeasurable (ae_of_all _ fun d => (hNfin _).lt_top)).symm
    have hΛfin' : ∫⁻ d, Λ (y - d) ∂ρ ≠ ∞ := fun htop =>
      hΛfin y (by rw [hΛeq y hy, htop, add_top])
    have hNfin' : ∫⁻ d, Nw (y - d) ∂ρ ≠ ∞ := fun htop =>
      hNfin y (by rw [hNeq y hy, htop, add_top])
    have e1 : (Λ y).toReal = f y + ∫ d, (Λ (y - d)).toReal ∂ρ := by
      rw [hΛeq y hy, ENNReal.toReal_add ENNReal.ofReal_ne_top hΛfin',
        ENNReal.toReal_ofReal (hf0 _), hΛint]
    have e2 : (Nw y).toReal = 1 + ∫ d, (Nw (y - d)).toReal ∂ρ := by
      rw [hNeq y hy, ENNReal.toReal_add ENNReal.one_ne_top hNfin', ENNReal.toReal_one, hNint]
    have e3 : ∫ d, W (y - d) ∂ρ
        = ∫ d, (Λ (y - d)).toReal ∂ρ - gv * ∫ d, (Nw (y - d)).toReal ∂ρ := by
      simp only [hWdef]
      rw [integral_sub (hiΛ y) ((hiN y).const_mul gv), integral_const_mul]
    rw [e3]
    simp only [hWdef]
    rw [e1, e2]
    ring
  -- bounds
  obtain ⟨Cf, hCf0, hCf⟩ := hCbd M'
  set CW : ℝ := (Cf + gv) * (Nw M').toReal with hCW
  have hWb : ∀ y ≤ M', |W y| ≤ CW := by
    intro y hy
    rcases le_or_gt y s with h | h
    · rw [hW0 y h, abs_zero]
      exact mul_nonneg (add_nonneg hCf0 hgv0) ENNReal.toReal_nonneg
    · have h1 : (Λ y).toReal ≤ Cf * (Nw M').toReal := by
        have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hNfin M'))
          (hΛle M' y Cf hy hCf hCf0)
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCf0] at this
      have h2 : (Nw y).toReal ≤ (Nw M').toReal := ENNReal.toReal_mono (hNfin M') (hNle M' y hy)
      have h3 : 0 ≤ (Λ y).toReal := ENNReal.toReal_nonneg
      have h4 : 0 ≤ (Nw y).toReal := ENNReal.toReal_nonneg
      simp only [hWdef, hCW]
      rw [abs_le]
      constructor <;> nlinarith
  -- the potential, with the base-stock correction
  set V : ℝ → ℝ := fun y => W y + (if s < S ∨ y = S then 0 else K) with hVdef
  have hVm : Measurable V := hWm.add (Measurable.ite
    ((MeasurableSet.const _).union (measurableSet_eq_fun measurable_id measurable_const))
    measurable_const measurable_const)
  have hiite : ∀ y, Integrable (fun d : ℝ≥0 => if s < S ∨ y - (d : ℝ) = S then (0 : ℝ) else K) ρ := by
    intro y
    refine Integrable.of_bound (C := K) (Measurable.ite ((MeasurableSet.const _).union
      (measurableSet_eq_fun (measurable_const.sub measurable_coe_nnreal_real) measurable_const))
      measurable_const measurable_const).aestronglyMeasurable (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs]
    split_ifs <;> simp [abs_of_nonneg hK, hK]
  have hiV : ∀ y, Integrable (fun d : ℝ≥0 => V (y - d)) ρ := fun y => (hiW y).add (hiite y)
  have hiteI : ∀ y, ∫ d, (if s < S ∨ y - (d : ℝ) = S then (0 : ℝ) else K) ∂ρ ≤ K := by
    intro y
    have := integral_mono (hiite y) (integrable_const K) (fun d => by
      simp only; split_ifs <;> linarith)
    simpa [integral_const, probReal_univ] using this
  have hVint : ∀ y, ∫ d, V (y - d) ∂ρ
      = ∫ d, W (y - d) ∂ρ + ∫ d, (if s < S ∨ y - (d : ℝ) = S then (0 : ℝ) else K) ∂ρ := fun y => by
    simp only [hVdef]
    exact integral_add (hiW y) (hiite y)
  refine ⟨gv, V, CW + K, hgv, hgv0, hVm, by positivity, fun y hy => ?_, hiV, fun x => ?_⟩
  · simp only [hVdef]
    refine (abs_add_le _ _).trans (add_le_add (hWb y hy) ?_)
    split_ifs <;> simp [abs_of_nonneg hK, hK]
  · rw [hVint]
    by_cases hlt : s < S
    · -- the case `s < S`: equality
      have hite0 : ∀ y, (if s < S ∨ y = S then (0 : ℝ) else K) = 0 := fun y => if_pos (Or.inl hlt)
      have hite0' : ∫ d, (if s < S ∨ (if x ≤ s then S else x) - (d : ℝ) = S then (0 : ℝ) else K) ∂ρ = 0 := by
        simp [hlt]
      rw [hite0']
      simp only [hVdef, hite0, add_zero]
      have hNS : 1 ≤ (Nw S).toReal := by
        have := ENNReal.toReal_mono (hNfin S) (one_le_renewal ρ (S - s) (by linarith))
        simpa using this
      have hWS : W S = -K := by
        simp only [hWdef]
        have hg : gv * (Nw S).toReal = K + (Λ S).toReal := by
          rw [hgvdef, if_pos hlt]
          field_simp
        linarith
      rcases le_or_gt x s with hx | hx
      · rw [if_pos hx, if_pos ⟨hx, by linarith⟩, hW0 x hx]
        have := hWeq S hlt
        linarith
      · rw [if_neg (not_le.2 hx), if_neg (fun h => by linarith [h.1])]
        have := hWeq x hx
        linarith
    · -- the base-stock case `s = S`
      have hs : s = S := le_antisymm hsS (not_lt.1 hlt)
      rcases le_or_gt x s with hx | hx
      · rw [if_pos hx]
        have hW' : ∀ d : ℝ≥0, W (S - d) = 0 := fun d => hW0 _ (by rw [hs]; linarith [NNReal.coe_nonneg d])
        simp only [hW', integral_zero, zero_add]
        have hI : ∫ d, (if s < S ∨ S - (d : ℝ) = S then (0 : ℝ) else K) ∂ρ
            = K * (ρ (Set.Ioi 0)).toReal := by
          have h1 : (fun d : ℝ≥0 => if s < S ∨ S - (d : ℝ) = S then (0 : ℝ) else K)
              = fun d => K * (Set.Ioi (0 : ℝ≥0)).indicator (1 : ℝ≥0 → ℝ) d := by
            funext d
            by_cases hd : 0 < d
            · have : S - (d : ℝ) ≠ S := by
                have : (0 : ℝ) < d := by exact_mod_cast hd
                intro h; linarith
              simp [hlt, this, Set.indicator_of_mem (show d ∈ Set.Ioi 0 from hd)]
            · have hd0 : d = 0 := le_antisymm (not_lt.1 hd) zero_le
              simp [hd0]
          rw [h1, integral_const_mul, integral_indicator_one measurableSet_Ioi, measureReal_def]
        rw [hI]
        simp only [hVdef, hW0 x hx, zero_add, hgvdef, if_neg hlt]
        rcases lt_or_eq_of_le (show x ≤ S by linarith) with hxS | hxS
        · rw [if_pos ⟨hx, hxS⟩, if_neg (by rintro (h | h) <;> [exact hlt h; linarith])]
          linarith
        · rw [if_neg (fun h => by linarith [h.2]), if_pos (Or.inr hxS)]
          linarith
      · rw [if_neg (not_le.2 hx), if_neg (fun h => by linarith [h.1])]
        have h1 := hWeq x hx
        have h2 := hiteI x
        simp only [hVdef, if_neg (show ¬ (s < S ∨ x = S) by
          rintro (h | h) <;> [exact hlt h; linarith])]
        linarith

theorem solution {α : Type} [MeasurableSpace α] [Zero α]
    (μ : Measure α) [IsProbabilityMeasure μ] (g : α → ℝ≥0) (hg : Measurable g)
    (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρg : μ.map g = ρ)
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ y, 0 ≤ f y)
    (K s S M : ℝ) (hK : 0 ≤ K) (hsS : s ≤ S)
    (act : ℕ → (ℕ → α) → Prop) [∀ t, DecidablePred (act t)] (X : ℕ → (ℕ → α) → ℝ)
    (hactm : ∀ t, MeasurableSet {d | act t d}) (hXm : ∀ t, Measurable (X t))
    (hactd : ∀ (t : ℕ) (d d' : ℕ → α), (∀ r < t, d r = d' r) → (act t d ↔ act t d'))
    (hXd : ∀ (t : ℕ) (d d' : ℕ → α), (∀ r < t, d r = d' r) → X t d = X t d')
    (hmono : ∀ t d, act t d → act (t + 1) d)
    (hstep : ∀ t d, act t d → X (t + 1) d = (if X t d ≤ s then S else X t d) - (g (d t) : ℝ))
    (hstart0 : ∀ d, act 0 d → X 0 d ≤ M)
    (hstart : ∀ t d, ¬ act t d → act (t + 1) d → X (t + 1) d ≤ M) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ T N : ℕ, T ≤ N →
      ∫⁻ z, ∑ t ∈ Finset.range T, (if act t (padHist N z) then ENNReal.ofReal
          (K * (if X t (padHist N z) ≤ s ∧ X t (padHist N z) < S then 1 else 0)
            + f (if X t (padHist N z) ≤ s then S else X t (padHist N z))) else 0)
        ∂(Measure.pi fun _ : Fin N => μ)
      ≤ T * ssAvgCost ρ f K s S + C := by
  set M' := max S M with hM'
  obtain ⟨gv, V, CV, hgv, hgv0, hVm, hCV0, hVb, hVint, hPois⟩ :=
    poisson_fn ρ hρ f hf hf0 K s S M' hK hsS (le_max_left _ _)
  have hfm : Measurable f := hf.measurable
  -- once started, the process stays at or below `M'`
  have hXle : ∀ t d, act t d → X t d ≤ M' := by
    intro t
    induction t with
    | zero => intro d h; exact (hstart0 d h).trans (le_max_right _ _)
    | succ t ih =>
      intro d h
      by_cases h' : act t d
      · rw [hstep t d h']
        have h1 := ih d h'
        have h2 : (if X t d ≤ s then S else X t d) ≤ M' := by
          split_ifs
          · exact le_max_left _ _
          · exact h1
        linarith [NNReal.coe_nonneg (g (d t))]
      · exact (hstart t d h' h).trans (le_max_right _ _)
  -- the Poisson inequality against the law `μ` of the history coordinate
  have hPoisμ : ∀ x, K * (if x ≤ s ∧ x < S then 1 else 0) + f (if x ≤ s then S else x)
      + ∫ a, V ((if x ≤ s then S else x) - (g a : ℝ)) ∂μ ≤ gv + V x := by
    intro x
    have h := hPois x
    have e : ∫ d, V ((if x ≤ s then S else x) - d) ∂ρ
        = ∫ a, V ((if x ≤ s then S else x) - (g a : ℝ)) ∂μ := by
      rw [← hρg, integral_map (f := fun d : ℝ≥0 => V ((if x ≤ s then S else x) - d)) hg.aemeasurable
        (hVm.comp (measurable_const.sub measurable_coe_nnreal_real)).aestronglyMeasurable]
    rwa [e] at h
  have hVintμ : ∀ y, Integrable (fun a : α => V (y - (g a : ℝ))) μ := by
    intro y
    have h := hVint y
    rw [← hρg] at h
    exact (integrable_map_measure
      (hVm.comp (measurable_const.sub measurable_coe_nnreal_real)).aestronglyMeasurable
      hg.aemeasurable).1 h
  -- cost and potential
  set cost : ℝ → ℝ := fun x => K * (if x ≤ s ∧ x < S then 1 else 0) + f (if x ≤ s then S else x)
    with hcost
  have hcost0 : ∀ x, 0 ≤ cost x := fun x => by
    have := hf0 (if x ≤ s then S else x)
    have : 0 ≤ K * (if x ≤ s ∧ x < S then (1 : ℝ) else 0) := by
      split_ifs <;> simp [hK]
    simp only [hcost]; linarith
  have hcostm : Measurable cost :=
    (measurable_const.mul (Measurable.ite ((measurableSet_le measurable_id measurable_const).inter
      (measurableSet_lt measurable_id measurable_const)) measurable_const measurable_const)).add
      (hfm.comp (Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
        measurable_id))
  set c : ℕ → (ℕ → α) → ℝ≥0∞ := fun t d =>
    if act t d then ENNReal.ofReal (cost (X t d)) else 0 with hc
  set Φ : ℕ → (ℕ → α) → ℝ≥0∞ := fun t d =>
    if act t d then ENNReal.ofReal (V (X t d) + CV) else ENNReal.ofReal (2 * CV) with hΦ
  have hcm : ∀ t, Measurable (c t) := fun t =>
    Measurable.ite (hactm t) (ENNReal.measurable_ofReal.comp (hcostm.comp (hXm t))) measurable_const
  have hΦm : ∀ t, Measurable (Φ t) := fun t =>
    Measurable.ite (hactm t) (ENNReal.measurable_ofReal.comp ((hVm.comp (hXm t)).add measurable_const))
      measurable_const
  have hΦle : ∀ t d, act t d → X t d ≤ M → Φ t d ≤ ENNReal.ofReal (2 * CV) := by
    intro t d h hX
    simp only [hΦ, if_pos h]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (abs_le.1 (hVb (X t d) (hX.trans (le_max_right _ _)))).2
    linarith
  -- one period
  have hstep1 : ∀ N T, T < N →
      ∫⁻ z, c T (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)
        + ∫⁻ z, Φ (T + 1) (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ENNReal.ofReal gv + ∫⁻ z, Φ T (padHist N z) ∂(Measure.pi fun _ : Fin N => μ) := by
    intro N T hT
    have hD := measurable_padHist' (α := α) N
    set F : (ℕ → α) → α → ℝ≥0∞ := fun d a =>
      if act T d then ENNReal.ofReal (cost (X T d))
        + ENNReal.ofReal (V ((if X T d ≤ s then S else X T d) - (g a : ℝ)) + CV) else Φ T d
      with hF
    have hFm : Measurable fun p : (ℕ → α) × α => F p.1 p.2 := by
      refine Measurable.ite (measurable_fst (hactm T))
        ((ENNReal.measurable_ofReal.comp (hcostm.comp ((hXm T).comp measurable_fst))).add
          (ENNReal.measurable_ofReal.comp ((hVm.comp ((Measurable.ite
            (measurableSet_le ((hXm T).comp measurable_fst) measurable_const) measurable_const
            ((hXm T).comp measurable_fst)).sub (hg.comp measurable_snd).coe_nnreal_real)).add
            measurable_const))) ((hΦm T).comp measurable_fst)
    have hFd : ∀ (d d' : ℕ → α) (a : α), (∀ r < T, d r = d' r) → F d a = F d' a := by
      intro d d' a h
      simp only [hF, hΦ, hXd T d d' h]
      by_cases ha : act T d
      · have ha' : act T d' := (hactd T d d' h).1 ha
        simp only [ha, ha', if_true]
      · have ha' : ¬ act T d' := fun h' => ha ((hactd T d d' h).2 h')
        simp only [ha, ha', if_false]
    have hpt : ∀ d : ℕ → α, c T d + Φ (T + 1) d ≤ F d (d T) := by
      intro d
      by_cases ha : act T d
      · simp only [hc, hΦ, hF, if_pos ha, if_pos (hmono T d ha), hstep T d ha]
        exact le_rfl
      · simp only [hc, hF, if_neg ha, zero_add]
        by_cases ha' : act (T + 1) d
        · refine (hΦle (T + 1) d ha' (hstart T d ha ha')).trans ?_
          simp only [hΦ, if_neg ha]
          exact le_rfl
        · simp only [hΦ, if_neg ha, if_neg ha']
          exact le_rfl
    have hinner : ∀ d : ℕ → α, ∫⁻ a, F d a ∂μ ≤ ENNReal.ofReal gv + Φ T d := by
      intro d
      by_cases ha : act T d
      · have hx := hXle T d ha
        set x := X T d with hxdef
        set p := (if x ≤ s then S else x) with hp
        have hpM : p ≤ M' := by
          simp only [hp]; split_ifs
          · exact le_max_left _ _
          · exact hx
        have hnn : ∀ a : α, 0 ≤ V (p - (g a : ℝ)) + CV := fun a => by
          have := (abs_le.1 (hVb (p - (g a : ℝ)) (by linarith [NNReal.coe_nonneg (g a)]))).1
          linarith
        have e1 : ∫⁻ a, F d a ∂μ = ENNReal.ofReal (cost x)
            + ENNReal.ofReal (∫ a, V (p - (g a : ℝ)) ∂μ + CV) := by
          simp only [hF, if_pos ha]
          rw [lintegral_add_left' measurable_const.aemeasurable, lintegral_const, measure_univ,
            mul_one]
          congr 1
          have hnn' : 0 ≤ᵐ[μ] (fun a => V (p - (g a : ℝ)) + CV) := ae_of_all _ (fun a => hnn a)
          have hint' : Integrable (fun a => V (p - (g a : ℝ)) + CV) μ :=
            (hVintμ p).add (integrable_const CV)
          have e2 := (ofReal_integral_eq_lintegral_ofReal hint' hnn').symm
          have e3 : ∫ a, (V (p - (g a : ℝ)) + CV) ∂μ = ∫ a, V (p - (g a : ℝ)) ∂μ + CV := by
            rw [integral_add (hVintμ p) (integrable_const CV), integral_const, probReal_univ,
              one_smul]
          rw [e3] at e2
          exact e2
        rw [e1]
        have hP := hPoisμ x
        have hI0 : 0 ≤ ∫ a, V (p - (g a : ℝ)) ∂μ + CV := by
          have h1 : 0 ≤ ∫ a, (V (p - (g a : ℝ)) + CV) ∂μ := integral_nonneg (fun a => hnn a)
          rwa [integral_add (hVintμ p) (integrable_const CV), integral_const, probReal_univ,
            one_smul] at h1
        rw [← ENNReal.ofReal_add (hcost0 x) hI0]
        simp only [hΦ, if_pos ha]
        rw [← ENNReal.ofReal_add hgv0 (by
          have := (abs_le.1 (hVb x hx)).1; linarith)]
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [hcost] at *
        linarith
      · simp only [hF, if_neg ha, lintegral_const, measure_univ, mul_one]
        exact le_add_self
    calc ∫⁻ z, c T (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)
          + ∫⁻ z, Φ (T + 1) (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)
        = ∫⁻ z, (c T (padHist N z) + Φ (T + 1) (padHist N z)) ∂(Measure.pi fun _ : Fin N => μ) :=
          (lintegral_add_left ((hcm T).comp hD) _).symm
      _ ≤ ∫⁻ z, F (padHist N z) (padHist N z T) ∂(Measure.pi fun _ : Fin N => μ) :=
          lintegral_mono fun z => hpt (padHist N z)
      _ = ∫⁻ z, ∫⁻ a, F (padHist N z) a ∂μ ∂(Measure.pi fun _ : Fin N => μ) :=
          lintegral_coord μ N T hT F hFm hFd
      _ ≤ ∫⁻ z, (ENNReal.ofReal gv + Φ T (padHist N z)) ∂(Measure.pi fun _ : Fin N => μ) :=
          lintegral_mono fun z => hinner (padHist N z)
      _ = ENNReal.ofReal gv + ∫⁻ z, Φ T (padHist N z) ∂(Measure.pi fun _ : Fin N => μ) := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  -- telescoping over the horizon
  have hind : ∀ N T, T ≤ N →
      ∫⁻ z, ∑ t ∈ Finset.range T, c t (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)
        + ∫⁻ z, Φ T (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ENNReal.ofReal (T * gv) + ∫⁻ z, Φ 0 (padHist N z) ∂(Measure.pi fun _ : Fin N => μ) := by
    intro N T
    induction T with
    | zero => intro _; simp
    | succ T ih =>
      intro hT
      have ih' := ih (by omega)
      have hD := measurable_padHist' (α := α) N
      simp only [Finset.sum_range_succ]
      have hmS : Measurable fun z : Fin N → α => ∑ t ∈ Finset.range T, c t (padHist N z) :=
        Finset.measurable_sum _ fun t _ => (hcm t).comp hD
      rw [lintegral_add_left hmS]
      have h1 := hstep1 N T (by omega)
      have hcast : ENNReal.ofReal (((T + 1 : ℕ) : ℝ) * gv)
          = ENNReal.ofReal (T * gv) + ENNReal.ofReal gv := by
        rw [← ENNReal.ofReal_add (by positivity) hgv0]
        congr 1
        push_cast
        ring
      rw [hcast]
      calc ∫⁻ z, ∑ t ∈ Finset.range T, c t (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)
            + ∫⁻ z, c T (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)
            + ∫⁻ z, Φ (T + 1) (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)
          = ∫⁻ z, ∑ t ∈ Finset.range T, c t (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)
            + (∫⁻ z, c T (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)
              + ∫⁻ z, Φ (T + 1) (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)) := by ring
        _ ≤ ∫⁻ z, ∑ t ∈ Finset.range T, c t (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)
            + (ENNReal.ofReal gv + ∫⁻ z, Φ T (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)) := by
            gcongr
        _ = (∫⁻ z, ∑ t ∈ Finset.range T, c t (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)
            + ∫⁻ z, Φ T (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)) + ENNReal.ofReal gv := by
            ring
        _ ≤ (ENNReal.ofReal (T * gv) + ∫⁻ z, Φ 0 (padHist N z) ∂(Measure.pi fun _ : Fin N => μ))
            + ENNReal.ofReal gv := by gcongr
        _ = _ := by ring
  refine ⟨ENNReal.ofReal (2 * CV), ENNReal.ofReal_ne_top, fun T N hTN => ?_⟩
  have hΦ0 : ∫⁻ z, Φ 0 (padHist N z) ∂(Measure.pi fun _ : Fin N => μ) ≤ ENNReal.ofReal (2 * CV) := by
    calc ∫⁻ z, Φ 0 (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)
        ≤ ∫⁻ _z, ENNReal.ofReal (2 * CV) ∂(Measure.pi fun _ : Fin N => μ) := by
          refine lintegral_mono fun z => ?_
          by_cases h : act 0 (padHist N z)
          · exact hΦle 0 _ h (hstart0 _ h)
          · simp only [hΦ, if_neg h]; exact le_rfl
      _ = ENNReal.ofReal (2 * CV) := by rw [lintegral_const, measure_univ, mul_one]
  have hT := hind N T hTN
  have hTg : ENNReal.ofReal (T * gv) = T * ssAvgCost ρ f K s S := by
    rw [hgv, ENNReal.ofReal_mul (Nat.cast_nonneg T), ENNReal.ofReal_natCast]
  calc ∫⁻ z, ∑ t ∈ Finset.range T, (if act t (padHist N z) then ENNReal.ofReal
          (K * (if X t (padHist N z) ≤ s ∧ X t (padHist N z) < S then 1 else 0)
            + f (if X t (padHist N z) ≤ s then S else X t (padHist N z))) else 0)
        ∂(Measure.pi fun _ : Fin N => μ)
      = ∫⁻ z, ∑ t ∈ Finset.range T, c t (padHist N z) ∂(Measure.pi fun _ : Fin N => μ) := rfl
    _ ≤ ∫⁻ z, ∑ t ∈ Finset.range T, c t (padHist N z) ∂(Measure.pi fun _ : Fin N => μ)
        + ∫⁻ z, Φ T (padHist N z) ∂(Measure.pi fun _ : Fin N => μ) := le_self_add
    _ ≤ ENNReal.ofReal (T * gv) + ∫⁻ z, Φ 0 (padHist N z) ∂(Measure.pi fun _ : Fin N => μ) := hT
    _ ≤ T * ssAvgCost ρ f K s S + ENNReal.ofReal (2 * CV) := by rw [hTg]; gcongr
