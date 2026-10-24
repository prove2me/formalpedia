-- Prove2me | solution 1 for StrictCompatLB.MeanField.lemma_F_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T15:40:47.741559+00:00
-- url     : https://prove2.me/submissions/a32abf23-fcc3-42f2-bd4c-c32f4b24191f

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace StrictCompatLB.MeanField.F1

open StrictCompatLB.MeanField

/-! ### Exponential clocks -/

section clocks
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

lemma expMeasure_Iic {r : ℝ} (hr : 0 < r) (a : ℝ) :
    expMeasure r (Set.Iic a) = ENNReal.ofReal (if 0 ≤ a then 1 - Real.exp (-(r * a)) else 0) := by
  haveI := isProbabilityMeasure_expMeasure hr
  rw [← cdf_expMeasure_eq hr, cdf_eq_real, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma exp_neg_null {r : ℝ} (hr : 0 < r) (τ : Ω → ℝ) (hτ : Measurable τ)
    (hmap : P.map τ = expMeasure r) : P {ω | τ ω < 0} = 0 := by
  have : {ω | τ ω < 0} = τ ⁻¹' (Set.Iio 0) := rfl
  rw [this, ← Measure.map_apply hτ measurableSet_Iio, hmap]
  have hU : Set.Iio (0 : ℝ) = ⋃ n : ℕ, Set.Iic (-(1 / ((n : ℝ) + 1))) := by
    ext x
    simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < -x by linarith)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [hU]
  apply measure_iUnion_null
  intro n
  rw [expMeasure_Iic hr, if_neg (by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith)]
  simp

lemma exp_le {r : ℝ} (hr : 0 < r) (τ : Ω → ℝ) (hτ : Measurable τ) (hmap : P.map τ = expMeasure r)
    {a : ℝ} (ha : 0 ≤ a) : P {ω | τ ω ≤ a} ≤ ENNReal.ofReal (r * a) := by
  have : {ω | τ ω ≤ a} = τ ⁻¹' (Set.Iic a) := rfl
  rw [this, ← Measure.map_apply hτ measurableSet_Iic, hmap, expMeasure_Iic hr, if_pos ha]
  apply ENNReal.ofReal_le_ofReal
  have := Real.add_one_le_exp (-(r * a))
  linarith

/-- Few clock epochs: the probability that the first `m` gaps sum to at most `T`. -/
lemma sum_small {r : ℝ} (hr : 0 < r) (τ : ℕ → Ω → ℝ) (hτ : ∀ k, Measurable (τ k))
    (hmap : ∀ k, P.map (τ k) = expMeasure r) {T : ℝ} (hT : 0 < T) (m : ℕ) (hm : 1 ≤ m) :
    P {ω | (∀ k, 0 ≤ τ k ω) ∧ ∑ k ∈ range m, τ k ω ≤ T} ≤ ENNReal.ofReal (4 * r * T / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set a := 2 * T / m with ha
  have ha0 : 0 ≤ a := by positivity
  set f : Ω → ℝ≥0∞ := fun ω => ∑ k ∈ range m, Set.indicator {ω | τ k ω ≤ a} 1 ω with hf
  have hfm : ∀ k ∈ range m, Measurable (Set.indicator {ω | τ k ω ≤ a} (1 : Ω → ℝ≥0∞)) :=
    fun k _ => measurable_one.indicator (measurableSet_le (hτ k) measurable_const)
  have hint : ∫⁻ ω, f ω ∂P ≤ ENNReal.ofReal (2 * r * T) := by
    simp only [hf]
    rw [lintegral_finset_sum _ hfm]
    calc ∑ k ∈ range m, ∫⁻ ω, Set.indicator {ω | τ k ω ≤ a} 1 ω ∂P
        = ∑ k ∈ range m, P {ω | τ k ω ≤ a} := by
          apply Finset.sum_congr rfl; intro k _
          exact lintegral_indicator_one (measurableSet_le (hτ k) measurable_const)
      _ ≤ ∑ k ∈ range m, ENNReal.ofReal (r * a) :=
          Finset.sum_le_sum (fun k _ => exp_le P hr (τ k) (hτ k) (hmap k) ha0)
      _ = ENNReal.ofReal (m * (r * a)) := by
          rw [sum_const, card_range, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal (2 * r * T) := by
          congr 1; rw [ha]; field_simp
  have hsub : {ω | (∀ k, 0 ≤ τ k ω) ∧ ∑ k ∈ range m, τ k ω ≤ T} ⊆
      {ω | ENNReal.ofReal ((m : ℝ) / 2) ≤ f ω} := by
    intro ω ⟨hpos, hsum⟩
    simp only [Set.mem_setOf_eq, hf]
    -- count the small gaps
    set G := (range m).filter (fun k => τ k ω ≤ a) with hG
    set B := (range m).filter (fun k => ¬ τ k ω ≤ a) with hB
    have hcard : G.card + B.card = m := by
      rw [hG, hB, Finset.card_filter_add_card_filter_not, card_range]
    have hBa : (B.card : ℝ) * a ≤ T := by
      calc (B.card : ℝ) * a = ∑ k ∈ B, a := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ k ∈ B, τ k ω := Finset.sum_le_sum (fun k hk => by
            simp only [hB, mem_filter] at hk; linarith [hk.2])
        _ ≤ ∑ k ∈ range m, τ k ω :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun k _ _ => hpos k)
        _ ≤ T := hsum
    have hBm : (B.card : ℝ) ≤ m / 2 := by
      rw [ha] at hBa
      have : (B.card : ℝ) * (2 * T / m) = (B.card : ℝ) * 2 * T / m := by ring
      rw [this, div_le_iff₀ hm0] at hBa
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      nlinarith
    have hGm : (m : ℝ) / 2 ≤ G.card := by
      have : (G.card : ℝ) + B.card = m := by exact_mod_cast hcard
      linarith
    have hfG : (∑ k ∈ range m, Set.indicator {ω | τ k ω ≤ a} (1 : Ω → ℝ≥0∞) ω) = G.card := by
      rw [hG, Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl; intro k _
      by_cases h : τ k ω ≤ a
      · rw [Set.indicator_of_mem (show ω ∈ {ω | τ k ω ≤ a} from h), if_pos h]; simp
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | τ k ω ≤ a} from h), if_neg h]; simp
    rw [hfG, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hGm
  have hmk := mul_meas_ge_le_lintegral₀ (μ := P) (f := f)
    (Finset.aemeasurable_fun_sum _ (fun k hk => (hfm k hk).aemeasurable))
    (ENNReal.ofReal ((m : ℝ) / 2))
  have hc0 : ENNReal.ofReal ((m : ℝ) / 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  calc P {ω | (∀ k, 0 ≤ τ k ω) ∧ ∑ k ∈ range m, τ k ω ≤ T}
      ≤ P {ω | ENNReal.ofReal ((m : ℝ) / 2) ≤ f ω} := measure_mono hsub
    _ ≤ ENNReal.ofReal (2 * r * T) / ENNReal.ofReal ((m : ℝ) / 2) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact le_trans hmk hint
    _ = ENNReal.ofReal (4 * r * T / m) := by
        rw [← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1; field_simp; ring

end clocks

/-! ### The jump count -/

lemma epoch_le (τ : ℕ → ℝ) (hτ : ∀ k, 0 ≤ τ k) {t T : ℝ} (htT : t ≤ T) (m : ℕ)
    (hm : T < ∑ k ∈ range (m + 1), τ k) : epochCount τ t ≤ m := by
  unfold epochCount
  apply csSup_le'
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  by_contra hc
  push Not at hc
  have : ∑ k ∈ range (m + 1), τ k ≤ ∑ k ∈ range n, τ k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      (fun k _ _ => hτ k)
  linarith

/-! ### Total number of tasks along the chain -/

def tot {N : ℕ} (z : Fin N → ℕ) : ℕ := ∑ u, z u

lemma tot_update {N : ℕ} (z : Fin N → ℕ) (v : Fin N) (c : ℕ) :
    tot (Function.update z v c) + z v = tot z + c := by
  unfold tot
  rw [Finset.sum_update_of_mem (mem_univ v), ← Finset.add_sum_erase _ _ (mem_univ v),
    Finset.sdiff_singleton_eq_erase]
  ring

lemma lbKernel_tot (lam : ℝ) (M : ℕ → ℕ) (N : ℕ) (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (z z' : Fin N → ℕ) (h : lbKernel lam M N route z z' ≠ 0) : tot z' ≤ tot z + 1 := by
  by_contra hc
  push Not at hc
  apply h
  unfold lbKernel
  have ha : ∀ v, z' ≠ arrive z v := by
    intro v hv; have := tot_update z v (z v + 1); rw [arrive] at hv; rw [← hv] at this; omega
  have hd : ∀ v, z' ≠ depart z v := by
    intro v hv; have := tot_update z v (z v - 1); rw [depart] at hv; rw [← hv] at this; omega
  simp [ha, hd]

lemma path_tot {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (lam : ℝ) (M : ℕ → ℕ) (N : ℕ)
    (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ) (z₀ : Fin N → ℕ) (Y : ℕ → Ω → (Fin N → ℕ))
    (rate : ℝ) (τ : ℕ → Ω → ℝ)
    (hproc : IsUniformizedProcess P (lbKernel lam M N route) rate z₀ Y τ) (n : ℕ) :
    P {ω | tot z₀ + n < tot (Y n ω)} = 0 := by
  set ext : (Fin (n + 1) → (Fin N → ℕ)) → ℕ → (Fin N → ℕ) :=
    fun f j => if h : j < n + 1 then f ⟨j, h⟩ else z₀ with hext
  set C : (Fin (n + 1) → (Fin N → ℕ)) → Set Ω := fun f => {ω | ∀ j ≤ n, Y j ω = ext f j}
  have hsub : {ω | tot z₀ + n < tot (Y n ω)} ⊆
      ⋃ f : {f : Fin (n + 1) → (Fin N → ℕ) // tot z₀ + n < tot (f ⟨n, by omega⟩)}, C f.1 := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    refine Set.mem_iUnion.mpr ⟨⟨fun j => Y j ω, hω⟩, ?_⟩
    intro j hj
    simp only [hext, dif_pos (show j < n + 1 by omega)]
  apply measure_mono_null hsub
  apply measure_iUnion_null
  rintro ⟨f, hf⟩
  have := hproc.2.2.1 n (ext f)
  simp only [C]
  rw [this, ENNReal.ofReal_eq_zero]
  by_cases h0 : ext f 0 = z₀
  · rw [if_pos h0, one_mul]
    have hprod : ∏ j ∈ range n, lbKernel lam M N route (ext f j) (ext f (j + 1)) = 0 := by
      by_contra hne
      have hall : ∀ j ∈ range n, lbKernel lam M N route (ext f j) (ext f (j + 1)) ≠ 0 := by
        intro j hj heq
        exact hne (Finset.prod_eq_zero hj heq)
      have hgrow : ∀ j, j ≤ n → tot (ext f j) ≤ tot z₀ + j := by
        intro j
        induction j with
        | zero => intro _; rw [h0]; omega
        | succ j ih =>
          intro hj
          have := lbKernel_tot lam M N route _ _ (hall j (by simp; omega))
          have := ih (by omega)
          omega
      have := hgrow n le_rfl
      have e : ext f n = f ⟨n, by omega⟩ := by simp [hext]
      rw [e] at this
      omega
    rw [hprod]
  · rw [if_neg h0, zero_mul]

/-! ### Occupancy bounds -/

lemma occ_le_tot {N : ℕ} (hN : 1 ≤ N) (z : Fin N → ℕ) {i : ℕ} (hi : 1 ≤ i) :
    occ z i ≤ (tot z : ℝ) / (i * N) := by
  unfold occ
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hip : (0 : ℝ) < i := by exact_mod_cast hi
  have key : i * Qcount z i ≤ tot z := by
    unfold Qcount tot
    calc i * (univ.filter (fun v => i ≤ z v)).card = ∑ v ∈ univ.filter (fun v => i ≤ z v), i := by
          rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ univ.filter (fun v => i ≤ z v), z v :=
          Finset.sum_le_sum (fun v hv => (mem_filter.mp hv).2)
      _ ≤ ∑ v, z v := Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun _ _ _ => Nat.zero_le _)
  rw [div_le_div_iff₀ hNp (by positivity)]
  have : (i : ℝ) * Qcount z i ≤ tot z := by exact_mod_cast key
  nlinarith

lemma tot_eq_sum_occ {N : ℕ} (hN : 1 ≤ N) (z : Fin N → ℕ) :
    (tot z : ℝ) / N = ∑ i ∈ Ico 1 (maxLen z + 1), occ z i := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  unfold occ
  rw [← Finset.sum_div]
  congr 1
  have : ∑ i ∈ Ico 1 (maxLen z + 1), Qcount z i = tot z := by
    unfold Qcount tot
    simp only [card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    have hu : z u ≤ maxLen z := Finset.le_sup (f := z) (mem_univ u)
    rw [← Finset.card_filter]
    have : (Ico 1 (maxLen z + 1)).filter (fun i => i ≤ z u) = Ico 1 (z u + 1) := by
      ext i; simp only [mem_filter, mem_Ico]; omega
    rw [this, Nat.card_Ico]; omega
  exact_mod_cast this.symm

end StrictCompatLB.MeanField.F1

open StrictCompatLB.MeanField StrictCompatLB.MeanField.F1 in
theorem solution (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (route : (N : ℕ) → Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (hroute : ∀ N, 1 ≤ N → IsRoutingRule M G N (route N))
    (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ) (hq₀ : InY q₀)
    (hinit : Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ)
    (hproc : ∀ N, 1 ≤ N → IsLBProcess P lam M N (route N) (z₀ N) (Y N) (τ N)) :
    ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ T : ℝ, 0 < T →
      ∃ i₀ : ℕ, 1 ≤ i₀ ∧ ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N ≥ N₁,
        P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, ε ≤ occPath (Y N) (τ N) ω t i₀} < ENNReal.ofReal δ := by
  intro ε hε δ hδ T hT
  have hq0 : ∀ i, 0 ≤ q₀ i := hq₀.1.2.1
  set S₀ := ∑' i, q₀ (i + 1) with hS₀
  have hS₀0 : 0 ≤ S₀ := tsum_nonneg (fun i => hq0 _)
  -- initial number of tasks
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (hinit.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num)))
  have hinit' : ∀ N, N₂ ≤ N → 1 ≤ N → (tot (z₀ N) : ℝ) / N ≤ S₀ + 1 := by
    intro N hN hN1
    have hl := hN₂ N hN
    rw [tot_eq_sum_occ hN1]
    set Mx := maxLen (z₀ N)
    have h1 : ∑ i ∈ Ico 1 (Mx + 1), occ (z₀ N) i ≤
        ∑ i ∈ Ico 1 (Mx + 1), q₀ i + ∑ i ∈ Ico 1 (Mx + 1), |occ (z₀ N) i - q₀ i| := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro i _
      linarith [le_abs_self (occ (z₀ N) i - q₀ i)]
    have h2 : ∑ i ∈ Ico 1 (Mx + 1), q₀ i ≤ S₀ := by
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
      have := (hq₀.2).sum_le_tsum (range Mx) (fun i _ => hq0 _)
      simpa [add_comm] using this
    have h3 : ∑ i ∈ Ico 1 (Mx + 1), |occ (z₀ N) i - q₀ i| < 1 := by
      rw [← ENNReal.ofReal_lt_one, ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
      calc _ ≤ ∑' i, ENNReal.ofReal |occ (z₀ N) i - q₀ i| := ENNReal.sum_le_tsum _
        _ < 1 := hl
    linarith
  set c := 8 * (lam + 1) * T / δ + 1 with hc
  have hc1 : 1 ≤ c := by have : 0 ≤ 8 * (lam + 1) * T / δ := by positivity
                         linarith
  have hcδ : 4 * (lam + 1) * T / c < δ := by
    rw [div_lt_iff₀ (by linarith)]
    have : 8 * (lam + 1) * T / δ * δ = 8 * (lam + 1) * T := by field_simp
    have hpos : 0 < 4 * (lam + 1) * T := by positivity
    nlinarith
  set i₀ := ⌈(S₀ + 1 + c) / ε⌉₊ + 1 with hi₀
  have hi₀ε : (S₀ + 1 + c) / i₀ < ε := by
    have h1 : (S₀ + 1 + c) / ε < i₀ := by
      rw [hi₀]; push_cast
      have := Nat.le_ceil ((S₀ + 1 + c) / ε); linarith
    have hi0 : (0 : ℝ) < i₀ := by rw [hi₀]; positivity
    rw [div_lt_iff₀ hi0]
    rw [div_lt_iff₀ hε] at h1
    linarith
  refine ⟨i₀, by omega, max N₂ 1, le_max_right _ _, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpr := hproc N hN1
  unfold IsLBProcess at hpr
  set r := (lam + 1) * (N : ℝ) with hr
  have hr0 : 0 < r := by positivity
  have hτm : ∀ k, Measurable (τ N k) := hpr.2.2.2.1
  have hmap : ∀ k, P.map (τ N k) = expMeasure r := hpr.2.2.2.2.2.1
  set m := ⌊c * N⌋₊ with hm
  have hmle : (m : ℝ) ≤ c * N := Nat.floor_le (by positivity)
  have hmgt : c * N < m + 1 := Nat.lt_floor_add_one _
  set B := {ω | (∀ k, 0 ≤ τ N k ω) ∧ ∑ k ∈ range (m + 1), τ N k ω ≤ T} with hB
  set Z1 := ⋃ k, {ω | τ N k ω < 0} with hZ1
  set Z2 := ⋃ n, {ω | tot (z₀ N) + n < tot (Y N n ω)} with hZ2
  have hZ1n : P Z1 = 0 := measure_iUnion_null (fun k => exp_neg_null P hr0 _ (hτm k) (hmap k))
  have hZ2n : P Z2 = 0 := measure_iUnion_null (fun n =>
    path_tot P lam M N (route N) (z₀ N) (Y N) r (τ N) hpr n)
  have hsub : {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, ε ≤ occPath (Y N) (τ N) ω t i₀} ⊆ B ∪ Z1 ∪ Z2 := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨hnB, hnZ1⟩, hnZ2⟩ := hcon
    have hpos : ∀ k, 0 ≤ τ N k ω := by
      intro k; by_contra h; push Not at h
      exact hnZ1 (Set.mem_iUnion.mpr ⟨k, h⟩)
    have htot : ∀ n, tot (Y N n ω) ≤ tot (z₀ N) + n := by
      intro n; by_contra h; push Not at h
      exact hnZ2 (Set.mem_iUnion.mpr ⟨n, h⟩)
    have hTlt : T < ∑ k ∈ range (m + 1), τ N k ω := by
      by_contra h; push Not at h
      exact hnB ⟨hpos, h⟩
    obtain ⟨t, ht, hge⟩ := hω
    set n := epochCount (fun k => τ N k ω) t with hn
    have hnm : n ≤ m := epoch_le (fun k => τ N k ω) hpos ht.2 m hTlt
    have hocc : occPath (Y N) (τ N) ω t i₀ = occ (Y N n ω) i₀ := rfl
    rw [hocc] at hge
    have h1 := occ_le_tot hN1 (Y N n ω) (show 1 ≤ i₀ by omega)
    have h2 : (tot (Y N n ω) : ℝ) ≤ tot (z₀ N) + m := by
      have := htot n
      have : tot (Y N n ω) ≤ tot (z₀ N) + m := by omega
      exact_mod_cast this
    have h3 : (tot (z₀ N) : ℝ) ≤ (S₀ + 1) * N := by
      have := hinit' N (le_trans (le_max_left _ _) hN) hN1
      rwa [div_le_iff₀ hNp] at this
    have hi0 : (0 : ℝ) < i₀ := by rw [hi₀]; positivity
    have h4 : (tot (Y N n ω) : ℝ) / (i₀ * N) ≤ (S₀ + 1 + c) / i₀ := by
      rw [div_le_div_iff₀ (by positivity) hi0]
      nlinarith
    linarith
  calc P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, ε ≤ occPath (Y N) (τ N) ω t i₀}
      ≤ P (B ∪ Z1 ∪ Z2) := measure_mono hsub
    _ ≤ P B + P Z1 + P Z2 := by
        calc P (B ∪ Z1 ∪ Z2) ≤ P (B ∪ Z1) + P Z2 := measure_union_le _ _
          _ ≤ P B + P Z1 + P Z2 := by gcongr; exact measure_union_le _ _
    _ = P B := by rw [hZ1n, hZ2n, add_zero, add_zero]
    _ ≤ ENNReal.ofReal (4 * r * T / ((m + 1 : ℕ) : ℝ)) :=
        sum_small P hr0 (τ N) hτm hmap hT (m + 1) (by omega)
    _ < ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_lt_ofReal_iff hδ]
        have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
        calc 4 * r * T / ((m + 1 : ℕ) : ℝ) ≤ 4 * r * T / (c * N) := by
              apply div_le_div_of_nonneg_left (by positivity) (by positivity)
              push_cast; linarith
          _ = 4 * (lam + 1) * T / c := by rw [hr]; field_simp
          _ < δ := hcδ
