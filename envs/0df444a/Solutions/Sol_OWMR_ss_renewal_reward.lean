-- Prove2me | solution 1 for OWMR.ss_renewal_reward
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T03:21:30.84884+00:00
-- url     : https://prove2.me/submissions/3895e7fa-b77e-4565-a67c-eeb26f219262

import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Prod

/-!
The occupation identity (10) for an `(s,S)` policy started at `S`, proved with a Poisson equation.

Write `w = S - s`, `h(x) = f(S - x)`, `M = U[0,w)`, `g* = (K + ∫_{[0,w)} h dU) / M`, and run the policy from
an arbitrary pre-order position `p ≤ S`. With
`ψ(x) = ∫_{[0,w-x)} h(x+u) U(du) - g* U[0, w-x)` (the expected remaining cycle cost, net of `g*` per
period) and `φ(q) = if q ≤ s then 0 else ψ(S - q)`, the renewal equation `U = δ₀ + ρ * U` gives
`ψ(x) = h(x) - g* + 𝔼 ψ(x + D)` for `x ∈ [0, w)` and `ψ(0) = -K`, hence the Poisson equation
`c(p) + 𝔼 φ(post(p) - D) = g* + φ(p)`. By induction over the horizon `T` (one-step split of the
demand sequence), `𝔼 ∑_{t<T} c_t + 𝔼 φ̃(pre_T) = T g* + φ̃(p)` for the shift `φ̃ = φ + A ≥ 0`, and
`φ̃` is bounded, so `T⁻¹ 𝔼 ∑_{t<T} c_t → g*`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR

private noncomputable def postF (s S q : ℝ) : ℝ := if q ≤ s then S else q

/-- Pre-order positions of the `(s,S)` policy started at pre-order position `p`. -/
private noncomputable def preG (s S p : ℝ) (d : ℕ → ℝ≥0) : ℕ → ℝ
  | 0 => p
  | t + 1 => postF s S (preG s S p d t) - (d t : ℝ)

private noncomputable def costG (f : ℝ → ℝ) (K s S p : ℝ) (d : ℕ → ℝ≥0) (t : ℕ) : ℝ :=
  K * (if preG s S p d t ≤ s then 1 else 0) + f (postF s S (preG s S p d t))

private lemma ssPre_eq (s S : ℝ) (d : ℕ → ℝ≥0) : ∀ t, ssPre s S d t = preG s S S d t
  | 0 => rfl
  | t + 1 => by
    simp only [ssPre, preG, postF]
    rw [ssPre_eq s S d t]

private lemma ssPeriodCost_eq (f : ℝ → ℝ) (K s S : ℝ) (hsS : s < S) (d : ℕ → ℝ≥0) (t : ℕ) :
    ssPeriodCost f K s S d t = costG f K s S S d t := by
  unfold ssPeriodCost ssPost costG postF
  rw [ssPre_eq]
  by_cases h : preG s S S d t ≤ s
  · simp [h, lt_of_le_of_lt h hsS]
  · simp [h]

private lemma preG_succ (s S p : ℝ) (d : ℕ → ℝ≥0) : ∀ t,
    preG s S p d (t + 1) = preG s S (postF s S p - (d 0 : ℝ)) (fun i => d (i + 1)) t
  | 0 => rfl
  | t + 1 => by
    show postF s S (preG s S p d (t + 1)) - (d (t + 1) : ℝ)
      = postF s S (preG s S (postF s S p - (d 0 : ℝ)) (fun i => d (i + 1)) t) - (d (t + 1) : ℝ)
    rw [preG_succ s S p d t]

private lemma postF_le (s S q : ℝ) (hq : q ≤ S) : postF s S q ≤ S := by
  unfold postF; split_ifs <;> linarith

private lemma preG_le (s S p : ℝ) (hp : p ≤ S) (d : ℕ → ℝ≥0) : ∀ t, preG s S p d t ≤ S
  | 0 => hp
  | t + 1 => by
    show postF s S (preG s S p d t) - (d t : ℝ) ≤ S
    linarith [postF_le s S _ (preG_le s S p hp d t), NNReal.coe_nonneg (d t)]

private lemma padHist_succ_zero {T : ℕ} (z : Fin (T + 1) → ℝ≥0) : padHist (T + 1) z 0 = z 0 := by
  simp only [padHist, dif_pos (Nat.succ_pos T)]
  rfl

private lemma padHist_succ_shift {T : ℕ} (z : Fin (T + 1) → ℝ≥0) :
    (fun i => padHist (T + 1) z (i + 1)) = padHist T (Fin.tail z) := by
  funext i
  by_cases h : i < T
  · simp only [padHist, dif_pos (Nat.succ_lt_succ h), dif_pos h]
    rfl
  · simp only [padHist, dif_neg (fun h' => h (Nat.lt_of_succ_lt_succ h')), dif_neg h]

private lemma measurable_padHist (T t : ℕ) :
    Measurable fun z : Fin T → ℝ≥0 => ((padHist T z t : ℝ≥0) : ℝ) := by
  by_cases h : t < T
  · simp only [padHist, dif_pos h]
    exact (measurable_pi_apply (⟨t, h⟩ : Fin T)).coe_nnreal_real
  · simp only [padHist, dif_neg h]
    exact measurable_const

private lemma measurable_preG (s S : ℝ) (T : ℕ) : ∀ t,
    Measurable fun q : ℝ × (Fin T → ℝ≥0) => preG s S q.1 (padHist T q.2) t
  | 0 => measurable_fst
  | t + 1 => by
    have ih := measurable_preG s S T t
    show Measurable fun q : ℝ × (Fin T → ℝ≥0) =>
      postF s S (preG s S q.1 (padHist T q.2) t) - ((padHist T q.2 t : ℝ≥0) : ℝ)
    refine Measurable.sub ?_ ((measurable_padHist T t).comp measurable_snd)
    unfold postF
    exact Measurable.ite (measurableSet_le ih measurable_const) measurable_const ih

private lemma measurable_costG (f : ℝ → ℝ) (hf : Measurable f) (K s S : ℝ) (T t : ℕ) :
    Measurable fun q : ℝ × (Fin T → ℝ≥0) => costG f K s S q.1 (padHist T q.2) t := by
  have h := measurable_preG s S T t
  unfold costG postF
  exact (measurable_const.mul (Measurable.ite (measurableSet_le h measurable_const)
    measurable_const measurable_const)).add
    (hf.comp (Measurable.ite (measurableSet_le h measurable_const) measurable_const h))

/-- Expected `T`-period cost from pre-order position `p`. -/
private noncomputable def VG (ρ : Measure ℝ≥0) (f : ℝ → ℝ) (K s S : ℝ) (T : ℕ) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal (costG f K s S p (padHist T z) t)
    ∂(Measure.pi fun _ : Fin T => ρ)

/-- Expected value of `φ` at the pre-order position of period `T`. -/
private noncomputable def WG (ρ : Measure ℝ≥0) (φ : ℝ → ℝ) (s S : ℝ) (T : ℕ) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (φ (preG s S p (padHist T z) T)) ∂(Measure.pi fun _ : Fin T => ρ)

private lemma measurable_VG (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ)
    (hf : Measurable f) (K s S : ℝ) (T : ℕ) : Measurable fun p => VG ρ f K s S T p :=
  Measurable.lintegral_prod_right' (f := fun q : ℝ × (Fin T → ℝ≥0) =>
    ∑ t ∈ Finset.range T, ENNReal.ofReal (costG f K s S q.1 (padHist T q.2) t))
    (Finset.measurable_sum _ fun t _ =>
      ENNReal.measurable_ofReal.comp (measurable_costG f hf K s S T t))

private lemma measurable_WG (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (φ : ℝ → ℝ)
    (hφ : Measurable φ) (s S : ℝ) (T : ℕ) : Measurable fun p => WG ρ φ s S T p :=
  Measurable.lintegral_prod_right' (f := fun q : ℝ × (Fin T → ℝ≥0) =>
    ENNReal.ofReal (φ (preG s S q.1 (padHist T q.2) T)))
    (ENNReal.measurable_ofReal.comp (hφ.comp (measurable_preG s S T T)))

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

private lemma VG_zero (ρ : Measure ℝ≥0) (f : ℝ → ℝ) (K s S p : ℝ) : VG ρ f K s S 0 p = 0 := by
  simp [VG]

private lemma WG_zero (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (φ : ℝ → ℝ) (s S p : ℝ) :
    WG ρ φ s S 0 p = ENNReal.ofReal (φ p) := by
  simp only [WG, preG, lintegral_const, measure_univ, mul_one]

private lemma VG_succ (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ) (hf : Measurable f)
    (K s S : ℝ) (T : ℕ) (p : ℝ) :
    VG ρ f K s S (T + 1) p = ENNReal.ofReal (K * (if p ≤ s then 1 else 0) + f (postF s S p))
      + ∫⁻ y, VG ρ f K s S T (postF s S p - (y : ℝ)) ∂ρ := by
  have hcost : ∀ (z : Fin (T + 1) → ℝ≥0) (t : ℕ), costG f K s S p (padHist (T + 1) z) (t + 1)
      = costG f K s S (postF s S p - (z 0 : ℝ)) (padHist T (Fin.tail z)) t := by
    intro z t
    unfold costG
    rw [preG_succ, padHist_succ_zero, padHist_succ_shift]
  have hF : Measurable fun q : ℝ≥0 × (Fin T → ℝ≥0) => ∑ t ∈ Finset.range T,
      ENNReal.ofReal (costG f K s S (postF s S p - (q.1 : ℝ)) (padHist T q.2) t) :=
    Finset.measurable_sum _ fun t _ => ENNReal.measurable_ofReal.comp
      ((measurable_costG f hf K s S T t).comp
        ((measurable_const.sub measurable_fst.coe_nnreal_real).prodMk measurable_snd))
  have h0 : ∀ z : Fin (T + 1) → ℝ≥0, costG f K s S p (padHist (T + 1) z) 0
      = K * (if p ≤ s then 1 else 0) + f (postF s S p) := fun z => rfl
  unfold VG
  simp_rw [Finset.sum_range_succ', hcost, h0]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one, add_comm]
  congr 1
  exact lintegral_pi_succ ρ T hF

private lemma WG_succ (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (φ : ℝ → ℝ) (hφ : Measurable φ)
    (s S : ℝ) (T : ℕ) (p : ℝ) :
    WG ρ φ s S (T + 1) p = ∫⁻ y, WG ρ φ s S T (postF s S p - (y : ℝ)) ∂ρ := by
  have hpre : ∀ z : Fin (T + 1) → ℝ≥0, preG s S p (padHist (T + 1) z) (T + 1)
      = preG s S (postF s S p - (z 0 : ℝ)) (padHist T (Fin.tail z)) T := by
    intro z
    rw [preG_succ, padHist_succ_zero, padHist_succ_shift]
  have hF : Measurable fun q : ℝ≥0 × (Fin T → ℝ≥0) =>
      ENNReal.ofReal (φ (preG s S (postF s S p - (q.1 : ℝ)) (padHist T q.2) T)) :=
    ENNReal.measurable_ofReal.comp (hφ.comp ((measurable_preG s S T T).comp
      ((measurable_const.sub measurable_fst.coe_nnreal_real).prodMk measurable_snd)))
  unfold WG
  simp_rw [hpre]
  exact lintegral_pi_succ ρ T hF

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

theorem solution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (f : ℝ → ℝ) (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    (K s S : ℝ) (hK : 0 ≤ K) (hsS : s < S) (hfb : ∃ C, ∀ y ∈ Set.Icc s S, f y ≤ C) :
    ssAvgCost ρ f K s S
      = ENNReal.ofReal ((K + ∫ x in Set.Ico 0 (S - s), f (S - x) ∂(renewalMeasure ρ))
          / (renewalMeasure ρ (Set.Ico 0 (S - s))).toReal) := by
  have : SFinite (renewalMeasure ρ) := by unfold renewalMeasure; infer_instance
  set w := S - s with hw
  have hw0 : 0 < w := by rw [hw]; linarith
  obtain ⟨C0, hC0⟩ := hfb
  set C := max C0 0 with hC
  have hC0' : 0 ≤ C := le_max_right _ _
  have hfC : ∀ y ∈ Set.Icc s S, f y ≤ C := fun y hy => (hC0 y hy).trans (le_max_left _ _)
  -- the renewal count and the target value
  have hUw : renewalMeasure ρ (Set.Ico 0 w) ≠ ∞ := (renewalMeasure_Ico_lt_top ρ hρ w).ne
  set M := (renewalMeasure ρ (Set.Ico 0 w)).toReal with hM
  have hM1 : 1 ≤ M := by
    have := ENNReal.toReal_mono hUw (one_le_renewal ρ w hw0)
    simpa [hM] using this
  have hM0 : 0 < M := by linarith
  set Ih := ∫ x in Set.Ico 0 w, f (S - x) ∂(renewalMeasure ρ) with hIh
  have hIh0 : 0 ≤ Ih := setIntegral_nonneg measurableSet_Ico fun x _ => hf0 _
  set g := (K + Ih) / M with hg
  have hg0 : 0 ≤ g := div_nonneg (by linarith) hM0.le
  have hgM : g * M = K + Ih := div_mul_cancel₀ _ hM0.ne'
  -- the window functionals `Λ`, `N` and the relative value `ψ`
  have hhm : Measurable fun x : ℝ => ENNReal.ofReal (f (S - x)) :=
    ENNReal.measurable_ofReal.comp (hf.comp (measurable_const.sub measurable_id))
  set Λ : ℝ → ℝ≥0∞ := fun x => ∫⁻ u in Set.Ico 0 (w - x), ENNReal.ofReal (f (S - (x + u)))
    ∂(renewalMeasure ρ) with hΛ
  set Nw : ℝ → ℝ≥0∞ := fun x => renewalMeasure ρ (Set.Ico 0 (w - x)) with hNw
  have hΛm : Measurable Λ := by
    have : Λ = fun x => ∫⁻ u, ({q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 < w - q.1}.indicator
        (fun q => ENNReal.ofReal (f (S - (q.1 + q.2))))) (x, u) ∂(renewalMeasure ρ) := by
      funext x
      rw [hΛ]
      simp only
      rw [← lintegral_indicator measurableSet_Ico]
      rfl
    rw [this]
    refine Measurable.lintegral_prod_right' (Measurable.indicator ?_ ?_)
    · exact ENNReal.measurable_ofReal.comp (hf.comp (measurable_const.sub
        (measurable_fst.add measurable_snd)))
    · exact (measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd (measurable_const.sub measurable_fst))
  have hNm : Measurable Nw := by
    have : Nw = fun x => ∫⁻ u, ({q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 < w - q.1}.indicator 1) (x, u)
        ∂(renewalMeasure ρ) := by
      funext x
      rw [hNw]
      simp only
      rw [← lintegral_indicator_one measurableSet_Ico]
      rfl
    rw [this]
    refine Measurable.lintegral_prod_right' (Measurable.indicator measurable_const ?_)
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_const.sub measurable_fst))
  have hΛle : ∀ x, 0 ≤ x → Λ x ≤ ENNReal.ofReal C * renewalMeasure ρ (Set.Ico 0 w) := by
    intro x hx
    calc Λ x ≤ ∫⁻ _u in Set.Ico 0 (w - x), ENNReal.ofReal C ∂(renewalMeasure ρ) := by
          refine setLIntegral_mono' measurableSet_Ico fun u hu => ENNReal.ofReal_le_ofReal ?_
          exact hfC _ ⟨by linarith [hu.2], by linarith [hu.1]⟩
      _ = ENNReal.ofReal C * renewalMeasure ρ (Set.Ico 0 (w - x)) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal C * renewalMeasure ρ (Set.Ico 0 w) :=
          mul_le_mul_of_nonneg_left (measure_mono (Set.Ico_subset_Ico_right (by linarith)))
            (by positivity)
  have hNle : ∀ x, 0 ≤ x → Nw x ≤ renewalMeasure ρ (Set.Ico 0 w) := fun x hx =>
    measure_mono (Set.Ico_subset_Ico_right (by linarith))
  have hΛfin : ∀ x, 0 ≤ x → Λ x ≠ ∞ := fun x hx =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hUw) (hΛle x hx)
  have hNfin : ∀ x, 0 ≤ x → Nw x ≠ ∞ := fun x hx => ne_top_of_le_ne_top hUw (hNle x hx)
  set ψ : ℝ → ℝ := fun x => (Λ x).toReal - g * (Nw x).toReal with hψ
  have hψm : Measurable ψ := (hΛm.ennreal_toReal).sub (measurable_const.mul hNm.ennreal_toReal)
  have hψw : ∀ x, w ≤ x → ψ x = 0 := by
    intro x hx
    have he : Set.Ico (0 : ℝ) (w - x) = ∅ := Set.Ico_eq_empty (by linarith)
    simp only [hψ, hΛ, hNw, he, Measure.restrict_empty, lintegral_zero_measure, measure_empty,
      ENNReal.toReal_zero, mul_zero, sub_zero]
  have hψ0 : ψ 0 = -K := by
    have hΛ0 : (Λ 0).toReal = Ih := by
      rw [hIh, integral_eq_lintegral_of_nonneg_ae (f := fun x => f (S - x))
        (ae_of_all _ fun x => hf0 _) (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable]
      simp only [hΛ, sub_zero, zero_add]
    have hN0 : (Nw 0).toReal = M := by simp only [hNw, sub_zero, hM]
    simp only [hψ]
    rw [hΛ0, hN0, hgM]
    ring
  have hψb : ∀ x, 0 ≤ x → |ψ x| ≤ (C + g) * M := by
    intro x hx
    have h1 : (Λ x).toReal ≤ C * M := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hUw) (hΛle x hx)
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0'] at this
    have h2 : (Nw x).toReal ≤ M := ENNReal.toReal_mono hUw (hNle x hx)
    have h3 := ENNReal.toReal_nonneg (a := Λ x)
    have h4 := ENNReal.toReal_nonneg (a := Nw x)
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left h2 hg0]
  -- the renewal equation for `ψ`
  have hψeq : ∀ x, 0 ≤ x → x < w → ψ x = f (S - x) - g + ∫ y, ψ (x + y) ∂ρ := by
    intro x hx0 hxw
    have hΛeq : Λ x = ENNReal.ofReal (f (S - x)) + ∫⁻ y, Λ (x + y) ∂ρ := by
      have := renewal_window ρ w hhm x hx0 hxw
      simp only [hΛ]
      convert this using 3
    have hNeq : Nw x = 1 + ∫⁻ y, Nw (x + y) ∂ρ := by
      have := renewal_window ρ w (G := fun _ => (1 : ℝ≥0∞)) measurable_const x hx0 hxw
      simp only [hNw]
      rw [← setLIntegral_one, this]
      simp only [setLIntegral_one]
    have hΛm' : Measurable fun y : ℝ≥0 => Λ (x + y) :=
      hΛm.comp (measurable_const.add measurable_coe_nnreal_real)
    have hNm' : Measurable fun y : ℝ≥0 => Nw (x + y) :=
      hNm.comp (measurable_const.add measurable_coe_nnreal_real)
    have hΛint : (∫⁻ y, Λ (x + y) ∂ρ).toReal = ∫ y, (Λ (x + y)).toReal ∂ρ :=
      (integral_toReal hΛm'.aemeasurable (ae_of_all _ fun y =>
        (hΛfin _ (by positivity)).lt_top)).symm
    have hNint : (∫⁻ y, Nw (x + y) ∂ρ).toReal = ∫ y, (Nw (x + y)).toReal ∂ρ :=
      (integral_toReal hNm'.aemeasurable (ae_of_all _ fun y =>
        (hNfin _ (by positivity)).lt_top)).symm
    have hΛfin' : ∫⁻ y, Λ (x + y) ∂ρ ≠ ∞ := by
      intro htop
      exact hΛfin x hx0 (by rw [hΛeq, htop, add_top])
    have hNfin' : ∫⁻ y, Nw (x + y) ∂ρ ≠ ∞ := by
      intro htop
      exact hNfin x hx0 (by rw [hNeq, htop, add_top])
    have hiΛ : Integrable (fun y : ℝ≥0 => (Λ (x + y)).toReal) ρ := by
      refine Integrable.of_bound hΛm'.ennreal_toReal.aestronglyMeasurable (C * M) (ae_of_all _ ?_)
      intro y
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hUw)
        (hΛle _ (by positivity : (0 : ℝ) ≤ x + y))
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0'] at this
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact this
    have hiN : Integrable (fun y : ℝ≥0 => (Nw (x + y)).toReal) ρ := by
      refine Integrable.of_bound hNm'.ennreal_toReal.aestronglyMeasurable M (ae_of_all _ ?_)
      intro y
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_mono hUw (hNle _ (by positivity))
    have e1 : (Λ x).toReal = f (S - x) + ∫ y, (Λ (x + y)).toReal ∂ρ := by
      rw [hΛeq, ENNReal.toReal_add ENNReal.ofReal_ne_top hΛfin', ENNReal.toReal_ofReal (hf0 _),
        hΛint]
    have e2 : (Nw x).toReal = 1 + ∫ y, (Nw (x + y)).toReal ∂ρ := by
      rw [hNeq, ENNReal.toReal_add ENNReal.one_ne_top hNfin', ENNReal.toReal_one, hNint]
    have e3 : ∫ y, ψ (x + y) ∂ρ
        = ∫ y, (Λ (x + y)).toReal ∂ρ - g * ∫ y, (Nw (x + y)).toReal ∂ρ := by
      simp only [hψ]
      rw [integral_sub hiΛ (hiN.const_mul g), integral_const_mul]
    simp only [hψ] at e3 ⊢
    rw [e3, e1, e2]
    ring
  -- the relative value function and the Poisson equation
  set A := (C + g) * M with hA
  set φ : ℝ → ℝ := fun q => (if q ≤ s then 0 else ψ (S - q)) + A with hφ
  have hφm : Measurable φ := by
    refine Measurable.add ?_ measurable_const
    exact Measurable.ite measurableSet_Iic measurable_const
      (hψm.comp (measurable_const.sub measurable_id))
  have hφbd : ∀ q, q ≤ S → 0 ≤ φ q ∧ φ q ≤ 2 * A := by
    intro q hq
    simp only [hφ]
    split_ifs with h
    · have : 0 ≤ A := by positivity
      constructor <;> linarith
    · have := abs_le.1 (hψb (S - q) (by linarith))
      constructor <;> linarith [this.1, this.2]
  have hshift : ∀ (x : ℝ) (y : ℝ≥0), 0 ≤ x → x < w →
      φ (S - x - (y : ℝ)) = ψ (x + y) + A := by
    intro x y hx0 hxw
    simp only [hφ]
    split_ifs with h
    · rw [hψw (x + y) (by rw [hw]; linarith)]
    · congr 1
      ring_nf
  have hpoisson : ∀ p, p ≤ S → K * (if p ≤ s then 1 else 0) + f (postF s S p)
      + ∫ y, φ (postF s S p - (y : ℝ)) ∂ρ = g + φ p := by
    intro p hp
    by_cases hps : p ≤ s
    · have hpost : postF s S p = S := by simp [postF, hps]
      have hint : ∫ y, φ (postF s S p - (y : ℝ)) ∂ρ = ∫ y, ψ (0 + y) ∂ρ + A := by
        rw [hpost]
        have : ∀ y : ℝ≥0, φ (S - (y : ℝ)) = ψ (0 + y) + A := fun y => by
          have := hshift 0 y le_rfl hw0
          rwa [sub_zero] at this
        simp_rw [this]
        rw [integral_add _ (integrable_const A), integral_const, probReal_univ, one_smul]
        refine Integrable.of_bound
          ((hψm.comp (measurable_const.add measurable_coe_nnreal_real)).aestronglyMeasurable)
          ((C + g) * M) (ae_of_all _ fun y => ?_)
        rw [Real.norm_eq_abs]
        exact hψb _ (by positivity)
      have he := hψeq 0 le_rfl hw0
      rw [hint, hpost]
      simp only [hφ, if_pos hps]
      rw [sub_zero] at he
      linarith [hψ0]
    · have hpost : postF s S p = p := by simp [postF, hps]
      have hx0 : 0 ≤ S - p := by linarith
      have hxw : S - p < w := by rw [hw]; linarith [lt_of_not_ge hps]
      have hint : ∫ y, φ (postF s S p - (y : ℝ)) ∂ρ = ∫ y, ψ ((S - p) + y) ∂ρ + A := by
        rw [hpost]
        have : ∀ y : ℝ≥0, φ (p - (y : ℝ)) = ψ ((S - p) + y) + A := fun y => by
          have := hshift (S - p) y hx0 hxw
          rwa [sub_sub_cancel] at this
        simp_rw [this]
        rw [integral_add _ (integrable_const A), integral_const, probReal_univ, one_smul]
        refine Integrable.of_bound
          ((hψm.comp (measurable_const.add measurable_coe_nnreal_real)).aestronglyMeasurable)
          ((C + g) * M) (ae_of_all _ fun y => ?_)
        rw [Real.norm_eq_abs]
        exact hψb _ (by positivity)
      have he := hψeq (S - p) hx0 hxw
      rw [hint, hpost]
      simp only [hφ, if_neg hps]
      rw [sub_sub_cancel] at he
      linarith
  -- the main identity, by induction over the horizon
  have hmain : ∀ T : ℕ, ∀ p, p ≤ S →
      VG ρ f K s S T p + WG ρ φ s S T p = ENNReal.ofReal (T * g + φ p) := by
    intro T
    induction T with
    | zero =>
      intro p hp
      rw [VG_zero, WG_zero, zero_add]
      simp
    | succ T ih =>
      intro p hp
      have hq : ∀ y : ℝ≥0, postF s S p - (y : ℝ) ≤ S := fun y => by
        linarith [postF_le s S p hp, NNReal.coe_nonneg y]
      have hcost0 : 0 ≤ K * (if p ≤ s then 1 else 0) + f (postF s S p) := by
        have : 0 ≤ K * (if p ≤ s then (1 : ℝ) else 0) := mul_nonneg hK (by split_ifs <;> norm_num)
        linarith [hf0 (postF s S p)]
      have hint : Integrable (fun y : ℝ≥0 => (T : ℝ) * g + φ (postF s S p - (y : ℝ))) ρ := by
        refine (integrable_const _).add (Integrable.of_bound (hφm.comp (measurable_const.sub
          measurable_coe_nnreal_real)).aestronglyMeasurable (2 * A) (ae_of_all _ fun y => ?_))
        rw [Real.norm_eq_abs, abs_of_nonneg (hφbd _ (hq y)).1]
        exact (hφbd _ (hq y)).2
      rw [VG_succ ρ f hf K s S T p, WG_succ ρ φ hφm s S T p, add_assoc,
        ← lintegral_add_left (f := fun y : ℝ≥0 => VG ρ f K s S T (postF s S p - (y : ℝ)))
          ((measurable_VG ρ f hf K s S T).comp (measurable_const.sub measurable_coe_nnreal_real))]
      rw [lintegral_congr fun y => ih _ (hq y),
        ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y =>
          add_nonneg (by positivity) (hφbd _ (hq y)).1),
        ← ENNReal.ofReal_add hcost0 (integral_nonneg fun y =>
          add_nonneg (by positivity) (hφbd _ (hq y)).1)]
      have hφint : Integrable (fun y : ℝ≥0 => φ (postF s S p - (y : ℝ))) ρ := by
        refine Integrable.of_bound (f := fun y : ℝ≥0 => φ (postF s S p - (y : ℝ)))
          ((hφm.comp (measurable_const.sub measurable_coe_nnreal_real)).aestronglyMeasurable)
          (2 * A) (ae_of_all _ fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hφbd _ (hq y)).1]
        exact (hφbd _ (hq y)).2
      congr 1
      rw [integral_add (integrable_const _) hφint, integral_const, probReal_univ, one_smul]
      have := hpoisson p hp
      push_cast
      linarith
  -- the long-run average
  have hconv : Tendsto (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * VG ρ f K s S T S) atTop
      (𝓝 (ENNReal.ofReal g)) := by
    have hφS := hφbd S le_rfl
    have hup : Tendsto (fun T : ℕ => ENNReal.ofReal (g + φ S / T)) atTop (𝓝 (ENNReal.ofReal g)) := by
      have := (tendsto_const_nhds (x := g)).add (tendsto_const_div_atTop_nhds_zero_nat (φ S))
      rw [add_zero] at this
      exact ENNReal.tendsto_ofReal this
    have hlo : Tendsto (fun T : ℕ => ENNReal.ofReal (g + (φ S - 2 * A) / T)) atTop
        (𝓝 (ENNReal.ofReal g)) := by
      have := (tendsto_const_nhds (x := g)).add
        (tendsto_const_div_atTop_nhds_zero_nat (φ S - 2 * A))
      rw [add_zero] at this
      exact ENNReal.tendsto_ofReal this
    have hdiv : ∀ T : ℕ, 1 ≤ T → ∀ a : ℝ,
        (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal a = ENNReal.ofReal (a / T) := by
      intro T hT a
      have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
      rw [ENNReal.ofReal_div_of_pos hTpos, ENNReal.ofReal_natCast, ENNReal.div_eq_inv_mul]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with T hT
      have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
      have hW : WG ρ φ s S T S ≤ ENNReal.ofReal (2 * A) := by
        calc WG ρ φ s S T S ≤ ∫⁻ _z, ENNReal.ofReal (2 * A) ∂(Measure.pi fun _ : Fin T => ρ) :=
              lintegral_mono fun z => ENNReal.ofReal_le_ofReal
                (hφbd _ (preG_le s S S le_rfl _ T)).2
          _ = ENNReal.ofReal (2 * A) := by rw [lintegral_const, measure_univ, mul_one]
      have hV : ENNReal.ofReal (T * g + φ S - 2 * A) ≤ VG ρ f K s S T S := by
        rw [ENNReal.ofReal_sub _ (by positivity : (0 : ℝ) ≤ 2 * A), ← hmain T S le_rfl]
        calc VG ρ f K s S T S + WG ρ φ s S T S - ENNReal.ofReal (2 * A)
            ≤ VG ρ f K s S T S + ENNReal.ofReal (2 * A) - ENNReal.ofReal (2 * A) :=
              tsub_le_tsub_right (add_le_add le_rfl hW) _
          _ = VG ρ f K s S T S := ENNReal.add_sub_cancel_right ENNReal.ofReal_ne_top
      calc ENNReal.ofReal (g + (φ S - 2 * A) / T)
          = (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal (T * g + φ S - 2 * A) := by
            rw [hdiv T hT]
            congr 1
            field_simp
            ring
        _ ≤ (T : ℝ≥0∞)⁻¹ * VG ρ f K s S T S := mul_le_mul_of_nonneg_left hV (by positivity)
    · filter_upwards [eventually_ge_atTop 1] with T hT
      have hV : VG ρ f K s S T S ≤ ENNReal.ofReal (T * g + φ S) := by
        rw [← hmain T S le_rfl]
        exact le_self_add
      calc (T : ℝ≥0∞)⁻¹ * VG ρ f K s S T S
          ≤ (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal (T * g + φ S) := mul_le_mul_of_nonneg_left hV (by positivity)
        _ = ENNReal.ofReal (g + φ S / T) := by
            rw [hdiv T hT]
            congr 1
            have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
            field_simp
  -- identify the average cost of the `(s,S)` policy
  have hss : (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * ∫⁻ z, ∑ t ∈ Finset.range T,
      ENNReal.ofReal (ssPeriodCost f K s S (padHist T z) t) ∂(Measure.pi fun _ : Fin T => ρ))
      = fun T : ℕ => (T : ℝ≥0∞)⁻¹ * VG ρ f K s S T S := by
    funext T
    simp only [VG, ssPeriodCost_eq f K s S hsS]
  unfold ssAvgCost
  rw [hss, hconv.limsup_eq]
