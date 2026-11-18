-- Prove2me | solution 1 for OWMR.sl_subsolution
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T04:28:10.716471+00:00
-- url     : https://prove2.me/submissions/c3e0c814-62e4-482d-b81c-8a90ab10de31

import Theorems.Thm_OWMR_sl_adapted_bound
import Theorems.Thm_OWMR_ss_renewal_reward
import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.ENNReal
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
Lemma 1 for the single-location problem: the value `J = 𝒥_D(f;K)` is attained by `(s,S)` cycles,
and there is a bounded relative value `v` with `-K ≤ v ≤ 0` and

  `J + (f(y) - J)⁺ ≤ f(y) + 𝔼 v(y - D) - v(y)`   for all `y`.

The proof is a direct (Zheng-type) construction, with no discounting or compactness argument.

* `J` is the infimum over `s < S`, `0 ≤ S`, of the closed-form cycle average
  `c(s,S) = (K + ∫_{[0,S-s)} f(S-x) U(dx)) / U[0,S-s)` (renewal measure `U`).
  The `(s,S)` policy started by one order from position `0` has average cost `c(s,S)`
  (`ss_renewal_reward`), so `𝒥 ≤ J`.
* If `f < J` somewhere, `{f < J}` is an interval `(a,b)` (convexity, continuity, coercivity), and
  `k(y) = K + ∫_{[0,y-a)} (f(y-z) - J) U(dz)` solves the Poisson equation
  `k(y) = f(y) - J + 𝔼 k(y - D)` for `y > a` (renewal equation `U = δ₀ + ρ * U`).
  On `(a,b)`, `0 ≤ k ≤ K`: the upper bound because `f < J` there, the lower bound because
  `k(y) = U[0,y-a) (c(a,y) - J)` and `J ≤ c(a,y)` (for `y < 0` after the shift to `S = 0`, using
  that `f` is nonincreasing on `(-∞,0]`). With `v = 0` on `(-∞,a]`, `k - K` on `(a,b)` and `-K`
  on `[b,∞)`, the inequality holds with equality on `(a,b)` and from `f ≥ J` elsewhere.
* The finite-horizon bound `sl_adapted_bound` for every admissible policy gives `J ≤ 𝒥`.
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



/-- If `v → 0`, then `limsup (u + v) ≤ limsup u` in `ℝ≥0∞`. -/
private lemma limsup_add_tendsto_zero (u v : ℕ → ℝ≥0∞) (hv : Tendsto v atTop (𝓝 0)) :
    limsup (fun n => u n + v n) atTop ≤ limsup u atTop := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  have hev : ∀ᶠ n in atTop, u n + v n ≤ u n + ε :=
    (hv.eventually (ge_mem_nhds hε')).mono fun n hn => add_le_add le_rfl hn
  calc limsup (fun n => u n + v n) atTop ≤ limsup (fun n => u n + (ε : ℝ≥0∞)) atTop :=
        limsup_le_limsup hev
    _ = limsup u atTop + ε :=
        limsup_add_const atTop u _ (by isBoundedDefault) (by isBoundedDefault)

/-! ### The `(s,S)` policy started by one order from position `0` -/

private lemma ssPre_dep (s S : ℝ) : ∀ (t : ℕ) (d d' : ℕ → ℝ≥0), (∀ r < t, d r = d' r) →
    ssPre s S d t = ssPre s S d' t
  | 0, _, _, _ => rfl
  | t + 1, d, d', h => by
    show (if ssPre s S d t ≤ s then S else ssPre s S d t) - (d t : ℝ)
      = (if ssPre s S d' t ≤ s then S else ssPre s S d' t) - (d' t : ℝ)
    rw [ssPre_dep s S t d d' (fun r hr => h r (by omega)), h t (by omega)]

private lemma measurable_ssPre (s S : ℝ) : ∀ t, Measurable fun d : ℕ → ℝ≥0 => ssPre s S d t
  | 0 => measurable_const
  | t + 1 => by
    have ih := measurable_ssPre s S t
    show Measurable fun d : ℕ → ℝ≥0 =>
      (if ssPre s S d t ≤ s then S else ssPre s S d t) - (d t : ℝ)
    exact (Measurable.ite (measurableSet_le ih measurable_const) measurable_const ih).sub
      (measurable_pi_apply t).coe_nnreal_real

/-- Order up to `S` in period `0`, then follow the `(s,S)` rule. -/
private noncomputable def ssPolicy (s S : ℝ) : SLPolicy Unit :=
  fun t _ d => if t = 0 then S else if ssPre s S d t ≤ s then S - ssPre s S d t else 0

private lemma slPos_ssPolicy (s S : ℝ) (d : ℕ → ℝ≥0) :
    ∀ t, slPos 0 (ssPolicy s S) () d t = ssPost s S d t
  | 0 => by
    have h0 : ssPost s S d 0 = S := by
      unfold ssPost
      split_ifs <;> rfl
    rw [h0]
    simp [slPos, ssPolicy]
  | t + 1 => by
    have ih := slPos_ssPolicy s S d t
    have h1 : slPos 0 (ssPolicy s S) () d (t + 1)
        = slPos 0 (ssPolicy s S) () d t + ssPolicy s S (t + 1) () d - (d t : ℝ) := by
      simp only [slPos, Finset.sum_range_succ]
      ring
    have h2 : ssPre s S d (t + 1) = ssPost s S d t - (d t : ℝ) := rfl
    have h3 : ssPost s S d (t + 1)
        = if ssPre s S d (t + 1) ≤ s then S else ssPre s S d (t + 1) := rfl
    have h4 : ssPolicy s S (t + 1) () d
        = if ssPre s S d (t + 1) ≤ s then S - ssPre s S d (t + 1) else 0 := by
      simp [ssPolicy]
    rw [h1, ih, h3, h4, h2]
    split_ifs <;> ring

private lemma ssPolicy_cost (f : ℝ → ℝ) (K s S : ℝ) (hK : 0 ≤ K) (d : ℕ → ℝ≥0) (t : ℕ) :
    slPeriodCost f K 0 (ssPolicy s S) () d t
      ≤ ssPeriodCost f K s S d t + (if t = 0 then K else 0) := by
  unfold slPeriodCost ssPeriodCost
  rw [slPos_ssPolicy]
  by_cases ht : t = 0
  · subst ht
    simp only [if_true]
    have : K * (if 0 < ssPolicy s S 0 () d then (1 : ℝ) else 0) ≤ K := by
      split_ifs <;> linarith
    have : 0 ≤ K * (if ssPre s S d 0 ≤ s ∧ ssPre s S d 0 < S then (1 : ℝ) else 0) := by
      split_ifs <;> linarith
    linarith
  · simp only [ht, if_false, add_zero]
    have hq : ssPolicy s S t () d
        = if ssPre s S d t ≤ s then S - ssPre s S d t else 0 := by simp [ssPolicy, ht]
    rw [hq]
    by_cases h1 : ssPre s S d t ≤ s
    · by_cases h2 : ssPre s S d t < S
      · simp [h1, h2]
      · have : ¬ (0 < S - ssPre s S d t) := by linarith
        simp only [h1, if_true, this, if_false, mul_zero, true_and, h2]
        linarith
    · simp only [h1, if_false, lt_irrefl, false_and]
      linarith

/-- The `(s,S)` average cost bounds the value (for `0 ≤ S`). -/
private lemma slValue_le_ss (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ)
    (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) (K s S : ℝ) (hK : 0 ≤ K) (hsS : s < S)
    (hS : 0 ≤ S) : slValue ρ f K ≤ ssAvgCost ρ f K s S := by
  have hadm : SLAdmissible (ssPolicy s S) := by
    refine ⟨fun t u d d' h => ?_, fun t => ?_, fun t u d => ?_⟩
    · simp only [ssPolicy]
      rw [ssPre_dep s S t d d' h]
    · simp only [ssPolicy]
      by_cases ht : t = 0
      · simp only [ht, if_true]
        exact measurable_const
      · simp only [ht, if_false]
        have hm : Measurable fun ω : Unit × (ℕ → ℝ≥0) => ssPre s S ω.2 t :=
          (measurable_ssPre s S t).comp measurable_snd
        exact Measurable.ite (measurableSet_le hm measurable_const) (measurable_const.sub hm)
          measurable_const
    · simp only [ssPolicy]
      split_ifs with h1 h2
      · exact hS
      · linarith
      · exact le_rfl
  have h1 : slValue ρ f K ≤ slAvgCost ρ f K 0 (ssPolicy s S) (Measure.dirac ()) := by
    unfold slValue
    exact iInf_le_of_le Unit (iInf_le_of_le inferInstance (iInf_le_of_le (Measure.dirac ())
      (iInf_le_of_le inferInstance (iInf_le_of_le (ssPolicy s S) (iInf_le_of_le hadm le_rfl)))))
  refine h1.trans ?_
  unfold slAvgCost ssAvgCost
  set Iss : ℕ → ℝ≥0∞ := fun T => ∫⁻ z, ∑ t ∈ Finset.range T,
    ENNReal.ofReal (ssPeriodCost f K s S (padHist T z) t) ∂(Measure.pi fun _ : Fin T => ρ)
    with hIss
  have hT : ∀ T : ℕ, ∫⁻ ω, ∑ t ∈ Finset.range T, ENNReal.ofReal
      (slPeriodCost f K 0 (ssPolicy s S) ω.1 (padHist T ω.2) t)
        ∂((Measure.dirac ()).prod (Measure.pi fun _ : Fin T => ρ)) ≤ Iss T + ENNReal.ofReal K := by
    intro T
    rw [Measure.dirac_prod]
    refine (lintegral_map_le _ _).trans ?_
    have hm : Measurable fun z : Fin T → ℝ≥0 => ∑ t ∈ Finset.range T,
        ENNReal.ofReal (ssPeriodCost f K s S (padHist T z) t) := by
      refine Finset.measurable_sum _ fun t _ => ENNReal.measurable_ofReal.comp ?_
      have hp : Measurable fun z : Fin T → ℝ≥0 => padHist T z := by
        refine measurable_pi_lambda _ fun r => ?_
        by_cases h : r < T
        · simp only [padHist, dif_pos h]
          exact measurable_pi_apply _
        · simp only [padHist, dif_neg h]
          exact measurable_const
      have hpre := (measurable_ssPre s S t).comp hp
      unfold ssPeriodCost ssPost
      exact (measurable_const.mul (Measurable.ite ((measurableSet_le hpre measurable_const).inter
        (measurableSet_lt hpre measurable_const)) measurable_const measurable_const)).add
        (hf.comp (Measurable.ite (measurableSet_le hpre measurable_const) measurable_const hpre))
    rw [hIss]
    simp only
    have hcK : ∫⁻ z, (∑ t ∈ Finset.range T, ENNReal.ofReal (ssPeriodCost f K s S (padHist T z) t)
        + ENNReal.ofReal K) ∂(Measure.pi fun _ : Fin T => ρ)
        = ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal (ssPeriodCost f K s S (padHist T z) t)
          ∂(Measure.pi fun _ : Fin T => ρ) + ENNReal.ofReal K := by
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    rw [← hcK]
    refine lintegral_mono fun z => ?_
    calc ∑ t ∈ Finset.range T, ENNReal.ofReal
            (slPeriodCost f K 0 (ssPolicy s S) () (padHist T z) t)
        ≤ ∑ t ∈ Finset.range T, (ENNReal.ofReal (ssPeriodCost f K s S (padHist T z) t)
            + (if t = 0 then ENNReal.ofReal K else 0)) := by
          refine Finset.sum_le_sum fun t _ => ?_
          have hc0 : 0 ≤ ssPeriodCost f K s S (padHist T z) t := by
            unfold ssPeriodCost
            have : 0 ≤ K * (if ssPre s S (padHist T z) t ≤ s ∧ ssPre s S (padHist T z) t < S
              then (1 : ℝ) else 0) := by split_ifs <;> linarith
            linarith [hf0 (ssPost s S (padHist T z) t)]
          calc ENNReal.ofReal (slPeriodCost f K 0 (ssPolicy s S) () (padHist T z) t)
              ≤ ENNReal.ofReal (ssPeriodCost f K s S (padHist T z) t + (if t = 0 then K else 0)) :=
                ENNReal.ofReal_le_ofReal (ssPolicy_cost f K s S hK _ t)
            _ = _ := by
                rw [ENNReal.ofReal_add hc0 (by split_ifs <;> linarith)]
                split_ifs <;> simp
      _ = ∑ t ∈ Finset.range T, ENNReal.ofReal (ssPeriodCost f K s S (padHist T z) t)
            + ∑ t ∈ Finset.range T, (if t = 0 then ENNReal.ofReal K else 0) :=
          Finset.sum_add_distrib
      _ ≤ _ := by
          gcongr
          rw [Finset.sum_ite_eq']
          split_ifs <;> simp
  have h0 : Tendsto (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal K) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.ofReal_ne_top (r := K)))
    simpa using this
  calc limsup (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * ∫⁻ ω, ∑ t ∈ Finset.range T, ENNReal.ofReal
          (slPeriodCost f K 0 (ssPolicy s S) ω.1 (padHist T ω.2) t)
            ∂((Measure.dirac ()).prod (Measure.pi fun _ : Fin T => ρ))) atTop
      ≤ limsup (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * Iss T + (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal K) atTop := by
        refine limsup_le_limsup (Eventually.of_forall fun T => ?_)
        dsimp only
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (hT T) (by positivity)
    _ ≤ limsup (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * Iss T) atTop :=
        limsup_add_tendsto_zero _ _ h0

theorem solution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (f : ℝ → ℝ) (hfc : Continuous f)
    (hfcv : ConvexOn ℝ Set.univ f) (hf0 : ∀ y, 0 ≤ f y)
    (hfco : ∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ f y)
    (hfa : AntitoneOn f (Set.Iic 0)) (K : ℝ) (hK : 0 ≤ K) :
    ∃ J : ℝ, 0 ≤ J ∧ slValue ρ f K = ENNReal.ofReal J ∧
      ∃ v : ℝ → ℝ, Measurable v ∧ (∀ y, -K ≤ v y ∧ v y ≤ 0) ∧
        ∀ y, J + max (f y - J) 0 ≤ f y + ∫ d, v (y - (d : ℝ)) ∂ρ - v y := by
  have hSF : SFinite (renewalMeasure ρ) := by unfold renewalMeasure; infer_instance
  have hfm : Measurable f := hfc.measurable
  -- the closed-form cycle average of the `(s,S)` policy
  set cyc : ℝ → ℝ → ℝ := fun s S =>
    (K + ∫ x in Set.Ico 0 (S - s), f (S - x) ∂(renewalMeasure ρ))
      / (renewalMeasure ρ (Set.Ico 0 (S - s))).toReal with hcyc
  have hcyc0 : ∀ s S, 0 ≤ cyc s S := fun s S =>
    div_nonneg (add_nonneg hK (setIntegral_nonneg measurableSet_Ico fun x _ => hf0 _))
      ENNReal.toReal_nonneg
  set ι := {p : ℝ × ℝ // p.1 < p.2 ∧ 0 ≤ p.2} with hι
  have : Nonempty ι := ⟨⟨(-1, 0), by norm_num⟩⟩
  set J : ℝ := ⨅ p : ι, cyc p.1.1 p.1.2 with hJdef
  have hbdd : BddBelow (Set.range fun p : ι => cyc p.1.1 p.1.2) :=
    ⟨0, by rintro _ ⟨p, rfl⟩; exact hcyc0 _ _⟩
  have hJ0 : 0 ≤ J := le_ciInf fun p => hcyc0 _ _
  have hJle : ∀ s S, s < S → 0 ≤ S → J ≤ cyc s S := fun s S h1 h2 =>
    ciInf_le hbdd (⟨(s, S), h1, h2⟩ : ι)
  -- `𝒥 ≤ c(s,S)` for every admissible pair, hence `𝒥 ≤ J`
  have hval_le : ∀ s S, s < S → 0 ≤ S → slValue ρ f K ≤ ENNReal.ofReal (cyc s S) := by
    intro s S hsS hS
    have hfb : ∃ C, ∀ y ∈ Set.Icc s S, f y ≤ C := by
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc.continuousOn
      exact ⟨C, fun y hy => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC y hy)⟩
    calc slValue ρ f K ≤ ssAvgCost ρ f K s S := slValue_le_ss ρ f hfm hf0 K s S hK hsS hS
      _ = ENNReal.ofReal (cyc s S) := ss_renewal_reward ρ hρ f hfm hf0 K s S hK hsS hfb
  have hval_le_J : slValue ρ f K ≤ ENNReal.ofReal J := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hlt : J < J + ε := by simpa using (show (0 : ℝ) < ε from hε)
    obtain ⟨p, hp⟩ := exists_lt_of_ciInf_lt hlt
    calc slValue ρ f K ≤ ENNReal.ofReal (cyc p.1.1 p.1.2) := hval_le _ _ p.2.1 p.2.2
      _ ≤ ENNReal.ofReal (J + ε) := ENNReal.ofReal_le_ofReal hp.le
      _ = ENNReal.ofReal J + ε := by
          rw [ENNReal.ofReal_add hJ0 (NNReal.coe_nonneg ε), ENNReal.ofReal_coe_nnreal]
  -- the bounded relative value
  obtain ⟨v, hvm, hvb, hvsub⟩ : ∃ v : ℝ → ℝ, Measurable v ∧ (∀ y, -K ≤ v y ∧ v y ≤ 0) ∧
      ∀ y, J + max (f y - J) 0 ≤ f y + ∫ d, v (y - (d : ℝ)) ∂ρ - v y := by
    by_cases hA : ∀ y, J ≤ f y
    · refine ⟨fun _ => 0, measurable_const, fun y => ⟨by linarith, le_rfl⟩, fun y => ?_⟩
      have h1 : max (f y - J) 0 = f y - J := max_eq_left (by linarith [hA y])
      simp only [integral_zero, sub_zero, add_zero, h1]
      linarith
    simp only [not_forall, not_le] at hA
    obtain ⟨y0, hy0⟩ := hA
    -- the interval `{f < J} = (a, b)`
    set A : Set ℝ := {y | f y < J} with hAdef
    obtain ⟨R, hR⟩ := hfco J
    have hAR : ∀ y ∈ A, |y| < R := fun y hy => by
      by_contra h
      exact absurd (hR y (not_lt.1 h)) (not_le.2 hy)
    have hAne : A.Nonempty := ⟨y0, hy0⟩
    have hAbb : BddBelow A := ⟨-R, fun y hy => by
      have := hAR y hy
      linarith [neg_abs_le y]⟩
    have hAba : BddAbove A := ⟨R, fun y hy => by
      have := hAR y hy
      linarith [le_abs_self y]⟩
    have hAopen : IsOpen A := isOpen_lt hfc continuous_const
    set a := sInf A with ha
    set b := sSup A with hb
    have ha_notin : a ∉ A := by
      intro haA
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hAopen a haA
      have hmem : a - ε / 2 ∈ A := hball (by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
        linarith)
      have := csInf_le hAbb hmem
      linarith
    have hb_notin : b ∉ A := by
      intro hbA
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hAopen b hbA
      have hmem : b + ε / 2 ∈ A := hball (by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
        linarith)
      have := le_csSup hAba hmem
      linarith
    have hK1 : ∀ y, y ≤ a → J ≤ f y := by
      intro y hy
      by_contra h
      have hyA : y ∈ A := not_le.1 h
      have hya : y = a := le_antisymm hy (csInf_le hAbb hyA)
      rw [hya] at hyA
      exact ha_notin hyA
    have hK2 : ∀ y, b ≤ y → J ≤ f y := by
      intro y hy
      by_contra h
      have hyA : y ∈ A := not_le.1 h
      have hyb : y = b := le_antisymm (le_csSup hAba hyA) hy
      rw [hyb] at hyA
      exact hb_notin hyA
    have hK3 : ∀ y, a < y → y < b → f y < J := by
      intro y h1 h2
      obtain ⟨y1, hy1A, hy1⟩ := exists_lt_of_csInf_lt hAne h1
      obtain ⟨y2, hy2A, hy2⟩ := exists_lt_of_lt_csSup hAne h2
      exact lt_of_le_of_lt (hfcv.le_max_of_mem_Icc (Set.mem_univ y1) (Set.mem_univ y2)
        ⟨hy1.le, hy2.le⟩) (max_lt hy1A hy2A)
    have hab : a < b := by
      have h1 : a ≤ y0 := csInf_le hAbb hy0
      have h2 : y0 ≤ b := le_csSup hAba hy0
      have h3 : a ≠ y0 := fun h => ha_notin (h ▸ hy0)
      exact lt_of_lt_of_le (lt_of_le_of_ne h1 h3) h2
    -- the expected cost and count of the periods before the position falls to `a`
    have hUfin : ∀ w, renewalMeasure ρ (Set.Ico 0 w) ≠ ∞ := fun w =>
      (renewalMeasure_Ico_lt_top ρ hρ w).ne
    set Λ : ℝ → ℝ≥0∞ := fun y => ∫⁻ z in Set.Ico 0 (y - a), ENNReal.ofReal (f (y - z))
      ∂(renewalMeasure ρ) with hΛ
    set Nw : ℝ → ℝ≥0∞ := fun y => renewalMeasure ρ (Set.Ico 0 (y - a)) with hNw
    have hΛm : Measurable Λ := by
      have : Λ = fun y => ∫⁻ z, ({p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 < p.1 - a}.indicator
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
      have : Nw = fun y => ∫⁻ z, ({p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 < p.1 - a}.indicator 1) (y, z)
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
    have hCbd : ∀ y, ∃ C, 0 ≤ C ∧ ∀ x ∈ Set.Icc a y, f x ≤ C := fun y => by
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := y)).exists_bound_of_continuousOn
        hfc.continuousOn
      refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
      have h1 : |f x| ≤ C := by simpa [Real.norm_eq_abs] using hC x hx
      exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
    have hNle : ∀ y y', y' ≤ y → Nw y' ≤ Nw y := fun y y' h =>
      measure_mono (Set.Ico_subset_Ico_right (by linarith))
    have hΛle : ∀ y y' C, y' ≤ y → (∀ x ∈ Set.Icc a y, f x ≤ C) → 0 ≤ C →
        Λ y' ≤ ENNReal.ofReal C * Nw y := by
      intro y y' C hy hC hC0
      calc Λ y' ≤ ∫⁻ _z in Set.Ico 0 (y' - a), ENNReal.ofReal C ∂(renewalMeasure ρ) := by
            refine setLIntegral_mono' measurableSet_Ico fun z hz => ENNReal.ofReal_le_ofReal ?_
            exact hC _ ⟨by linarith [hz.2], by linarith [hz.1]⟩
        _ = ENNReal.ofReal C * Nw y' := setLIntegral_const _ _
        _ ≤ ENNReal.ofReal C * Nw y := by gcongr; exact hNle y y' hy
    have hNfin : ∀ y, Nw y ≠ ∞ := fun y => hUfin _
    have hΛfin : ∀ y, Λ y ≠ ∞ := fun y => by
      obtain ⟨C, hC0, hC⟩ := hCbd y
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hNfin y))
        (hΛle y y C le_rfl hC hC0)
    -- the relative value `k(y) = K + ∫_{[0,y-a)} (f(y-z) - J) U(dz)`
    set kk : ℝ → ℝ := fun y => K + (Λ y).toReal - J * (Nw y).toReal with hkk
    have hkkm : Measurable kk :=
      (measurable_const.add hΛm.ennreal_toReal).sub (measurable_const.mul hNm.ennreal_toReal)
    have hkk_le : ∀ y, y ≤ a → kk y = K := by
      intro y hy
      have he : Set.Ico (0 : ℝ) (y - a) = ∅ := Set.Ico_eq_empty (by linarith)
      simp only [hkk, hΛ, hNw, he, Measure.restrict_empty, lintegral_zero_measure, measure_empty,
        ENNReal.toReal_zero, mul_zero, add_zero, sub_zero]
    have hkk_upper : ∀ y, a < y → y < b → kk y ≤ K := by
      intro y h1 h2
      have hle : Λ y ≤ ENNReal.ofReal J * Nw y := by
        calc Λ y ≤ ∫⁻ _z in Set.Ico 0 (y - a), ENNReal.ofReal J ∂(renewalMeasure ρ) := by
              refine setLIntegral_mono' measurableSet_Ico fun z hz => ENNReal.ofReal_le_ofReal ?_
              exact (hK3 _ (by linarith [hz.2]) (by linarith [hz.1])).le
          _ = ENNReal.ofReal J * Nw y := setLIntegral_const _ _
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hNfin y)) hle
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hJ0] at this
      simp only [hkk]
      linarith
    have hNpos : ∀ y, a < y → 1 ≤ (Nw y).toReal := by
      intro y hy
      have := ENNReal.toReal_mono (hNfin y) (one_le_renewal ρ (y - a) (by linarith))
      simpa using this
    have hInt : ∀ y, (∫ x in Set.Ico 0 (y - a), f (y - x) ∂(renewalMeasure ρ)) = (Λ y).toReal := by
      intro y
      rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => f (y - x)) (ae_of_all _ fun x => hf0 _)
        (hfm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable]
    have hkk_nonneg : ∀ y, a < y → 0 ≤ kk y := by
      intro y hy
      have hJc : J ≤ (K + (Λ y).toReal) / (Nw y).toReal := by
        rcases le_or_gt 0 y with hy0 | hy0
        · have := hJle a y hy hy0
          simp only [hcyc] at this
          rwa [hInt y] at this
        · -- shift the cycle up to the target `0`
          have h0 := hJle (a - y) 0 (by linarith) le_rfl
          simp only [hcyc] at h0
          have hw : (0 : ℝ) - (a - y) = y - a := by ring
          rw [hw] at h0
          refine h0.trans (div_le_div_of_nonneg_right ?_ ENNReal.toReal_nonneg)
          have hmono : ∫⁻ z in Set.Ico 0 (y - a), ENNReal.ofReal (f (0 - z)) ∂(renewalMeasure ρ)
              ≤ Λ y := by
            refine setLIntegral_mono' measurableSet_Ico fun z hz => ENNReal.ofReal_le_ofReal ?_
            have hz0 : 0 ≤ z := hz.1
            exact hfa (show y - z ∈ Set.Iic 0 by simp only [Set.mem_Iic]; linarith)
              (show 0 - z ∈ Set.Iic 0 by simp only [Set.mem_Iic]; linarith) (by linarith)
          have := ENNReal.toReal_mono (hΛfin y) hmono
          rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => f (0 - x))
            (ae_of_all _ fun x => hf0 _)
            (hfm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable]
          linarith
      have hNp := hNpos y hy
      rw [le_div_iff₀ (by linarith)] at hJc
      simp only [hkk]
      linarith
    -- the renewal equations
    have hΛeq : ∀ y, a < y → Λ y = ENNReal.ofReal (f y) + ∫⁻ d, Λ (y - d) ∂ρ := by
      intro y hy
      have hG : Measurable fun z : ℝ => ENNReal.ofReal (f (y - z)) :=
        ENNReal.measurable_ofReal.comp (hfm.comp (measurable_const.sub measurable_id))
      have h := renewal_window ρ (y - a) hG 0 le_rfl (by linarith)
      simp only [sub_zero, zero_add] at h
      simp only [hΛ]
      rw [h]
      congr 1
      refine lintegral_congr fun d => ?_
      rw [show y - (d : ℝ) - a = y - a - d by ring]
      refine lintegral_congr fun u => ?_
      rw [show y - ((d : ℝ) + u) = y - d - u by ring]
    have hNeq : ∀ y, a < y → Nw y = 1 + ∫⁻ d, Nw (y - d) ∂ρ := by
      intro y hy
      have h := renewal_window ρ (y - a) (G := fun _ => (1 : ℝ≥0∞)) measurable_const 0 le_rfl
        (by linarith)
      simp only [sub_zero, zero_add, setLIntegral_one] at h
      simp only [hNw]
      rw [h]
      congr 1
      refine lintegral_congr fun d => ?_
      rw [show y - (d : ℝ) - a = y - a - d by ring]
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
    have hikk : ∀ y, Integrable (fun d : ℝ≥0 => kk (y - d)) ρ := fun y =>
      ((integrable_const K).add (hiΛ y)).sub ((hiN y).const_mul J)
    have hkkeq : ∀ y, a < y → kk y = f y - J + ∫ d, kk (y - d) ∂ρ := by
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
      have e3 : ∫ d, kk (y - d) ∂ρ
          = K + ∫ d, (Λ (y - d)).toReal ∂ρ - J * ∫ d, (Nw (y - d)).toReal ∂ρ := by
        simp only [hkk]
        have i1 : Integrable (fun d : ℝ≥0 => K + (Λ (y - d)).toReal) ρ :=
          (integrable_const K).add (hiΛ y)
        have i2 : Integrable (fun d : ℝ≥0 => J * (Nw (y - d)).toReal) ρ := (hiN y).const_mul J
        rw [integral_sub i1 i2, integral_add (integrable_const K) (hiΛ y), integral_const_mul,
          integral_const, probReal_univ, one_smul]
      rw [e3]
      simp only [hkk]
      rw [e1, e2]
      ring
    -- the bounded relative value `v`
    set v : ℝ → ℝ := fun y => if y < b then kk y - K else -K with hv
    have hvm : Measurable v :=
      Measurable.ite measurableSet_Iio (hkkm.sub measurable_const) measurable_const
    have hvb : ∀ y, -K ≤ v y ∧ v y ≤ 0 := by
      intro y
      simp only [hv]
      split_ifs with h
      · rcases le_or_gt y a with h' | h'
        · rw [hkk_le y h']
          constructor <;> linarith
        · have := hkk_nonneg y h'
          have := hkk_upper y h' h
          constructor <;> linarith
      · constructor <;> linarith
    have hvint : ∀ y, Integrable (fun d : ℝ≥0 => v (y - d)) ρ := by
      intro y
      refine Integrable.of_bound (hvm.comp (measurable_const.sub
        measurable_coe_nnreal_real)).aestronglyMeasurable K (ae_of_all _ fun d => ?_)
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨(hvb _).1, by linarith [(hvb (y - (d : ℝ))).2]⟩
    refine ⟨v, hvm, hvb, fun y => ?_⟩
    rcases le_or_gt y a with hya | hya
    · -- at or below `a`: no relative value, and `f ≥ J`
      have hfy := hK1 y hya
      have hv0 : (fun d : ℝ≥0 => v (y - d)) = fun _ => 0 := by
        funext d
        have h1 : y - (d : ℝ) ≤ a := by linarith [NNReal.coe_nonneg d]
        simp only [hv, if_pos (show y - (d : ℝ) < b by linarith), hkk_le _ h1, sub_self]
      have hvy : v y = 0 := by
        simp only [hv, if_pos (show y < b by linarith), hkk_le _ hya, sub_self]
      rw [hv0, integral_zero, hvy, max_eq_left (by linarith)]
      linarith
    rcases lt_or_ge y b with hyb | hyb
    · -- inside `(a, b)`: the Poisson equation gives equality
      have hfy := hK3 y hya hyb
      have hvd : (fun d : ℝ≥0 => v (y - d)) = fun d : ℝ≥0 => kk (y - d) - K := by
        funext d
        simp only [hv, if_pos (show y - (d : ℝ) < b by linarith [NNReal.coe_nonneg d])]
      have hvy : v y = kk y - K := by simp only [hv, if_pos hyb]
      have hI : ∫ d, v (y - (d : ℝ)) ∂ρ = ∫ d, kk (y - d) ∂ρ - K := by
        rw [hvd, integral_sub (hikk y) (integrable_const K), integral_const, probReal_univ,
          one_smul]
      rw [hI, hvy, max_eq_right (by linarith)]
      have := hkkeq y hya
      linarith
    · -- at or above `b`: the relative value is at its minimum `-K`
      have hfy := hK2 y hyb
      have hvy : v y = -K := by simp only [hv, if_neg (not_lt.2 hyb)]
      have hge : -K ≤ ∫ d, v (y - (d : ℝ)) ∂ρ := by
        have := integral_mono (integrable_const (-K)) (hvint y) (fun d => (hvb (y - d)).1)
        simpa [integral_const, probReal_univ] using this
      rw [hvy, max_eq_left (by linarith)]
      linarith
  -- `J ≤ 𝒥`: the finite-horizon bound for every admissible policy
  have hval_ge : ENNReal.ofReal J ≤ slValue ρ f K := by
    unfold slValue
    refine le_iInf fun Ut => le_iInf fun ms => le_iInf fun νt => le_iInf fun hν =>
      le_iInf fun qt => le_iInf fun hadm => ?_
    have hb : ∀ T : ℕ, ENNReal.ofReal (T * J) ≤ ∫⁻ ω, ∑ t ∈ Finset.range T,
        ENNReal.ofReal (slPeriodCost f K 0 qt ω.1 (padHist T ω.2) t)
          ∂(νt.prod (Measure.pi fun _ : Fin T => ρ)) + ENNReal.ofReal K := by
      intro T
      exact sl_adapted_bound ρ νt (fun x => x) measurable_id qt hadm.1 hadm.2.1 hadm.2.2 0 f hfm
        hf0 K J v hvm hvb (fun y => by
          have := hvsub y
          have h2 : J ≤ J + max (f y - J) 0 := le_add_of_nonneg_right (le_max_right _ _)
          exact h2.trans this) T T le_rfl
    unfold slAvgCost
    set I : ℕ → ℝ≥0∞ := fun T => ∫⁻ ω, ∑ t ∈ Finset.range T,
        ENNReal.ofReal (slPeriodCost f K 0 qt ω.1 (padHist T ω.2) t)
          ∂(νt.prod (Measure.pi fun _ : Fin T => ρ)) with hI
    have h1 : ∀ T : ℕ, 1 ≤ T →
        ENNReal.ofReal J ≤ (T : ℝ≥0∞)⁻¹ * I T + (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal K := by
      intro T hT
      rw [← mul_add]
      have hT0 : (T : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
      calc ENNReal.ofReal J = (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal (T * J) := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← mul_assoc,
              ENNReal.inv_mul_cancel hT0 (ENNReal.natCast_ne_top T), one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hb T) (by positivity)
    have h0 : Tendsto (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal K) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero
        (Or.inr (ENNReal.ofReal_ne_top (r := K)))
      simpa using this
    calc ENNReal.ofReal J = limsup (fun _ : ℕ => ENNReal.ofReal J) atTop :=
          (limsup_const (ENNReal.ofReal J)).symm
      _ ≤ limsup (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * I T + (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal K) atTop :=
          limsup_le_limsup (eventually_atTop.2 ⟨1, h1⟩)
      _ ≤ limsup (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * I T) atTop :=
          limsup_add_tendsto_zero _ _ h0
  exact ⟨J, hJ0, le_antisymm hval_le_J hval_ge, v, hvm, hvb, hvsub⟩
