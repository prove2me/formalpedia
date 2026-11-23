-- Prove2me | solution 1 for OptStochMatch.Tight.theorem_3_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:55:33.434019+00:00
-- url     : https://prove2.me/submissions/d06024f0-b581-4385-813c-17a7346aaab0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Laws
import Theorems.Thm_OptStochMatch_Tight_lemma_3_2
import Theorems.Thm_OptStochMatch_Tight_proposition_3_5

namespace AuxThm31

open MeasureTheory ProbabilityTheory Set Filter OptStochMatch.Tight
open scoped NNReal ENNReal BigOperators Topology

lemma expOne_real_Iic (x : ℝ) :
    expOne.real (Iic x) = if 0 ≤ x then 1 - Real.exp (-x) else 0 := by
  rw [← cdf_eq_real]
  change (cdf (expMeasure 1)) x = _
  simpa using cdf_expMeasure_eq (r := 1) (by norm_num) x

lemma expOne_ae_pos : ∀ᵐ e ∂expOne, 0 < e := by
  rw [ae_iff]
  have hset : {e : ℝ | ¬ 0 < e} = Iic 0 := by ext e; simp
  rw [hset]
  apply (measureReal_eq_zero_iff (s := Iic 0)).mp
  simp [expOne_real_Iic]

lemma expOne_Ioi {u : ℝ} (hu : 0 ≤ u) :
    expOne (Ioi u) = ENNReal.ofReal (Real.exp (-u)) := by
  have hcompl := measureReal_compl (μ := expOne) (s := Iic u) measurableSet_Iic
  have hcdf : expOne.real (Iic u) = 1 - Real.exp (-u) := by
    rw [expOne_real_Iic, if_pos hu]
  have hreal : expOne.real (Ioi u) = Real.exp (-u) := by
    rw [← compl_Iic, hcompl, probReal_univ, hcdf]
    ring
  rw [← hreal, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma lintegral_expOne_id : (∫⁻ e : ℝ, ENNReal.ofReal e ∂expOne) = 1 := by
  have hn : 0 ≤ᵐ[expOne] (fun e : ℝ => e) := expOne_ae_pos.mono fun _ h => h.le
  rw [lintegral_eq_lintegral_meas_lt expOne hn measurable_id.aemeasurable]
  have hcongr : ∫⁻ u in Ioi (0 : ℝ), expOne {e : ℝ | u < e} =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-u)) :=
    setLIntegral_congr_fun measurableSet_Ioi fun u hu => expOne_Ioi hu.le
  rw [hcongr]
  have hderiv : ∀ u ∈ Ici (0 : ℝ), HasDerivAt (fun w : ℝ => -Real.exp (-w)) (Real.exp (-u)) u := by
    intro u _
    have h1 : HasDerivAt (fun w : ℝ => -w) (-1) u := (hasDerivAt_id u).neg
    have h2 := h1.exp.neg
    have hrew : -(Real.exp (-u) * -1) = Real.exp (-u) := by ring
    exact hrew ▸ h2
  have htend : Tendsto (fun w : ℝ => -Real.exp (-w)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).neg
  have hint_on : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg (by fun_prop) (fun u hu => hderiv u (mem_Ici.mpr hu.le))
      (fun u _ => (Real.exp_pos _).le) htend
  have hval : ∫ u in Ioi (0 : ℝ), Real.exp (-u) = 1 := by
    have h := integral_Ioi_of_hasDerivAt_of_nonneg (by fun_prop) (fun u hu => hderiv u (mem_Ici.mpr hu.le))
      (fun u _ => (Real.exp_pos _).le) htend
    simpa using h
  rw [← ofReal_integral_eq_lintegral_ofReal hint_on (Eventually.of_forall fun u => (Real.exp_pos _).le),
    hval, ENNReal.ofReal_one]

lemma integrable_expOne_id : Integrable (fun e : ℝ => e) expOne := by
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (expOne_ae_pos.mono fun _ h => h.le), lintegral_expOne_id]
  exact ENNReal.one_lt_top

lemma integral_expOne_id : (∫ e : ℝ, e ∂expOne) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (expOne_ae_pos.mono fun _ h => h.le)
    measurable_id.aestronglyMeasurable, lintegral_expOne_id]
  simp

lemma demandLaw_ae_nonneg (m : ℕ) : ∀ᵐ z ∂(demandLaw m), ∀ i, 0 ≤ z i := by
  unfold demandLaw
  refine eventually_all.mpr fun i => ?_
  exact (MeasureTheory.Measure.tendsto_eval_ae_ae (μ := fun _ : Fin m => expOne) (i := i)).eventually
    (expOne_ae_pos.mono fun _ h => h.le)

lemma integrable_demand_coord {m : ℕ} (i : Fin m) :
    Integrable (fun z : Fin m → ℝ => z i) (demandLaw m) := by
  unfold demandLaw
  have hmp := MeasureTheory.measurePreserving_eval (fun _ : Fin m => expOne) i
  have hint : Integrable (fun e : ℝ => e) (Measure.map (Function.eval i) (Measure.pi fun _ : Fin m => expOne)) := by
    rw [hmp.map_eq]; exact integrable_expOne_id
  exact hint.comp_measurable (measurable_pi_apply i)

lemma integral_demand_coord {m : ℕ} (i : Fin m) :
    (∫ z : Fin m → ℝ, z i ∂(demandLaw m)) = 1 := by
  unfold demandLaw
  have hmp := MeasureTheory.measurePreserving_eval (fun _ : Fin m => expOne) i
  have hmap := integral_map (μ := Measure.pi fun _ : Fin m => expOne)
    (measurable_pi_apply i).aemeasurable measurable_id.aestronglyMeasurable
  change MeasurePreserving (fun f : Fin m → ℝ => f i) _ _ at hmp
  rw [hmp.map_eq] at hmap
  simpa [integral_expOne_id] using hmap.symm

lemma maxDefPois_bounds {m : ℕ} (N : Ty m → ℕ) :
    0 ≤ maxDefPois N ∧ maxDefPois N ≤ (m : ℤ) := by
  refine ⟨?_, ?_⟩
  · unfold maxDefPois
    have h0 : defPois N ∅ = 0 := by simp [defPois, coverCount]
    rw [← h0]
    exact Finset.le_sup' (defPois N) (Finset.mem_univ (∅ : Finset (Fin m)))
  · refine Finset.sup'_le Finset.univ_nonempty _ fun A _ => ?_
    unfold defPois
    have hcard : A.card ≤ m := (Finset.card_le_univ A).trans (by simp)
    omega

lemma measurable_maxDefPois {m : ℕ} : Measurable (maxDefPois (m := m)) :=
  measurable_of_countable _

lemma card_fin_lt_maxDefPois {m : ℕ} (N : Ty m → ℕ) :
    ((Finset.univ.filter fun l : Fin m => ((l : ℕ) : ℤ) < maxDefPois N).card : ℝ) =
      (maxDefPois N : ℝ) := by
  obtain ⟨h0, hm⟩ := maxDefPois_bounds N
  let k : ℕ := (maxDefPois N).toNat
  have hk_eq : (k : ℤ) = maxDefPois N := Int.toNat_of_nonneg h0
  have hk_le : k ≤ m := by omega
  have hbij : (Finset.univ.filter fun l : Fin m => ((l : ℕ) : ℤ) < maxDefPois N).card =
      (Finset.range k).card := by
    refine Finset.card_bij (fun l _ => (l : ℕ)) ?_ ?_ ?_
    · intro l hl
      have hlt : ((l : ℕ) : ℤ) < (k : ℤ) := by rw [hk_eq]; exact (Finset.mem_filter.mp hl).2
      exact Finset.mem_range.mpr (Int.ofNat_lt.mp hlt)
    · intro l₁ _ l₂ _ heq
      exact Fin.ext heq
    · intro r hr
      have hlt : r < k := Finset.mem_range.mp hr
      refine ⟨⟨r, lt_of_lt_of_le hlt hk_le⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      rw [← hk_eq]
      exact Int.ofNat_lt.mpr hlt
  rw [hbij, Finset.card_range, ← Int.cast_natCast, hk_eq]

end AuxThm31

open MeasureTheory ProbabilityTheory OptStochMatch.Tight AuxThm31
open scoped NNReal ENNReal BigOperators

theorem solution {m : ℕ} (lam : Ty m → ℝ≥0) :
    ∫ N, optPois N ∂(countLaw lam) = ∫ z, optExp lam z ∂(demandLaw m) := by
  have : IsProbabilityMeasure (countLaw lam) := by unfold countLaw; infer_instance
  have : IsProbabilityMeasure (demandLaw m) := by unfold demandLaw; infer_instance
  obtain ⟨hL32_pois, hL32_exp⟩ := lemma_3_2 lam
  have hmeas_mdp_real : Measurable (fun N : Ty m → ℕ => (maxDefPois N : ℝ)) :=
    measurable_of_countable _
  have hint_mdp : Integrable (fun N : Ty m → ℕ => (maxDefPois N : ℝ)) (countLaw lam) := by
    refine (integrable_const (m : ℝ)).mono' hmeas_mdp_real.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun N => ?_
    obtain ⟨h0, hm⟩ := maxDefPois_bounds N
    rw [Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast h0)]
    exact_mod_cast hm
  have hlhs : ∫ N, optPois N ∂(countLaw lam) =
      (m : ℝ) - ∫ N, (maxDefPois N : ℝ) ∂(countLaw lam) := by
    simp_rw [hL32_pois]
    rw [integral_sub (integrable_const _) hint_mdp, integral_const]
    simp
  have hcont_mde : Continuous (maxDefExp lam) := by
    unfold maxDefExp
    refine Continuous.finset_sup'_apply _ fun A _ => ?_
    unfold defExp
    exact (continuous_finsetSum A fun i _ => continuous_apply i).sub continuous_const
  have hint_sum_z : Integrable (fun z : Fin m → ℝ => ∑ i, z i) (demandLaw m) :=
    integrable_finsetSum _ fun i _ => integrable_demand_coord i
  have hint_mde : Integrable (maxDefExp lam) (demandLaw m) := by
    refine hint_sum_z.mono' hcont_mde.measurable.aestronglyMeasurable ?_
    filter_upwards [demandLaw_ae_nonneg m] with z hz
    have h0 : 0 ≤ maxDefExp lam z := by
      unfold maxDefExp
      have he : defExp lam z ∅ = 0 := by simp [defExp, coverRate]
      rw [← he]
      exact Finset.le_sup' (defExp lam z) (Finset.mem_univ (∅ : Finset (Fin m)))
    have hle : maxDefExp lam z ≤ ∑ i, z i := by
      refine Finset.sup'_le Finset.univ_nonempty _ fun A _ => ?_
      unfold defExp
      have hcr : 0 ≤ coverRate lam A := Finset.sum_nonneg fun S _ => NNReal.coe_nonneg _
      have hsub : ∑ i ∈ A, z i ≤ ∑ i, z i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) fun i _ _ => hz i
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hle
  have hrhs : ∫ z, optExp lam z ∂(demandLaw m) =
      (m : ℝ) - ∫ z, maxDefExp lam z ∂(demandLaw m) := by
    have hae : optExp lam =ᵐ[demandLaw m] fun z => ∑ i, z i - maxDefExp lam z := by
      filter_upwards [demandLaw_ae_nonneg m] with z hz
      exact hL32_exp z hz
    rw [integral_congr_ae hae, integral_sub hint_sum_z hint_mde,
      integral_finsetSum _ fun i _ => integrable_demand_coord i]
    simp [integral_demand_coord]
  rw [hlhs, hrhs]
  congr 1
  let S_sum : (Ty m → ℕ) × (Fin m → ℝ) → ℝ := fun p =>
    ∑ l ∈ (Finset.univ.filter fun l : Fin m => ((l : ℕ) : ℤ) < maxDefPois p.1), p.2 l
  have hmeas_S : Measurable S_sum := by
    have heq : S_sum = fun p => ∑ l : Fin m,
        if ((l : ℕ) : ℤ) < maxDefPois p.1 then p.2 l else 0 := by
      ext p; simp [S_sum, Finset.sum_filter]
    rw [heq]
    refine Finset.measurable_sum _ fun l _ => ?_
    have hcond : MeasurableSet {p : (Ty m → ℕ) × (Fin m → ℝ) | ((l : ℕ) : ℤ) < maxDefPois p.1} :=
      measurableSet_lt measurable_const (measurable_maxDefPois.comp measurable_fst)
    exact Measurable.ite hcond ((measurable_pi_apply l).comp measurable_snd) measurable_const
  have hint_prod_z : Integrable (fun p : (Ty m → ℕ) × (Fin m → ℝ) => ∑ l : Fin m, p.2 l)
      ((countLaw lam).prod (demandLaw m)) :=
    hint_sum_z.comp_snd (countLaw lam)
  have hint_S : Integrable S_sum ((countLaw lam).prod (demandLaw m)) := by
    refine hint_prod_z.mono' hmeas_S.aestronglyMeasurable ?_
    have hae_prod : ∀ᵐ p ∂((countLaw lam).prod (demandLaw m)), ∀ l, 0 ≤ p.2 l :=
      Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd) (demandLaw_ae_nonneg m)
    filter_upwards [hae_prod] with p hp
    have h0 : 0 ≤ S_sum p := Finset.sum_nonneg fun l _ => hp l
    have hle : S_sum p ≤ ∑ l : Fin m, p.2 l :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun l _ _ => hp l
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hle
  have hmap_eq := (proposition_3_5 lam).2.1
  have hm1 := (integral_map (μ := demandLaw m) hcont_mde.measurable.aemeasurable
    measurable_id.aestronglyMeasurable).symm
  have hm2 := integral_map (μ := (countLaw lam).prod (demandLaw m)) hmeas_S.aemeasurable
    measurable_id.aestronglyMeasurable
  have heq_int : ∫ z, maxDefExp lam z ∂(demandLaw m) =
      ∫ p, S_sum p ∂((countLaw lam).prod (demandLaw m)) := by
    calc
      ∫ z, maxDefExp lam z ∂(demandLaw m)
        = ∫ x, x ∂((demandLaw m).map (maxDefExp lam)) := hm1
      _ = ∫ x, x ∂(((countLaw lam).prod (demandLaw m)).map S_sum) := by rw [hmap_eq]
      _ = ∫ p, S_sum p ∂((countLaw lam).prod (demandLaw m)) := hm2
  rw [heq_int, integral_prod _ hint_S]
  symm
  refine integral_congr_ae (Filter.Eventually.of_forall fun N => ?_)
  let F_N : Finset (Fin m) := Finset.univ.filter fun l : Fin m => ((l : ℕ) : ℤ) < maxDefPois N
  change ∫ z : Fin m → ℝ, ∑ l ∈ F_N, z l ∂(demandLaw m) = (maxDefPois N : ℝ)
  rw [integral_finsetSum F_N fun l _ => integrable_demand_coord l]
  simp only [integral_demand_coord, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact card_fin_lt_maxDefPois N
