-- Prove2me | solution 1 for VectorPayoffs.Convex.approachable_of_slack
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T21:26:27.820474+00:00
-- url     : https://prove2.me/submissions/17b3f09a-144b-4320-ac90-ae7b2b13b5ee

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game
import Theorems.Thm_VectorPayoffs_Convex_blackwell_lemma

/-!
Blackwell (1956), Theorem 1 with approximate separation.  The proof of Theorem 1 only uses that the
cross term `⟨x̄ₙ - y, E(xₙ₊₁ | past) - y⟩` is nonpositive; it tolerates a term `≤ κ / n`, since
`(2n/(n+1)²) · κ/n = 2κ/(n+1)²` is absorbed in the constant `c` of Blackwell's recursion
`E(δₙ₊₁ | past) ≤ (1 - 2/(n+1)) δₙ + c/(n+1)²` for `δₙ = dist(x̄ₙ, S)²`.  See `step_bound`,
`satisfies_recursion` and `approachable_of_slack_proof`; the probabilistic core is the LEMMA of
Blackwell's paper (an imported platform theorem).  The conditional law of the next outcome is read off
from `IsPlay` through the measure identity `restrict_map_eq`.
-/

open MeasureTheory

namespace VectorPayoffs.Convex

namespace Game

variable {N r s : ℕ} (G : Game N r s)

theorem exists_norm_bound : ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ x ∈ G.X, ‖x‖ ≤ ρ := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp G.isBounded_X
  exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩

variable {G}

/-- Almost surely every outcome of a play lies in `X`. -/
theorem ae_mem_X {f : Strategy N r} {g : Strategy N s} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {x : ℕ → Ω → E N} (hp : G.IsPlay f g μ x)
    (n : ℕ) : ∀ᵐ ω ∂μ, x (n + 1) ω ∈ G.X := by
  have hhist : Measurable (hist x n) :=
    measurable_pi_iff.mpr fun k => hp.1 k
  have hm : MeasurableSpace.comap (hist x n) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    hhist.comap_le
  have hB : MeasurableSet G.Xᶜ := G.isClosed_X.measurableSet.compl
  have hmeas : MeasurableSet (x (n + 1) ⁻¹' G.Xᶜ) := hp.1 n hB
  have hint : Integrable ((x (n + 1) ⁻¹' G.Xᶜ).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hmeas
  have hcond := hp.2 n G.Xᶜ hB
  have hzero : (fun ω => ∑ i, ∑ j, f.toFun n (hist x n ω) i * g.toFun n (hist x n ω) j *
      (G.m i j G.Xᶜ).toReal) = fun _ => 0 := by
    ext ω
    simp [G.m_compl_X]
  rw [hzero] at hcond
  have h1 : ∫ ω, ((x (n + 1) ⁻¹' G.Xᶜ).indicator (fun _ => (1 : ℝ))) ω ∂μ = 0 := by
    rw [← integral_condExp hm, integral_congr_ae hcond]
    simp
  have h2 := (integral_eq_zero_iff_of_nonneg (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    hint).mp h1
  filter_upwards [h2] with ω hω
  by_contra hx
  have : (x (n + 1) ⁻¹' G.Xᶜ).indicator (fun _ => (1 : ℝ)) ω = 1 :=
    Set.indicator_of_mem (by simpa using hx) _
  simp [this] at hω
  exact hx hω

theorem ae_all_mem_X {f : Strategy N r} {g : Strategy N s} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {x : ℕ → Ω → E N} (hp : G.IsPlay f g μ x) :
    ∀ᵐ ω ∂μ, ∀ k, 1 ≤ k → x k ω ∈ G.X := by
  rw [ae_all_iff]
  intro k
  by_cases hk : 1 ≤ k
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    filter_upwards [ae_mem_X hp n] with ω hω _ using hω
  · exact ae_of_all _ (fun ω h => absurd h hk)

theorem avg_succ {Ω : Type} (x : ℕ → Ω → E N) (n : ℕ) (ω : Ω) :
    avg x (n + 1) ω = ((n : ℝ) / ((n : ℝ) + 1)) • avg x n ω + (1 / ((n : ℝ) + 1)) • x (n + 1) ω := by
  unfold avg avgHist hist
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  by_cases hn : n = 0
  · subst hn; simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [smul_smul]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [smul_add]
    congr 1
    · congr 1; field_simp
    · rw [one_div]

theorem avg_mem_X {Ω : Type} {x : ℕ → Ω → E N} {ω : Ω} (hx : ∀ k, 1 ≤ k → x k ω ∈ G.X)
    {n : ℕ} (hn : 1 ≤ n) : avg x n ω ∈ G.X := by
  unfold avg avgHist hist
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have : (n : ℝ)⁻¹ • ∑ k : Fin n, x (k.val + 1) ω = ∑ k : Fin n, (n : ℝ)⁻¹ • x (k.val + 1) ω := by
    rw [Finset.smul_sum]
  rw [this]
  refine G.convex_X.sum_mem (fun k _ => by positivity) ?_ (fun k _ => hx _ (by omega))
  simp [Finset.sum_const, hn0.ne']


/-- The conditional mean `∑ i, ∑ j, p_i q_j m̄(i,j)` of the next outcome given the history `h`. -/
noncomputable def condMean (G : Game N r s) (f : Strategy N r) (g : Strategy N s) (n : ℕ)
    (h : Fin n → E N) : E N :=
  ∑ i, ∑ j, (f.toFun n h i * g.toFun n h j) • G.mbar i j

instance instIsProbabilityMeasure_m (G : Game N r s) (i : Fin r) (j : Fin s) :
    IsProbabilityMeasure (G.m i j) := G.isProb i j

theorem ae_mem_X_m (i : Fin r) (j : Fin s) : ∀ᵐ z ∂(G.m i j), z ∈ G.X := by
  have := G.m_compl_X i j
  rw [← compl_mem_ae_iff] at this
  filter_upwards [this] with z hz using by simpa using hz

theorem integrable_inner_m (i : Fin r) (j : Fin s) (v : E N) :
    Integrable (fun z => inner ℝ v z) (G.m i j) := by
  obtain ⟨ρ, hρ0, hρ⟩ := G.exists_norm_bound
  refine Integrable.of_bound (continuous_const.inner continuous_id).aestronglyMeasurable
    (‖v‖ * ρ) ?_
  filter_upwards [ae_mem_X_m (G := G) i j] with z hz
  calc ‖inner ℝ v z‖ ≤ ‖v‖ * ‖z‖ := norm_inner_le_norm v z
    _ ≤ ‖v‖ * ρ := mul_le_mul_of_nonneg_left (hρ z hz) (norm_nonneg _)

theorem integrable_id_m (i : Fin r) (j : Fin s) : Integrable (fun z : E N => z) (G.m i j) := by
  obtain ⟨ρ, hρ0, hρ⟩ := G.exists_norm_bound
  refine Integrable.of_bound continuous_id.aestronglyMeasurable ρ ?_
  filter_upwards [ae_mem_X_m (G := G) i j] with z hz using hρ z hz

theorem condMean_norm_le (f : Strategy N r) (g : Strategy N s) (n : ℕ) (h : Fin n → E N) :
    ‖G.condMean f g n h‖ ≤ ∑ i, ∑ j, ‖G.mbar i j‖ := by
  unfold condMean
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  have hp := f.mem n h
  have hq := g.mem n h
  have h1 : f.toFun n h i ≤ 1 := by
    have := Finset.single_le_sum (fun k _ => hp.1 k) (Finset.mem_univ i)
    rw [hp.2] at this; exact this
  have h2 : g.toFun n h j ≤ 1 := by
    have := Finset.single_le_sum (fun k _ => hq.1 k) (Finset.mem_univ j)
    rw [hq.2] at this; exact this
  have h3 : |f.toFun n h i * g.toFun n h j| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg (hp.1 i) (hq.1 j))]
    nlinarith [hp.1 i, hq.1 j]
  exact mul_le_of_le_one_left (norm_nonneg _) h3


section Play

variable {f : Strategy N r} {g : Strategy N s} {Ω : Type} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {x : ℕ → Ω → E N}

theorem measurable_hist (hp : G.IsPlay f g μ x) (n : ℕ) : Measurable (hist x n) :=
  measurable_pi_iff.mpr fun k => hp.1 k

theorem measurable_p (hp : G.IsPlay f g μ x) (n : ℕ) (i : Fin r) :
    Measurable (fun ω => f.toFun n (hist x n ω) i) :=
  (measurable_pi_apply i).comp ((f.meas n).comp (measurable_hist hp n))

theorem measurable_q (hp : G.IsPlay f g μ x) (n : ℕ) (j : Fin s) :
    Measurable (fun ω => g.toFun n (hist x n ω) j) :=
  (measurable_pi_apply j).comp ((g.meas n).comp (measurable_hist hp n))

theorem pq_nonneg (n : ℕ) (h : Fin n → E N) (i : Fin r) (j : Fin s) :
    0 ≤ f.toFun n h i * g.toFun n h j :=
  mul_nonneg ((f.mem n h).1 i) ((g.mem n h).1 j)

theorem pq_le_one (n : ℕ) (h : Fin n → E N) (i : Fin r) (j : Fin s) :
    f.toFun n h i * g.toFun n h j ≤ 1 := by
  have hp := f.mem n h
  have hq := g.mem n h
  have h1 : f.toFun n h i ≤ 1 := by
    have := Finset.single_le_sum (fun k _ => hp.1 k) (Finset.mem_univ i)
    rw [hp.2] at this; exact this
  have h2 : g.toFun n h j ≤ 1 := by
    have := Finset.single_le_sum (fun k _ => hq.1 k) (Finset.mem_univ j)
    rw [hq.2] at this; exact this
  nlinarith [hp.1 i, hq.1 j]

theorem integrable_pq (hp : G.IsPlay f g μ x) (n : ℕ) (i : Fin r) (j : Fin s) :
    Integrable (fun ω => f.toFun n (hist x n ω) i * g.toFun n (hist x n ω) j) μ := by
  refine Integrable.of_bound ((measurable_p hp n i).mul (measurable_q hp n j)).aestronglyMeasurable
    1 (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pq_nonneg n _ i j)]
  exact pq_le_one n _ i j

theorem restrict_map_eq (hp : G.IsPlay f g μ x) (n : ℕ) {s' : Set Ω}
    (hs : MeasurableSet[MeasurableSpace.comap (hist x n) inferInstance] s') :
    (μ.restrict s').map (x (n + 1)) =
      ∑ ij : Fin r × Fin s, ENNReal.ofReal (∫ ω in s', f.toFun n (hist x n ω) ij.1 *
        g.toFun n (hist x n ω) ij.2 ∂μ) • G.m ij.1 ij.2 := by
  classical
  ext B hB
  have hhist := measurable_hist hp n
  have hm : MeasurableSpace.comap (hist x n) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    hhist.comap_le
  have hs' : MeasurableSet s' := hm _ hs
  have hxB : MeasurableSet (x (n + 1) ⁻¹' B) := hp.1 n hB
  rw [Measure.map_apply (hp.1 n) hB, Measure.restrict_apply hxB]
  have hint : Integrable ((x (n + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const _).indicator hxB
  have hcond := hp.2 n B hB
  have hreal : (μ (x (n + 1) ⁻¹' B ∩ s')).toReal = ∑ i, ∑ j,
      (∫ ω in s', f.toFun n (hist x n ω) i * g.toFun n (hist x n ω) j ∂μ) *
        (G.m i j B).toReal := by
    have e1 : (μ (x (n + 1) ⁻¹' B ∩ s')).toReal =
        ∫ ω in s', ((x (n + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ))) ω ∂μ := by
      rw [setIntegral_indicator hxB, setIntegral_const]
      simp [measureReal_def, Set.inter_comm]
    rw [e1, ← setIntegral_condExp hm hint hs]
    rw [setIntegral_congr_ae hs' (hcond.mono (fun ω h _ => h))]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finset_sum]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [integral_mul_const]
      · intro j _
        exact ((integrable_pq hp n i j).mul_const _).integrableOn
    · intro i _
      exact (integrable_finset_sum _ (fun j _ => (integrable_pq hp n i j).mul_const _)).integrableOn
  have hw : ∀ i j, 0 ≤ ∫ ω in s', f.toFun n (hist x n ω) i * g.toFun n (hist x n ω) j ∂μ :=
    fun i j => setIntegral_nonneg hs' (fun ω _ => pq_nonneg n _ i j)
  rw [Measure.finset_sum_apply, Fintype.sum_prod_type]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ (x (n + 1) ⁻¹' B ∩ s')), hreal,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (hw i j) ENNReal.toReal_nonneg))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hw i j) ENNReal.toReal_nonneg)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ENNReal.ofReal_mul (hw i j), ENNReal.ofReal_toReal (measure_ne_top _ _)]


theorem condExp_inner_next (hp : G.IsPlay f g μ x) (n : ℕ) (v : E N) :
    μ[fun ω => inner ℝ v (x (n + 1) ω) | MeasurableSpace.comap (hist x n) inferInstance]
      =ᵐ[μ] fun ω => inner ℝ v (G.condMean f g n (hist x n ω)) := by
  classical
  have hhist := measurable_hist hp n
  have hm : MeasurableSpace.comap (hist x n) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    hhist.comap_le
  obtain ⟨ρ, hρ0, hρ⟩ := G.exists_norm_bound
  have hcont : Continuous (fun z : E N => inner ℝ v z) := continuous_const.inner continuous_id
  have hfint : Integrable (fun ω => inner ℝ v (x (n + 1) ω)) μ := by
    refine Integrable.of_bound (hcont.measurable.comp (hp.1 n)).aestronglyMeasurable (‖v‖ * ρ) ?_
    filter_upwards [ae_mem_X hp n] with ω hω
    calc ‖inner ℝ v (x (n + 1) ω)‖ ≤ ‖v‖ * ‖x (n + 1) ω‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * ρ := mul_le_mul_of_nonneg_left (hρ _ hω) (norm_nonneg _)
  have hφ : Measurable (fun h : Fin n → E N => inner ℝ v (G.condMean f g n h)) := by
    unfold condMean
    refine measurable_const.inner (Finset.measurable_sum _ (fun i _ =>
      Finset.measurable_sum _ (fun j _ => ?_)))
    exact (((measurable_pi_apply i).comp (f.meas n)).mul
      ((measurable_pi_apply j).comp (g.meas n))).smul_const _
  have hgmeas : Measurable[MeasurableSpace.comap (hist x n) inferInstance]
      (fun ω => inner ℝ v (G.condMean f g n (hist x n ω))) :=
    @Measurable.comp Ω (Fin n → E N) ℝ (MeasurableSpace.comap (hist x n) inferInstance)
      inferInstance inferInstance (fun h : Fin n → E N => inner ℝ v (G.condMean f g n h))
      (hist x n) hφ (Measurable.of_comap_le le_rfl)
  have hgint : Integrable (fun ω => inner ℝ v (G.condMean f g n (hist x n ω))) μ := by
    refine Integrable.of_bound (hgmeas.mono hm le_rfl).aestronglyMeasurable
      (‖v‖ * ∑ i, ∑ j, ‖G.mbar i j‖) (ae_of_all _ fun ω => ?_)
    calc ‖inner ℝ v (G.condMean f g n (hist x n ω))‖
        ≤ ‖v‖ * ‖G.condMean f g n (hist x n ω)‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * ∑ i, ∑ j, ‖G.mbar i j‖ :=
          mul_le_mul_of_nonneg_left (condMean_norm_le _ _ _ _) (norm_nonneg _)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hfint (fun s _ _ => hgint.integrableOn)
    (fun s hs _ => ?_) hgmeas.stronglyMeasurable.aestronglyMeasurable).symm
  have hs' : MeasurableSet s := hm _ hs
  have hw : ∀ i j, 0 ≤ ∫ ω in s, f.toFun n (hist x n ω) i * g.toFun n (hist x n ω) j ∂μ :=
    fun i j => setIntegral_nonneg hs' (fun ω _ => pq_nonneg n _ i j)
  -- the right-hand side
  have hR : ∫ ω in s, inner ℝ v (x (n + 1) ω) ∂μ = ∑ i, ∑ j,
      (∫ ω in s, f.toFun n (hist x n ω) i * g.toFun n (hist x n ω) j ∂μ) *
        inner ℝ v (G.mbar i j) := by
    have e1 : ∫ ω in s, inner ℝ v (x (n + 1) ω) ∂μ =
        ∫ z, inner ℝ v z ∂((μ.restrict s).map (x (n + 1))) :=
      (integral_map (hp.1 n).aemeasurable hcont.aestronglyMeasurable).symm
    rw [e1, restrict_map_eq hp n hs, integral_finsetSum_measure, Fintype.sum_prod_type]
    · refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [integral_smul_measure, ENNReal.toReal_ofReal (hw i j), smul_eq_mul, integral_inner
        (integrable_id_m i j) v]
      rfl
    · intro ij _
      exact (integrable_inner_m ij.1 ij.2 v).smul_measure ENNReal.ofReal_ne_top
  -- the left-hand side
  have hL : ∫ ω in s, inner ℝ v (G.condMean f g n (hist x n ω)) ∂μ = ∑ i, ∑ j,
      (∫ ω in s, f.toFun n (hist x n ω) i * g.toFun n (hist x n ω) j ∂μ) *
        inner ℝ v (G.mbar i j) := by
    have e2 : ∀ ω, inner ℝ v (G.condMean f g n (hist x n ω)) = ∑ i, ∑ j,
        (f.toFun n (hist x n ω) i * g.toFun n (hist x n ω) j) * inner ℝ v (G.mbar i j) := by
      intro ω
      unfold condMean
      simp only [inner_sum, inner_smul_right]
    simp_rw [e2]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [integral_mul_const]
      · intro j _
        exact ((integrable_pq hp n i j).mul_const _).integrableOn
    · intro i _
      exact (integrable_finsetSum _ (fun j _ => (integrable_pq hp n i j).mul_const _)).integrableOn
  rw [hL, hR]


/-- The σ-algebra generated by the first `n` outcomes. -/
abbrev past (x : ℕ → Ω → E N) (n : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (hist x n) inferInstance

theorem past_le (hp : G.IsPlay f g μ x) (n : ℕ) : past x n ≤ (inferInstance : MeasurableSpace Ω) :=
  (measurable_hist hp n).comap_le

theorem measurable_past_fun {β : Type*} [MeasurableSpace β] (n : ℕ) (φ : (Fin n → E N) → β)
    (hφ : Measurable φ) : Measurable[past x n] (fun ω => φ (hist x n ω)) :=
  @Measurable.comp Ω (Fin n → E N) β (past x n) inferInstance inferInstance φ (hist x n) hφ
    (Measurable.of_comap_le le_rfl)

theorem measurable_avg_past (n : ℕ) : Measurable[past x n] (fun ω => avg x n ω) := by
  have hφ : Measurable (fun h : Fin n → E N => avgHist h) := by
    unfold avgHist
    have hsum : Measurable (fun h : Fin n → E N => ∑ k, h k) :=
      Finset.measurable_sum _ (fun k _ => measurable_pi_apply k)
    exact hsum.const_smul ((n : ℝ)⁻¹)
  have := measurable_past_fun (x := x) n (fun h : Fin n → E N => avgHist h) hφ
  exact this

theorem condExp_inner_V (hp : G.IsPlay f g μ x) (n : ℕ) {V : Ω → E N}
    (hV : Measurable[past x n] V) {C : ℝ} (hC : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ C) :
    μ[fun ω => inner ℝ (V ω) (x (n + 1) ω) | past x n] =ᵐ[μ]
      fun ω => inner ℝ (V ω) (G.condMean f g n (hist x n ω)) := by
  classical
  have hm := past_le hp n
  obtain ⟨ρ, hρ0, hρ⟩ := G.exists_norm_bound
  let b := EuclideanSpace.basisFun (Fin N) ℝ
  have e1 : ∀ (u z : E N), inner ℝ u z = ∑ l, inner ℝ u (b l) * inner ℝ (b l) z :=
    fun u z => (b.sum_inner_mul_inner u z).symm
  have hu_meas : ∀ l, Measurable[past x n] (fun ω => inner ℝ (V ω) (b l)) :=
    fun l => hV.inner measurable_const
  have hu_int : ∀ l, Integrable (fun ω => inner ℝ (V ω) (b l)) μ := by
    intro l
    refine Integrable.of_bound ((hu_meas l).mono hm le_rfl).aestronglyMeasurable C ?_
    filter_upwards [hC] with ω hω
    calc ‖inner ℝ (V ω) (b l)‖ ≤ ‖V ω‖ * ‖b l‖ := norm_inner_le_norm _ _
      _ ≤ C := by rw [b.orthonormal.1 l, mul_one]; exact hω
  have hg_int : ∀ l, Integrable (fun ω => inner ℝ (b l) (x (n + 1) ω)) μ := by
    intro l
    have hcont : Continuous (fun z : E N => inner ℝ (b l) z) := continuous_const.inner continuous_id
    refine Integrable.of_bound (hcont.measurable.comp (hp.1 n)).aestronglyMeasurable (1 * ρ) ?_
    filter_upwards [ae_mem_X hp n] with ω hω
    calc ‖inner ℝ (b l) (x (n + 1) ω)‖ ≤ ‖b l‖ * ‖x (n + 1) ω‖ := norm_inner_le_norm _ _
      _ ≤ 1 * ρ := by rw [b.orthonormal.1 l]; exact mul_le_mul_of_nonneg_left (hρ _ hω) zero_le_one
  have hprod_int : ∀ l, Integrable (fun ω => inner ℝ (V ω) (b l) * inner ℝ (b l) (x (n + 1) ω)) μ := by
    intro l
    have hcont : Continuous (fun z : E N => inner ℝ (b l) z) := continuous_const.inner continuous_id
    refine Integrable.of_bound (((hu_meas l).mono hm le_rfl).mul
      (hcont.measurable.comp (hp.1 n))).aestronglyMeasurable (C * (1 * ρ)) ?_
    filter_upwards [hC, ae_mem_X hp n] with ω hω hx
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |inner ℝ (V ω) (b l)| ≤ C := by
      calc |inner ℝ (V ω) (b l)| = ‖inner ℝ (V ω) (b l)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖V ω‖ * ‖b l‖ := norm_inner_le_norm _ _
        _ ≤ C := by rw [b.orthonormal.1 l, mul_one]; exact hω
    have h2 : |inner ℝ (b l) (x (n + 1) ω)| ≤ 1 * ρ := by
      calc |inner ℝ (b l) (x (n + 1) ω)| = ‖inner ℝ (b l) (x (n + 1) ω)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖b l‖ * ‖x (n + 1) ω‖ := norm_inner_le_norm _ _
        _ ≤ 1 * ρ := by
          rw [b.orthonormal.1 l]; exact mul_le_mul_of_nonneg_left (hρ _ hx) zero_le_one
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
  have hE : ∀ l, μ[fun ω => inner ℝ (V ω) (b l) * inner ℝ (b l) (x (n + 1) ω) | past x n]
      =ᵐ[μ] fun ω => inner ℝ (V ω) (b l) * inner ℝ (b l) (G.condMean f g n (hist x n ω)) := by
    intro l
    have h1 := condExp_mul_of_stronglyMeasurable_left (m := past x n)
      (hu_meas l).stronglyMeasurable (hprod_int l) (hg_int l)
    have h2 := condExp_inner_next hp n (b l)
    filter_upwards [h1, h2] with ω e1' e2'
    exact e1'.trans (congrArg (fun t => inner ℝ (V ω) (b l) * t) e2')
  have hsum : (fun ω => inner ℝ (V ω) (x (n + 1) ω)) =
      ∑ l, fun ω => inner ℝ (V ω) (b l) * inner ℝ (b l) (x (n + 1) ω) := by
    ext ω
    simp only [Finset.sum_apply]
    exact e1 _ _
  rw [hsum]
  refine (condExp_finsetSum (fun l _ => hprod_int l) (past x n)).trans ?_
  have hall : ∀ᵐ ω ∂μ, ∀ l, μ[fun ω => inner ℝ (V ω) (b l) * inner ℝ (b l) (x (n + 1) ω)
      | past x n] ω = inner ℝ (V ω) (b l) * inner ℝ (b l) (G.condMean f g n (hist x n ω)) :=
    ae_all_iff.mpr hE
  filter_upwards [hall] with ω hω
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun l _ => hω l)]
  exact (e1 _ _).symm


theorem real_bound {t u R Y D a c2 m : ℝ} (ht0 : 0 ≤ t) (htR : t ≤ R) (hu : |u| ≤ R * Y)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hc0 : 0 ≤ c2) (hc2 : c2 ≤ 2) (hm : 1 ≤ m) (hD : 0 ≤ D) :
    |a ^ 2 * t ^ 2 - c2 * u + (D + t) ^ 2 / m| ≤ R ^ 2 + 2 * (R * Y) + (D + R) ^ 2 := by
  have hR0 : 0 ≤ R := ht0.trans htR
  have h1 : a ^ 2 * t ^ 2 ≤ R ^ 2 := by
    have : a ^ 2 ≤ 1 := by nlinarith
    have : t ^ 2 ≤ R ^ 2 := by nlinarith
    nlinarith [sq_nonneg a, sq_nonneg t]
  have h2 : |c2 * u| ≤ 2 * (R * Y) := by
    rw [abs_mul, abs_of_nonneg hc0]
    have : 0 ≤ |u| := abs_nonneg _
    nlinarith
  have h3 : (D + t) ^ 2 / m ≤ (D + R) ^ 2 := by
    have hm0 : 0 < m := by linarith
    rw [div_le_iff₀ hm0]
    have : (D + t) ^ 2 ≤ (D + R) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (D + R)]
  have h4 : 0 ≤ (D + t) ^ 2 / m := by positivity
  have h5 : 0 ≤ a ^ 2 * t ^ 2 := by positivity
  rw [abs_le]
  constructor
  · have := (abs_le.mp h2).2
    nlinarith
  · have := (abs_le.mp h2).1
    nlinarith

theorem norm_comb_sq (V Z : E N) (a b : ℝ) :
    ‖a • V + b • Z‖ ^ 2 = a ^ 2 * ‖V‖ ^ 2 + 2 * (a * b) * inner ℝ V Z + b ^ 2 * ‖Z‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring


theorem step_y (hp : G.IsPlay f g μ x) {S : Set (E N)} {y : E N} (hy : y ∈ S) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ∀ z ∈ G.X, ‖z‖ ≤ ρ) {n : ℕ} (hn : 1 ≤ n) :
    μ[fun ω => (Metric.infDist (avg x (n + 1) ω) S) ^ 2 | past x n] ≤ᵐ[μ]
      fun ω => ((n : ℝ) / ((n : ℝ) + 1)) ^ 2 * ‖avg x n ω - y‖ ^ 2 +
        (2 * (n : ℝ) / ((n : ℝ) + 1) ^ 2) *
          inner ℝ (avg x n ω - y) (G.condMean f g n (hist x n ω) - y) +
        (2 * ρ + ‖avg x n ω - y‖) ^ 2 / ((n : ℝ) + 1) ^ 2 := by
  classical
  have hm := past_le hp n
  set R : ℝ := ρ + ‖y‖ with hR
  have hR0 : 0 ≤ R := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set a : ℝ := (n : ℝ) / ((n : ℝ) + 1) with ha
  set b : ℝ := 1 / ((n : ℝ) + 1) with hb
  have hab : a + b = 1 := by rw [ha, hb]; field_simp
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one hn1]; linarith
  set c2 : ℝ := 2 * (n : ℝ) / ((n : ℝ) + 1) ^ 2 with hc2
  have hc20 : 0 ≤ c2 := by positivity
  have hc22 : c2 ≤ 2 := by
    rw [hc2, div_le_iff₀ (by positivity)]
    nlinarith
  have hm1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hX := ae_all_mem_X hp
  let V : Ω → E N := fun ω => avg x n ω - y
  have hVm : Measurable[past x n] V := (measurable_avg_past n).sub measurable_const
  have hVm' : Measurable V := hVm.mono hm le_rfl
  have hVb : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ R := by
    filter_upwards [hX] with ω h
    calc ‖avg x n ω - y‖ ≤ ‖avg x n ω‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ R := add_le_add (hρ _ (avg_mem_X h hn)) le_rfl
  let Θ₁ : Ω → ℝ := fun ω => a ^ 2 * ‖V ω‖ ^ 2 - c2 * inner ℝ (V ω) y +
    (2 * ρ + ‖V ω‖) ^ 2 / ((n : ℝ) + 1) ^ 2
  have hΘ₁m : Measurable[past x n] Θ₁ := by
    have h1 : Measurable[past x n] (fun ω => ‖V ω‖) := measurable_norm.comp hVm
    have h2 : Measurable[past x n] (fun ω => inner ℝ (V ω) y) := hVm.inner measurable_const
    exact (((h1.pow_const 2).const_mul _).sub (h2.const_mul _)).add
      (((h1.const_add _).pow_const 2).div_const _)
  have hΘ₁int : Integrable Θ₁ μ := by
    refine Integrable.of_bound (hΘ₁m.mono hm le_rfl).aestronglyMeasurable
      (R ^ 2 + 2 * (R * ‖y‖) + (2 * ρ + R) ^ 2) ?_
    filter_upwards [hVb] with ω hω
    rw [Real.norm_eq_abs]
    refine real_bound (norm_nonneg _) hω ?_ ha0 ha1 hc20 hc22 hm1 (by positivity)
    calc |inner ℝ (V ω) y| = ‖inner ℝ (V ω) y‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖V ω‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ R * ‖y‖ := mul_le_mul_of_nonneg_right hω (norm_nonneg _)
  have hxint : Integrable (fun ω => inner ℝ (V ω) (x (n + 1) ω)) μ := by
    obtain ⟨ρ', hρ'0, hρ'⟩ := G.exists_norm_bound
    refine Integrable.of_bound ((hVm'.inner (hp.1 n)).aestronglyMeasurable) (R * ρ') ?_
    filter_upwards [hVb, ae_mem_X hp n] with ω h1 h2
    calc ‖inner ℝ (V ω) (x (n + 1) ω)‖ ≤ ‖V ω‖ * ‖x (n + 1) ω‖ := norm_inner_le_norm _ _
      _ ≤ R * ρ' := mul_le_mul h1 (hρ' _ h2) (norm_nonneg _) hR0
  let Θ : Ω → ℝ := fun ω => Θ₁ ω + c2 * inner ℝ (V ω) (x (n + 1) ω)
  have hΘint : Integrable Θ μ := hΘ₁int.add (hxint.const_mul c2)
  -- the pointwise bound
  have hδmeas : Measurable (fun ω => (Metric.infDist (avg x (n + 1) ω) S) ^ 2) :=
    (((Metric.continuous_infDist_pt S).measurable.comp
      ((measurable_avg_past (x := x) (n + 1)).mono (past_le hp (n + 1)) le_rfl)).pow_const 2)
  have hle : ∀ ω, (∀ k, 1 ≤ k → x k ω ∈ G.X) →
      (Metric.infDist (avg x (n + 1) ω) S) ^ 2 ≤ Θ ω := by
    intro ω h
    have hxX : x (n + 1) ω ∈ G.X := h (n + 1) (by omega)
    have hav : avg x n ω ∈ G.X := avg_mem_X h hn
    have hd : Metric.infDist (avg x (n + 1) ω) S ≤ ‖avg x (n + 1) ω - y‖ := by
      rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hy
    have hd0 : 0 ≤ Metric.infDist (avg x (n + 1) ω) S := Metric.infDist_nonneg
    have hsq : (Metric.infDist (avg x (n + 1) ω) S) ^ 2 ≤ ‖avg x (n + 1) ω - y‖ ^ 2 := by
      nlinarith
    have hdec : avg x (n + 1) ω - y = a • V ω + b • (x (n + 1) ω - y) := by
      rw [avg_succ]
      simp only [V, smul_sub]
      have : y = a • y + b • y := by rw [← add_smul, hab, one_smul]
      conv_lhs => rw [this]
      simp only [← ha, ← hb]
      abel
    have hZ : ‖x (n + 1) ω - y‖ ≤ 2 * ρ + ‖V ω‖ := by
      calc ‖x (n + 1) ω - y‖ = ‖(x (n + 1) ω - avg x n ω) + (avg x n ω - y)‖ := by
            congr 1; abel
        _ ≤ ‖x (n + 1) ω - avg x n ω‖ + ‖avg x n ω - y‖ := norm_add_le _ _
        _ ≤ 2 * ρ + ‖V ω‖ := by
            have : ‖x (n + 1) ω - avg x n ω‖ ≤ 2 * ρ := by
              calc ‖x (n + 1) ω - avg x n ω‖ ≤ ‖x (n + 1) ω‖ + ‖avg x n ω‖ := norm_sub_le _ _
                _ ≤ ρ + ρ := add_le_add (hρ _ hxX) (hρ _ hav)
                _ = 2 * ρ := by ring
            exact add_le_add this le_rfl
    have hZsq : ‖x (n + 1) ω - y‖ ^ 2 ≤ (2 * ρ + ‖V ω‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hZ 2
    rw [hdec, norm_comb_sq] at hsq
    have hab2 : 2 * (a * b) = c2 := by rw [ha, hb, hc2]; field_simp
    have hb2 : b ^ 2 = 1 / ((n : ℝ) + 1) ^ 2 := by rw [hb]; field_simp
    have hinn : inner ℝ (V ω) (x (n + 1) ω - y) =
        inner ℝ (V ω) (x (n + 1) ω) - inner ℝ (V ω) y := inner_sub_right _ _ _
    have hbz : b ^ 2 * ‖x (n + 1) ω - y‖ ^ 2 ≤ (2 * ρ + ‖V ω‖) ^ 2 / ((n : ℝ) + 1) ^ 2 := by
      rw [hb2]
      calc 1 / ((n : ℝ) + 1) ^ 2 * ‖x (n + 1) ω - y‖ ^ 2
          ≤ 1 / ((n : ℝ) + 1) ^ 2 * (2 * ρ + ‖V ω‖) ^ 2 :=
            mul_le_mul_of_nonneg_left hZsq (by positivity)
        _ = (2 * ρ + ‖V ω‖) ^ 2 / ((n : ℝ) + 1) ^ 2 := by ring
    simp only [Θ, Θ₁]
    rw [hab2, hinn] at hsq
    nlinarith
  have hint_δ : Integrable (fun ω => (Metric.infDist (avg x (n + 1) ω) S) ^ 2) μ := by
    refine Integrable.of_bound hδmeas.aestronglyMeasurable (R ^ 2) ?_
    filter_upwards [hX] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hd : Metric.infDist (avg x (n + 1) ω) S ≤ ‖avg x (n + 1) ω - y‖ := by
      rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hy
    have hd0 : 0 ≤ Metric.infDist (avg x (n + 1) ω) S := Metric.infDist_nonneg
    have hnr : ‖avg x (n + 1) ω - y‖ ≤ R :=
      (norm_sub_le _ _).trans (add_le_add (hρ _ (avg_mem_X h (by omega))) le_rfl)
    exact pow_le_pow_left₀ hd0 (hd.trans hnr) 2
  have hmono := condExp_mono (m := past x n) hint_δ hΘint
    (by filter_upwards [hX] with ω h using hle ω h)
  have hcΘ : μ[Θ | past x n] =ᵐ[μ] fun ω =>
      Θ₁ ω + c2 * inner ℝ (V ω) (G.condMean f g n (hist x n ω)) := by
    have e : Θ = Θ₁ + c2 • (fun ω => inner ℝ (V ω) (x (n + 1) ω)) := by
      ext ω; simp [Θ]
    rw [e]
    have c1 := condExp_add hΘ₁int (hxint.smul c2) (past x n)
    have c3 := condExp_smul (μ := μ) c2 (fun ω => inner ℝ (V ω) (x (n + 1) ω)) (past x n)
    have c4 := condExp_of_stronglyMeasurable hm hΘ₁m.stronglyMeasurable hΘ₁int
    have c5 := condExp_inner_V hp n hVm hVb
    filter_upwards [c1, c3, c5] with ω h1 h3 h5
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h3 ⊢
    rw [h1, c4, h3, h5]
  filter_upwards [hmono, hcΘ] with ω h1 h2
  refine h1.trans (le_of_eq (h2.trans ?_))
  simp only [Θ₁, inner_sub_right]
  ring


theorem condMean_mem_R (f : Strategy N r) (g : Strategy N s) (n : ℕ) (h : Fin n → E N) :
    G.condMean f g n h ∈ G.R (f.toFun n h) := by
  have e : G.condMean f g n h = ∑ j, g.toFun n h j • ∑ i, f.toFun n h i • G.mbar i j := by
    unfold condMean
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← mul_smul, mul_comm]
  rw [e]
  unfold R
  exact (convex_convexHull ℝ _).sum_mem (fun j _ => (g.mem n h).1 j) (g.mem n h).2
    (fun j _ => subset_convexHull ℝ _ ⟨j, rfl⟩)

theorem le_of_dense {D S : Set (E N)} (hDS : D ⊆ S) (hSD : S ⊆ closure D) {Ψ : E N → ℝ}
    (hΨ : Continuous Ψ) {e : ℝ} (h : ∀ y ∈ D, e ≤ Ψ y) {y : E N} (hy : y ∈ S) : e ≤ Ψ y := by
  have : closure D ⊆ {z | e ≤ Ψ z} := closure_minimal h (isClosed_le continuous_const hΨ)
  exact this (hSD hy)

theorem step_bound (hp : G.IsPlay f g μ x) {S : Set (E N)} (hne : S.Nonempty) {κ : ℝ}
    (hκ : 0 ≤ κ)
    (hslack : ∀ n, 1 ≤ n → ∀ h : Fin n → E N, avgHist h ∈ G.X → avgHist h ∉ S →
      ∃ y ∈ S, (∀ z ∈ S, dist (avgHist h) y ≤ dist (avgHist h) z) ∧
        ∀ w ∈ G.R (f.toFun n h), inner ℝ (avgHist h - y) (w - y) ≤ κ / n)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ z ∈ G.X, ‖z‖ ≤ ρ) {A0 : ℝ}
    (hA0 : ∀ z ∈ G.X, Metric.infDist z S ≤ A0) {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂μ, μ[fun ω => (Metric.infDist (avg x (n + 1) ω) S) ^ 2 | past x n] ω ≤
      (1 - 2 / ((n : ℝ) + 1)) * (Metric.infDist (avg x n ω) S) ^ 2 +
        (A0 ^ 2 + (2 * ρ + A0) ^ 2 + 2 * κ) / ((n : ℝ) + 1) ^ 2 := by
  classical
  obtain ⟨D, hDS, hDc, hSD⟩ : ∃ D : Set (E N), D ⊆ S ∧ D.Countable ∧ S ⊆ closure D := by
    obtain ⟨t, htc, htd⟩ := TopologicalSpace.exists_countable_dense S
    refine ⟨Subtype.val '' t, Subtype.coe_image_subset S t, htc.image _, ?_⟩
    intro y hy
    have h1 : (⟨y, hy⟩ : S) ∈ closure t := by rw [htd.closure_eq]; trivial
    exact image_closure_subset_closure_image continuous_subtype_val ⟨_, h1, rfl⟩
  have hall : ∀ᵐ ω ∂μ, ∀ y ∈ D,
      μ[fun ω => (Metric.infDist (avg x (n + 1) ω) S) ^ 2 | past x n] ω ≤
      ((n : ℝ) / ((n : ℝ) + 1)) ^ 2 * ‖avg x n ω - y‖ ^ 2 +
        (2 * (n : ℝ) / ((n : ℝ) + 1) ^ 2) *
          inner ℝ (avg x n ω - y) (G.condMean f g n (hist x n ω) - y) +
        (2 * ρ + ‖avg x n ω - y‖) ^ 2 / ((n : ℝ) + 1) ^ 2 :=
    (ae_ball_iff hDc).mpr (fun y hy => step_y hp (hDS hy) hρ0 hρ hn)
  filter_upwards [hall, ae_all_mem_X hp] with ω hω hX
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set a : ℝ := (n : ℝ) / ((n : ℝ) + 1) with ha
  set b : ℝ := 1 / ((n : ℝ) + 1) with hb
  have hab : a = 1 - b := by rw [ha, hb]; field_simp; ring
  have hc2 : 0 ≤ 2 * (n : ℝ) / ((n : ℝ) + 1) ^ 2 := by positivity
  have hav : avg x n ω ∈ G.X := avg_mem_X hX hn
  have hdA : Metric.infDist (avg x n ω) S ≤ A0 := hA0 _ hav
  have hd0 : 0 ≤ Metric.infDist (avg x n ω) S := Metric.infDist_nonneg
  have hA00 : 0 ≤ A0 := hd0.trans hdA
  set M : E N := G.condMean f g n (hist x n ω) with hM
  have hcont : Continuous (fun y : E N =>
      ((n : ℝ) / ((n : ℝ) + 1)) ^ 2 * ‖avg x n ω - y‖ ^ 2 +
        (2 * (n : ℝ) / ((n : ℝ) + 1) ^ 2) * inner ℝ (avg x n ω - y) (M - y) +
        (2 * ρ + ‖avg x n ω - y‖) ^ 2 / ((n : ℝ) + 1) ^ 2) := by fun_prop
  by_cases hxS : avg x n ω ∈ S
  · have hle := le_of_dense hDS hSD hcont hω hxS
    have hz : Metric.infDist (avg x n ω) S = 0 := Metric.infDist_zero_of_mem hxS
    simp only [sub_self, norm_zero, inner_zero_left, mul_zero, add_zero] at hle
    rw [hz]
    refine hle.trans ?_
    have h1 : (2 * ρ + 0) ^ 2 ≤ A0 ^ 2 + (2 * ρ + A0) ^ 2 + 2 * κ := by nlinarith
    simp only [add_zero, zero_pow two_ne_zero, mul_zero, zero_add] at h1 ⊢
    rw [div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  · obtain ⟨y, hyS, hmin, hineq⟩ := hslack n hn (hist x n ω) hav hxS
    have hle := le_of_dense hDS hSD hcont hω hyS
    have hMR : M ∈ G.R (f.toFun n (hist x n ω)) := condMean_mem_R _ _ _ _
    have hin : inner ℝ (avg x n ω - y) (M - y) ≤ κ / n := hineq M hMR
    have hdist : ‖avg x n ω - y‖ = Metric.infDist (avg x n ω) S := by
      rw [← dist_eq_norm]
      exact le_antisymm ((Metric.le_infDist hne).mpr (fun z hz => hmin z hz))
        (Metric.infDist_le_dist_of_mem hyS)
    set d := Metric.infDist (avg x n ω) S with hd
    rw [hdist] at hle
    refine hle.trans ?_
    have hb2 : 1 / ((n : ℝ) + 1) ^ 2 = b ^ 2 := by rw [hb]; field_simp
    have h2 : (2 * (n : ℝ) / ((n : ℝ) + 1) ^ 2) * inner ℝ (avg x n ω - y) (M - y) ≤
        2 * κ * b ^ 2 := by
      calc (2 * (n : ℝ) / ((n : ℝ) + 1) ^ 2) * inner ℝ (avg x n ω - y) (M - y)
          ≤ (2 * (n : ℝ) / ((n : ℝ) + 1) ^ 2) * (κ / n) := mul_le_mul_of_nonneg_left hin hc2
        _ = 2 * κ * b ^ 2 := by rw [← hb2]; field_simp
    have ha2 : ((n : ℝ) / ((n : ℝ) + 1)) ^ 2 = (1 - b) ^ 2 := by
      rw [hb]; field_simp; ring
    have e1 : (2 * ρ + d) ^ 2 / ((n : ℝ) + 1) ^ 2 = b ^ 2 * (2 * ρ + d) ^ 2 := by
      rw [← hb2]; ring
    have e2 : (A0 ^ 2 + (2 * ρ + A0) ^ 2 + 2 * κ) / ((n : ℝ) + 1) ^ 2 =
        b ^ 2 * (A0 ^ 2 + (2 * ρ + A0) ^ 2 + 2 * κ) := by
      rw [← hb2]; ring
    have e3 : 2 / ((n : ℝ) + 1) = 2 * b := by rw [hb]; ring
    have h4 : d ^ 2 ≤ A0 ^ 2 := pow_le_pow_left₀ hd0 hdA 2
    have h5 : (2 * ρ + d) ^ 2 ≤ (2 * ρ + A0) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    rw [ha2, e1, e2, e3]
    nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg b),
      mul_le_mul_of_nonneg_left h5 (sq_nonneg b), h2]


theorem past_mono (hp : G.IsPlay f g μ x) {j m : ℕ} (hjm : j ≤ m) : past x j ≤ past x m := by
  have hg : Measurable (fun (h : Fin m → E N) (i : Fin j) => h (Fin.castLE hjm i)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have : hist x j = (fun (h : Fin m → E N) (i : Fin j) => h (Fin.castLE hjm i)) ∘ hist x m := rfl
  unfold past
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hg.comap_le

/-- The squared distance of the running average to `S`. -/
noncomputable def dsq (S : Set (E N)) (x : ℕ → Ω → E N) (n : ℕ) (ω : Ω) : ℝ :=
  (Metric.infDist (avg x n ω) S) ^ 2

theorem measurable_dsq_past (S : Set (E N)) (n : ℕ) : Measurable[past x n] (dsq S x n) := by
  have h := measurable_avg_past (x := x) n
  exact ((Metric.continuous_infDist_pt S).measurable.comp h).pow_const 2

theorem measurable_dsq (hp : G.IsPlay f g μ x) (S : Set (E N)) (n : ℕ) :
    Measurable (dsq S x n) :=
  (measurable_dsq_past (x := x) S n).mono (past_le hp n) le_rfl

theorem pastSigma_le (hp : G.IsPlay f g μ x) (S : Set (E N)) (m : ℕ) :
    pastSigma (dsq S x) m ≤ past x m := by
  unfold pastSigma
  have hmeas : Measurable[past x m] (fun ω (i : Fin m) => dsq S x (i.val + 1) ω) := by
    refine @measurable_pi_lambda Ω (Fin m) (fun _ => ℝ) (past x m) _ _ (fun i => ?_)
    have h1 : Measurable[past x (i.val + 1)] (dsq S x (i.val + 1)) := measurable_dsq_past S _
    exact h1.mono (past_mono hp (by omega)) le_rfl
  exact hmeas.comap_le

theorem dsq_bounds (hp : G.IsPlay f g μ x) {S : Set (E N)} {A0 : ℝ}
    (hA0 : ∀ z ∈ G.X, Metric.infDist z S ≤ A0) :
    ∀ᵐ ω ∂μ, ∀ n, 1 ≤ n → 0 ≤ dsq S x n ω ∧ dsq S x n ω ≤ A0 ^ 2 := by
  filter_upwards [ae_all_mem_X hp] with ω hX n hn
  have hd0 : 0 ≤ Metric.infDist (avg x n ω) S := Metric.infDist_nonneg
  exact ⟨sq_nonneg _, pow_le_pow_left₀ hd0 (hA0 _ (avg_mem_X hX hn)) 2⟩


theorem measurable_dsq_pastSigma (S : Set (E N)) (m : ℕ) (hm : 1 ≤ m) :
    Measurable[pastSigma (dsq S x) m] (dsq S x m) := by
  have h := @measurable_pi_apply (Fin m) (fun _ => ℝ) _ ⟨m - 1, by omega⟩
  have h2 : Measurable[pastSigma (dsq S x) m] (fun ω (i : Fin m) => dsq S x (i.val + 1) ω) :=
    Measurable.of_comap_le le_rfl
  have h3 := h.comp h2
  convert h3 using 1
  funext ω
  simp [Nat.sub_add_cancel hm]

theorem satisfies_recursion (hp : G.IsPlay f g μ x) {S : Set (E N)} (hne : S.Nonempty) {κ : ℝ}
    (hκ : 0 ≤ κ)
    (hslack : ∀ n, 1 ≤ n → ∀ h : Fin n → E N, avgHist h ∈ G.X → avgHist h ∉ S →
      ∃ y ∈ S, (∀ z ∈ S, dist (avgHist h) y ≤ dist (avgHist h) z) ∧
        ∀ w ∈ G.R (f.toFun n h), inner ℝ (avgHist h - y) (w - y) ≤ κ / n)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ z ∈ G.X, ‖z‖ ≤ ρ) {A0 : ℝ}
    (hA0 : ∀ z ∈ G.X, Metric.infDist z S ≤ A0) :
    SatisfiesRecursion (A0 ^ 2) (4 * ρ * A0) (A0 ^ 2 + (2 * ρ + A0) ^ 2 + 2 * κ) μ
      (dsq S x) := by
  classical
  have hbnd := dsq_bounds (S := S) hp hA0
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 1 ≤ m := by omega
    simp only [Nat.add_sub_cancel]
    have hsb := step_bound hp hne hκ hslack hρ0 hρ hA0 hm
    have hG := past_le hp m
    have hH := pastSigma_le hp S m
    have hδint : Integrable (dsq S x (m + 1)) μ := by
      refine Integrable.of_bound (measurable_dsq hp S (m + 1)).aestronglyMeasurable (A0 ^ 2) ?_
      filter_upwards [hbnd] with ω h
      rw [Real.norm_eq_abs, abs_of_nonneg (h (m + 1) (by omega)).1]
      exact (h (m + 1) (by omega)).2
    set RHS : Ω → ℝ := fun ω => (1 - 2 / ((m : ℝ) + 1)) * dsq S x m ω +
      (A0 ^ 2 + (2 * ρ + A0) ^ 2 + 2 * κ) / ((m : ℝ) + 1) ^ 2 with hRHS
    have hRHSm : Measurable[pastSigma (dsq S x) m] RHS :=
      ((measurable_dsq_pastSigma S m hm).const_mul _).add_const _
    have hHle : pastSigma (dsq S x) m ≤ (inferInstance : MeasurableSpace Ω) := hH.trans hG
    have hRHSint : Integrable RHS μ := by
      have : Integrable (dsq S x m) μ := by
        refine Integrable.of_bound (measurable_dsq hp S m).aestronglyMeasurable (A0 ^ 2) ?_
        filter_upwards [hbnd] with ω h
        rw [Real.norm_eq_abs, abs_of_nonneg (h m hm).1]
        exact (h m hm).2
      exact (this.const_mul _).add (integrable_const _)
    have h1 : μ[μ[dsq S x (m + 1) | past x m] | pastSigma (dsq S x) m] =ᵐ[μ]
        μ[dsq S x (m + 1) | pastSigma (dsq S x) m] := condExp_condExp_of_le hH hG
    have h2 : μ[μ[dsq S x (m + 1) | past x m] | pastSigma (dsq S x) m] ≤ᵐ[μ]
        μ[RHS | pastSigma (dsq S x) m] :=
      condExp_mono integrable_condExp hRHSint (hsb.mono fun ω h => h)
    have h3 : μ[RHS | pastSigma (dsq S x) m] = RHS :=
      condExp_of_stronglyMeasurable hHle hRHSm.stronglyMeasurable hRHSint
    rw [h3] at h2
    filter_upwards [h1, h2] with ω e1 e2 _
    rw [← e1]
    push_cast
    exact e2
  · intro n hn
    filter_upwards [hbnd] with ω h using h n hn
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 1 ≤ m := by omega
    simp only [Nat.add_sub_cancel]
    filter_upwards [hbnd, ae_all_mem_X hp] with ω h hX
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hav : avg x m ω ∈ G.X := avg_mem_X hX hm
    have hxX : x (m + 1) ω ∈ G.X := hX (m + 1) (by omega)
    have hstep : avg x (m + 1) ω - avg x m ω = (1 / ((m : ℝ) + 1)) • (x (m + 1) ω - avg x m ω) := by
      rw [avg_succ, smul_sub]
      have : ((m : ℝ) / ((m : ℝ) + 1)) = 1 - 1 / ((m : ℝ) + 1) := by field_simp; ring
      rw [this, sub_smul, one_smul]
      abel
    have hdist : dist (avg x (m + 1) ω) (avg x m ω) ≤ 2 * ρ / ((m : ℝ) + 1) := by
      rw [dist_eq_norm, hstep, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have : ‖x (m + 1) ω - avg x m ω‖ ≤ 2 * ρ :=
        (norm_sub_le _ _).trans (by linarith [hρ _ hxX, hρ _ hav])
      calc 1 / ((m : ℝ) + 1) * ‖x (m + 1) ω - avg x m ω‖ ≤ 1 / ((m : ℝ) + 1) * (2 * ρ) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = 2 * ρ / ((m : ℝ) + 1) := by ring
    have hlip : |Metric.infDist (avg x (m + 1) ω) S - Metric.infDist (avg x m ω) S| ≤
        2 * ρ / ((m : ℝ) + 1) := by
      refine (abs_sub_le_iff.mpr ⟨?_, ?_⟩)
      · have := Metric.infDist_le_infDist_add_dist (x := avg x (m + 1) ω) (y := avg x m ω) (s := S)
        linarith
      · have := Metric.infDist_le_infDist_add_dist (x := avg x m ω) (y := avg x (m + 1) ω) (s := S)
        rw [dist_comm] at this
        linarith
    have hd1 := hA0 _ (avg_mem_X hX (by omega : 1 ≤ m + 1))
    have hd2 := hA0 _ hav
    have hn1 : 0 ≤ Metric.infDist (avg x (m + 1) ω) S := Metric.infDist_nonneg
    have hn2 : 0 ≤ Metric.infDist (avg x m ω) S := Metric.infDist_nonneg
    unfold dsq
    push_cast
    set u := Metric.infDist (avg x (m + 1) ω) S with hu
    set v := Metric.infDist (avg x m ω) S with hv
    have e : u ^ 2 - v ^ 2 = (u - v) * (u + v) := by ring
    rw [e, abs_mul, abs_of_nonneg (add_nonneg hn1 hn2)]
    calc |u - v| * (u + v) ≤ (2 * ρ / ((m : ℝ) + 1)) * (2 * A0) :=
          mul_le_mul hlip (by linarith) (add_nonneg hn1 hn2) (by positivity)
      _ = 4 * ρ * A0 / ((m : ℝ) + 1) := by ring

end Play

theorem approachable_of_slack_proof {N r s : ℕ} (G : Game N r s) (S : Set (E N)) (κ : ℝ)
    (hκ : 0 ≤ κ) (f : Strategy N r)
    (hslack : ∀ n, 1 ≤ n → ∀ h : Fin n → E N, avgHist h ∈ G.X → avgHist h ∉ S →
      ∃ y ∈ S, (∀ z ∈ S, dist (avgHist h) y ≤ dist (avgHist h) z) ∧
        ∀ w ∈ G.R (f.toFun n h), inner ℝ (avgHist h - y) (w - y) ≤ κ / n) :
    G.ApproachableWith S f := by
  classical
  intro ε hε
  by_cases hne : S.Nonempty
  swap
  · refine ⟨0, ?_⟩
    intro g Ω _ μ _ x hx
    exfalso
    have hs : 0 < s := by
      by_contra h0
      have : s = 0 := by omega
      subst this
      have := (g.mem 0 (fun _ => 0)).2
      simp at this
    have hXne : G.X.Nonempty := by
      by_contra hX
      rw [Set.not_nonempty_iff_eq_empty] at hX
      have hr : 0 < r := by
        by_contra h0
        have : r = 0 := by omega
        subst this
        have := (f.mem 0 (fun _ => 0)).2
        simp at this
      have h1 := G.isProb ⟨0, hr⟩ ⟨0, hs⟩
      have h2 := G.m_compl_X ⟨0, hr⟩ ⟨0, hs⟩
      rw [hX, Set.compl_empty] at h2
      simp at h2
    obtain ⟨x₀, hx₀⟩ := hXne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    obtain ⟨y, hy, _⟩ := hslack 1 le_rfl (fun _ => x₀) (by simpa [avgHist] using hx₀)
      (by simp [hne])
    simp [hne] at hy
  obtain ⟨s₀, hs₀⟩ := hne
  obtain ⟨ρ, hρ0, hρ⟩ := G.exists_norm_bound
  set A0 : ℝ := ρ + ‖s₀‖ with hA0def
  have hA00 : 0 ≤ A0 := by positivity
  have hA0 : ∀ z ∈ G.X, Metric.infDist z S ≤ A0 := by
    intro z hz
    refine (Metric.infDist_le_dist_of_mem hs₀).trans ?_
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (add_le_add (hρ z hz) le_rfl)
  have hne : S.Nonempty := ⟨s₀, hs₀⟩
  have hε' : 0 < min ε (ε ^ 2) := lt_min hε (by positivity)
  obtain ⟨N₀, hN₀⟩ := blackwell_lemma (A0 ^ 2) (4 * ρ * A0) (A0 ^ 2 + (2 * ρ + A0) ^ 2 + 2 * κ)
    (min ε (ε ^ 2)) hε'
  refine ⟨N₀, ?_⟩
  intro g Ω _ μ _ x hx
  have hrec := satisfies_recursion hx hne hκ hslack hρ0 hρ hA0
  have hlt := hN₀ Ω μ (dsq S x) (fun n hn => measurable_dsq hx S n) hrec
  have hsub : {ω | ∃ n, N₀ ≤ n ∧ 1 ≤ n ∧ ENNReal.ofReal ε ≤ Metric.infEDist (avg x n ω) S} ⊆
      {ω | ∃ n, N₀ ≤ n ∧ 1 ≤ n ∧ min ε (ε ^ 2) ≤ dsq S x n ω} := by
    rintro ω ⟨n, hn0, hn1, hle⟩
    refine ⟨n, hn0, hn1, ?_⟩
    have hfin : Metric.infEDist (avg x n ω) S ≠ ⊤ := fun h =>
      hne.ne_empty (Metric.infEDist_eq_top_iff.mp h)
    have h1 : ε ≤ Metric.infDist (avg x n ω) S := by
      rw [Metric.infDist]
      exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hle
    unfold dsq
    calc min ε (ε ^ 2) ≤ ε ^ 2 := min_le_right _ _
      _ ≤ (Metric.infDist (avg x n ω) S) ^ 2 := pow_le_pow_left₀ hε.le h1 2
  calc (μ {ω | ∃ n, N₀ ≤ n ∧ 1 ≤ n ∧ ENNReal.ofReal ε ≤ Metric.infEDist (avg x n ω) S}).toReal
      ≤ (μ {ω | ∃ n, N₀ ≤ n ∧ 1 ≤ n ∧ min ε (ε ^ 2) ≤ dsq S x n ω}).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    _ < min ε (ε ^ 2) := hlt
    _ ≤ ε := min_le_left _ _

end Game

end VectorPayoffs.Convex

open VectorPayoffs.Convex in
theorem solution {N r s : ℕ} (G : Game N r s) (S : Set (E N)) (κ : ℝ) (hκ : 0 ≤ κ)
    (f : Strategy N r)
    (hslack : ∀ n, 1 ≤ n → ∀ h : Fin n → E N, avgHist h ∈ G.X → avgHist h ∉ S →
      ∃ y ∈ S, (∀ z ∈ S, dist (avgHist h) y ≤ dist (avgHist h) z) ∧
        ∀ w ∈ G.R (f.toFun n h), inner ℝ (avgHist h - y) (w - y) ≤ κ / n) :
    G.ApproachableWith S f :=
  Game.approachable_of_slack_proof G S κ hκ f hslack
