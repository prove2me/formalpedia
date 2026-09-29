-- Prove2me | solution 1 for VectorPayoffs.Convex.theorem1_recursion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:32:43.654205+00:00
-- url     : https://prove2.me/submissions/c2111f64-30ed-41c8-a93d-4e59ccd31179

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game
import Definitions.Def_VectorPayoffs_Convex_Recursion

open MeasureTheory

namespace VectorPayoffs.Convex

open ProbabilityTheory

/-- The conditional law of the next outcome given a history `h` of length `m`. -/
noncomputable def aux_tr_ker {N r s : ℕ} (G : Game N r s) (f : Strategy N r) (g : Strategy N s)
    (m : ℕ) : Kernel (Fin m → E N) (E N) where
  toFun h := ∑ i, ∑ j, ENNReal.ofReal (f.toFun m h i * g.toFun m h j) • G.m i j
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ (fun B _ => ?_)
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
    exact (ENNReal.measurable_ofReal.comp
      (((measurable_pi_apply i).comp (f.meas m)).mul
        ((measurable_pi_apply j).comp (g.meas m)))).mul_const _

lemma aux_tr_ker_eq {N r s : ℕ} (G : Game N r s) (f : Strategy N r) (g : Strategy N s)
    (m : ℕ) (h : Fin m → E N) :
    aux_tr_ker G f g m h = ∑ i, ∑ j, ENNReal.ofReal (f.toFun m h i * g.toFun m h j) • G.m i j :=
  rfl

lemma aux_tr_ker_apply {N r s : ℕ} (G : Game N r s) (f : Strategy N r) (g : Strategy N s)
    (m : ℕ) (h : Fin m → E N) (B : Set (E N)) :
    aux_tr_ker G f g m h B =
      ∑ i, ∑ j, ENNReal.ofReal (f.toFun m h i * g.toFun m h j) * G.m i j B := by
  rw [aux_tr_ker_eq]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]

lemma aux_tr_sum_ofReal {r s : ℕ} (p : Fin r → ℝ) (q : Fin s → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ j, 0 ≤ q j) (a : Fin r → Fin s → ENNReal) (ha : ∀ i j, a i j ≠ ⊤) :
    ∑ i, ∑ j, ENNReal.ofReal (p i * q j) * a i j =
      ENNReal.ofReal (∑ i, ∑ j, p i * q j * (a i j).toReal) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (hp i) (hq j)) ENNReal.toReal_nonneg))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (hp i) (hq j)) ENNReal.toReal_nonneg)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ENNReal.ofReal_mul (mul_nonneg (hp i) (hq j)), ENNReal.ofReal_toReal (ha i j)]

instance aux_tr_ker_markov {N r s : ℕ} (G : Game N r s) (f : Strategy N r) (g : Strategy N s)
    (m : ℕ) : IsMarkovKernel (aux_tr_ker G f g m) := by
  refine ⟨fun h => ⟨?_⟩⟩
  rw [aux_tr_ker_apply]
  rw [aux_tr_sum_ofReal _ _ (f.mem m h).1 (g.mem m h).1 _
    (fun i j => by have := G.isProb i j; exact measure_ne_top _ _)]
  have h1 : ∀ i j, (G.m i j Set.univ).toReal = 1 := fun i j => by
    have := G.isProb i j; simp
  simp only [h1, mul_one]
  rw [← Finset.sum_mul_sum, (f.mem m h).2, (g.mem m h).2, mul_one, ENNReal.ofReal_one]

lemma aux_tr_hist_meas {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {x : ℕ → Ω → E N}
    (hx : ∀ n, Measurable (x (n + 1))) (m : ℕ) : Measurable (hist x m) :=
  measurable_pi_lambda _ (fun k => hx k.val)

lemma aux_tr_joint {N r s : ℕ} (G : Game N r s) (f : Strategy N r) (g : Strategy N s)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (x : ℕ → Ω → E N)
    (hx : G.IsPlay f g μ x) (m : ℕ) :
    μ.map (fun ω => (hist x m ω, x (m+1) ω)) = μ.map (hist x m) ⊗ₘ aux_tr_ker G f g m := by
  have hH : Measurable (hist x m) := aux_tr_hist_meas hx.1 m
  have hY : Measurable (x (m+1)) := hx.1 m
  have hle : MeasurableSpace.comap (hist x m) inferInstance ≤ ‹MeasurableSpace Ω› := hH.comap_le
  refine Measure.ext_prod (fun {A B} hA hB => ?_)
  rw [Measure.map_apply (hH.prodMk hY) (hA.prod hB), Measure.compProd_apply_prod hA hB,
    setLIntegral_map hA (Kernel.measurable_coe _ hB) hH, Set.mk_preimage_prod]
  set F : Ω → ℝ := fun ω => ∑ i, ∑ j, f.toFun m (hist x m ω) i * g.toFun m (hist x m ω) j *
    (G.m i j B).toReal with hF
  have hce : μ[(x (m + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap (hist x m) inferInstance] =ᵐ[μ] F := hx.2 m B hB
  have hFint : Integrable F μ := integrable_condExp.congr hce
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg ((f.mem m _).1 i) ((g.mem m _).1 j)) ENNReal.toReal_nonneg))
  have hk : ∀ ω, aux_tr_ker G f g m (hist x m ω) B = ENNReal.ofReal (F ω) := by
    intro ω
    rw [aux_tr_ker_apply, aux_tr_sum_ofReal _ _ (f.mem m _).1 (g.mem m _).1 _
      (fun i j => by have := G.isProb i j; exact measure_ne_top _ _)]
  simp_rw [hk]
  rw [← ofReal_integral_eq_lintegral_ofReal hFint.integrableOn (ae_of_all _ hF0),
    integral_congr_ae (ae_restrict_of_ae hce.symm),
    setIntegral_condExp hle ((integrable_const (1:ℝ)).indicator (hY hB)) ⟨A, hA, rfl⟩,
    setIntegral_indicator (hY hB), setIntegral_const, smul_eq_mul, mul_one, ofReal_measureReal]

/-- The squared distance of the next average from `S`, as a function of (history, outcome). -/
noncomputable def aux_tr_phi {N : ℕ} (S : Set (E N)) (m : ℕ) (q : (Fin m → E N) × E N) : ℝ :=
  Metric.infDist (((m:ℝ)+1)⁻¹ • (∑ k, q.1 k + q.2)) S ^ 2

lemma aux_tr_phi_cont {N : ℕ} (S : Set (E N)) (m : ℕ) : Continuous (aux_tr_phi S m) := by
  have h1 : Continuous (fun q : (Fin m → E N) × E N => ((m:ℝ)+1)⁻¹ • (∑ k, q.1 k + q.2)) := by
    fun_prop
  exact ((Metric.continuous_infDist_pt S).comp h1).pow 2

lemma aux_tr_cont_avg {N : ℕ} (S : Set (E N)) (k : ℕ) :
    Continuous (fun h : Fin k → E N => Metric.infDist (avgHist h) S ^ 2) := by
  have h1 : Continuous (fun h : Fin k → E N => avgHist h) := by
    unfold avgHist; fun_prop
  exact ((Metric.continuous_infDist_pt S).comp h1).pow 2

lemma aux_tr_avg_succ {N : ℕ} {Ω : Type} (x : ℕ → Ω → E N) (m : ℕ) (ω : Ω) :
    avg x (m+1) ω = ((m:ℝ)+1)⁻¹ • (∑ k, hist x m ω k + x (m+1) ω) := by
  simp only [avg, avgHist, hist, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
  push_cast
  rfl

lemma aux_tr_split {N m : ℕ} (hm : 1 ≤ m) (h : Fin m → E N) (z : E N) :
    ((m:ℝ)+1)⁻¹ • (∑ k, h k + z) = avgHist h + ((m:ℝ)+1)⁻¹ • (z - avgHist h) := by
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hsum : ∑ k, h k = (m:ℝ) • avgHist h := by
    unfold avgHist; rw [smul_smul, mul_inv_cancel₀ hm', one_smul]
  rw [hsum]
  have hc : ((m:ℝ)+1)⁻¹ * m = 1 - ((m:ℝ)+1)⁻¹ := by
    field_simp
    ring
  rw [smul_add, smul_smul, hc, smul_sub, sub_smul, one_smul]
  abel

lemma aux_tr_avg_mem {N r s : ℕ} (G : Game N r s) {m : ℕ} (hm : 1 ≤ m) (h : Fin m → E N)
    (hX : ∀ k, h k ∈ G.X) : avgHist h ∈ G.X := by
  unfold avgHist
  rw [Finset.smul_sum]
  refine G.convex_X.sum_mem (fun _ _ => by positivity) ?_ (fun k _ => hX k)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast (show m ≠ 0 by omega))

lemma aux_tr_memX {N r s : ℕ} (G : Game N r s) (f : Strategy N r) (g : Strategy N s)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (x : ℕ → Ω → E N)
    (hx : G.IsPlay f g μ x) (k : ℕ) : ∀ᵐ ω ∂μ, x (k+1) ω ∈ G.X := by
  have hB : MeasurableSet (G.Xᶜ) := G.isClosed_X.measurableSet.compl
  have hle : MeasurableSpace.comap (hist x k) inferInstance ≤ ‹MeasurableSpace Ω› :=
    (aux_tr_hist_meas hx.1 k).comap_le
  have h1 := hx.2 k _ hB
  simp only [G.m_compl_X, ENNReal.toReal_zero, mul_zero, Finset.sum_const_zero] at h1
  have h2 : ∫ ω, (x (k+1) ⁻¹' G.Xᶜ).indicator (fun _ => (1:ℝ)) ω ∂μ = 0 := by
    rw [← integral_condExp hle, integral_congr_ae h1]
    simp
  rw [integral_indicator ((hx.1 k) hB), setIntegral_const, smul_eq_mul, mul_one,
    measureReal_eq_zero_iff] at h2
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h2] with ω hω
  simpa using hω

lemma aux_tr_int_id {N : ℕ} (X : Set (E N)) (hXb : Bornology.IsBounded X) (ν : Measure (E N))
    [IsFiniteMeasure ν] (hν : ν Xᶜ = 0) : Integrable (fun z => z) ν := by
  obtain ⟨R, hR⟩ := hXb.subset_closedBall 0
  refine Integrable.of_bound measurable_id.aestronglyMeasurable R ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hν] with z hz
  have : z ∈ X := by simpa using hz
  simpa using hR this

lemma aux_tr_mean {N r s : ℕ} (G : Game N r s) (f : Strategy N r) (g : Strategy N s) (m : ℕ)
    (h : Fin m → E N) :
    ∫ z, z ∂(aux_tr_ker G f g m h) = ∑ i, ∑ j, (f.toFun m h i * g.toFun m h j) • G.mbar i j := by
  have hI : ∀ i j, Integrable (fun z : E N => z) (G.m i j) := fun i j => by
    have := G.isProb i j
    exact aux_tr_int_id G.X G.isBounded_X _ (G.m_compl_X i j)
  rw [aux_tr_ker_eq, integral_finsetSum_measure (fun i _ => integrable_finsetSum_measure.2
    (fun j _ => (hI i j).smul_measure ENNReal.ofReal_ne_top))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finsetSum_measure (fun j _ => (hI i j).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_smul_measure,
    ENNReal.toReal_ofReal (mul_nonneg ((f.mem m h).1 i) ((g.mem m h).1 j))]
  rfl

lemma aux_tr_det {N r s : ℕ} (G : Game N r s) (S : Set (E N))
    (p : E N → Fin r → ℝ)
    (hsep : ∀ x ∉ S, p x ∈ stdSimplex ℝ (Fin r) ∧ G.BlackwellCondition S (p x) x)
    (f : Strategy N r) (g : Strategy N s)
    (hf : ∀ n, 1 ≤ n → ∀ h : Fin n → E N, avgHist h ∉ S → f.toFun n h = p (avgHist h))
    {m : ℕ} (hm : 1 ≤ m) (h : Fin m → E N) (hX : ∀ k, h k ∈ G.X) :
    ∫ z, aux_tr_phi S m (h, z) ∂(aux_tr_ker G f g m h) ≤
      (1 - 2 / ((m:ℝ)+1)) * Metric.infDist (avgHist h) S ^ 2 +
        Metric.diam G.X ^ 2 / ((m:ℝ)+1) ^ 2 := by
  have hAX : avgHist h ∈ G.X := aux_tr_avg_mem G hm h hX
  have hw0R : (∑ i, ∑ j, (f.toFun m h i * g.toFun m h j) • G.mbar i j) ∈ G.R (f.toFun m h) := by
    have hq := g.mem m h
    have e : (∑ i, ∑ j, (f.toFun m h i * g.toFun m h j) • G.mbar i j) =
        ∑ j, g.toFun m h j • ∑ i, f.toFun m h i • G.mbar i j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_smul, mul_comm]
    rw [e]
    exact (convex_convexHull ℝ _).sum_mem (fun j _ => hq.1 j) hq.2
      (fun j _ => subset_convexHull ℝ _ (Set.mem_range_self j))
  obtain ⟨y, hyS, hyd, hyw⟩ : ∃ y ∈ S, dist (avgHist h) y ≤ Metric.infDist (avgHist h) S ∧
      inner ℝ (avgHist h - y)
        ((∑ i, ∑ j, (f.toFun m h i * g.toFun m h j) • G.mbar i j) - y) ≤ 0 := by
    by_cases hAS : avgHist h ∈ S
    · exact ⟨avgHist h, hAS, by simp [Metric.infDist_nonneg], by simp⟩
    · obtain ⟨_, y, hyS, hcl, hsepw⟩ := hsep (avgHist h) hAS
      refine ⟨y, hyS, (Metric.le_infDist ⟨y, hyS⟩).2 hcl, ?_⟩
      have hfe := hf m hm h hAS
      have hRe : G.R (f.toFun m h) = G.R (p (avgHist h)) := by rw [hfe]
      rw [hRe] at hw0R
      exact hsepw _ hw0R
  have ht0 : 0 < ((m:ℝ)+1)⁻¹ := by positivity
  have ht2 : 2 * ((m:ℝ)+1)⁻¹ ≤ 1 := by
    have : (2:ℝ) ≤ (m:ℝ) + 1 := by
      have : (1:ℝ) ≤ m := by exact_mod_cast hm
      linarith
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    exact this
  generalize ht : ((m:ℝ)+1)⁻¹ = t at ht0 ht2
  generalize hA : avgHist h = A at hAX hyd hyw
  generalize hw : (∑ i, ∑ j, (f.toFun m h i * g.toFun m h j) • G.mbar i j) = w0 at hyw
  have hu : ‖A - y‖ ≤ Metric.infDist A S := by rw [← dist_eq_norm]; exact hyd
  have hc0 : 0 ≤ Metric.diam G.X := Metric.diam_nonneg
  have hker0 : aux_tr_ker G f g m h G.Xᶜ = 0 := by
    rw [aux_tr_ker_apply]; simp [G.m_compl_X]
  have hae : ∀ᵐ z ∂(aux_tr_ker G f g m h), z ∈ G.X := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hker0] with z hz
    simpa using hz
  have hid : Integrable (fun z : E N => z) (aux_tr_ker G f g m h) :=
    aux_tr_int_id G.X G.isBounded_X _ hker0
  set K : ℝ := (1 - 2 * t) * Metric.infDist A S ^ 2 - 2 * t * inner ℝ (A - y) y +
    t ^ 2 * Metric.diam G.X ^ 2 with hK
  have hpt : ∀ z ∈ G.X, aux_tr_phi S m (h, z) ≤ K + 2 * t * inner ℝ (A - y) z := by
    intro z hz
    have hsplit := aux_tr_split hm h z
    rw [ht, hA] at hsplit
    have h1 : aux_tr_phi S m (h, z) ≤ ‖(A - y) + t • (z - A)‖ ^ 2 := by
      unfold aux_tr_phi
      simp only
      rw [ht, hsplit]
      have := Metric.infDist_le_dist_of_mem (x := A + t • (z - A)) hyS
      rw [dist_eq_norm] at this
      have e : A + t • (z - A) - y = (A - y) + t • (z - A) := by abel
      rw [e] at this
      exact pow_le_pow_left₀ Metric.infDist_nonneg this 2
    have h2 : ‖(A - y) + t • (z - A)‖ ^ 2 =
        ‖A - y‖ ^ 2 + 2 * t * inner ℝ (A - y) (z - A) + t ^ 2 * ‖z - A‖ ^ 2 := by
      rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg ht0.le]
      ring
    have h3 : inner ℝ (A - y) (z - A) = inner ℝ (A - y) z - inner ℝ (A - y) y - ‖A - y‖ ^ 2 := by
      have e2 : z - A = (z - y) - (A - y) := by abel
      rw [e2, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq]
    have h4 : ‖z - A‖ ≤ Metric.diam G.X := by
      rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem G.isBounded_X hz hAX
    have h5 : ‖A - y‖ ^ 2 ≤ Metric.infDist A S ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
    have h6 : ‖z - A‖ ^ 2 ≤ Metric.diam G.X ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h4 2
    rw [h2, h3] at h1
    have h7 : (1 - 2*t) * ‖A - y‖ ^ 2 ≤ (1 - 2*t) * Metric.infDist A S ^ 2 :=
      mul_le_mul_of_nonneg_left h5 (by linarith)
    have h8 : t ^ 2 * ‖z - A‖ ^ 2 ≤ t ^ 2 * Metric.diam G.X ^ 2 :=
      mul_le_mul_of_nonneg_left h6 (by positivity)
    rw [hK]
    linear_combination h1 + h7 + h8
  have hgint : Integrable (fun z => K + 2 * t * inner ℝ (A - y) z) (aux_tr_ker G f g m h) :=
    (integrable_const K).add ((hid.const_inner (A - y)).const_mul (2 * t))
  have hmono : ∫ z, aux_tr_phi S m (h, z) ∂(aux_tr_ker G f g m h) ≤
      ∫ z, (K + 2 * t * inner ℝ (A - y) z) ∂(aux_tr_ker G f g m h) :=
    integral_mono_of_nonneg (ae_of_all _ (fun z => by unfold aux_tr_phi; positivity)) hgint
      (by filter_upwards [hae] with z hz; exact hpt z hz)
  have hval : ∫ z, (K + 2 * t * inner ℝ (A - y) z) ∂(aux_tr_ker G f g m h) =
      K + 2 * t * inner ℝ (A - y) w0 := by
    rw [integral_add (integrable_const K) ((hid.const_inner (A - y)).const_mul (2 * t)),
      integral_const, integral_const_mul, integral_inner hid (A - y), aux_tr_mean, hw]
    simp
  rw [hval] at hmono
  have hin : inner ℝ (A - y) w0 - inner ℝ (A - y) y ≤ 0 := by
    rw [← inner_sub_right]; exact hyw
  have e1 : 2 / ((m:ℝ)+1) = 2 * t := by rw [← ht, div_eq_mul_inv]
  have e2 : Metric.diam G.X ^ 2 / ((m:ℝ)+1) ^ 2 = t ^ 2 * Metric.diam G.X ^ 2 := by
    rw [← ht, inv_pow, div_eq_mul_inv, mul_comm]
  rw [e1, e2]
  have h9 : 2 * t * (inner ℝ (A - y) w0 - inner ℝ (A - y) y) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hin
  rw [hK] at hmono
  linear_combination hmono + h9

lemma aux_tr_condexp {N r s : ℕ} (G : Game N r s) (S : Set (E N)) (f : Strategy N r)
    (g : Strategy N s) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : ℕ → Ω → E N) (hx : G.IsPlay f g μ x) (m : ℕ)
    (hint : Integrable (fun ω => aux_tr_phi S m (hist x m ω, x (m+1) ω)) μ) :
    μ[fun ω => aux_tr_phi S m (hist x m ω, x (m+1) ω) |
        MeasurableSpace.comap (hist x m) inferInstance]
      =ᵐ[μ] fun ω => ∫ z, aux_tr_phi S m (hist x m ω, z) ∂(aux_tr_ker G f g m (hist x m ω)) := by
  have hH := aux_tr_hist_meas hx.1 m
  have h1 := condExp_prod_ae_eq_integral_condDistrib hH (hx.1 m).aemeasurable
    (aux_tr_phi_cont S m).stronglyMeasurable hint
  have h2 := condDistrib_ae_eq_of_measure_eq_compProd (hist x m) (hx.1 m).aemeasurable
    (aux_tr_joint G f g μ x hx m)
  have h3 := ae_of_ae_map hH.aemeasurable h2
  filter_upwards [h1, h3] with ω hω1 hω2
  rw [hω1, hω2]

end VectorPayoffs.Convex

open VectorPayoffs.Convex
open MeasureTheory

theorem solution {N r s : ℕ} (G : Game N r s) (S : Set (E N)) (hS : IsClosed S)
    (p : E N → Fin r → ℝ)
    (hsep : ∀ x ∉ S, p x ∈ stdSimplex ℝ (Fin r) ∧ G.BlackwellCondition S (p x) x)
    (f : Strategy N r)
    (hf : ∀ n, 1 ≤ n → ∀ h : Fin n → E N, avgHist h ∉ S → f.toFun n h = p (avgHist h)) :
    ∃ a b : ℝ, ∀ (g : Strategy N s) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (x : ℕ → Ω → E N), G.IsPlay f g μ x →
        SatisfiesRecursion a b (Metric.diam G.X ^ 2) μ
          (fun n ω => Metric.infDist (avg x n ω) S ^ 2) := by
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    obtain ⟨_, y, hy, _⟩ := hsep 0 (by simp [hne])
    simp [hne] at hy
  obtain ⟨s0, hs0⟩ := hSne
  obtain ⟨R0, hR0⟩ := G.isBounded_X.subset_closedBall 0
  have hXR : ∀ z ∈ G.X, ‖z‖ ≤ max R0 0 := fun z hz =>
    (mem_closedBall_zero_iff.1 (hR0 hz)).trans (le_max_left _ _)
  have hR : 0 ≤ max R0 0 := le_max_right _ _
  generalize max R0 0 = R at hXR hR
  have hD : ∀ z ∈ G.X, Metric.infDist z S ≤ R + ‖s0‖ := fun z hz =>
    (Metric.infDist_le_dist_of_mem hs0).trans (by
      rw [dist_eq_norm]; exact (norm_sub_le _ _).trans (by linarith [hXR z hz]))
  have hD0 : 0 ≤ R + ‖s0‖ := by positivity
  generalize R + ‖s0‖ = D at hD hD0
  refine ⟨D ^ 2, 4 * D * R, ?_⟩
  intro g Ω _ μ _ x hx
  have hmemX : ∀ᵐ ω ∂μ, ∀ k, x (k+1) ω ∈ G.X :=
    ae_all_iff.2 (fun k => aux_tr_memX G f g μ x hx k)
  have havgX : ∀ᵐ ω ∂μ, ∀ n, 1 ≤ n → avg x n ω ∈ G.X := by
    filter_upwards [hmemX] with ω hω n hn
    exact aux_tr_avg_mem G hn _ (fun k => hω k.val)
  set δ : ℕ → Ω → ℝ := fun n ω => Metric.infDist (avg x n ω) S ^ 2 with hδ
  have hδmeas : ∀ k, Measurable (δ k) := fun k =>
    (aux_tr_cont_avg S k).measurable.comp (aux_tr_hist_meas hx.1 k)
  have hδbd : ∀ k, 1 ≤ k → ∀ᵐ ω ∂μ, 0 ≤ δ k ω ∧ δ k ω ≤ D ^ 2 := by
    intro k hk
    filter_upwards [havgX] with ω hω
    exact ⟨by positivity, pow_le_pow_left₀ Metric.infDist_nonneg (hD _ (hω k hk)) 2⟩
  have hδint : ∀ k, 1 ≤ k → Integrable (δ k) μ := fun k hk =>
    Integrable.of_bound (hδmeas k).aestronglyMeasurable (D ^ 2) (by
      filter_upwards [hδbd k hk] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg hω.1]; exact hω.2)
  refine ⟨?_, hδbd, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 1 ≤ m := by omega
    simp only [Nat.add_sub_cancel]
    have hH := aux_tr_hist_meas hx.1 m
    have hFle : MeasurableSpace.comap (hist x m) inferInstance ≤ ‹MeasurableSpace Ω› :=
      hH.comap_le
    have hPle : pastSigma δ m ≤ MeasurableSpace.comap (hist x m) inferInstance := by
      have hΨ : Measurable (fun (h : Fin m → E N) (i : Fin m) =>
          Metric.infDist (avgHist (fun k : Fin (i.val + 1) =>
            h ⟨k.val, Nat.lt_of_lt_of_le k.isLt i.isLt⟩)) S ^ 2) := by
        refine measurable_pi_lambda _ (fun i => ?_)
        exact ((aux_tr_cont_avg S (i.val+1)).comp
          (continuous_pi (fun k : Fin (i.val + 1) => continuous_apply
            (⟨k.val, Nat.lt_of_lt_of_le k.isLt i.isLt⟩ : Fin m)))).measurable
      have e : (fun ω (i : Fin m) => δ (i.val + 1) ω) = (fun (h : Fin m → E N) (i : Fin m) =>
          Metric.infDist (avgHist (fun k : Fin (i.val + 1) =>
            h ⟨k.val, Nat.lt_of_lt_of_le k.isLt i.isLt⟩)) S ^ 2) ∘ hist x m := rfl
      unfold pastSigma
      rw [e, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hΨ.comap_le
    have hsplitδ : δ (m+1) = fun ω => aux_tr_phi S m (hist x m ω, x (m+1) ω) := by
      funext ω
      simp only [hδ, aux_tr_phi]
      rw [aux_tr_avg_succ]
    have hce := aux_tr_condexp G S f g μ x hx m (hsplitδ ▸ hδint (m+1) (by omega))
    rw [← hsplitδ] at hce
    have hbd : ∀ᵐ ω ∂μ, ∫ z, aux_tr_phi S m (hist x m ω, z) ∂(aux_tr_ker G f g m (hist x m ω)) ≤
        (1 - 2 / ((m:ℝ)+1)) * δ m ω + Metric.diam G.X ^ 2 / ((m:ℝ)+1) ^ 2 := by
      filter_upwards [hmemX] with ω hω
      exact aux_tr_det G S p hsep f g hf hm (hist x m ω) (fun k => hω k.val)
    have hBint : Integrable (fun ω => (1 - 2 / ((m:ℝ)+1)) * δ m ω +
        Metric.diam G.X ^ 2 / ((m:ℝ)+1) ^ 2) μ :=
      ((hδint m hm).const_mul _).add (integrable_const _)
    have hδm : Measurable[pastSigma δ m] (δ m) := by
      have h1 : Measurable[pastSigma δ m] (fun ω (i : Fin m) => δ (i.val + 1) ω) :=
        comap_measurable _
      have h2 := (measurable_pi_apply (⟨m - 1, by omega⟩ : Fin m)).comp h1
      have e : (fun v : Fin m → ℝ => v ⟨m - 1, by omega⟩) ∘
          (fun ω (i : Fin m) => δ (i.val + 1) ω) = δ m := by
        funext ω
        simp only [Function.comp_apply, Nat.sub_add_cancel hm]
      rwa [e] at h2
    have hBsm : StronglyMeasurable[pastSigma δ m] (fun ω => (1 - 2 / ((m:ℝ)+1)) * δ m ω +
        Metric.diam G.X ^ 2 / ((m:ℝ)+1) ^ 2) :=
      ((hδm.const_mul _).add_const _).stronglyMeasurable
    have h1 := condExp_condExp_of_le (μ := μ) (f := δ (m+1)) hPle hFle
    have h2 := condExp_mono (m := pastSigma δ m) integrable_condExp hBint (hce.trans_le hbd)
    have h3 := condExp_of_stronglyMeasurable (hPle.trans hFle) hBsm hBint
    rw [h3] at h2
    filter_upwards [h1, h2] with ω hω1 hω2 _
    rw [← hω1]
    push_cast
    exact hω2
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 1 ≤ m := by omega
    simp only [Nat.add_sub_cancel]
    filter_upwards [havgX, hmemX] with ω hω hω'
    have hAX := hω m hm
    have hzX := hω' m
    have hPX := hω (m+1) (by omega)
    have hP : avg x (m+1) ω = avg x m ω + ((m:ℝ)+1)⁻¹ • (x (m+1) ω - avg x m ω) := by
      rw [aux_tr_avg_succ]; exact aux_tr_split hm (hist x m ω) (x (m+1) ω)
    have hdist : dist (avg x (m+1) ω) (avg x m ω) ≤ 2 * R / ((m:ℝ)+1) := by
      rw [hP, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by positivity)]
      have : ‖x (m+1) ω - avg x m ω‖ ≤ 2 * R :=
        (norm_sub_le _ _).trans (by linarith [hXR _ hzX, hXR _ hAX])
      rw [inv_mul_eq_div]
      exact div_le_div_of_nonneg_right this (by positivity)
    have hab : |Metric.infDist (avg x (m+1) ω) S - Metric.infDist (avg x m ω) S| ≤
        dist (avg x (m+1) ω) (avg x m ω) := by
      rw [abs_sub_le_iff]
      constructor
      · linarith [Metric.infDist_le_infDist_add_dist (s := S) (x := avg x (m+1) ω)
          (y := avg x m ω)]
      · linarith [Metric.infDist_le_infDist_add_dist (s := S) (x := avg x m ω)
          (y := avg x (m+1) ω), dist_comm (avg x m ω) (avg x (m+1) ω)]
    have hP0 := Metric.infDist_nonneg (x := avg x (m+1) ω) (s := S)
    have hA0 := Metric.infDist_nonneg (x := avg x m ω) (s := S)
    have hPD := hD _ hPX
    have hAD := hD _ hAX
    have e : Metric.infDist (avg x (m+1) ω) S ^ 2 - Metric.infDist (avg x m ω) S ^ 2 =
        (Metric.infDist (avg x (m+1) ω) S - Metric.infDist (avg x m ω) S) *
          (Metric.infDist (avg x (m+1) ω) S + Metric.infDist (avg x m ω) S) := by ring
    simp only [hδ]
    rw [e, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ Metric.infDist (avg x (m+1) ω) S +
      Metric.infDist (avg x m ω) S)]
    have e2 : 4 * D * R / ((m + 1 : ℕ) : ℝ) = (2 * R / ((m:ℝ)+1)) * (2 * D) := by
      push_cast; ring
    rw [e2]
    exact mul_le_mul (hab.trans hdist) (by linarith) (by positivity) (by positivity)
