-- Prove2me | solution 1 for VectorPayoffs.Convex.T_approachable_transpose
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:37:51.103258+00:00
-- url     : https://prove2.me/submissions/76f91653-0400-44fa-9997-397029fa408b

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game

open MeasureTheory

namespace VectorPayoffs.Convex

lemma aux_Tat_hist_meas {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (x : ℕ → Ω → E N)
    (hx : ∀ n, Measurable (x (n + 1))) (n : ℕ) : Measurable (hist x n) :=
  measurable_pi_lambda _ (fun k => hx k.val)

lemma aux_Tat_hist_le {N : ℕ} {Ω : Type} (x : ℕ → Ω → E N) {k n : ℕ} (h : k ≤ n) :
    Measurable[MeasurableSpace.comap (hist x n) inferInstance] (hist x k) := by
  refine @measurable_pi_lambda _ _ _ (MeasurableSpace.comap (hist x n) inferInstance) _ _ ?_
  intro i
  have : (fun ω => hist x k ω i) = (fun v : Fin n → E N => v (Fin.castLE h i)) ∘ hist x n := rfl
  rw [this]
  exact (measurable_pi_apply _).comp (comap_measurable _)

lemma aux_Tat_F_mono {N : ℕ} {Ω : Type} (x : ℕ → Ω → E N) {k n : ℕ} (h : k ≤ n) :
    MeasurableSpace.comap (hist x k) inferInstance ≤
      MeasurableSpace.comap (hist x n) inferInstance :=
  (aux_Tat_hist_le x h).comap_le

lemma aux_Tat_p_meas {N r : ℕ} (g : Strategy N r) {Ω : Type} (x : ℕ → Ω → E N) (k : ℕ)
    (i : Fin r) :
    Measurable[MeasurableSpace.comap (hist x k) inferInstance]
      (fun ω => g.toFun k (hist x k ω) i) :=
  (measurable_pi_apply i).comp ((g.meas k).comp (comap_measurable (hist x k)))

/-- The conditional mean of the next outcome. -/
noncomputable def aux_Tat_y {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ) (g : Strategy N r)
    {Ω : Type} (x : ℕ → Ω → E N) (n : ℕ) (ω : Ω) : E N :=
  ∑ j, ∑ i, (q₀ j * g.toFun n (hist x n ω) i) • G.mbar i j

lemma aux_Tat_y_meas {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ) (g : Strategy N r)
    {Ω : Type} (x : ℕ → Ω → E N) (n : ℕ) :
    Measurable[MeasurableSpace.comap (hist x n) inferInstance] (aux_Tat_y G q₀ g x n) := by
  unfold aux_Tat_y
  refine Finset.measurable_sum _ (fun j _ => ?_)
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact ((aux_Tat_p_meas g x n i).const_mul _).smul_const _

lemma aux_Tat_mbar_mem {N r s : ℕ} (G : Game N r s) (i : Fin r) (j : Fin s) :
    G.mbar i j ∈ G.X := by
  have := G.isProb i j
  obtain ⟨C, hC⟩ := G.isBounded_X.exists_norm_le
  have hae : ∀ᵐ z ∂(G.m i j), z ∈ G.X := ae_iff.2 (G.m_compl_X i j)
  have hint : Integrable (fun z : E N => z) (G.m i j) :=
    (integrable_const C).mono' aestronglyMeasurable_id (hae.mono fun z hz => hC z hz)
  exact G.convex_X.integral_mem G.isClosed_X hae hint

lemma aux_Tat_T_sub {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ)
    (hq₀ : q₀ ∈ stdSimplex ℝ (Fin s)) : G.T q₀ ⊆ G.X := by
  refine convexHull_min ?_ G.convex_X
  rintro _ ⟨i, rfl⟩
  exact G.convex_X.sum_mem (fun j _ => hq₀.1 j) hq₀.2 (fun j _ => aux_Tat_mbar_mem G i j)

lemma aux_Tat_y_mem {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ) (g : Strategy N r)
    {Ω : Type} (x : ℕ → Ω → E N) (n : ℕ) (ω : Ω) : aux_Tat_y G q₀ g x n ω ∈ G.T q₀ := by
  have hp := g.mem n (hist x n ω)
  have : aux_Tat_y G q₀ g x n ω =
      ∑ i, g.toFun n (hist x n ω) i • ∑ j, q₀ j • G.mbar i j := by
    unfold aux_Tat_y
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smul_smul, mul_comm]
  rw [this]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hp.1 i) hp.2
    (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)

lemma aux_Tat_simplex_le_one {k : ℕ} {v : Fin k → ℝ} (hv : v ∈ stdSimplex ℝ (Fin k)) (i : Fin k) :
    v i ≤ 1 := by
  have := Finset.single_le_sum (fun j _ => hv.1 j) (Finset.mem_univ i)
  rw [hv.2] at this
  exact this

lemma aux_Tat_p_int {N r : ℕ} (g : Strategy N r) {Ω : Type} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (x : ℕ → Ω → E N) (hx : ∀ n, Measurable (x (n + 1)))
    (n : ℕ) (i : Fin r) (c : ℝ) (hc : |c| ≤ 1) :
    Integrable (fun ω => c * g.toFun n (hist x n ω) i) ν := by
  have hm : MeasurableSpace.comap (hist x n) inferInstance ≤ ‹MeasurableSpace Ω› :=
    (aux_Tat_hist_meas x hx n).comap_le
  have hmeas : Measurable (fun ω => g.toFun n (hist x n ω) i) :=
    (aux_Tat_p_meas g x n i).mono hm le_rfl
  refine (integrable_const (1 : ℝ)).mono' (hmeas.const_mul c).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have h0 := (g.mem n (hist x n ω)).1 i
  have h1 := aux_Tat_simplex_le_one (g.mem n (hist x n ω)) i
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
  nlinarith [abs_nonneg c]

lemma aux_Tat_meas_eq {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ)
    (hq₀ : q₀ ∈ stdSimplex ℝ (Fin s)) (g : Strategy N r) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (x : ℕ → Ω → E N)
    (hx : G.transpose.IsPlay (Strategy.const q₀ hq₀) g μ x) (n : ℕ) (A : Set Ω)
    (hA : MeasurableSet[MeasurableSpace.comap (hist x n) inferInstance] A) :
    (μ.restrict A).map (x (n + 1)) =
      ∑ j, ∑ i, ENNReal.ofReal (∫ ω in A, q₀ j * g.toFun n (hist x n ω) i ∂μ) • G.m i j := by
  have hm : MeasurableSpace.comap (hist x n) inferInstance ≤ ‹MeasurableSpace Ω› :=
    (aux_Tat_hist_meas x hx.1 n).comap_le
  have hA' : MeasurableSet A := hm A hA
  have hint : ∀ j i, Integrable (fun ω => q₀ j * g.toFun n (hist x n ω) i) (μ.restrict A) :=
    fun j i => aux_Tat_p_int g (μ.restrict A) x hx.1 n i (q₀ j)
      (by rw [abs_of_nonneg (hq₀.1 j)]; exact aux_Tat_simplex_le_one hq₀ j)
  have hnn : ∀ j i, 0 ≤ ∫ ω in A, q₀ j * g.toFun n (hist x n ω) i ∂μ := fun j i =>
    setIntegral_nonneg hA' (fun ω _ => mul_nonneg (hq₀.1 j) ((g.mem n _).1 i))
  ext B hB
  have hxB : MeasurableSet (x (n + 1) ⁻¹' B) := hx.1 n hB
  have key : μ[(x (n + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap (hist x n) inferInstance]
      =ᵐ[μ] fun ω => ∑ j, ∑ i, q₀ j * g.toFun n (hist x n ω) i * (G.m i j B).toReal :=
    hx.2 n B hB
  have h1 : ∫ ω in A, (x (n + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω ∂μ
      = (μ (x (n + 1) ⁻¹' B ∩ A)).toReal := by
    rw [integral_indicator_const _ hxB, smul_eq_mul, mul_one, measureReal_restrict_apply hxB,
      measureReal_def]
  have h2 := setIntegral_condExp (μ := μ) hm
    ((integrable_const (μ := μ) (1 : ℝ)).indicator hxB) hA
  have h3 : ∫ ω in A, (μ[(x (n + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap (hist x n) inferInstance]) ω ∂μ
      = ∫ ω in A, ∑ j, ∑ i, q₀ j * g.toFun n (hist x n ω) i * (G.m i j B).toReal ∂μ :=
    setIntegral_congr_ae hA' (key.mono fun ω h _ => h)
  have h4 : ∫ ω in A, ∑ j, ∑ i, q₀ j * g.toFun n (hist x n ω) i * (G.m i j B).toReal ∂μ
      = ∑ j, ∑ i, (∫ ω in A, q₀ j * g.toFun n (hist x n ω) i ∂μ) * (G.m i j B).toReal := by
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _
      (fun i _ => (hint j i).mul_const _))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_finsetSum _ (fun i _ => (hint j i).mul_const _)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_mul_const]
  rw [Measure.map_apply (hx.1 n) hB, Measure.restrict_apply hxB]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  have hfin : ∀ j i, ENNReal.ofReal (∫ ω in A, q₀ j * g.toFun n (hist x n ω) i ∂μ) *
      G.m i j B ≠ ⊤ := fun j i => by
    have := G.isProb i j
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.sum_ne_top.2 fun j _ => ENNReal.sum_ne_top.2 fun i _ => hfin j i)]
  rw [← h1, ← h2, h3, h4, ENNReal.toReal_sum (fun j _ => ENNReal.sum_ne_top.2 fun i _ => hfin j i)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ENNReal.toReal_sum (fun i _ => hfin j i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hnn j i)]

lemma aux_Tat_bound {N r s : ℕ} (G : Game N r s) : ∃ C, 0 ≤ C ∧ ∀ z ∈ G.X, ‖z‖ ≤ C := by
  obtain ⟨C, hC⟩ := G.isBounded_X.exists_norm_le
  exact ⟨max C 0, le_max_right _ _, fun z hz => (hC z hz).trans (le_max_left _ _)⟩

lemma aux_Tat_id_int {N r s : ℕ} (G : Game N r s) (i : Fin r) (j : Fin s) :
    Integrable (fun z : E N => z) (G.m i j) := by
  have := G.isProb i j
  obtain ⟨C, _, hC⟩ := aux_Tat_bound G
  have hae : ∀ᵐ z ∂(G.m i j), z ∈ G.X := ae_iff.2 (G.m_compl_X i j)
  exact (integrable_const C).mono' aestronglyMeasurable_id (hae.mono fun z hz => hC z hz)

lemma aux_Tat_setIntegral_eq {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ)
    (hq₀ : q₀ ∈ stdSimplex ℝ (Fin s)) (g : Strategy N r) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (x : ℕ → Ω → E N)
    (hx : G.transpose.IsPlay (Strategy.const q₀ hq₀) g μ x) (n : ℕ) (A : Set Ω)
    (hA : MeasurableSet[MeasurableSpace.comap (hist x n) inferInstance] A) :
    ∫ ω in A, x (n + 1) ω ∂μ = ∫ ω in A, aux_Tat_y G q₀ g x n ω ∂μ := by
  have hm : MeasurableSpace.comap (hist x n) inferInstance ≤ ‹MeasurableSpace Ω› :=
    (aux_Tat_hist_meas x hx.1 n).comap_le
  have hA' : MeasurableSet A := hm A hA
  have hint : ∀ j i, Integrable (fun ω => q₀ j * g.toFun n (hist x n ω) i) (μ.restrict A) :=
    fun j i => aux_Tat_p_int g (μ.restrict A) x hx.1 n i (q₀ j)
      (by rw [abs_of_nonneg (hq₀.1 j)]; exact aux_Tat_simplex_le_one hq₀ j)
  have hnn : ∀ j i, 0 ≤ ∫ ω in A, q₀ j * g.toFun n (hist x n ω) i ∂μ := fun j i =>
    setIntegral_nonneg hA' (fun ω _ => mul_nonneg (hq₀.1 j) ((g.mem n _).1 i))
  have h1 : ∫ z, z ∂((μ.restrict A).map (x (n + 1))) = ∫ ω in A, x (n + 1) ω ∂μ :=
    integral_map (hx.1 n).aemeasurable aestronglyMeasurable_id
  rw [← h1, aux_Tat_meas_eq G q₀ hq₀ g μ x hx n A hA]
  rw [integral_finsetSum_measure (fun j _ => integrable_finsetSum_measure.2
    (fun i _ => (aux_Tat_id_int G i j).smul_measure ENNReal.ofReal_ne_top))]
  unfold aux_Tat_y
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun i _ => (hint j i).smul_const _))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_finsetSum_measure (fun i _ =>
    (aux_Tat_id_int G i j).smul_measure ENNReal.ofReal_ne_top)]
  rw [integral_finsetSum _ (fun i _ => (hint j i).smul_const _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_smul_measure, integral_smul_const, ENNReal.toReal_ofReal (hnn j i)]
  rfl

lemma aux_Tat_ae_mem {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ)
    (hq₀ : q₀ ∈ stdSimplex ℝ (Fin s)) (g : Strategy N r) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (x : ℕ → Ω → E N)
    (hx : G.transpose.IsPlay (Strategy.const q₀ hq₀) g μ x) (n : ℕ) :
    ∀ᵐ ω ∂μ, x (n + 1) ω ∈ G.X := by
  have h := aux_Tat_meas_eq G q₀ hq₀ g μ x hx n Set.univ MeasurableSet.univ
  have h2 := congrArg (fun ν : Measure (E N) => ν G.Xᶜ) h
  simp only [Measure.restrict_univ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    G.m_compl_X, smul_zero, Finset.sum_const_zero] at h2
  rw [Measure.map_apply (hx.1 n) G.isClosed_X.isOpen_compl.measurableSet] at h2
  exact ae_iff.2 h2

lemma aux_Tat_orth {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ)
    (hq₀ : q₀ ∈ stdSimplex ℝ (Fin s)) (g : Strategy N r) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (x : ℕ → Ω → E N)
    (hx : G.transpose.IsPlay (Strategy.const q₀ hq₀) g μ x) (n : ℕ) (Z : Ω → E N)
    (hZ : Measurable[MeasurableSpace.comap (hist x n) inferInstance] Z) (c : ℝ)
    (hZc : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ c) :
    ∫ ω, inner ℝ (Z ω) (x (n + 1) ω - aux_Tat_y G q₀ g x n ω) ∂μ = 0 := by
  obtain ⟨C, hC0, hC⟩ := aux_Tat_bound G
  have hm : MeasurableSpace.comap (hist x n) inferInstance ≤ ‹MeasurableSpace Ω› :=
    (aux_Tat_hist_meas x hx.1 n).comap_le
  have hxmem := aux_Tat_ae_mem G q₀ hq₀ g μ x hx n
  have hxint : Integrable (x (n + 1)) μ :=
    (integrable_const C).mono' (hx.1 n).aestronglyMeasurable (hxmem.mono fun ω h => hC _ h)
  have hymeas : Measurable (aux_Tat_y G q₀ g x n) := (aux_Tat_y_meas G q₀ g x n).mono hm le_rfl
  have hybd : ∀ ω, ‖aux_Tat_y G q₀ g x n ω‖ ≤ C := fun ω =>
    hC _ (aux_Tat_T_sub G q₀ hq₀ (aux_Tat_y_mem G q₀ g x n ω))
  have hyint : Integrable (aux_Tat_y G q₀ g x n) μ :=
    (integrable_const C).mono' hymeas.aestronglyMeasurable (Filter.Eventually.of_forall hybd)
  have hZm : Measurable Z := hZ.mono hm le_rfl
  have hce : aux_Tat_y G q₀ g x n =ᵐ[μ] μ[x (n + 1) | MeasurableSpace.comap (hist x n) inferInstance] :=
    ae_eq_condExp_of_forall_setIntegral_eq hm hxint (fun s _ _ => hyint.integrableOn)
      (fun s hs _ => (aux_Tat_setIntegral_eq G q₀ hq₀ g μ x hx n s hs).symm)
      (aux_Tat_y_meas G q₀ g x n).stronglyMeasurable.aestronglyMeasurable
  have hZx : Integrable (fun ω => inner ℝ (Z ω) (x (n + 1) ω)) μ := by
    refine (integrable_const (c * C)).mono'
      (hZm.aestronglyMeasurable.inner (hx.1 n).aestronglyMeasurable) ?_
    filter_upwards [hZc, hxmem] with ω h1 h2
    calc ‖inner ℝ (Z ω) (x (n + 1) ω)‖ ≤ ‖Z ω‖ * ‖x (n + 1) ω‖ := norm_inner_le_norm _ _
      _ ≤ c * C := mul_le_mul h1 (hC _ h2) (norm_nonneg _) ((norm_nonneg _).trans h1)
  have hZy : Integrable (fun ω => inner ℝ (Z ω) (aux_Tat_y G q₀ g x n ω)) μ := by
    refine (integrable_const (c * C)).mono'
      (hZm.aestronglyMeasurable.inner hymeas.aestronglyMeasurable) ?_
    filter_upwards [hZc] with ω h1
    calc ‖inner ℝ (Z ω) (aux_Tat_y G q₀ g x n ω)‖
        ≤ ‖Z ω‖ * ‖aux_Tat_y G q₀ g x n ω‖ := norm_inner_le_norm _ _
      _ ≤ c * C := mul_le_mul h1 (hybd ω) (norm_nonneg _) ((norm_nonneg _).trans h1)
  have hpull := condExp_bilin_of_stronglyMeasurable_left
    (innerSL ℝ : E N →L[ℝ] E N →L[ℝ] ℝ) hZ.stronglyMeasurable (g := x (n + 1)) hZx hxint
  have e1 : ∫ ω, inner ℝ (Z ω) (x (n + 1) ω) ∂μ =
      ∫ ω, inner ℝ (Z ω) (aux_Tat_y G q₀ g x n ω) ∂μ := by
    calc ∫ ω, inner ℝ (Z ω) (x (n + 1) ω) ∂μ
        = ∫ ω, (μ[fun ω => (innerSL ℝ : E N →L[ℝ] E N →L[ℝ] ℝ) (Z ω) (x (n + 1) ω) |
            MeasurableSpace.comap (hist x n) inferInstance]) ω ∂μ :=
          (integral_condExp hm).symm
      _ = ∫ ω, (innerSL ℝ : E N →L[ℝ] E N →L[ℝ] ℝ) (Z ω)
            ((μ[x (n + 1) | MeasurableSpace.comap (hist x n) inferInstance]) ω) ∂μ :=
          integral_congr_ae hpull
      _ = ∫ ω, inner ℝ (Z ω) (aux_Tat_y G q₀ g x n ω) ∂μ :=
          integral_congr_ae (hce.mono fun ω h => by dsimp only; rw [← h]; rfl)
  simp_rw [inner_sub_right]
  rw [integral_sub hZx hZy, e1, sub_self]

/-- The martingale `S n = ∑_{k<n} (x_{k+1} - y_k)`. -/
noncomputable def aux_Tat_S {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ) (g : Strategy N r)
    {Ω : Type} (x : ℕ → Ω → E N) (n : ℕ) (ω : Ω) : E N :=
  ∑ k ∈ Finset.range n, (x (k + 1) ω - aux_Tat_y G q₀ g x k ω)

lemma aux_Tat_S_meas {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ) (g : Strategy N r)
    {Ω : Type} (x : ℕ → Ω → E N) (n : ℕ) :
    Measurable[MeasurableSpace.comap (hist x n) inferInstance] (aux_Tat_S G q₀ g x n) := by
  unfold aux_Tat_S
  refine Finset.measurable_sum _ (fun k hk => ?_)
  have hk' : k < n := Finset.mem_range.1 hk
  refine Measurable.sub ?_ ?_
  · have : x (k + 1) = (fun v : Fin n → E N => v ⟨k, hk'⟩) ∘ hist x n := rfl
    rw [this]
    exact (measurable_pi_apply _).comp (comap_measurable _)
  · exact (aux_Tat_y_meas G q₀ g x k).mono (aux_Tat_F_mono x hk'.le) le_rfl

lemma aux_Tat_S_succ {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ) (g : Strategy N r)
    {Ω : Type} (x : ℕ → Ω → E N) (n : ℕ) (ω : Ω) :
    aux_Tat_S G q₀ g x (n + 1) ω =
      aux_Tat_S G q₀ g x n ω + (x (n + 1) ω - aux_Tat_y G q₀ g x n ω) := by
  unfold aux_Tat_S
  rw [Finset.sum_range_succ]

lemma aux_Tat_S_incr {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ) (g : Strategy N r)
    {Ω : Type} (x : ℕ → Ω → E N) (ω : Ω) (K : ℝ)
    (hK : ∀ k, ‖x (k + 1) ω - aux_Tat_y G q₀ g x k ω‖ ≤ K) (a j : ℕ) :
    ‖aux_Tat_S G q₀ g x (a + j) ω - aux_Tat_S G q₀ g x a ω‖ ≤ j * K := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← add_assoc, aux_Tat_S_succ, add_sub_right_comm]
    calc _ ≤ ‖aux_Tat_S G q₀ g x (a + j) ω - aux_Tat_S G q₀ g x a ω‖ +
          ‖x (a + j + 1) ω - aux_Tat_y G q₀ g x (a + j) ω‖ := norm_add_le _ _
      _ ≤ j * K + K := add_le_add ih (hK _)
      _ = ((j + 1 : ℕ) : ℝ) * K := by push_cast; ring

lemma aux_Tat_d_bd {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ)
    (hq₀ : q₀ ∈ stdSimplex ℝ (Fin s)) (g : Strategy N r) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (x : ℕ → Ω → E N)
    (hx : G.transpose.IsPlay (Strategy.const q₀ hq₀) g μ x) (C : ℝ)
    (hC : ∀ z ∈ G.X, ‖z‖ ≤ C) :
    ∀ᵐ ω ∂μ, ∀ k, ‖x (k + 1) ω - aux_Tat_y G q₀ g x k ω‖ ≤ 2 * C := by
  rw [ae_all_iff]
  intro k
  filter_upwards [aux_Tat_ae_mem G q₀ hq₀ g μ x hx k] with ω hω
  calc _ ≤ ‖x (k + 1) ω‖ + ‖aux_Tat_y G q₀ g x k ω‖ := norm_sub_le _ _
    _ ≤ C + C := add_le_add (hC _ hω)
        (hC _ (aux_Tat_T_sub G q₀ hq₀ (aux_Tat_y_mem G q₀ g x k ω)))
    _ = 2 * C := by ring

lemma aux_Tat_var {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ)
    (hq₀ : q₀ ∈ stdSimplex ℝ (Fin s)) (g : Strategy N r) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (x : ℕ → Ω → E N)
    (hx : G.transpose.IsPlay (Strategy.const q₀ hq₀) g μ x) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ z ∈ G.X, ‖z‖ ≤ C) (n : ℕ) :
    Integrable (fun ω => ‖aux_Tat_S G q₀ g x n ω‖ ^ 2) μ ∧
      ∫ ω, ‖aux_Tat_S G q₀ g x n ω‖ ^ 2 ∂μ ≤ n * (2 * C) ^ 2 := by
  have hd := aux_Tat_d_bd G q₀ hq₀ g μ x hx C hC
  have hSbd : ∀ n, ∀ᵐ ω ∂μ, ‖aux_Tat_S G q₀ g x n ω‖ ≤ n * (2 * C) := fun n => by
    filter_upwards [hd] with ω hω
    have := aux_Tat_S_incr G q₀ g x ω (2 * C) hω 0 n
    simpa [aux_Tat_S] using this
  have hSm : ∀ n, Measurable (aux_Tat_S G q₀ g x n) := fun n =>
    (aux_Tat_S_meas G q₀ g x n).mono (aux_Tat_hist_meas x hx.1 n).comap_le le_rfl
  have hym : ∀ n, Measurable (aux_Tat_y G q₀ g x n) := fun n =>
    (aux_Tat_y_meas G q₀ g x n).mono (aux_Tat_hist_meas x hx.1 n).comap_le le_rfl
  have hSint : ∀ n, Integrable (fun ω => ‖aux_Tat_S G q₀ g x n ω‖ ^ 2) μ := fun n => by
    refine (integrable_const ((n * (2 * C)) ^ 2)).mono'
      ((hSm n).norm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hSbd n] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hω 2
  refine ⟨hSint n, ?_⟩
  induction n with
  | zero => simp [aux_Tat_S]
  | succ n ih =>
    have hdm : Measurable (fun ω => x (n + 1) ω - aux_Tat_y G q₀ g x n ω) :=
      (hx.1 n).sub (hym n)
    have hdint : Integrable (fun ω => ‖x (n + 1) ω - aux_Tat_y G q₀ g x n ω‖ ^ 2) μ := by
      refine (integrable_const ((2 * C) ^ 2)).mono' (hdm.norm.pow_const 2).aestronglyMeasurable ?_
      filter_upwards [hd] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hω n) 2
    have hiint : Integrable (fun ω => 2 * inner ℝ (aux_Tat_S G q₀ g x n ω)
        (x (n + 1) ω - aux_Tat_y G q₀ g x n ω)) μ := by
      refine Integrable.const_mul ?_ _
      refine (integrable_const (n * (2 * C) * (2 * C))).mono'
        ((hSm n).aestronglyMeasurable.inner hdm.aestronglyMeasurable) ?_
      filter_upwards [hd, hSbd n] with ω h1 h2
      calc _ ≤ ‖aux_Tat_S G q₀ g x n ω‖ * ‖x (n + 1) ω - aux_Tat_y G q₀ g x n ω‖ :=
            norm_inner_le_norm _ _
        _ ≤ n * (2 * C) * (2 * C) := mul_le_mul h2 (h1 n) (norm_nonneg _)
            (by positivity)
    have horth := aux_Tat_orth G q₀ hq₀ g μ x hx n (aux_Tat_S G q₀ g x n)
      (aux_Tat_S_meas G q₀ g x n) _ (hSbd n)
    have heq : (fun ω => ‖aux_Tat_S G q₀ g x (n + 1) ω‖ ^ 2) = fun ω =>
        ‖aux_Tat_S G q₀ g x n ω‖ ^ 2 + 2 * inner ℝ (aux_Tat_S G q₀ g x n ω)
          (x (n + 1) ω - aux_Tat_y G q₀ g x n ω) +
          ‖x (n + 1) ω - aux_Tat_y G q₀ g x n ω‖ ^ 2 := by
      funext ω
      rw [aux_Tat_S_succ, norm_add_sq_real]
    have h12 : Integrable (fun ω => ‖aux_Tat_S G q₀ g x n ω‖ ^ 2 + 2 * inner ℝ
        (aux_Tat_S G q₀ g x n ω) (x (n + 1) ω - aux_Tat_y G q₀ g x n ω)) μ :=
      (hSint n).add hiint
    rw [heq, integral_add h12 hdint, integral_add (hSint n) hiint,
      integral_const_mul, horth, mul_zero, add_zero]
    have hle : ∫ ω, ‖x (n + 1) ω - aux_Tat_y G q₀ g x n ω‖ ^ 2 ∂μ ≤ (2 * C) ^ 2 := by
      have := integral_mono_ae hdint (integrable_const ((2 * C) ^ 2))
        (by filter_upwards [hd] with ω hω
            exact pow_le_pow_left₀ (norm_nonneg _) (hω n) 2)
      simpa using this
    have ih' := ih
    push_cast
    linarith

lemma aux_Tat_tail (M n : ℕ) :
    ∑ m ∈ Finset.range n, ((((m + (M + 1) : ℕ) : ℝ)) ^ 2)⁻¹ ≤ 2 / ((M : ℝ) + 1) := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) M (n + (M + 1))
  rw [← Finset.Ico_add_one_left_eq_Ioo] at h
  have h2 := Finset.sum_Ico_add' (fun i : ℕ => (((i : ℕ) : ℝ) ^ 2)⁻¹) 0 n (M + 1)
  rw [zero_add] at h2
  rw [Finset.range_eq_Ico, h2]
  exact h

lemma aux_Tat_cheb {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ)
    (hq₀ : q₀ ∈ stdSimplex ℝ (Fin s)) (g : Strategy N r) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (x : ℕ → Ω → E N)
    (hx : G.transpose.IsPlay (Strategy.const q₀ hq₀) g μ x) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ z ∈ G.X, ‖z‖ ≤ C) (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 1 ≤ m) :
    μ {ω | δ * (m : ℝ) ^ 2 ≤ ‖aux_Tat_S G q₀ g x (m ^ 2) ω‖} ≤
      ENNReal.ofReal ((2 * C) ^ 2 / δ ^ 2 * ((m : ℝ) ^ 2)⁻¹) := by
  obtain ⟨hint, hvar⟩ := aux_Tat_var G q₀ hq₀ g μ x hx C hC0 hC (m ^ 2)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hcheb := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => sq_nonneg ‖aux_Tat_S G q₀ g x (m ^ 2) ω‖) hint
    ((δ * (m : ℝ) ^ 2) ^ 2)
  have hsub : {ω | δ * (m : ℝ) ^ 2 ≤ ‖aux_Tat_S G q₀ g x (m ^ 2) ω‖} ⊆
      {ω | (δ * (m : ℝ) ^ 2) ^ 2 ≤ ‖aux_Tat_S G q₀ g x (m ^ 2) ω‖ ^ 2} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact pow_le_pow_left₀ (by positivity) hω 2
  set P := μ.real {ω | (δ * (m : ℝ) ^ 2) ^ 2 ≤ ‖aux_Tat_S G q₀ g x (m ^ 2) ω‖ ^ 2} with hP
  have hP0 : 0 ≤ P := measureReal_nonneg
  have h1 : P ≤ (2 * C) ^ 2 / δ ^ 2 * ((m : ℝ) ^ 2)⁻¹ := by
    have h3 : (δ * (m : ℝ) ^ 2) ^ 2 * P ≤ (m : ℝ) ^ 2 * (2 * C) ^ 2 := by
      have := hcheb.trans hvar
      push_cast at this
      exact this
    rw [← div_eq_mul_inv, div_div, le_div_iff₀ (by positivity)]
    have h4 : (m : ℝ) ^ 2 * (P * (δ ^ 2 * (m : ℝ) ^ 2)) ≤ (m : ℝ) ^ 2 * (2 * C) ^ 2 := by
      calc (m : ℝ) ^ 2 * (P * (δ ^ 2 * (m : ℝ) ^ 2)) = (δ * (m : ℝ) ^ 2) ^ 2 * P := by ring
        _ ≤ _ := h3
    exact le_of_mul_le_mul_left h4 (by positivity)
  calc μ {ω | δ * (m : ℝ) ^ 2 ≤ ‖aux_Tat_S G q₀ g x (m ^ 2) ω‖}
      ≤ μ {ω | (δ * (m : ℝ) ^ 2) ^ 2 ≤ ‖aux_Tat_S G q₀ g x (m ^ 2) ω‖ ^ 2} := measure_mono hsub
    _ = ENNReal.ofReal P := (ofReal_measureReal).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal h1

lemma aux_Tat_main {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ)
    (hq₀ : q₀ ∈ stdSimplex ℝ (Fin s)) :
    G.transpose.ApproachableWith (G.T q₀) (Strategy.const q₀ hq₀) := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := aux_Tat_bound G
  have hK0 : 0 ≤ 2 * C := by positivity
  have hδ : 0 < ε / 2 := by positivity
  obtain ⟨M, hM⟩ := exists_nat_gt (4 * (2 * C) / ε + 8 * (2 * C) ^ 2 / ε ^ 3)
  have hA0 : 0 ≤ 4 * (2 * C) / ε := by positivity
  have hB0 : 0 ≤ 8 * (2 * C) ^ 2 / ε ^ 3 := by positivity
  have hM1 : 4 * (2 * C) / ε < (M : ℝ) + 1 := by linarith
  have hM2 : 8 * (2 * C) ^ 2 / ε ^ 3 < (M : ℝ) + 1 := by linarith
  have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  -- 2K ≤ δ (M+1)
  have hKδ : 2 * (2 * C) ≤ ε / 2 * ((M : ℝ) + 1) := by
    rw [div_lt_iff₀ hε] at hM1
    linarith
  have hfinal : (2 * C) ^ 2 / (ε / 2) ^ 2 * (2 / ((M : ℝ) + 1)) < ε := by
    rw [div_lt_iff₀ (by positivity)] at hM2
    have e : (2 * C) ^ 2 / (ε / 2) ^ 2 * (2 / ((M : ℝ) + 1)) =
        8 * (2 * C) ^ 2 / (ε ^ 2 * ((M : ℝ) + 1)) := by
      field_simp
      ring
    rw [e, div_lt_iff₀ (by positivity)]
    nlinarith
  refine ⟨(M + 1) ^ 2, ?_⟩
  intro g Ω _ μ _ x hx
  set c : ℝ := (2 * C) ^ 2 / (ε / 2) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hNull : μ {ω | ¬ ∀ k, ‖x (k + 1) ω - aux_Tat_y G q₀ g x k ω‖ ≤ 2 * C} = 0 :=
    ae_iff.1 (aux_Tat_d_bd G q₀ hq₀ g μ x hx C hC)
  have hsub : {ω | ∃ n, (M + 1) ^ 2 ≤ n ∧ 1 ≤ n ∧
      ENNReal.ofReal ε ≤ Metric.infEDist (avg x n ω) (G.T q₀)} ⊆
      {ω | ¬ ∀ k, ‖x (k + 1) ω - aux_Tat_y G q₀ g x k ω‖ ≤ 2 * C} ∪
        ⋃ m : ℕ, {ω | ε / 2 * (((m + (M + 1) : ℕ) : ℝ)) ^ 2 ≤
          ‖aux_Tat_S G q₀ g x ((m + (M + 1)) ^ 2) ω‖} := by
    rintro ω ⟨n, hn, hn1, hdist⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, Set.mem_ofPred_eq,
      not_not, not_le] at hcon
    obtain ⟨hK, hev⟩ := hcon
    have hm'1 : Nat.sqrt n ^ 2 ≤ n := Nat.sqrt_le' n
    have hm'2 : n < (Nat.sqrt n + 1) ^ 2 := Nat.lt_succ_sqrt' n
    have hm'3 : M + 1 ≤ Nat.sqrt n := Nat.le_sqrt'.2 hn
    have hev' := hev (Nat.sqrt n - (M + 1))
    rw [Nat.sub_add_cancel hm'3] at hev'
    have hinc := aux_Tat_S_incr G q₀ g x ω (2 * C) hK (Nat.sqrt n ^ 2) (n - Nat.sqrt n ^ 2)
    rw [Nat.add_sub_cancel' hm'1] at hinc
    have hj : ((n - Nat.sqrt n ^ 2 : ℕ) : ℝ) ≤ 2 * (Nat.sqrt n : ℝ) := by
      have : n - Nat.sqrt n ^ 2 ≤ 2 * Nat.sqrt n := by
        have e : (Nat.sqrt n + 1) ^ 2 = Nat.sqrt n ^ 2 + 2 * Nat.sqrt n + 1 := by ring
        rw [e] at hm'2
        generalize Nat.sqrt n ^ 2 = t at *
        omega
      exact_mod_cast this
    set mr : ℝ := (Nat.sqrt n : ℝ) with hmr
    have hmr1 : (M : ℝ) + 1 ≤ mr := by
      rw [hmr]; exact_mod_cast hm'3
    have hmrn : mr ^ 2 ≤ (n : ℝ) := by rw [hmr]; exact_mod_cast hm'1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hSn : ‖aux_Tat_S G q₀ g x n ω‖ < ε * n := by
      have t1 : ‖aux_Tat_S G q₀ g x n ω‖ ≤ ‖aux_Tat_S G q₀ g x (Nat.sqrt n ^ 2) ω‖ +
          ‖aux_Tat_S G q₀ g x n ω - aux_Tat_S G q₀ g x (Nat.sqrt n ^ 2) ω‖ := by
        have := norm_add_le (aux_Tat_S G q₀ g x (Nat.sqrt n ^ 2) ω)
          (aux_Tat_S G q₀ g x n ω - aux_Tat_S G q₀ g x (Nat.sqrt n ^ 2) ω)
        rwa [add_sub_cancel] at this
      have t2 : ((n - Nat.sqrt n ^ 2 : ℕ) : ℝ) * (2 * C) ≤ 2 * mr * (2 * C) :=
        mul_le_mul_of_nonneg_right hj hK0
      have t3 : 2 * mr * (2 * C) ≤ ε / 2 * mr ^ 2 := by
        have : 2 * (2 * C) ≤ ε / 2 * mr := le_trans hKδ
          (mul_le_mul_of_nonneg_left hmr1 hδ.le)
        nlinarith
      have t4 : ε / 2 * mr ^ 2 ≤ ε / 2 * n := mul_le_mul_of_nonneg_left hmrn hδ.le
      linarith
    have havg : avg x n ω = (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, x (k + 1) ω := by
      unfold avg avgHist hist
      rw [Fin.sum_univ_eq_sum_range (fun k => x (k + 1) ω) n]
    have hybar : (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, aux_Tat_y G q₀ g x k ω ∈ G.T q₀ := by
      rw [Finset.smul_sum]
      refine (convex_convexHull ℝ _).sum_mem (fun k _ => by positivity) ?_
        (fun k _ => aux_Tat_y_mem G q₀ g x k ω)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    have hdiff : avg x n ω - (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, aux_Tat_y G q₀ g x k ω =
        (n : ℝ)⁻¹ • aux_Tat_S G q₀ g x n ω := by
      rw [havg, ← smul_sub, ← Finset.sum_sub_distrib]
      rfl
    have hnorm : ‖avg x n ω - (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, aux_Tat_y G q₀ g x k ω‖ < ε := by
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast, inv_mul_lt_iff₀ hnpos]
      linarith
    have hlt : Metric.infEDist (avg x n ω) (G.T q₀) < ENNReal.ofReal ε := by
      calc Metric.infEDist (avg x n ω) (G.T q₀)
          ≤ edist (avg x n ω) ((n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, aux_Tat_y G q₀ g x k ω) :=
            Metric.infEDist_le_edist_of_mem hybar
        _ = ENNReal.ofReal (dist (avg x n ω)
              ((n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, aux_Tat_y G q₀ g x k ω)) := edist_dist _ _
        _ < ENNReal.ofReal ε := by
            rw [dist_eq_norm]
            exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hnorm
    exact absurd hdist (not_le.2 hlt)
  have hEv : ∀ m : ℕ, μ {ω | ε / 2 * (((m + (M + 1) : ℕ) : ℝ)) ^ 2 ≤
      ‖aux_Tat_S G q₀ g x ((m + (M + 1)) ^ 2) ω‖} ≤
      ENNReal.ofReal (c * ((((m + (M + 1) : ℕ) : ℝ)) ^ 2)⁻¹) := fun m =>
    aux_Tat_cheb G q₀ hq₀ g μ x hx C hC0 hC (ε / 2) hδ (m + (M + 1)) (by omega)
  have htsum : ∑' m : ℕ, μ {ω | ε / 2 * (((m + (M + 1) : ℕ) : ℝ)) ^ 2 ≤
      ‖aux_Tat_S G q₀ g x ((m + (M + 1)) ^ 2) ω‖} ≤
      ENNReal.ofReal (c * (2 / ((M : ℝ) + 1))) := by
    refine ENNReal.tsum_le_of_sum_range_le (fun n => ?_)
    calc _ ≤ ∑ m ∈ Finset.range n, ENNReal.ofReal (c * ((((m + (M + 1) : ℕ) : ℝ)) ^ 2)⁻¹) :=
          Finset.sum_le_sum (fun m _ => hEv m)
      _ = ENNReal.ofReal (∑ m ∈ Finset.range n, c * ((((m + (M + 1) : ℕ) : ℝ)) ^ 2)⁻¹) :=
          (ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)).symm
      _ ≤ ENNReal.ofReal (c * (2 / ((M : ℝ) + 1))) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (aux_Tat_tail M n) hc0
  have hmeas_le : μ {ω | ∃ n, (M + 1) ^ 2 ≤ n ∧ 1 ≤ n ∧
      ENNReal.ofReal ε ≤ Metric.infEDist (avg x n ω) (G.T q₀)} ≤
      ENNReal.ofReal (c * (2 / ((M : ℝ) + 1))) := by
    calc _ ≤ _ := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ 0 + ∑' m : ℕ, μ {ω | ε / 2 * (((m + (M + 1) : ℕ) : ℝ)) ^ 2 ≤
            ‖aux_Tat_S G q₀ g x ((m + (M + 1)) ^ 2) ω‖} :=
          add_le_add (le_of_eq hNull) (measure_iUnion_le _)
      _ ≤ _ := by rw [zero_add]; exact htsum
  calc _ ≤ c * (2 / ((M : ℝ) + 1)) := ENNReal.toReal_le_of_le_ofReal (by positivity) hmeas_le
    _ < ε := hfinal

end VectorPayoffs.Convex

open VectorPayoffs.Convex

theorem solution {N r s : ℕ} (G : Game N r s) (q₀ : Fin s → ℝ)
    (hq₀ : q₀ ∈ stdSimplex ℝ (Fin s)) :
    G.transpose.ApproachableWith (G.T q₀) (Strategy.const q₀ hq₀) :=
  aux_Tat_main G q₀ hq₀
