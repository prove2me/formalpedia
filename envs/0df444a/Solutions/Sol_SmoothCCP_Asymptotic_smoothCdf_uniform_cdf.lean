-- Prove2me | solution 1 for SmoothCCP.Asymptotic.smoothCdf_uniform_cdf
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T07:30:13.954791+00:00
-- url     : https://prove2.me/submissions/6b498584-dc7e-4502-bc80-413e7d5f1293

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting

open MeasureTheory Filter Topology
open SmoothCCP.Feasibility

namespace SolSmoothCdfAux

/-- Continuous majorant of `1{|y| < ε}`: equal to `1` on `[-ε, ε]`, `0` outside `[-2ε, 2ε]`. -/
noncomputable def psi (ε y : ℝ) : ℝ := min 1 (max 0 (2 - |y| / ε))

theorem psi_nonneg (ε y : ℝ) : 0 ≤ psi ε y :=
  le_min zero_le_one (le_max_left _ _)

theorem psi_le_one (ε y : ℝ) : psi ε y ≤ 1 := min_le_left _ _

theorem psi_continuous (ε : ℝ) : Continuous (psi ε) := by
  unfold psi
  fun_prop

theorem psi_mono {ε ε' : ℝ} (hε : 0 < ε) (h : ε ≤ ε') (y : ℝ) : psi ε y ≤ psi ε' y := by
  unfold psi
  have : |y| / ε' ≤ |y| / ε := div_le_div_of_nonneg_left (abs_nonneg y) hε h
  exact min_le_min le_rfl (max_le_max le_rfl (by linarith))

theorem psi_eq_zero {ε y : ℝ} (hε : 0 < ε) (hy : 2 * ε < |y|) : psi ε y = 0 := by
  unfold psi
  have : 2 < |y| / ε := by rw [lt_div_iff₀ hε]; linarith
  have h2 : max 0 (2 - |y| / ε) = 0 := max_eq_left (by linarith)
  rw [h2]; simp

theorem gam_sub_ind_le {ε : ℝ} {g : ℝ → ℝ} (hg : AdmissibleGamma ε g) (y : ℝ) :
    |Gam ε g y - (if y ≤ 0 then 1 else 0)| ≤ psi ε y := by
  have hε := hg.pos
  unfold Gam
  by_cases h1 : y ≤ -ε
  · have : y ≤ 0 := by linarith
    simp only [h1, this, if_true, sub_self, abs_zero]
    exact psi_nonneg ε y
  · by_cases h2 : y < ε
    · have hmem : y ∈ Set.Icc (-ε) ε := ⟨by linarith, h2.le⟩
      have hgy := hg.mapsTo y hmem
      have hpsi : psi ε y = 1 := by
        unfold psi
        have hy : |y| < ε := abs_lt.mpr ⟨by linarith, h2⟩
        have : |y| / ε < 1 := by rw [div_lt_one hε]; exact hy
        have h3 : max 0 (2 - |y| / ε) = 2 - |y| / ε := max_eq_right (by linarith)
        rw [h3]; exact min_eq_left (by linarith)
      rw [hpsi]
      simp only [h1, if_false, h2, if_true]
      split_ifs
      · rw [abs_le]; constructor <;> linarith [hgy.1, hgy.2]
      · rw [abs_le]; constructor <;> linarith [hgy.1, hgy.2]
    · have : ¬ y ≤ 0 := by intro h; apply h2; linarith
      simp only [h1, h2, this, if_false, sub_self, abs_zero]
      exact psi_nonneg ε y

end SolSmoothCdfAux

open SolSmoothCdfAux

theorem solution
    {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    (X : Set (Fin n → ℝ)) (hX : IsClosed X) (C : (Fin n → ℝ) → Ξ → ℝ)
    (hA31 : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (hA32meas : ∀ x ∈ X, Measurable (C x))
    (hA32cont : ∀ᵐ s ∂Pξ, Continuous (fun x => C x s))
    (γ : ℝ → ℝ → ℝ) (hγ : ∀ ε > 0, SmoothCCP.Feasibility.AdmissibleGamma ε (γ ε))
    (U : Set (Fin n → ℝ)) (hU : IsCompact U) (hUX : U ⊆ X) :
    TendstoUniformlyOn (fun (ε : ℝ) (x : Fin n → ℝ) => SmoothCCP.Feasibility.smoothCdf Pξ C ε (γ ε) 0 x)
      (fun x => SmoothCCP.Feasibility.cdf Pξ C 0 x) (𝓝[>] (0 : ℝ)) U := by
  -- H ε x = ∫ ψ_ε(C(x, ξ)) dℙ
  set H : ℝ → (Fin n → ℝ) → ℝ := fun ε x => ∫ s, psi ε (C x s) ∂Pξ with hH
  have hpsimeas : ∀ ε, ∀ x ∈ X, AEStronglyMeasurable (fun s => psi ε (C x s)) Pξ :=
    fun ε x hx => ((psi_continuous ε).measurable.comp (hA32meas x hx)).aestronglyMeasurable
  have hpsiint : ∀ ε, ∀ x ∈ X, Integrable (fun s => psi ε (C x s)) Pξ := by
    intro ε x hx
    refine Integrable.of_bound (hpsimeas ε x hx) 1 (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (psi_nonneg _ _)]
    exact psi_le_one _ _
  -- (1) the key bound |F_ε(0;x) - F(0;x)| ≤ H ε x
  have hbound : ∀ ε > 0, ∀ x ∈ X,
      dist (cdf Pξ C 0 x) (smoothCdf Pξ C ε (γ ε) 0 x) ≤ H ε x := by
    intro ε hε x hx
    have hms : MeasurableSet {s | C x s ≤ 0} := measurableSet_le (hA32meas x hx) measurable_const
    have hcdf : cdf Pξ C 0 x = ∫ s, Set.indicator {s | C x s ≤ 0} (1 : Ξ → ℝ) s ∂Pξ := by
      unfold cdf; rw [integral_indicator_one hms]
    have hgc : Continuous (Gam ε (γ ε)) := (hγ ε hε).differentiable.continuous
    have hgmeas : AEStronglyMeasurable (fun s => Gam ε (γ ε) (C x s - 0)) Pξ :=
      (hgc.measurable.comp ((hA32meas x hx).sub measurable_const)).aestronglyMeasurable
    have hgint : Integrable (fun s => Gam ε (γ ε) (C x s - 0)) Pξ := by
      refine Integrable.of_bound hgmeas 1 (Filter.Eventually.of_forall fun s => ?_)
      have h := (gam_sub_ind_le (hγ ε hε) (C x s - 0))
      unfold Gam
      rw [Real.norm_eq_abs]
      split_ifs with h1 h2
      · simp
      · have := (hγ ε hε).mapsTo (C x s - 0) ⟨by linarith, h2.le⟩
        rw [abs_le]; constructor <;> linarith [this.1, this.2]
      · simp
    have hiint : Integrable (fun s => Set.indicator {s | C x s ≤ 0} (1 : Ξ → ℝ) s) Pξ :=
      (integrable_const (1 : ℝ)).indicator hms
    unfold smoothCdf
    rw [hcdf, Real.dist_eq, ← integral_sub hiint hgint, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hpsiint ε x hx) (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_sub_comm]
    have h := gam_sub_ind_le (hγ ε hε) (C x s - 0)
    rw [sub_zero] at h ⊢
    have hind : Set.indicator {s | C x s ≤ 0} (1 : Ξ → ℝ) s = if C x s ≤ 0 then 1 else 0 := by
      simp [Set.indicator_apply]
    rw [hind]
    exact h
  -- (2) H ε · is continuous on X
  have hHcont : ∀ ε, ContinuousOn (H ε) X := by
    intro ε
    refine continuousOn_of_dominated (bound := fun _ => (1 : ℝ)) (hpsimeas ε) ?_
      (integrable_const _) ?_
    · intro x hx
      refine Filter.Eventually.of_forall fun s => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (psi_nonneg _ _)]
      exact psi_le_one _ _
    · filter_upwards [hA32cont] with s hs
      exact ((psi_continuous ε).comp hs).continuousOn
  -- (3) for fixed x ∈ X, H ε x → 0 as ε → 0⁺
  have hHlim : ∀ x ∈ X, Tendsto (fun ε => H ε x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro x hx
    have hnz : ∀ᵐ s ∂Pξ, C x s ≠ 0 := by
      rw [ae_iff]
      simpa using hA31 x hx 0
    have := tendsto_integral_filter_of_dominated_convergence (μ := Pξ) (l := 𝓝[>] (0 : ℝ))
      (F := fun ε s => psi ε (C x s)) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (Filter.Eventually.of_forall fun ε => hpsimeas ε x hx)
      (Filter.Eventually.of_forall fun ε => Filter.Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (psi_nonneg _ _)]; exact psi_le_one _ _)
      (integrable_const _) (by
        filter_upwards [hnz] with s hs
        have hpos : 0 < |C x s| / 2 := by positivity
        apply tendsto_const_nhds.congr'
        filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
        rw [psi_eq_zero hε.1 (by linarith [hε.2])])
    simpa using this
  -- (4) compactness (Dini-type) argument
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have key : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ U, H ε x < δ := by
    refine hU.induction_on (p := fun t => ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ t, H ε x < δ)
      (Filter.Eventually.of_forall fun _ x hx => absurd hx (Set.notMem_empty x))
      (fun s t hst ht => ht.mono fun ε h x hx => h x (hst hx))
      (fun s t hs ht => (hs.and ht).mono fun ε h x hx => hx.elim (h.1 x) (h.2 x)) ?_
    intro x hx
    obtain ⟨ε0, hε0, hε0pos⟩ :=
      (((hHlim x (hUX hx)).eventually (gt_mem_nhds hδ)).and self_mem_nhdsWithin).exists
    refine ⟨U ∩ {x' | H ε0 x' < δ}, ?_, ?_⟩
    · have hcU : ContinuousWithinAt (H ε0) U x := ((hHcont ε0).mono hUX) x hx
      have := hcU.eventually (gt_mem_nhds hε0)
      exact Filter.inter_mem self_mem_nhdsWithin this
    · filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < ε0 from hε0pos)] with ε hε x' hx'
      have hle : H ε x' ≤ H ε0 x' :=
        integral_mono (hpsiint ε x' (hUX hx'.1)) (hpsiint ε0 x' (hUX hx'.1))
          (fun s => psi_mono hε.1 hε.2 _)
      exact lt_of_le_of_lt hle hx'.2
  filter_upwards [key, self_mem_nhdsWithin] with ε hε hεpos x hx
  exact lt_of_le_of_lt (hbound ε hεpos x (hUX hx)) (hε x hx)
