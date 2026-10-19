-- Prove2me | solution 1 for RelPartMech.metric_hessian_of_gSymbol_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:01:32.58401+00:00
-- url     : https://prove2.me/submissions/ed526b39-46a4-424b-8908-bb311552a54d

import Mathlib
import Definitions.Def_RelPartMech_coordinates

open scoped ContDiff
open MeasureTheory Set Filter Topology

namespace RPHAux

open RelPartMech

variable {n : ℕ}

lemma clm_expand (L : Coord n →L[ℝ] ℝ) (v : Coord n) :
    L v = ∑ β, v β * L (Pi.single β 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  congr 1; funext β
  rw [show Pi.single β (v β) = v β • (Pi.single β 1 : Coord n) by
    ext j; by_cases h : j = β <;> simp [h], map_smul, smul_eq_mul]

lemma smooth_of_pd (f : Coord n → ℝ) (hd : Differentiable ℝ f)
    (hp : ∀ β, ContDiff ℝ ∞ (pd β f)) : ContDiff ℝ ∞ f := by
  rw [contDiff_infty_iff_fderiv]
  refine ⟨hd, ?_⟩
  have : fderiv ℝ f = fun x => ∑ β, pd β f x • (ContinuousLinearMap.proj β : Coord n →L[ℝ] ℝ) := by
    funext x; ext v
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, pd]
    rw [clm_expand]
    congr 1; funext β; ring
  rw [this]
  exact ContDiff.sum fun β _ => (hp β).smul contDiff_const

/-- the integrand of the Poincaré homotopy formula -/
noncomputable def PF (om : Fin n → Coord n → ℝ) (x : Coord n) (t : ℝ) : ℝ :=
  ∑ β, x β * om β (t • x)

noncomputable def PF' (om : Fin n → Coord n → ℝ) (x : Coord n) (t : ℝ) : Coord n →L[ℝ] ℝ :=
  ∑ β, (om β (t • x) • (ContinuousLinearMap.proj β : Coord n →L[ℝ] ℝ) +
    x β • (t • fderiv ℝ (om β) (t • x)))

lemma PF_hasFDerivAt (om : Fin n → Coord n → ℝ) (hom : ∀ β, ContDiff ℝ ∞ (om β)) (x : Coord n) (t : ℝ) :
    HasFDerivAt (fun x => PF om x t) (PF' om x t) x := by
  unfold PF PF'
  have : (fun x : Coord n => ∑ β, x β * om β (t • x)) = ∑ β, (fun x : Coord n => x β * om β (t • x)) := by
    funext x; simp
  rw [this]
  apply HasFDerivAt.sum
  intro β _
  have h1 : HasFDerivAt (fun x : Coord n => x β) (ContinuousLinearMap.proj β : Coord n →L[ℝ] ℝ) x :=
    (ContinuousLinearMap.proj β : Coord n →L[ℝ] ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun x : Coord n => om β (t • x)) ((fderiv ℝ (om β) (t • x)).comp
      (t • ContinuousLinearMap.id ℝ (Coord n))) x := by
    have hs : HasFDerivAt (fun x : Coord n => t • x) (t • ContinuousLinearMap.id ℝ (Coord n)) x :=
      (t • ContinuousLinearMap.id ℝ (Coord n)).hasFDerivAt
    exact (((hom β).differentiable (by simp)) (t • x)).hasFDerivAt.comp x hs
  have h3 : HasFDerivAt (fun x : Coord n => x β * om β (t • x)) _ x := h1.mul h2
  refine h3.congr_fderiv ?_
  ext v
  simp
  ring

lemma PF'_cont (om : Fin n → Coord n → ℝ) (hom : ∀ β, ContDiff ℝ ∞ (om β)) :
    Continuous (fun p : Coord n × ℝ => PF' om p.1 p.2) := by
  unfold PF'
  apply continuous_finset_sum
  intro β _
  have hc : Continuous (fderiv ℝ (om β)) := (hom β).continuous_fderiv (by simp)
  have hom' : Continuous (om β) := (hom β).continuous
  fun_prop

lemma PF_cont (om : Fin n → Coord n → ℝ) (hom : ∀ β, ContDiff ℝ ∞ (om β)) :
    Continuous (fun p : Coord n × ℝ => PF om p.1 p.2) := by
  unfold PF
  have hom' : ∀ β, Continuous (om β) := fun β => (hom β).continuous
  fun_prop

noncomputable def PV (om : Fin n → Coord n → ℝ) (x : Coord n) : ℝ := ∫ t in Ioc (0:ℝ) 1, PF om x t

lemma PV_hasFDerivAt (om : Fin n → Coord n → ℝ) (hom : ∀ β, ContDiff ℝ ∞ (om β)) (x : Coord n) :
    HasFDerivAt (PV om) (∫ t in Ioc (0:ℝ) 1, PF' om x t) x := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall x 1).prod isCompact_Icc |>.exists_bound_of_continuousOn
    (PF'_cont om hom).continuousOn (f := fun p : Coord n × ℝ => PF' om p.1 p.2)
    (s := Metric.closedBall x 1 ×ˢ Icc (0:ℝ) 1)
  unfold PV
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (Metric.ball_mem_nhds x one_pos)
  · exact Eventually.of_forall fun x' =>
      ((PF_cont om hom).comp (Continuous.prodMk_right x')).aestronglyMeasurable
  · exact ((PF_cont om hom).comp (Continuous.prodMk_right x)).continuousOn.integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  · exact ((PF'_cont om hom).comp (Continuous.prodMk_right x)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht x' hx'
    exact hC (x', t) ⟨Metric.ball_subset_closedBall hx', Ioc_subset_Icc_self ht⟩
  · exact integrableOn_const (by simp)
  · exact Eventually.of_forall fun t x' _ => PF_hasFDerivAt om hom x' t

lemma PV_pd (om : Fin n → Coord n → ℝ) (hom : ∀ β, ContDiff ℝ ∞ (om β))
    (hcl : ∀ α β x, pd α (om β) x = pd β (om α) x) (α : Fin n) (x : Coord n) :
    pd α (PV om) x = om α x := by
  have hI : Integrable (fun t => PF' om x t) (volume.restrict (Ioc (0:ℝ) 1)) :=
    ((PF'_cont om hom).comp (Continuous.prodMk_right x)).continuousOn.integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  unfold pd
  rw [(PV_hasFDerivAt om hom x).fderiv, ContinuousLinearMap.integral_apply hI]
  have hval : ∀ t : ℝ, PF' om x t (Pi.single α 1) =
      om α (t • x) + t * fderiv ℝ (om α) (t • x) x := by
    intro t
    unfold PF'
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    · simp [Pi.single_apply]
    · rw [clm_expand (fderiv ℝ (om α) (t • x)) x, Finset.mul_sum]
      congr 1; funext β
      have := hcl α β (t • x)
      unfold pd at this
      rw [this]; ring
  simp_rw [hval]
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hd : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ => t * om α (t • x))
      (om α (t • x) + t * fderiv ℝ (om α) (t • x) x) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => t • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have h2 := (((hom α).differentiable (by simp)) (t • x)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => t * om α (t • x)) _ t := (hasDerivAt_id' t).mul h2
    exact h3.congr_deriv (by simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp
  · apply Continuous.intervalIntegrable
    have hc : Continuous (fderiv ℝ (om α)) := (hom α).continuous_fderiv (by simp)
    have hc2 : Continuous (om α) := (hom α).continuous
    fun_prop

theorem poincare (om : Fin n → Coord n → ℝ) (hom : ∀ β, ContDiff ℝ ∞ (om β))
    (hcl : ∀ α β x, pd α (om β) x = pd β (om α) x) :
    ∃ V : Coord n → ℝ, ContDiff ℝ ∞ V ∧ ∀ α x, pd α V x = om α x := by
  refine ⟨PV om, ?_, PV_pd om hom hcl⟩
  apply smooth_of_pd
  · exact fun x => (PV_hasFDerivAt om hom x).differentiableAt
  · intro β
    have : pd β (PV om) = om β := funext (PV_pd om hom hcl β)
    rw [this]; exact hom β

end RPHAux

open RelPartMech in
theorem solution {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (hG : ∀ α β γ x, gSymbol g α β γ x = 0) :
    ∃ S : Coord n → ℝ, ContDiff ℝ ∞ S ∧ ∀ α β x, g x α β = pd α (pd β S) x := by
  obtain ⟨hs, hsym, -⟩ := hg
  have h1 : ∀ γ : Fin n, ∃ V : Coord n → ℝ, ContDiff ℝ ∞ V ∧ ∀ β x, pd β V x = g x β γ := by
    intro γ
    refine RPHAux.poincare (fun β x => g x β γ) (fun β => hs β γ) ?_
    intro α β x
    have := hG α β γ x
    unfold gSymbol at this
    linarith
  choose V hVs hV using h1
  obtain ⟨S, hS, hSV⟩ := RPHAux.poincare V hVs (by
    intro α β x
    rw [hV, hV, hsym])
  refine ⟨S, hS, fun α β x => ?_⟩
  have : pd β S = V β := funext (hSV β)
  rw [this, hV]
