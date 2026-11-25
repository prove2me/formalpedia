-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.flatGraph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:54:46.54873+00:00
-- url     : https://prove2.me/submissions/e0c31a49-30fc-4d75-99ef-1e051c088684

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableFd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_tendsto_lint
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_enorm_sq_V
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_int_comb
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_wd_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_wdb_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_reindex
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_dop_div
import Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_dop_sb__0996b08225dc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
open FlatWeightedEstimates
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (hGraph : B.GraphSt (V n) volume ℝ) (hSmooth : B.SmoothSt (V n) volume)
    (hSupp : B.SupportSt (V n) volume) (hStd : B.StdSt (V n) volume) : FlatGraphStatement n := by
  intro Ω K G D S hΩ hK hKΩ hvan hG hD hS hdiv hsb
  obtain ⟨r, hr, hrΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  refine ⟨Metric.cthickening r K, hK.cthickening, hrΩ, fun δ hδ => ?_⟩
  have hGj : ∀ j, MemLp (fun u => G u j) 2 volume := fun j =>
    (EuclideanSpace.proj j : V n →L[ℂ] ℂ).comp_memLp' hG
  have hSjk : ∀ j k, MemLp (fun u => S u j k) 2 volume := fun j k =>
    ((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj j : (Fin n → Fin n → ℂ) →L[ℂ] (Fin n → ℂ))).comp_memLp' hS
  have hGl : ∀ j, LocallyIntegrable (fun u => G u j) volume := fun j =>
    (hGj j).locallyIntegrable (by norm_num)
  have hWD : B.IsWeakD volume (cD n) (vD n)
      (fun p => fun u => G u (finProdFinEquiv.symm p).1) D := by
    refine ⟨fun p => hGl _, hD.locallyIntegrable (by norm_num), fun φ hφ hc => ?_⟩
    have hI := fun j => int_comb (hGl j) hφ hc (1 / 2) (-Complex.I / 2) (bas n j)
      (Complex.I • bas n j)
    have e1 := hdiv φ hφ hc
    simp only [wd_eq] at e1
    rw [integral_finsetSum _ (fun j _ => (hI j).1),
      Finset.sum_congr rfl (fun j _ => (hI j).2)] at e1
    have h2 := reindex (n := n) (fun q => ![(1 : ℂ) / 2, -Complex.I / 2] q.2 *
      ∫ y, G y q.1 * fderiv ℝ φ y (![bas n q.1, Complex.I • bas n q.1] q.2))
    have h3 : ∑ p, cD n p * ∫ x, (fun u => G u (finProdFinEquiv.symm p).1) x *
        fderiv ℝ φ x (vD n p) = ∑ j, (1 / 2 * (∫ y, G y j * fderiv ℝ φ y (bas n j)) +
          -Complex.I / 2 * ∫ y, G y j * fderiv ℝ φ y (Complex.I • bas n j)) :=
      h2.trans (Finset.sum_congr rfl fun j _ => by simp)
    rw [h3, e1, neg_neg]
  have hWS : ∀ j k, B.IsWeakD volume cS (vS n j k)
      (fun p => ![fun u => G u k, fun u => G u k, fun u => G u j, fun u => G u j] p)
      (fun u => S u j k) := by
    intro j k
    refine ⟨fun p => ?_, (hSjk j k).locallyIntegrable (by norm_num), fun φ hφ hc => ?_⟩
    · fin_cases p <;> exact hGl _
    have hk := int_comb (hGl k) hφ hc (1 / 2) (Complex.I / 2) (bas n j) (Complex.I • bas n j)
    have hj := int_comb (hGl j) hφ hc (1 / 2) (Complex.I / 2) (bas n k) (Complex.I • bas n k)
    have e1 := hsb φ hφ hc j k
    simp only [wdb_eq] at e1
    rw [integral_sub hk.1 hj.1, hk.2, hj.2] at e1
    rw [Fin.sum_univ_four]
    simp only [cS, vS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination e1
  have hKr : ∀ t : ℝ, 0 < t → (B.Kernel.std (V n) volume t).r = t := fun t ht => by
    simp [B.Kernel.std, B.Kernel.ofBump, B.stdBump, ht]
  have hGD := hGraph (𝓝[>] 0) (fun t => B.Kernel.std (V n) volume t) hStd _ _ _ _ _ hWD
    (fun p => hGj _) hD
  have hGS := fun j k => hGraph (𝓝[>] 0) (fun t => B.Kernel.std (V n) volume t) hStd _ _ _ _ _
    (hWS j k) (fun p => by fin_cases p <;> exact hGj _) (hSjk j k)
  have T1 : Tendsto (fun t => ∑ j, ∫⁻ y,
      ‖B.moll (B.Kernel.std (V n) volume t) (fun u => G u j) y - G y j‖ₑ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ
      (fun j _ => tendsto_lint _ (hGD.1 (finProdFinEquiv (j, 0))))
    simpa using this
  have T2 := tendsto_lint _ hGD.2
  have T3 : Tendsto (fun t => ∑ j, ∑ k, ∫⁻ y, ‖(B.Dop cS (vS n j k)
      (fun p => B.moll (B.Kernel.std (V n) volume t)
        (![fun u => G u k, fun u => G u k, fun u => G u j, fun u => G u j] p)) -
      fun u => S u j k) y‖ₑ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ (fun j _ => tendsto_finsetSum Finset.univ
      (fun k _ => tendsto_lint _ (hGS j k).2))
    simpa using this
  have e4 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have e5 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < r := nhdsWithin_le_nhds (Iio_mem_nhds hr)
  have ev := (((T1.eventually (gt_mem_nhds hδ)).and (T2.eventually (gt_mem_nhds hδ))).and
    (T3.eventually (gt_mem_nhds hδ))).and (e4.and e5)
  obtain ⟨t, ⟨⟨h1, h2⟩, h3⟩, ht0', htr'⟩ := ev.exists
  have hmc : ∀ j, ContDiff ℝ ∞ (B.moll (B.Kernel.std (V n) volume t) (fun u => G u j)) :=
    fun j => hSmooth _ _ (hGl j)
  refine ⟨fun y => WithLp.toLp 2 (fun j => B.moll (B.Kernel.std (V n) volume t)
    (fun u => G u j) y), ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_piLp' 2 fun j => hmc j
  · intro y hy
    have hz : ∀ j, B.moll (B.Kernel.std (V n) volume t) (fun u => G u j) y = 0 := by
      intro j
      by_contra hne
      have hm := hSupp (B.Kernel.std (V n) volume t) (fun u => G u j) (Function.mem_support.2 hne)
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hm
      apply hy
      have haK : a ∈ K := by
        by_contra haK
        exact ha (by simp [(hvan a haK).1])
      refine Metric.mem_cthickening_of_dist_le _ a r K haK ?_
      rw [hKr t ht0', mem_ball_zero_iff] at hb
      rw [dist_eq_norm, add_sub_cancel_left]
      linarith
    beta_reduce
    rw [show (fun j => B.moll (B.Kernel.std (V n) volume t) (fun u => G u j) y) = 0 from funext hz]
    simp
  · refine lt_of_le_of_lt (le_of_eq ?_) h1
    refine (lintegral_congr fun y => ?_).trans (lintegral_finsetSum' _ (fun j _ => ?_))
    · rw [enorm_sq_V]
      rfl
    · exact (((hmc j).continuous.aestronglyMeasurable.sub (hGj j).1).enorm).pow_const 2
  · refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h2
    exact congrArg (fun s => ‖s - D y‖ₑ ^ 2)
      (dop_div (fun j => B.moll (B.Kernel.std (V n) volume t) (fun u => G u j)) y).symm
  · let Q : Fin n → Fin n → V n → ℝ≥0∞ := fun j k y => ‖(B.Dop cS (vS n j k)
        (fun p => B.moll (B.Kernel.std (V n) volume t)
          (![fun u => G u k, fun u => G u k, fun u => G u j, fun u => G u j] p)) -
        fun u => S u j k) y‖ₑ ^ 2
    have hmeas : ∀ j k, AEMeasurable (Q j k) volume := fun j k =>
      ((((Finset.measurable_sum _ fun p _ => (measurable_fderiv_apply_const ℝ _ _).const_mul
        _).aestronglyMeasurable).sub (hSjk j k).1).enorm).pow_const 2
    have hsum : ∫⁻ y, ∑ j, ∑ k, Q j k y = ∑ j, ∑ k, ∫⁻ y, Q j k y := by
      rw [lintegral_finsetSum' _ (fun j _ => Finset.aemeasurable_fun_sum _ fun k _ => hmeas j k)]
      exact Finset.sum_congr rfl fun j _ => lintegral_finsetSum' _ fun k _ => hmeas j k
    refine lt_of_le_of_lt (le_trans (lintegral_mono fun y => ?_) hsum.le) h3
    have hA : ∀ j k, Q j k y =
        ‖wdb n j (fun u => B.moll (B.Kernel.std (V n) volume t) (fun u => G u k) u) y -
          wdb n k (fun u => B.moll (B.Kernel.std (V n) volume t) (fun u => G u j) u) y -
          S y j k‖ₑ ^ 2 := fun j k => by
      simp only [Q]
      rw [Pi.sub_apply, dop_sb' j k _ _ _ rfl rfl rfl rfl y]
      rfl
    refine le_of_le_of_eq ?_ (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hA j k).symm
    beta_reduce
    unfold sq2
    refine le_trans (ENNReal.ofReal_le_ofReal (half_le_self (by positivity))) (le_of_eq ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
end ReciprocityTheory.L2DbarEstimates.F
