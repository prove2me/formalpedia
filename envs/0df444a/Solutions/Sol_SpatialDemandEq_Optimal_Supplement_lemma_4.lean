-- Prove2me | solution 1 for SpatialDemandEq.Optimal.Supplement.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:11:42.996333+00:00
-- url     : https://prove2.me/submissions/699ad391-2ee1-425e-92e4-efe0dda0a170

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model
import Definitions.Def_SpatialDemandEq_Optimal_Supplement_MMatrix
import Definitions.Def_SpatialDemandEq_Optimal_Supplement_Model

open MeasureTheory SpatialDemandEq.Optimal

open SpatialDemandEq
open SpatialDemandEq.Optimal
open SpatialDemandEq.Optimal.Supplement

theorem solution {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (dst : E n → E n → ℝ)
    (xs : Fin K → E n) (c lam : ℝ) (hS : Standing S ν dst xs c lam) (μ : Fin K → ℝ)
    (w : Fin K → ℝ)
    (hdiff : ∀ j, DifferentiableAt ℝ
      (fun w' : Fin K → ℝ => area ν (cell S (distFn dst xs) w' j)) w) :
    IsMMatrix (1 - Dmat ν S (distFn dst xs) c lam μ w) := by
      have := hS.prob
      set d := distFn dst xs with hd
      have hcont : ∀ k, Continuous (d k) := fun k =>
        hS.metric.1.comp (continuous_id.prodMk continuous_const)
      have hcellEq : ∀ (w' : Fin K → ℝ) k, cell S d w' k =
          S ∩ ⋂ j, ⋂ (_ : j ≠ k), {x | d k x + w' k ≤ d j x + w' j} := by
        intro w' k; ext x; simp [cell]
      have hmeas : ∀ (w' : Fin K → ℝ) k, MeasurableSet (cell S d w' k) := by
        intro w' k
        rw [hcellEq]
        refine hS.closed.measurableSet.inter (MeasurableSet.iInter fun j => MeasurableSet.iInter
          fun _ => measurableSet_le ?_ ?_)
        · exact ((hcont k).add continuous_const).measurable
        · exact ((hcont j).add continuous_const).measurable
      have hνS : ν S = 1 := (prob_compl_eq_zero_iff hS.closed.measurableSet).1 hS.supp
      have hsum : ∀ w' : Fin K → ℝ, ∑ j, area ν (cell S d w' j) = 1 := by
        intro w'
        have hU : (⋃ j, cell S d w' j) = S := by
          apply Set.Subset.antisymm
          · exact Set.iUnion_subset fun j x hx => hx.1
          · intro x hx
            obtain ⟨k, -, hk⟩ := Finset.exists_min_image Finset.univ (fun k => d k x + w' k)
              ⟨⟨0, hS.K_pos⟩, Finset.mem_univ _⟩
            exact Set.mem_iUnion.2 ⟨k, hx, fun j _ => hk j (Finset.mem_univ _)⟩
        have hdisj : Pairwise (Function.onFun (AEDisjoint ν) (fun j => cell S d w' j)) := by
          intro j k hjk
          show ν (cell S d w' j ∩ cell S d w' k) = 0
          have hsub : cell S d w' j ∩ cell S d w' k ⊆
              (fun x => d j x - d k x) ⁻¹' {w' k - w' j} := by
            intro x ⟨hx1, hx2⟩
            have a1 := hx1.2 k (Ne.symm hjk)
            have a2 := hx2.2 j hjk
            simp only [Set.mem_preimage, Set.mem_singleton_iff]
            linarith
          refine measure_mono_null hsub ?_
          have hm : Measurable (fun x => d j x - d k x) := ((hcont j).sub (hcont k)).measurable
          rw [← Measure.map_apply hm (measurableSet_singleton _)]
          exact hS.regular j k hjk (Real.volume_singleton)
        have h1 := measure_iUnion₀ hdisj (fun j => (hmeas w' j).nullMeasurableSet)
        rw [hU, hνS, tsum_fintype] at h1
        unfold area
        rw [← ENNReal.toReal_sum (fun j _ => measure_ne_top ν _), ← h1]
        simp
      have hPsum : ∀ k, ∑ j, partialArea ν S d w j k = 0 := by
        have hF : HasFDerivAt (∑ j : Fin K, fun w' => area ν (cell S d w' j))
            (∑ j, fderiv ℝ (fun w' => area ν (cell S d w' j)) w) w :=
          HasFDerivAt.sum (fun j _ => (hdiff j).hasFDerivAt)
        have hfun : (∑ j : Fin K, fun w' => area ν (cell S d w' j)) = fun _ => (1:ℝ) := by
          funext w'; simp [Finset.sum_apply, hsum]
        rw [hfun] at hF
        have h0 := hF.unique (hasFDerivAt_const (1:ℝ) w)
        intro k
        have := congrArg (fun L => L (Pi.single k (1:ℝ))) h0
        simpa [partialArea, ContinuousLinearMap.coe_sum', Finset.sum_apply] using this
      have hPnn : ∀ j k, j ≠ k → 0 ≤ partialArea ν S d w j k := by
        intro j k hjk
        set e : Fin K → ℝ := Pi.single k 1 with he
        have hmono : Monotone (fun t : ℝ => area ν (cell S d (w + t • e) j)) := by
          intro s t hst
          apply ENNReal.toReal_mono (measure_ne_top ν _)
          apply measure_mono
          intro x hx
          refine ⟨hx.1, fun i hi => ?_⟩
          have h1 := hx.2 i hi
          have hej : e j = 0 := by simp [he, Pi.single_apply, hjk]
          have hei : 0 ≤ e i := by
            simp only [he, Pi.single_apply]; split_ifs <;> norm_num
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hej, mul_zero] at h1 ⊢
          nlinarith
        have hh : HasDerivAt (fun t : ℝ => w + t • e) e 0 := by
          simpa using ((hasDerivAt_id (0:ℝ)).smul_const e).const_add w
        have hf : HasFDerivAt (fun w' => area ν (cell S d w' j))
            (fderiv ℝ (fun w' => area ν (cell S d w' j)) w) ((fun t : ℝ => w + t • e) 0) := by
          simpa using (hdiff j).hasFDerivAt
        have hg := hf.comp_hasDerivAt (0:ℝ) hh
        have := hmono.deriv_nonneg (x := 0)
        rw [show (fun t : ℝ => area ν (cell S d (w + t • e) j)) =
          (fun w' => area ν (cell S d w' j)) ∘ (fun t : ℝ => w + t • e) from rfl, hg.deriv] at this
        simpa [partialArea] using this
      set P := partialArea ν S d w with hPdef
      set α : Fin K → ℝ := fun j => lam * c / (μ j - lam * area ν (cell S d w j)) ^ 2 with hαdef
      have hα : ∀ j, 0 ≤ α j := fun j =>
        div_nonneg (mul_nonneg hS.lam_pos.le hS.c_pos.le) (sq_nonneg _)
      have hD : ∀ j k, Dmat ν S d c lam μ w j k = α j * P j k := fun j k => rfl
      refine ⟨fun i j hij => ?_, fun z hz => ?_⟩
      · rw [Matrix.sub_apply, Matrix.one_apply_ne hij, hD]
        have := mul_nonneg (hα i) (hPnn i j hij)
        linarith
      rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
        ← Matrix.exists_vecMul_eq_zero_iff] at hz
      obtain ⟨v, hv0, hv⟩ := hz
      set y : Fin K → ℂ := fun j => (α j : ℂ) * v j with hydef
      have hrow : ∀ k, (1 - z) * v k = ∑ j, y j * (P j k : ℂ) := by
        intro k
        have := congrFun hv k
        simp [Matrix.vecMul, dotProduct, Matrix.algebraMap_eq_diagonal, Matrix.sub_apply,
          Matrix.map_apply, Matrix.one_apply, Matrix.diagonal_apply, mul_sub,
          Finset.sum_sub_distrib, hD] at this
        have h2 : ∑ x, v x * (((if x = k then 1 else 0 : ℝ)) : ℂ) = v k := by
          rw [Finset.sum_eq_single k] <;> simp_all
        rw [h2] at this
        rw [show ∑ j, y j * (P j k : ℂ) = ∑ x, v x * ((α x : ℂ) * (P x k)) from
          Finset.sum_congr rfl fun j _ => by simp only [hydef]; ring]
        linear_combination -this
      have hy : ∀ k, (1 - z) * y k = (α k : ℂ) * ∑ j, y j * (P j k : ℂ) := by
        intro k
        rw [← hrow k, hydef]; ring
      by_cases hy0 : ∀ j, y j = 0
      · obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
        have h1 := hrow k
        simp only [hy0, zero_mul, Finset.sum_const_zero] at h1
        have : 1 - z = 0 := by
          rcases mul_eq_zero.1 h1 with h | h
          · exact h
          · exact absurd h hk
        have hz1 : z = 1 := by linear_combination -this
        rw [hz1]; norm_num
      push Not at hy0
      obtain ⟨j0, hj0⟩ := hy0
      obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun j => ‖y j‖)
        ⟨j0, Finset.mem_univ _⟩
      have hkpos : 0 < ‖y k‖ :=
        lt_of_lt_of_le (norm_pos_iff.2 hj0) (hk j0 (Finset.mem_univ _))
      have hkey : (1 - z) * y k * starRingEnd ℂ (y k) =
          (α k : ℂ) * ∑ j, (P j k : ℂ) * (y j * starRingEnd ℂ (y k)) := by
        rw [hy k, mul_assoc, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring
      have hre := congrArg Complex.re hkey
      rw [mul_assoc, Complex.mul_conj, Complex.re_mul_ofReal, Complex.re_ofReal_mul,
        Complex.re_sum] at hre
      have hterm : ∀ j, ((P j k : ℂ) * (y j * starRingEnd ℂ (y k))).re ≤
          P j k * Complex.normSq (y k) := by
        intro j
        rw [Complex.re_ofReal_mul]
        by_cases hjk : j = k
        · subst hjk
          rw [Complex.mul_conj, Complex.ofReal_re]
        · apply mul_le_mul_of_nonneg_left _ (hPnn j k hjk)
          calc (y j * starRingEnd ℂ (y k)).re ≤ ‖y j * starRingEnd ℂ (y k)‖ := Complex.re_le_norm _
            _ = ‖y j‖ * ‖y k‖ := by rw [norm_mul, Complex.norm_conj]
            _ ≤ ‖y k‖ * ‖y k‖ := mul_le_mul_of_nonneg_right (hk j (Finset.mem_univ _)) (norm_nonneg _)
            _ = Complex.normSq (y k) := by rw [Complex.normSq_eq_norm_sq]; ring
      have hsumle : ∑ j, ((P j k : ℂ) * (y j * starRingEnd ℂ (y k))).re ≤ 0 := by
        calc _ ≤ ∑ j, P j k * Complex.normSq (y k) := Finset.sum_le_sum fun j _ => hterm j
          _ = (∑ j, P j k) * Complex.normSq (y k) := by rw [Finset.sum_mul]
          _ = 0 := by rw [hPsum k, zero_mul]
      have hns : 0 < Complex.normSq (y k) := by
        rw [Complex.normSq_eq_norm_sq]; positivity
      have h3 : (1 - z).re * Complex.normSq (y k) ≤ 0 := by
        rw [hre]; exact mul_nonpos_of_nonneg_of_nonpos (hα k) hsumle
      have h4 : (1 - z).re ≤ 0 := by
        by_contra h; push Not at h; linarith [mul_pos h hns]
      simp only [Complex.sub_re, Complex.one_re] at h4
      linarith
