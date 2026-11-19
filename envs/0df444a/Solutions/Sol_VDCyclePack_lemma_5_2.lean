-- Prove2me | solution 1 for VDCyclePack.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:54:08.123763+00:00
-- url     : https://prove2.me/submissions/df2de98b-187b-412d-88d1-d1f7a80e21c7

import Mathlib

open MeasureTheory ProbabilityTheory

lemma concave_log3 : ConcaveOn ℝ (Set.Ici (0:ℝ)) (fun x => Real.log (x + 3)) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hx3 : x + 3 ∈ Set.Ioi (0:ℝ) := by simp only [Set.mem_Ioi]; linarith [Set.mem_Ici.mp hx]
  have hy3 : y + 3 ∈ Set.Ioi (0:ℝ) := by simp only [Set.mem_Ioi]; linarith [Set.mem_Ici.mp hy]
  have h := (strictConcaveOn_log_Ioi.concaveOn).2 hx3 hy3 ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have e : a * (x + 3) + b * (y + 3) = a * x + b * y + 3 := by
    have : b = 1 - a := by linarith
    subst this; ring
  rw [e] at h; exact h

theorem solution {Ω ι : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] [Fintype ι] (I : ι → Ω → ℝ)
    (hmeas : ∀ i, Measurable (I i)) (hbern : ∀ i ω, I i ω = 0 ∨ I i ω = 1)
    (hind : ProbabilityTheory.iIndepFun I μ) :
    ∫ ω, (∑ i, I i ω) * Real.logb 2 ((∑ i, I i ω) + 2) ∂μ ≤
      (∫ ω, (∑ i, I i ω) ∂μ) * Real.logb 2 ((∫ ω, (∑ i, I i ω) ∂μ) + 3) := by
  classical
  have hI01 : ∀ i ω, 0 ≤ I i ω ∧ I i ω ≤ 1 := fun i ω => by
    rcases hbern i ω with h | h <;> rw [h] <;> norm_num
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  -- R_i = sum of the others
  set R : ι → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, I j ω with hR
  have hRfun : ∀ i, R i = ∑ j ∈ Finset.univ.erase i, I j := by
    intro i; funext ω; simp [hR, Finset.sum_apply]
  have hRm : ∀ i, Measurable (R i) := fun i => Finset.measurable_sum _ (fun j _ => hmeas j)
  have hR0 : ∀ i ω, 0 ≤ R i ω := fun i ω => Finset.sum_nonneg (fun j _ => (hI01 j ω).1)
  have hRn : ∀ i ω, R i ω ≤ n := fun i ω => by
    calc R i ω ≤ ∑ _j ∈ Finset.univ.erase i, (1:ℝ) := Finset.sum_le_sum (fun j _ => (hI01 j ω).2)
      _ ≤ ∑ _j : ι, (1:ℝ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => zero_le_one)
      _ = n := by simp [hn]
  have hsplit : ∀ i ω, ∑ j, I j ω = I i ω + R i ω := fun i ω => by
    simp only [hR]; exact (Finset.add_sum_erase Finset.univ (fun j => I j ω) (Finset.mem_univ i)).symm
  have hInt_bdd : ∀ (f : Ω → ℝ) (C : ℝ), Measurable f → (∀ ω, |f ω| ≤ C) → Integrable f μ :=
    fun f C hf hC => Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hC ω))
  have hlogR_bdd : ∀ i ω, |Real.log (R i ω + 3)| ≤ Real.log (n + 3) := fun i ω => by
    have h3 : 1 ≤ R i ω + 3 := by linarith [hR0 i ω]
    rw [abs_of_nonneg (Real.log_nonneg h3)]
    exact Real.log_le_log (by linarith) (by linarith [hRn i ω])
  -- pointwise identity
  have hpt : ∀ ω, (∑ i, I i ω) * Real.log ((∑ i, I i ω) + 2) =
      ∑ i, I i ω * Real.log (R i ω + 3) := by
    intro ω
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    rcases hbern i ω with h | h
    · rw [h]; ring
    · rw [hsplit i ω, h]; ring_nf
  have hterm : ∀ i, ∫ ω, I i ω * Real.log (R i ω + 3) ∂μ ≤
      (∫ ω, I i ω ∂μ) * Real.log ((∫ ω, ∑ j, I j ω ∂μ) + 3) := by
    intro i
    have hind_i : IndepFun (I i) (fun ω => Real.log (R i ω + 3)) μ := by
      have h1 := hind.indepFun_finsetSum_of_notMem hmeas (s := Finset.univ.erase i) (i := i)
        (Finset.notMem_erase i _)
      rw [← hRfun i] at h1
      exact h1.symm.comp measurable_id ((Real.measurable_log.comp (measurable_id.add_const 3)))
    rw [hind_i.integral_fun_mul_eq_mul_integral (hmeas i).aestronglyMeasurable
      ((Real.measurable_log.comp ((hRm i).add_const 3))).aestronglyMeasurable]
    have hp0 : 0 ≤ ∫ ω, I i ω ∂μ := integral_nonneg (fun ω => (hI01 i ω).1)
    apply mul_le_mul_of_nonneg_left _ hp0
    have hRi : Integrable (R i) μ := hInt_bdd _ n (hRm i) (fun ω => by
      rw [abs_of_nonneg (hR0 i ω)]; exact hRn i ω)
    have hjensen := concave_log3.le_map_integral (μ := μ) (f := R i)
      (ContinuousOn.log (continuousOn_id.add continuousOn_const) ?_) isClosed_Ici
      (Filter.Eventually.of_forall (fun ω => Set.mem_Ici.mpr (hR0 i ω))) hRi
      (hInt_bdd _ _ (Real.measurable_log.comp ((hRm i).add_const 3)) (hlogR_bdd i))
    · refine hjensen.trans (Real.log_le_log ?_ ?_)
      · have := integral_nonneg (μ := μ) (f := R i) (fun ω => hR0 i ω); linarith
      · have hsum : ∫ ω, ∑ j, I j ω ∂μ = (∫ ω, I i ω ∂μ) + ∫ ω, R i ω ∂μ := by
          rw [← integral_add ((hInt_bdd _ 1 (hmeas i) (fun ω => by
            rw [abs_of_nonneg (hI01 i ω).1]; exact (hI01 i ω).2))) hRi]
          congr 1; funext ω; exact hsplit i ω
        linarith
    · intro x hx
      have := Set.mem_Ici.mp hx
      simp only [id, ne_eq]; linarith
  -- assemble in natural log
  have hmain : ∫ ω, (∑ i, I i ω) * Real.log ((∑ i, I i ω) + 2) ∂μ ≤
      (∫ ω, (∑ i, I i ω) ∂μ) * Real.log ((∫ ω, (∑ i, I i ω) ∂μ) + 3) := by
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun i _ => hInt_bdd (fun ω => I i ω * Real.log (R i ω + 3)) (Real.log (n + 3))
      (by exact (hmeas i).mul (Real.measurable_log.comp ((hRm i).add_const 3))) (fun ω => by
        rw [abs_mul]
        calc |I i ω| * |Real.log (R i ω + 3)| ≤ 1 * Real.log (n + 3) :=
              mul_le_mul (by rw [abs_of_nonneg (hI01 i ω).1]; exact (hI01 i ω).2) (hlogR_bdd i ω)
                (abs_nonneg _) zero_le_one
          _ = Real.log (n + 3) := one_mul _))]
    calc ∑ i, ∫ ω, I i ω * Real.log (R i ω + 3) ∂μ
        ≤ ∑ i, (∫ ω, I i ω ∂μ) * Real.log ((∫ ω, ∑ j, I j ω ∂μ) + 3) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = _ := by
          rw [← Finset.sum_mul, ← integral_finsetSum _ (fun i _ => hInt_bdd (I i) 1 (hmeas i) (fun ω => by
            rw [abs_of_nonneg (hI01 i ω).1]; exact (hI01 i ω).2))]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [Real.logb]
  have e1 : ∫ ω, (∑ i, I i ω) * (Real.log ((∑ i, I i ω) + 2) / Real.log 2) ∂μ =
      (∫ ω, (∑ i, I i ω) * Real.log ((∑ i, I i ω) + 2) ∂μ) / Real.log 2 := by
    rw [← integral_div]; congr 1; funext ω; ring
  rw [e1, mul_div_assoc', div_le_div_iff_of_pos_right hl2]
  exact hmain
