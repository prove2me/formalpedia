-- Prove2me | solution 1 for Rudin.ch10_simplex_ftc
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T03:12:16.509081+00:00
-- url     : https://prove2.me/submissions/b9af8544-e705-4497-ac5a-dd1666a60e71

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory Set

namespace Rudin


lemma isClosed_stdSimplex (k : ℕ) : IsClosed (stdSimplex k) := by
  have h1 : IsClosed {u : Fin k → ℝ | ∀ i, 0 ≤ u i} := by
    have h : {u : Fin k → ℝ | ∀ i, 0 ≤ u i} = ⋂ i : Fin k, {u : Fin k → ℝ | 0 ≤ u i} := by
      ext u; simp
    rw [h]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {u : Fin k → ℝ | ∑ i, u i ≤ 1} :=
    isClosed_le (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const
  exact h1.inter h2

lemma measurableSet_stdSimplex (k : ℕ) : MeasurableSet (stdSimplex k) :=
  (isClosed_stdSimplex k).measurableSet

lemma isCompact_stdSimplex (k : ℕ) : IsCompact (stdSimplex k) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨isClosed_stdSimplex k, ?_⟩
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, fun u hu => ?_⟩
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
  calc u i ≤ ∑ j, u j := Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)
    _ ≤ 1 := hu.2




/-- The point of `ℝ^{k+1}` whose `c`-th coordinate is `t` and whose remaining coordinates,
in order, are those of `y`. -/
noncomputable def ins {k : ℕ} (c : Fin (k + 1)) (t : ℝ) (y : Fin k → ℝ) : Fin (k + 1) → ℝ :=
  Fin.insertNth (α := fun _ => ℝ) c t y

@[simp] lemma ins_same {k : ℕ} (c : Fin (k + 1)) (t : ℝ) (y : Fin k → ℝ) : ins c t y c = t := by
  simp [ins]

@[simp] lemma ins_succAbove {k : ℕ} (c : Fin (k + 1)) (t : ℝ) (y : Fin k → ℝ) (s : Fin k) :
    ins c t y (c.succAbove s) = y s := by
  simp [ins]

lemma ins_self {k : ℕ} (c : Fin (k + 1)) (x : Fin (k + 1) → ℝ) :
    ins c (x c) (fun s => x (c.succAbove s)) = x := by
  rw [ins, Fin.insertNth_eq_iff]
  exact ⟨rfl, rfl⟩

lemma ins_sum {k : ℕ} (c : Fin (k + 1)) (t : ℝ) (y : Fin k → ℝ) :
    ∑ i, ins c t y i = t + ∑ s, y s := by
  rw [Fin.sum_univ_succAbove _ c]
  simp

lemma ins_eq_add {k : ℕ} (c : Fin (k + 1)) (t : ℝ) (y : Fin k → ℝ) :
    ins c t y = ins c 0 y + t • (Pi.single c 1 : Fin (k + 1) → ℝ) := by
  funext i
  refine Fin.succAboveCases c ?_ ?_ i
  · simp
  · intro s
    simp [Fin.succAbove_ne c s]

lemma continuous_ins {k : ℕ} (c : Fin (k + 1)) :
    Continuous fun p : ℝ × (Fin k → ℝ) => ins c p.1 p.2 := by
  rw [continuous_pi_iff]
  intro i
  refine Fin.succAboveCases c ?_ ?_ i
  · have h : (fun p : ℝ × (Fin k → ℝ) => ins c p.1 p.2 c) = fun p => p.1 := by
      funext p; simp
    rw [h]
    exact continuous_fst
  · intro s
    have h : (fun p : ℝ × (Fin k → ℝ) => ins c p.1 p.2 (c.succAbove s)) = fun p => p.2 s := by
      funext p; simp
    rw [h]
    exact (continuous_apply s).comp continuous_snd

lemma mem_stdSimplex_ins {k : ℕ} (c : Fin (k + 1)) (t : ℝ) (y : Fin k → ℝ) :
    ins c t y ∈ stdSimplex (k + 1) ↔ 0 ≤ t ∧ (∀ s, 0 ≤ y s) ∧ t + ∑ s, y s ≤ 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1 c, fun s => by simpa using h1 (c.succAbove s), ?_⟩
    rw [← ins_sum c t y]
    exact h2
  · rintro ⟨ht, hy, hsum⟩
    refine ⟨fun i => ?_, by rw [ins_sum]; exact hsum⟩
    refine Fin.succAboveCases c ?_ ?_ i
    · simpa using ht
    · intro s
      simpa using hy s

lemma continuous_partialDeriv {k : ℕ} {f : (Fin k → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (c : Fin k) :
    Continuous (partialDeriv f c) := by
  have h : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single c (1 : ℝ))).continuous.comp h

lemma hasDerivAt_ins {k : ℕ} {f : (Fin (k + 1) → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (c : Fin (k + 1)) (y : Fin k → ℝ) (t : ℝ) :
    HasDerivAt (fun t => f (ins c t y)) (partialDeriv f c (ins c t y)) t := by
  have h1 : HasDerivAt (fun t : ℝ => ins c t y) (Pi.single c 1) t := by
    have h2 : (fun t : ℝ => ins c t y)
        = fun t => ins c 0 y + t • (Pi.single c 1 : Fin (k + 1) → ℝ) := by
      funext s
      exact ins_eq_add c s y
    rw [h2]
    simpa using ((hasDerivAt_id t).smul_const (Pi.single c (1 : ℝ))).const_add (ins c 0 y)
  exact (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt t h1

lemma isCompact_preimage_ins {k : ℕ} (c : Fin (k + 1)) :
    IsCompact ((fun p : ℝ × (Fin k → ℝ) => ins c p.1 p.2) ⁻¹' stdSimplex (k + 1)) := by
  have himg : (fun p : ℝ × (Fin k → ℝ) => ins c p.1 p.2) ⁻¹' stdSimplex (k + 1)
      = (fun x : Fin (k + 1) → ℝ => (x c, fun s => x (c.succAbove s))) '' stdSimplex (k + 1) := by
    ext p
    constructor
    · intro hp
      exact ⟨ins c p.1 p.2, hp, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      simpa [ins_self c x] using hx
  rw [himg]
  exact (isCompact_stdSimplex (k + 1)).image (by fun_prop)

/-- The fundamental theorem of calculus on the standard simplex: integrating the `c`-th partial
derivative of a `C'` function over `Q^{k+1}` leaves the difference of the values of the function
on the two faces of `Q^{k+1}` transversal to the `c`-th coordinate. -/
theorem integral_partialDeriv_stdSimplex {k : ℕ} {f : (Fin (k + 1) → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) (c : Fin (k + 1)) :
    ∫ x in stdSimplex (k + 1), partialDeriv f c x
      = ∫ y in stdSimplex k, (f (ins c (1 - ∑ s, y s) y) - f (ins c 0 y)) := by
  classical
  have hEfun : ⇑((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) c).symm)
      = fun p : ℝ × (Fin k → ℝ) => ins c p.1 p.2 := by
    funext p
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, ins]
  have hmp : MeasurePreserving (fun p : ℝ × (Fin k → ℝ) => ins c p.1 p.2) volume volume := by
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) c).symm
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) c)
    rwa [hEfun] at h
  have hemb : MeasurableEmbedding fun p : ℝ × (Fin k → ℝ) => ins c p.1 p.2 := by
    have h := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) c).symm.measurableEmbedding
    rwa [hEfun] at h
  rw [← hmp.setIntegral_preimage_emb hemb (partialDeriv f c) (stdSimplex (k + 1))]
  have hTc : IsCompact ((fun p : ℝ × (Fin k → ℝ) => ins c p.1 p.2) ⁻¹' stdSimplex (k + 1)) :=
    isCompact_preimage_ins c
  have hTm : MeasurableSet ((fun p : ℝ × (Fin k → ℝ) => ins c p.1 p.2) ⁻¹' stdSimplex (k + 1)) :=
    hTc.isClosed.measurableSet
  have hFc : Continuous fun p : ℝ × (Fin k → ℝ) => partialDeriv f c (ins c p.1 p.2) :=
    (continuous_partialDeriv hf c).comp (continuous_ins c)
  have hint : Integrable
      (((fun p : ℝ × (Fin k → ℝ) => ins c p.1 p.2) ⁻¹' stdSimplex (k + 1)).indicator
        fun p => partialDeriv f c (ins c p.1 p.2)) := by
    rw [integrable_indicator_iff hTm]
    exact hFc.continuousOn.integrableOn_compact hTc
  rw [← integral_indicator hTm, Measure.volume_eq_prod, integral_prod_symm _
      (by rwa [Measure.volume_eq_prod] at hint),
    ← integral_indicator (measurableSet_stdSimplex k)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ stdSimplex k
  · rw [indicator_of_mem hy]
    have hsum : (0 : ℝ) ≤ 1 - ∑ s, y s := by linarith [hy.2]
    have heq : ∀ t : ℝ,
        (((fun p : ℝ × (Fin k → ℝ) => ins c p.1 p.2) ⁻¹' stdSimplex (k + 1)).indicator
            fun p => partialDeriv f c (ins c p.1 p.2)) (t, y)
          = (Icc (0 : ℝ) (1 - ∑ s, y s)).indicator
              (fun t => partialDeriv f c (ins c t y)) t := by
      intro t
      by_cases ht : t ∈ Icc (0 : ℝ) (1 - ∑ s, y s)
      · rw [indicator_of_mem ht, indicator_of_mem]
        exact (mem_stdSimplex_ins c t y).2 ⟨ht.1, hy.1, by have := ht.2; linarith⟩
      · rw [indicator_of_notMem ht, indicator_of_notMem]
        intro hmem
        obtain ⟨h1, -, h3⟩ := (mem_stdSimplex_ins c t y).1 hmem
        exact ht ⟨h1, by linarith⟩
    simp_rw [heq]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hsum]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_ins hf c y t)
      (((continuous_partialDeriv hf c).comp
        ((continuous_ins c).comp (Continuous.prodMk continuous_id
          continuous_const))).intervalIntegrable _ _)
  · rw [indicator_of_notMem hy]
    have hzero : ∀ t : ℝ,
        (((fun p : ℝ × (Fin k → ℝ) => ins c p.1 p.2) ⁻¹' stdSimplex (k + 1)).indicator
          fun p => partialDeriv f c (ins c p.1 p.2)) (t, y) = 0 := by
      intro t
      refine indicator_of_notMem (fun hmem => hy ?_) _
      obtain ⟨h1, h2, h3⟩ := (mem_stdSimplex_ins c t y).1 hmem
      exact ⟨h2, by linarith⟩
    simp_rw [hzero]
    simp


end Rudin


theorem solution (k : ℕ) (f : (Fin (k + 1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (c : Fin (k + 1)) :
    ∫ x in Rudin.stdSimplex (k + 1), Rudin.partialDeriv f c x
      = ∫ y in Rudin.stdSimplex k,
          (f (Fin.insertNth (α := fun _ => ℝ) c (1 - ∑ s, y s) y)
            - f (Fin.insertNth (α := fun _ => ℝ) c 0 y)) :=
  Rudin.integral_partialDeriv_stdSimplex hf c
