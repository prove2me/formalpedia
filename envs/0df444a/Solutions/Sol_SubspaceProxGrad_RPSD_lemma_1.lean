-- Prove2me | solution 1 for SubspaceProxGrad.RPSD.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T12:42:54.69727+00:00
-- url     : https://prove2.me/submissions/fdb71c35-90fd-4a70-b6ee-a3a91c0fce52

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic
import Definitions.Def_SubspaceProxGrad_RPSD_Setting

open MeasureTheory ProbabilityTheory
open SubspaceProxGrad.RPSD

set_option autoImplicit false

namespace AvgProjectionProof

lemma proj_integrable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (pr : Measure Ω) [IsProbabilityMeasure pr] (S : Ω → Submodule ℝ (E n))
    (hS : ∀ x : E n, Measurable fun ω => (S ω).starProjection x) (x : E n) :
    Integrable (fun ω => (S ω).starProjection x) pr := by
  exact (integrable_const ‖x‖).mono' (hS x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => (S ω).norm_starProjection_apply_le x)

lemma inner_proj {n : ℕ} (S : Submodule ℝ (E n)) (x : E n) :
    inner ℝ x (S.starProjection x) = ‖S.starProjection x‖ ^ 2 := by
  have h := S.re_inner_starProjection_eq_normSq x
  change inner ℝ (S.starProjection x) x = ‖S.starProjection x‖ ^ 2 at h
  rw [real_inner_comm] at h
  exact h

lemma average_positive {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (pr : Measure Ω) [IsProbabilityMeasure pr] (S : Ω → Submodule ℝ (E n))
    (hS : ∀ x : E n, Measurable fun ω => (S ω).starProjection x)
    (hadm : IsAdmissible pr S) (P : E n →L[ℝ] E n) (hP : IsAvgProj pr S P)
    (x : E n) (hx : x ≠ 0) : 0 < inner ℝ x (P x) := by
  have hi := (proj_integrable pr S hS x).const_inner (𝕜 := ℝ) x
  have heq : inner ℝ x (P x) = ∫ ω, inner ℝ x ((S ω).starProjection x) ∂pr := by
    rw [hP x, integral_inner (proj_integrable pr S hS x)]
  have hn : ∀ ω, 0 ≤ inner ℝ x ((S ω).starProjection x) := by
    intro ω
    rw [inner_proj]
    positivity
  rw [heq]
  apply lt_of_le_of_ne (integral_nonneg hn)
  intro hz
  have ha := (integral_eq_zero_iff_of_nonneg hn hi).mp hz.symm
  have ho : ∀ᵐ ω ∂pr, x ∈ (S ω)ᗮ := by
    filter_upwards [ha] with ω hω
    apply (S ω).starProjection_apply_eq_zero_iff.mp
    rw [inner_proj] at hω
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hω)
  have hm : pr {ω | x ∈ (S ω)ᗮ} = 1 := by
    calc
      pr {ω | x ∈ (S ω)ᗮ} = pr Set.univ := measure_congr (by
        filter_upwards [ho] with ω hω
        exact propext (iff_of_true hω (Set.mem_univ ω)))
      _ = 1 := measure_univ
  exact (ne_of_lt (hadm x hx)) hm

end AvgProjectionProof

theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    [IsProbabilityMeasure pr] (S : Ω → Submodule ℝ (E n))
    (hS : ∀ x : E n, Measurable fun ω => (S ω).starProjection x)
    (hadm : IsAdmissible pr S) (P : E n →L[ℝ] E n) (hP : IsAvgProj pr S P) :
    IsSelfAdjoint P ∧ (∀ x : E n, x ≠ 0 → 0 < inner ℝ x (P x)) ∧
      0 < lamMin P ∧ lamMax P ≤ 1 := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hi := AvgProjectionProof.proj_integrable pr S hS
  have hp := AvgProjectionProof.average_positive pr S hS hadm P hP
  have hsym : IsSelfAdjoint P := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    change inner ℝ (P x) y = inner ℝ x (P y)
    rw [← real_inner_comm (P x) y, hP x, hP y, ← integral_inner (hi x), ← integral_inner (hi y)]
    apply integral_congr_ae
    filter_upwards [] with ω
    calc
      inner ℝ y ((S ω).starProjection x) =
          inner ℝ ((S ω).starProjection x) y := real_inner_comm _ _
      _ = inner ℝ x ((S ω).starProjection y) :=
        (S ω).inner_starProjection_left_eq_right x y
  have hnorm : ∀ x, ‖P x‖ ≤ ‖x‖ := by
    intro x
    rw [hP x]
    calc
      ‖∫ ω, (S ω).starProjection x ∂pr‖ ≤ ∫ ω, ‖(S ω).starProjection x‖ ∂pr :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ _ : Ω, ‖x‖ ∂pr := integral_mono (hi x).norm (integrable_const _) fun ω =>
        (S ω).norm_starProjection_apply_le x
      _ = ‖x‖ := by simp
  have hs : (Metric.sphere (0 : E n) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  letI : Nonempty (Metric.sphere (0 : E n) 1) := hs.to_subtype
  have hc : Continuous (fun x : E n => inner ℝ x (P x)) := continuous_id.inner P.continuous
  obtain ⟨z, hz, hmin⟩ := (isCompact_sphere (0 : E n) 1).exists_isMinOn hs hc.continuousOn
  have hz0 : z ≠ 0 := by
    intro h
    simpa [h] using hz
  have hlo : 0 < lamMin P := by
    exact lt_of_lt_of_le (hp z hz0) (le_ciInf fun x => hmin x.property)
  have hhi : lamMax P ≤ 1 := by
    apply ciSup_le
    intro x
    have hx : ‖(x : E n)‖ = 1 := by simpa using x.property
    calc
      inner ℝ (x : E n) (P x) ≤ ‖(x : E n)‖ * ‖P x‖ := real_inner_le_norm _ _
      _ ≤ ‖(x : E n)‖ * ‖(x : E n)‖ := mul_le_mul_of_nonneg_left (hnorm x) (norm_nonneg _)
      _ = 1 := by rw [hx]; norm_num
  exact ⟨hsym, hp, hlo, hhi⟩

#print axioms solution
