-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P06.regularized_semigroup_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:19:20.469956+00:00
-- url     : https://prove2.me/submissions/da6f2827-447e-4d6a-9bac-600627254793

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06
noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology

namespace QAlgorithms.Papers.Independent.Next46.P06

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem S200R_res_eq (T : ℝ → X →L[ℂ] X) (x : X) :
    semigroupResolventOne T x = ∫ v in Ioi (0:ℝ), Real.exp (-v) • T v x := by
  unfold semigroupResolventOne
  congr 1
  funext v
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.coe_smul]

theorem S200R_meas (T : ℝ → X →L[ℂ] X) (hT : BoundedSemigroup T) (x : X) (c : ℝ) (hc : 0 ≤ c) :
    AEStronglyMeasurable (fun v : ℝ => Real.exp (-v) • T v x) (volume.restrict (Ioi c)) := by
  have h1 : ContinuousOn (fun v : ℝ => Real.exp (-v) • T v x) (Ioi c) :=
    ((Real.continuous_exp.comp continuous_neg).continuousOn).smul
      ((hT.2.2.2 x).mono (Ioi_subset_Ioi hc))
  exact h1.aestronglyMeasurable measurableSet_Ioi

theorem S200R_pt (T : ℝ → X →L[ℂ] X) (M : ℝ) (hM : ∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ M)
    (x : X) (v : ℝ) (hv : 0 ≤ v) :
    ‖Real.exp (-v) • T v x‖ ≤ M * ‖x‖ * Real.exp (-v) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have := (T v).le_opNorm x
  have h2 : ‖T v‖ * ‖x‖ ≤ M * ‖x‖ := mul_le_mul_of_nonneg_right (hM v hv) (norm_nonneg _)
  nlinarith [Real.exp_pos (-v)]

theorem S200R_int (T : ℝ → X →L[ℂ] X) (hT : BoundedSemigroup T) (x : X) (c : ℝ) (hc : 0 ≤ c) :
    IntegrableOn (fun v : ℝ => Real.exp (-v) • T v x) (Ioi c) := by
  obtain ⟨M, -, hM⟩ := hT.2.2.1
  refine Integrable.mono' ((integrableOn_exp_neg_Ioi c).const_mul (M * ‖x‖))
    (S200R_meas T hT x c hc) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
  exact S200R_pt T M hM x v (hc.trans (le_of_lt hv))

theorem S200R_tail (T : ℝ → X →L[ℂ] X) (hT : BoundedSemigroup T) (M : ℝ)
    (hM : ∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ M) (x : X) (c : ℝ) (hc : 0 ≤ c) :
    ‖∫ v in Ioi c, Real.exp (-v) • T v x‖ ≤ M * ‖x‖ * Real.exp (-c) := by
  rw [← integral_exp_neg_Ioi c, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi c).const_mul (M * ‖x‖)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
  exact S200R_pt T M hM x v (hc.trans (le_of_lt hv))

/-- The resolvent as a CLM. -/
def S200R_R (T : ℝ → X →L[ℂ] X) (hT : BoundedSemigroup T) : X →L[ℂ] X :=
  LinearMap.mkContinuous
    { toFun := fun x => ∫ v in Ioi (0:ℝ), Real.exp (-v) • T v x
      map_add' := fun x y => by
        simp only [map_add, smul_add]
        exact integral_add (S200R_int T hT x 0 le_rfl) (S200R_int T hT y 0 le_rfl)
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        congr 1; funext v; rw [smul_comm] }
    (Classical.choose hT.2.2.1)
    (fun x => by
      have h := S200R_tail T hT _ (Classical.choose_spec hT.2.2.1).2 x 0 le_rfl
      simpa using h)

theorem S200R_R_apply (T : ℝ → X →L[ℂ] X) (hT : BoundedSemigroup T) (x : X) :
    S200R_R T hT x = ∫ v in Ioi (0:ℝ), Real.exp (-v) • T v x := rfl

theorem S200R_onePlus (T : ℝ → X →L[ℂ] X) (hT : BoundedSemigroup T) :
    onePlusInverse (negativeGenerator T) = S200R_R T hT := by
  have hG : graphInverse (graphAdd identityGraph (negativeGenerator T)) =
      banachBoundedGraph (S200R_R T hT) := by
    ext ⟨w, x⟩
    simp only [graphInverse, graphAdd, identityGraph, negativeGenerator, banachBoundedGraph,
      mem_setOf_eq]
    constructor
    · rintro ⟨y, z, rfl, hz, rfl⟩
      rw [S200R_R_apply, ← S200R_res_eq]; exact hz.symm
    · intro h
      refine ⟨x, w - x, rfl, ?_, by abel⟩
      simp only [add_sub_cancel]
      rw [S200R_res_eq, ← S200R_R_apply]; exact h.symm
  have hB : Bounded (graphInverse (graphAdd identityGraph (negativeGenerator T))) :=
    ⟨_, hG⟩
  unfold onePlusInverse boundedValue
  rw [dif_pos hB]
  have hs := Classical.choose_spec hB
  ext x
  have hx : (x, S200R_R T hT x) ∈ graphInverse (graphAdd identityGraph (negativeGenerator T)) := by
    rw [hG]; rfl
  rw [hs] at hx
  exact hx.symm


theorem S200R_shiftInt (g : ℝ → X) (t : ℝ) :
    ∫ u in Ioi (0:ℝ), g (u + t) = ∫ v in Ioi t, g v := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun v => (Ioi t).indicator g v) t]
  congr 1; funext u
  by_cases hu : 0 < u
  · rw [indicator_of_mem (show u ∈ Ioi (0:ℝ) from hu),
      indicator_of_mem (show u + t ∈ Ioi t by simp [hu])]
  · rw [indicator_of_notMem (show u ∉ Ioi (0:ℝ) from hu),
      indicator_of_notMem (show u + t ∉ Ioi t by simpa using hu)]

theorem S200R_shift (T : ℝ → X →L[ℂ] X) (hT : BoundedSemigroup T) (x : X) (t : ℝ) (ht : 0 ≤ t) :
    T t (S200R_R T hT x) = Real.exp t • ∫ v in Ioi t, Real.exp (-v) • T v x := by
  rw [S200R_R_apply, ← (T t).integral_comp_comm (S200R_int T hT x 0 le_rfl),
    ← S200R_shiftInt (fun v => Real.exp (-v) • T v x) t, ← integral_smul]
  refine setIntegral_congr_fun (measurableSet_Ioi (a := (0:ℝ))) (fun u hu => ?_)
  have hu' : (0:ℝ) < u := hu
  rw [ContinuousLinearMap.map_smul_of_tower, smul_smul]
  have hTT : T t (T u x) = T (u + t) x := by
    rcases ht.lt_or_eq with ht' | ht'
    · rw [add_comm, hT.2.1 t u ht' hu']; rfl
    · subst ht'; rw [hT.1, add_zero]; rfl
  rw [hTT]
  congr 1
  rw [← Real.exp_add]; congr 1; ring

theorem S200R_lip (T : ℝ → X →L[ℂ] X) (hT : BoundedSemigroup T) (M : ℝ)
    (hM : ∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ M) (x : X) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖T t (S200R_R T hT x) - T s (S200R_R T hT x)‖ ≤ 2 * M * ‖x‖ * (t - s) := by
  set g : ℝ → X := fun v => Real.exp (-v) • T v x with hg
  have hsplit : ∫ v in Ioi s, g v = (∫ v in Ioc s t, g v) + ∫ v in Ioi t, g v := by
    rw [← Ioc_union_Ioi_eq_Ioi hst]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      ((S200R_int T hT x s hs).mono_set Ioc_subset_Ioi_self) (S200R_int T hT x t (hs.trans hst))
  rw [S200R_shift T hT x t (hs.trans hst), S200R_shift T hT x s hs, hsplit]
  have e1 : Real.exp t • (∫ v in Ioi t, g v) - Real.exp s • ((∫ v in Ioc s t, g v) + ∫ v in Ioi t, g v)
      = (Real.exp t - Real.exp s) • (∫ v in Ioi t, g v) - Real.exp s • (∫ v in Ioc s t, g v) := by
    rw [smul_add, sub_smul]; abel
  rw [e1]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 le_rfl)
  have hA := S200R_tail T hT M hM x t (hs.trans hst)
  have hB : ‖∫ v in Ioc s t, g v‖ ≤ M * ‖x‖ * Real.exp (-s) * volume.real (Ioc s t) := by
    refine norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top (fun v hv => ?_)
    refine (S200R_pt T M hM x v (hs.trans (le_of_lt hv.1))).trans ?_
    have : Real.exp (-v) ≤ Real.exp (-s) := Real.exp_le_exp.2 (by linarith [hv.1])
    exact mul_le_mul_of_nonneg_left this (mul_nonneg hM0 (norm_nonneg _))
  rw [Real.volume_real_Ioc_of_le hst] at hB
  have hes : Real.exp s ≤ Real.exp t := Real.exp_le_exp.2 hst
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
    abs_of_pos (Real.exp_pos _)]
  have k1 : (Real.exp t - Real.exp s) * ‖∫ v in Ioi t, g v‖
      ≤ (Real.exp t - Real.exp s) * (M * ‖x‖ * Real.exp (-t)) :=
    mul_le_mul_of_nonneg_left hA (by linarith)
  have k2 : Real.exp s * ‖∫ v in Ioc s t, g v‖ ≤ Real.exp s * (M * ‖x‖ * Real.exp (-s) * (t - s)) :=
    mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le
  have q1 : (Real.exp t - Real.exp s) * Real.exp (-t) = 1 - Real.exp (-(t - s)) := by
    rw [sub_mul, ← Real.exp_add, ← Real.exp_add]; ring_nf; simp
  have q2 : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
  have q3 : 1 - Real.exp (-(t - s)) ≤ t - s := by linarith [Real.add_one_le_exp (-(t - s))]
  have hMx : 0 ≤ M * ‖x‖ := mul_nonneg hM0 (norm_nonneg _)
  have r1 : (Real.exp t - Real.exp s) * (M * ‖x‖ * Real.exp (-t)) = M * ‖x‖ * (1 - Real.exp (-(t - s))) := by
    rw [← q1]; ring
  have r2 : Real.exp s * (M * ‖x‖ * Real.exp (-s) * (t - s)) = M * ‖x‖ * (t - s) := by
    rw [show Real.exp s * (M * ‖x‖ * Real.exp (-s) * (t - s)) = (Real.exp s * Real.exp (-s)) * (M * ‖x‖ * (t - s)) by ring, q2, one_mul]
  have r3 : M * ‖x‖ * (1 - Real.exp (-(t - s))) ≤ M * ‖x‖ * (t - s) := mul_le_mul_of_nonneg_left q3 hMx
  nlinarith

end QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Next46.P06 in
open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore) in
theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [CompleteSpace X] (T : ℝ → X →L[ℂ] X)
    (hT : BoundedSemigroup T) (hnd : NondegenerateSemigroup T) :
    let A := negativeGenerator T
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      ‖(T t).comp (onePlusInverse A) - (T s).comp (onePlusInverse A)‖ ≤ L * |t - s| := by
  intro A
  obtain ⟨M, hM0, hM⟩ := hT.2.2.1
  have hR : onePlusInverse A = S200R_R T hT := S200R_onePlus T hT
  refine ⟨2 * M, by linarith, fun s t hs ht => ?_⟩
  rw [hR]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x => ?_)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  rcases le_total s t with hst | hts
  · rw [abs_of_nonneg (by linarith)]
    have := S200R_lip T hT M hM x s t hs hst
    linarith
  · rw [abs_of_nonpos (by linarith), norm_sub_rev]
    have := S200R_lip T hT M hM x t s ht hts
    linarith

