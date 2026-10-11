-- Prove2me | solution 1 for UhlenbeckGauge.yangMills_ge_boundaryChernSimons
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-10T21:40:42.758+00:00
-- url     : https://prove2.me/submissions/fdff6524-563b-4814-83dc-36410f0843f4

import Definitions.Def_uhlenbeck_gauge_box_defs
import Theorems.Thm_UhlenbeckGauge_norm_add_hodgeStar_sq
import Theorems.Thm_UhlenbeckGauge_integral_trWedge_eq_boundaryChernSimons
import Theorems.Thm_UhlenbeckGauge_curvature_isAntisymm_isSuNValued

open UhlenbeckGauge Matrix MeasureTheory
open scoped ContDiff ComplexOrder
set_option autoImplicit false

noncomputable section

private lemma ymge_re_trace_nonneg {n : ℕ} (X : Mat n) : 0 ≤ (trace (X * Xᴴ)).re := by
  have h := (posSemidef_self_mul_conjTranspose X).trace_nonneg
  exact (Complex.nonneg_iff.mp h).1

private lemma ymge_normSq_nonneg {n : ℕ} (G : TwoForm n) : 0 ≤ normSq G := by
  unfold normSq
  refine Finset.sum_nonneg (fun μ _ => Finset.sum_nonneg (fun ν _ => ?_))
  split_ifs
  · exact ymge_re_trace_nonneg _
  · exact le_refl _

private lemma ymge_pointwise {n : ℕ} (F : TwoForm n) (hF : IsAntisymm F)
    (hsu : IsSuNValued F) :
    -(trWedge F).re ≤ normSq F ∧ (trWedge F).re ≤ normSq F := by
  obtain ⟨h1, h2⟩ := norm_add_hodgeStar_sq F hF hsu
  have e1 := congrArg Complex.re h1
  have e2 := congrArg Complex.re h2
  simp at e1 e2
  have p1 := ymge_normSq_nonneg (F + hodgeStar F)
  have p2 := ymge_normSq_nonneg (F - hodgeStar F)
  constructor <;> linarith

private lemma ymge_cont_entry {n : ℕ} (A : Connection n) (hA : IsSUConnection A)
    (μ ν : Fin 4) (i j : Fin n) : Continuous (fun x => curvature A x μ ν i j) := by
  have hpd : ∀ (ρ σ : Fin 4) (i j : Fin n),
      Continuous (fun x => partialDeriv ρ (fun y => A y σ) x i j) := by
    intro ρ σ i j
    exact ((hA.1 σ i j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hAc : ∀ (σ : Fin 4) (i j : Fin n), Continuous (fun x => A x σ i j) :=
    fun σ i j => (hA.1 σ i j).continuous
  simp only [curvature, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]
  exact (((hpd μ ν i j).sub (hpd ν μ i j)).add
    ((continuous_finsetSum _ (fun k _ => (hAc μ i k).mul (hAc ν k j))).sub
      (continuous_finsetSum _ (fun k _ => (hAc ν i k).mul (hAc μ k j)))))

private lemma ymge_cont_mat {n : ℕ} (A : Connection n) (hA : IsSUConnection A)
    (μ ν : Fin 4) : Continuous (fun x => curvature A x μ ν) := by
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  exact ymge_cont_entry A hA μ ν i j

private lemma ymge_cont_normSq {n : ℕ} (A : Connection n) (hA : IsSUConnection A) :
    Continuous (fun x => normSq (curvature A x)) := by
  unfold normSq
  refine continuous_finsetSum _ (fun μ _ => continuous_finsetSum _ (fun ν _ => ?_))
  refine continuous_if_const _ (fun _ => ?_) (fun _ => continuous_const)
  exact Complex.continuous_re.comp
    (((ymge_cont_mat A hA μ ν).matrix_mul (ymge_cont_mat A hA μ ν).matrix_conjTranspose).matrix_trace)

private lemma ymge_cont_trWedge {n : ℕ} (A : Connection n) (hA : IsSUConnection A) :
    Continuous (fun x => trWedge (curvature A x)) := by
  unfold trWedge
  refine continuous_const.mul (continuous_finsetSum _ (fun μ _ => continuous_finsetSum _
    (fun ν _ => continuous_finsetSum _ (fun ρ _ => continuous_finsetSum _ (fun σ _ => ?_)))))
  exact continuous_const.mul
    (((ymge_cont_mat A hA μ ν).matrix_mul (ymge_cont_mat A hA ρ σ)).matrix_trace)

end

theorem solution {n : ℕ} (a b : R4) (hab : a ≤ b)
    (A : Connection n) (hA : IsSUConnection A) :
    -(boundaryChernSimons a b A).re ≤ yangMills a b A ∧
      (boundaryChernSimons a b A).re ≤ yangMills a b A := by
  have hint_n : IntegrableOn (fun x => normSq (curvature A x)) (Set.Icc a b) :=
    (ymge_cont_normSq A hA).continuousOn.integrableOn_compact isCompact_Icc
  have hint_t : IntegrableOn (fun x => trWedge (curvature A x)) (Set.Icc a b) :=
    (ymge_cont_trWedge A hA).continuousOn.integrableOn_compact isCompact_Icc
  have hint_re : IntegrableOn (fun x => (trWedge (curvature A x)).re) (Set.Icc a b) :=
    hint_t.re
  have key : (∫ x in Set.Icc a b, (trWedge (curvature A x)).re) =
      (boundaryChernSimons a b A).re := by
    rw [← integral_trWedge_eq_boundaryChernSimons a b hab A hA]
    exact integral_re hint_t
  have hpt : ∀ x, -(trWedge (curvature A x)).re ≤ normSq (curvature A x) ∧
      (trWedge (curvature A x)).re ≤ normSq (curvature A x) := fun x =>
    ymge_pointwise (curvature A x) (curvature_isAntisymm_isSuNValued A hA x).1
      (curvature_isAntisymm_isSuNValued A hA x).2
  unfold yangMills
  constructor
  · rw [← key, ← integral_neg]
    exact setIntegral_mono hint_re.neg hint_n (fun x => (hpt x).1)
  · rw [← key]
    exact setIntegral_mono hint_re hint_n (fun x => (hpt x).2)
