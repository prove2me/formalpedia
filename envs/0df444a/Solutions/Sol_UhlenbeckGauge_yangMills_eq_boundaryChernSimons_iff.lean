-- Prove2me | solution 1 for UhlenbeckGauge.yangMills_eq_boundaryChernSimons_iff
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-10T21:43:22.516857+00:00
-- url     : https://prove2.me/submissions/310111fe-ec1a-4a1e-b5f4-3a8c86e174e3

import Definitions.Def_uhlenbeck_gauge_box_defs
import Theorems.Thm_UhlenbeckGauge_norm_add_hodgeStar_sq
import Theorems.Thm_UhlenbeckGauge_integral_trWedge_eq_boundaryChernSimons
import Theorems.Thm_UhlenbeckGauge_curvature_isAntisymm_isSuNValued

open UhlenbeckGauge Matrix MeasureTheory
open scoped ContDiff ComplexOrder
set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

private lemma trace_norm_cast' {n : ℕ} (A : Mat n) :
    ((trace (A * Aᴴ)).re : ℂ) = trace (A * Aᴴ) := by
  have h : star (trace (A * Aᴴ)) = trace (A * Aᴴ) := by
    rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

private lemma re_trace_nonneg {n : ℕ} (X : Mat n) : 0 ≤ (trace (X * Xᴴ)).re := by
  have h := (posSemidef_self_mul_conjTranspose X).trace_nonneg
  exact (Complex.nonneg_iff.mp h).1

private lemma eq_zero_of_re_trace {n : ℕ} (X : Mat n) (h : (trace (X * Xᴴ)).re = 0) :
    X = 0 := by
  rw [← trace_mul_conjTranspose_self_eq_zero_iff, ← trace_norm_cast' X, h]
  simp

private lemma normSq_nonneg' {n : ℕ} (G : TwoForm n) : 0 ≤ normSq G := by
  unfold normSq
  refine Finset.sum_nonneg (fun μ _ => Finset.sum_nonneg (fun ν _ => ?_))
  split_ifs
  · exact re_trace_nonneg _
  · exact le_refl _

private lemma eq_zero_of_normSq {n : ℕ} (G : TwoForm n) (h : normSq G = 0) (μ ν : Fin 4)
    (hlt : μ < ν) : G μ ν = 0 := by
  unfold normSq at h
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun μ _ => Finset.sum_nonneg (fun ν _ => by
    split_ifs
    · exact re_trace_nonneg (G μ ν)
    · exact le_refl (0:ℝ)))).mp h μ (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun ν _ => by
    split_ifs
    · exact re_trace_nonneg (G μ ν)
    · exact le_refl (0:ℝ))).mp h1 ν (Finset.mem_univ _)
  rw [if_pos hlt] at h2
  exact eq_zero_of_re_trace _ h2

private lemma eq_zero_of_antisymm_normSq {n : ℕ} (G : TwoForm n) (hG : IsAntisymm G)
    (h : normSq G = 0) : G = 0 := by
  funext μ ν
  rcases lt_trichotomy μ ν with hlt | heq | hgt
  · exact eq_zero_of_normSq G h μ ν hlt
  · subst heq
    have h1 := hG μ μ
    ext i j
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.neg_apply] at h2
    simp only [Pi.zero_apply, Matrix.zero_apply]
    linear_combination h2 / 2
  · rw [hG ν μ, eq_zero_of_normSq G h ν μ hgt, neg_zero]
    rfl

private lemma levi_swap01 (μ ν ρ σ : Fin 4) : levi ν μ ρ σ = -levi μ ν ρ σ := by
  unfold levi
  have : (Matrix.of fun i : Fin 4 => (Pi.single (![ν, μ, ρ, σ] i) (1 : ℤ) : Fin 4 → ℤ)) =
      (Matrix.of fun i : Fin 4 => (Pi.single (![μ, ν, ρ, σ] i) (1 : ℤ) : Fin 4 → ℤ)).submatrix
        (Equiv.swap 0 1) id := by
    ext i j
    fin_cases i <;> rfl
  rw [this, Matrix.det_permute, Equiv.Perm.sign_swap (by decide)]
  push_cast
  ring

private lemma hodge_antisymm {n : ℕ} (F : TwoForm n) : IsAntisymm (hodgeStar F) := by
  intro μ ν
  simp only [hodgeStar, levi_swap01 μ ν, mul_neg, neg_smul, Finset.sum_neg_distrib]

private lemma normSq_zero' {n : ℕ} : normSq (0 : TwoForm n) = 0 := by
  simp [normSq]

private lemma box_subset (a b : R4) (hab : ∀ μ, a μ < b μ) :
    Set.Icc a b ⊆ closure (interior (Set.Icc a b)) := by
  rw [← Set.pi_univ_Icc, interior_pi_set Set.finite_univ, closure_pi_set]
  apply Set.pi_mono
  intro i _
  rw [closure_interior_Icc (hab i).ne]

private lemma integral_eq_zero_iff_on_box (a b : R4) (hab : ∀ μ, a μ < b μ) (f : R4 → ℝ)
    (hf : Continuous f) (hnn : ∀ x, 0 ≤ f x) :
    ∫ x in Set.Icc a b, f x = 0 ↔ ∀ x ∈ Set.Icc a b, f x = 0 := by
  constructor
  · intro h
    have hae := (setIntegral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hnn)
      (hf.continuousOn.integrableOn_compact isCompact_Icc)).mp h
    have := Measure.eqOn_of_ae_eq hae hf.continuousOn continuousOn_const (box_subset a b hab)
    intro x hx
    exact this hx
  · intro h
    rw [setIntegral_congr_fun measurableSet_Icc h]
    simp

private lemma cont_curv {n : ℕ} (A : Connection n) (hA : IsSUConnection A) (μ ν : Fin 4) :
    Continuous (fun x => curvature A x μ ν) := by
  have hpd : ∀ ρ σ, Continuous (fun x => partialDeriv ρ (fun y => A y σ) x) := by
    intro ρ σ
    apply continuous_matrix
    intro i j
    exact (((hA.1 σ i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hAc : ∀ ρ, Continuous (fun x => A x ρ) := by
    intro ρ
    apply continuous_matrix
    intro i j
    exact (hA.1 ρ i j).continuous
  unfold curvature
  exact ((hpd μ ν).sub (hpd ν μ)).add
    (((hAc μ).matrix_mul (hAc ν)).sub ((hAc ν).matrix_mul (hAc μ)))

private lemma cont_normSq {n : ℕ} (A : Connection n) (hA : IsSUConnection A) :
    Continuous (fun x => normSq (curvature A x)) := by
  unfold normSq
  refine continuous_finsetSum _ (fun μ _ => continuous_finsetSum _ (fun ν _ => ?_))
  split_ifs
  · exact Complex.continuous_re.comp
      ((cont_curv A hA μ ν).matrix_mul (cont_curv A hA μ ν).matrix_conjTranspose).matrix_trace
  · exact continuous_const

private lemma cont_trWedge {n : ℕ} (A : Connection n) (hA : IsSUConnection A) :
    Continuous (fun x => trWedge (curvature A x)) := by
  unfold trWedge
  exact continuous_const.mul (continuous_finsetSum _ (fun μ _ => continuous_finsetSum _
    (fun ν _ => continuous_finsetSum _ (fun ρ _ => continuous_finsetSum _ (fun σ _ =>
      continuous_const.mul ((cont_curv A hA μ ν).matrix_mul (cont_curv A hA ρ σ)).matrix_trace)))))

private lemma re_identities {n : ℕ} (F : TwoForm n) (hF : IsAntisymm F) (hsu : IsSuNValued F) :
    normSq (F + hodgeStar F) = 2 * normSq F - 2 * (trWedge F).re ∧
    normSq (F - hodgeStar F) = 2 * normSq F + 2 * (trWedge F).re := by
  obtain ⟨h1, h2⟩ := norm_add_hodgeStar_sq F hF hsu
  constructor
  · have := congrArg Complex.re h1
    simpa using this
  · have := congrArg Complex.re h2
    simpa using this

end

theorem solution {n : ℕ} (a b : R4) (hab : ∀ μ, a μ < b μ)
    (A : Connection n) (hA : IsSUConnection A) :
    (yangMills a b A = -(boundaryChernSimons a b A).re ↔
        ∀ x ∈ Set.Icc a b, IsSelfDual (curvature A x)) ∧
      (yangMills a b A = (boundaryChernSimons a b A).re ↔
        ∀ x ∈ Set.Icc a b, IsAntiSelfDual (curvature A x)) := by
  have hab' : a ≤ b := fun μ => (hab μ).le
  have hN := cont_normSq A hA
  have hT := cont_trWedge A hA
  have hTre : Continuous (fun x => (trWedge (curvature A x)).re) :=
    Complex.continuous_re.comp hT
  have hCS : (boundaryChernSimons a b A).re =
      ∫ x in Set.Icc a b, (trWedge (curvature A x)).re := by
    rw [← integral_trWedge_eq_boundaryChernSimons a b hab' A hA]
    exact (integral_re (hT.continuousOn.integrableOn_compact isCompact_Icc)).symm
  have hm : yangMills a b A + (boundaryChernSimons a b A).re =
      ∫ x in Set.Icc a b, (normSq (curvature A x) + (trWedge (curvature A x)).re) := by
    rw [hCS, yangMills, integral_add (hN.continuousOn.integrableOn_compact isCompact_Icc)
      (hTre.continuousOn.integrableOn_compact isCompact_Icc)]
  have hp : yangMills a b A - (boundaryChernSimons a b A).re =
      ∫ x in Set.Icc a b, (normSq (curvature A x) - (trWedge (curvature A x)).re) := by
    rw [hCS, yangMills, integral_sub (hN.continuousOn.integrableOn_compact isCompact_Icc)
      (hTre.continuousOn.integrableOn_compact isCompact_Icc)]
  have key := fun x => re_identities (curvature A x)
    (curvature_isAntisymm_isSuNValued A hA x).1 (curvature_isAntisymm_isSuNValued A hA x).2
  have hFa := fun x => (curvature_isAntisymm_isSuNValued A hA x).1
  constructor
  · have e1 : yangMills a b A = -(boundaryChernSimons a b A).re ↔
        yangMills a b A + (boundaryChernSimons a b A).re = 0 :=
      ⟨fun h => by linarith, fun h => by linarith⟩
    rw [e1, hm, integral_eq_zero_iff_on_box a b hab
      (fun x => normSq (curvature A x) + (trWedge (curvature A x)).re) (hN.add hTre) (fun x => by
      nlinarith [(key x).2, normSq_nonneg' (curvature A x - hodgeStar (curvature A x))])]
    apply forall₂_congr
    intro x _
    constructor
    · intro h
      have h0 : normSq (curvature A x - hodgeStar (curvature A x)) = 0 := by
        linarith [(key x).2]
      have hG : IsAntisymm (curvature A x - hodgeStar (curvature A x)) := by
        intro μ ν
        simp only [Pi.sub_apply, hFa x μ ν, hodge_antisymm (curvature A x) μ ν]
        abel
      have := eq_zero_of_antisymm_normSq _ hG h0
      exact (sub_eq_zero.mp this).symm
    · intro h
      have h2 := (key x).2
      rw [show hodgeStar (curvature A x) = curvature A x from h, sub_self, normSq_zero'] at h2
      linarith
  · have e1 : yangMills a b A = (boundaryChernSimons a b A).re ↔
        yangMills a b A - (boundaryChernSimons a b A).re = 0 :=
      ⟨fun h => by linarith, fun h => by linarith⟩
    rw [e1, hp, integral_eq_zero_iff_on_box a b hab
      (fun x => normSq (curvature A x) - (trWedge (curvature A x)).re) (hN.sub hTre) (fun x => by
      nlinarith [(key x).1, normSq_nonneg' (curvature A x + hodgeStar (curvature A x))])]
    apply forall₂_congr
    intro x _
    constructor
    · intro h
      have h0 : normSq (curvature A x + hodgeStar (curvature A x)) = 0 := by
        linarith [(key x).1]
      have hG : IsAntisymm (curvature A x + hodgeStar (curvature A x)) := by
        intro μ ν
        simp only [Pi.add_apply, hFa x μ ν, hodge_antisymm (curvature A x) μ ν]
        abel
      have := eq_zero_of_antisymm_normSq _ hG h0
      exact (eq_neg_of_add_eq_zero_right this)
    · intro h
      have h2 := (key x).1
      rw [show hodgeStar (curvature A x) = -curvature A x from h, add_neg_cancel,
        normSq_zero'] at h2
      linarith
