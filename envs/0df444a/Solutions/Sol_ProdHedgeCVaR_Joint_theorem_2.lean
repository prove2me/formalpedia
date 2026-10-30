-- Prove2me | solution 1 for ProdHedgeCVaR.Joint.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T09:25:07.02837+00:00
-- url     : https://prove2.me/submissions/eb7fdda0-59e4-492e-a25c-4c8bbabf60ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_ProdHedgeCVaR_Joint_Model
import Theorems.Thm_ProdHedgeCVaR_Joint_theorem_1
import Theorems.Thm_ProdHedgeCVaR_Joint_eq_45_unique
import Theorems.Thm_ProdHedgeCVaR_Joint_eq_49
import Theorems.Thm_ProdHedgeCVaR_Joint_eq_47
import Theorems.Thm_ProdHedgeCVaR_Joint_eq_50
import Theorems.Thm_ProdHedgeCVaR_Joint_eq_53_system
import Theorems.Thm_ProdHedgeCVaR_Joint_theorem_2_optimum_slack
import Theorems.Thm_ProdHedgeCVaR_Joint_theorem_2_optimum_binding

open MeasureTheory ProbabilityTheory Filter Topology BlackScholesModel ProdHedgeCVaR.Joint

namespace P2MSolProdHedgeThm2

lemma Z_pos {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (ω : Ω) : 0 < M.Z ω :=
  Real.exp_pos _

lemma Z_meas {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid) : Measurable M.Z := by
  have hW : Measurable M.W := hM.W_meas.mono hM.G_le le_rfl
  unfold Model.Z
  fun_prop

lemma stdNormalCDF_mono' : Monotone stdNormalCDF := by
  intro x y hxy
  unfold stdNormalCDF
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hint : Integrable (fun z : ℝ => Real.exp (-z ^ 2 / 2)) := by
    have := integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only
    ring_nf
  apply setIntegral_mono_set hint.integrableOn
  · exact Eventually.of_forall fun z => (Real.exp_pos _).le
  · exact (Set.Iic_subset_Iic.mpr hxy).eventuallyLE

lemma stdNormalCDF_nonneg' (x : ℝ) : 0 ≤ stdNormalCDF x := by
  unfold stdNormalCDF
  exact mul_nonneg (by positivity)
    (setIntegral_nonneg measurableSet_Iic fun z _ => (Real.exp_pos _).le)

lemma Delta_meas {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid) (Q : ℝ) :
    Measurable (M.Delta Q) := by
  have hA : Measurable M.A := hM.A_meas.mono hM.G_le le_rfl
  unfold Model.Delta
  exact stdNormalCDF_mono'.measurable.comp ((measurable_const.sub hA).div_const _)

lemma G_int {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (hZ : Integrable M.Z M.P) (lam Q : ℝ) (hlam : 0 ≤ lam) :
    Integrable (fun ω => min (lam * M.Z ω) (M.Delta Q ω)) M.P := by
  refine (hZ.const_mul lam).mono' ?_ ?_
  · exact ((measurable_const.mul (Z_meas M hM)).min (Delta_meas M hM Q)).aestronglyMeasurable
  · refine Eventually.of_forall fun ω => ?_
    have h1 : 0 ≤ M.Delta Q ω := stdNormalCDF_nonneg' _
    have h2 : 0 ≤ lam * M.Z ω := mul_nonneg hlam (Z_pos M ω).le
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min h2 h1)]
    exact min_le_left _ _

lemma Z_int {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (lamC : ℝ) (h : M.IsLamC α lamC) :
    Integrable M.Z M.P ∧ 0 < lamC := by
  obtain ⟨_, hnn, ⟨hb0, _, _⟩, -⟩ := eq_45_unique M hM α hα0 hα1
  have hl0 : 0 ≤ lamC := hnn lamC h
  have hne : lamC ≠ 0 := by
    rintro rfl
    unfold Model.IsLamC at h
    linarith
  obtain ⟨-, -, -, h4⟩ := eq_49 M hM α hα0 hα1 lamC h
  have hI : ∫ ω, M.Z ω ∂M.P = 1 := mul_left_cancel₀ hne (h4.trans (mul_one _).symm)
  refine ⟨?_, lt_of_le_of_ne hl0 (Ne.symm hne)⟩
  by_contra hni
  rw [integral_undef hni] at hI
  norm_num at hI

lemma PM_pos {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (lamC : ℝ) (h : M.IsLamC α lamC) :
    0 < M.PM {ω | lamC * M.Z ω ≤ 1} := by
  obtain ⟨hZ, -⟩ := Z_int M hM α hα0 hα1 lamC h
  have hS : MeasurableSet {ω | lamC * M.Z ω ≤ 1} :=
    measurableSet_le (measurable_const.mul (Z_meas M hM)) measurable_const
  have hnn : 0 ≤ M.PM {ω | lamC * M.Z ω ≤ 1} :=
    setIntegral_nonneg hS fun ω _ => (Z_pos M ω).le
  refine lt_of_le_of_ne hnn fun h0 => ?_
  have h1 := (setIntegral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun ω => (Z_pos M ω).le) hZ.integrableOn).mp h0.symm
  have h2 : ∀ᵐ ω ∂M.P.restrict {ω | lamC * M.Z ω ≤ 1}, False :=
    h1.mono fun ω hω => (Z_pos M ω).ne' hω
  have h3 : M.P.restrict {ω | lamC * M.Z ω ≤ 1} = 0 :=
    ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp h2)
  have h4 : M.P {ω | lamC * M.Z ω ≤ 1} = 0 := Measure.restrict_eq_zero.mp h3
  have h5 : ∀ᵐ ω ∂M.P, ω ∉ {ω | lamC * M.Z ω ≤ 1} := measure_eq_zero_iff_ae_notMem.mp h4
  have h6 : M.beta lamC = 0 := by
    unfold Model.beta
    refine integral_eq_zero_of_ae (h5.mono fun ω hω => ?_)
    simp only [Set.mem_setOf_eq, not_le] at hω
    simp only [Pi.zero_apply]
    exact max_eq_right (by linarith)
  unfold Model.IsLamC at h
  linarith

end P2MSolProdHedgeThm2

open P2MSolProdHedgeThm2 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (∃! lam, M.IsLamC α lam) ∧ (∀ lam, M.IsLamC α lam → ∃! Q, M.IsQC α lam Q) ∧
    ∀ lamC QC, M.IsLamC α lamC → M.IsQC α lamC QC →
      (M.CC lamC QC ≤ M.θ.C →
        {x | M.IsOptimal36 α x} = {(M.mC lamC QC, max QC 0)} ∧
        M.Eq35 (M.mC lamC QC) (max QC 0) lamC ∧
        (M.CC lamC QC < M.θ.C → ∀ lam, M.Eq35 (M.mC lamC QC) (max QC 0) lam ↔ lam = lamC)) ∧
      (M.θ.C ≤ M.CC lamC QC →
        (∃! y : ℝ × ℝ, 0 ≤ y.1 ∧ M.Eq53 y.1 y.2 ∧ M.IsQC α y.1 y.2) ∧
        ∀ lamS QS, 0 ≤ lamS → M.Eq53 lamS QS → M.IsQC α lamS QS →
          {x | M.IsOptimal36 α x} = {(M.θ.p * QS - M.θ.C, QS)} ∧
          M.Eq35 (M.θ.p * QS - M.θ.C) QS lamS ∧
          lamC ≤ lamS ∧ QS ≤ QC) ∧
      (∀ x, M.IsOptimal36 α x → min M.θ.C (M.CC lamC QC) / M.θ.p ≤ x.2) := by
  obtain ⟨hlamU, hlamNN, -, -, hQ⟩ := eq_45_unique M hM α hα0 hα1
  refine ⟨hlamU, fun lam h => (hQ lam h).1, ?_⟩
  intro lamC QC hlamC hQC
  have hp := hM.params.p_pos
  have hc := hM.params.c_pos
  obtain ⟨h50a, -, h50c⟩ := eq_50 M hM α hα0 hα1 lamC QC hlamC hQC
  have hEq35C : M.Eq35 (M.mC lamC QC) (max QC 0) lamC := (h50a _).mpr rfl
  have hl0 := hlamNN lamC hlamC
  obtain ⟨h47a, -⟩ := eq_47 M hM α hα0 hα1 lamC QC hlamC hQC
  obtain ⟨hZ, -⟩ := Z_int M hM α hα0 hα1 lamC hlamC
  refine ⟨?_, ?_, ?_⟩
  · intro hC
    refine ⟨theorem_2_optimum_slack M hM α hα0 hα1 lamC QC hlamC hQC hC, hEq35C, ?_⟩
    intro hClt lam
    obtain ⟨hm0, hcons⟩ := h50c hC
    have hpos : 0 < M.mC lamC QC - M.θ.p * max QC 0 + M.θ.C := by
      have hPM := PM_pos M hM α hα0 hα1 lamC hlamC
      have : M.mC lamC QC - M.θ.p * max QC 0 + M.θ.C
          = (M.θ.C - M.CC lamC QC) / M.PM {ω | lamC * M.Z ω ≤ 1} := by
        unfold Model.mC; ring
      rw [this]
      exact div_pos (by linarith) hPM
    obtain ⟨-, huniq, -⟩ := theorem_1 M hM _ _ hm0 (le_max_right _ _) hcons
    obtain ⟨l0, -, hl0u⟩ := huniq hpos
    constructor
    · intro h
      exact (hl0u _ h).trans (hl0u _ hEq35C).symm
    · rintro rfl
      exact hEq35C
  · intro hC
    obtain ⟨hsys, -, hmonoQ, hantiL⟩ := eq_53_system M hM α hα0 hα1 lamC QC hlamC hQC hC
    refine ⟨hsys, ?_⟩
    intro lamS QS hlS h53 hQS
    refine ⟨theorem_2_optimum_binding M hM α hα0 hα1 lamC QC hlamC hQC hC lamS QS hlS h53 hQS,
      ?_, ?_⟩
    · refine ⟨hlS, ?_⟩
      have hK : M.K (M.θ.p * QS - M.θ.C) QS - QS = 0 := by
        unfold Model.K
        field_simp
        ring
      rw [hK, zero_mul, zero_add]
      exact h53
    · have hStrict := (hQ lamC hlamC).2.1
      have hGmono : ∀ Q l1 l2 : ℝ, 0 ≤ l1 → l1 ≤ l2 →
          (M.θ.p + M.θ.c) * ∫ ω, min (l1 * M.Z ω) (M.Delta Q ω) ∂M.P
            ≤ (M.θ.p + M.θ.c) * ∫ ω, min (l2 * M.Z ω) (M.Delta Q ω) ∂M.P := by
        intro Q l1 l2 h1 h12
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact integral_mono (G_int M hM hZ l1 Q h1) (G_int M hM hZ l2 Q (h1.trans h12))
          fun ω => min_le_min_right _ (mul_le_mul_of_nonneg_right h12 (Z_pos M ω).le)
      unfold Model.IsQC at hQS hQC
      have hle : lamC ≤ lamS := by
        by_contra hlt
        push_neg at hlt
        have h1 : (M.θ.p + M.θ.c) * ∫ ω, min (lamC * M.Z ω) (M.Delta QC ω) ∂M.P
            ≤ (M.θ.p + M.θ.c) * ∫ ω, min (lamC * M.Z ω) (M.Delta QS ω) ∂M.P := by
          rw [hQC, ← hQS]
          exact hGmono QS lamS lamC hlS hlt.le
        have hQle : QC ≤ QS := hStrict.le_iff_le.mp h1
        have hF : M.CC lamC QC ≤ M.θ.C := by
          rw [← h53]
          exact (hmonoQ lamC hl0 hQle).trans
            (hantiL QS (Set.mem_Ici.mpr hlS) (Set.mem_Ici.mpr hl0) hlt.le)
        have hEq : M.CC lamC QC = M.θ.C := le_antisymm hF hC
        have hsolC : 0 ≤ (lamC, QC).1 ∧ M.Eq53 (lamC, QC).1 (lamC, QC).2 ∧
            M.IsQC α (lamC, QC).1 (lamC, QC).2 := ⟨hl0, hEq, hQC⟩
        have hsolS : 0 ≤ (lamS, QS).1 ∧ M.Eq53 (lamS, QS).1 (lamS, QS).2 ∧
            M.IsQC α (lamS, QS).1 (lamS, QS).2 := ⟨hlS, h53, hQS⟩
        have := hsys.unique hsolC hsolS
        simp only [Prod.mk.injEq] at this
        linarith [this.1]
      refine ⟨hle, ?_⟩
      have h1 : (M.θ.p + M.θ.c) * ∫ ω, min (lamC * M.Z ω) (M.Delta QS ω) ∂M.P
          ≤ (M.θ.p + M.θ.c) * ∫ ω, min (lamC * M.Z ω) (M.Delta QC ω) ∂M.P := by
        rw [hQC, ← hQS]
        exact hGmono QS lamC lamS hl0 hle
      exact hStrict.le_iff_le.mp h1
  · intro x hx
    have hx' : x ∈ {x | M.IsOptimal36 α x} := hx
    rcases le_total (M.CC lamC QC) M.θ.C with hC | hC
    · rw [theorem_2_optimum_slack M hM α hα0 hα1 lamC QC hlamC hQC hC] at hx'
      rw [Set.mem_singleton_iff.mp hx', min_eq_right hC, div_le_iff₀ hp]
      linarith
    · obtain ⟨hsys, hsysB, -, -⟩ := eq_53_system M hM α hα0 hα1 lamC QC hlamC hQC hC
      obtain ⟨⟨lamS, QS⟩, ⟨hlS, h53, hQS⟩, -⟩ := hsys
      have hB := (hsysB (lamS, QS) hlS h53 hQS).1
      rw [theorem_2_optimum_binding M hM α hα0 hα1 lamC QC hlamC hQC hC lamS QS hlS h53 hQS]
        at hx'
      rw [Set.mem_singleton_iff.mp hx', min_eq_left hC, div_le_iff₀ hp]
      simp only at hB ⊢
      linarith
