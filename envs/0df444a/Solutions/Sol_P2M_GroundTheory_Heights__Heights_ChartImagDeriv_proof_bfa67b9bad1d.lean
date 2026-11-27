-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartImagDeriv_proof_bfa67b9bad1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:54:08.986837+00:00
-- url     : https://prove2.me/submissions/1521a5e6-4d7f-4742-9f84-8c27b681dd75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartImagDeriv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCChartImagDeriv_Y_apply_6a483f1f4a19
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_one_le_radius_6e45f36c6393


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
open MCChartImagDeriv
namespace GroundTheory.Heights₂.Heights
namespace ChartImagDeriv
theorem _root_.solution (h₁ : AnalyticDerivBound.Statement) (h₂ : CuspTimeDeriv.Statement) :
    ChartImagDeriv.Statement := by
  intro D
  have hKc : IsCompact (Prod.fst '' D.K) := D.isCompact_K.image continuous_fst
  have hKs : Prod.fst '' D.K ⊆ D.U := by
    rintro _ ⟨p, hp, rfl⟩
    exact (D.K_subset hp).1
  have hA := fun j l => h₁ (fun z => D.τ0 z j l) D.U (Prod.fst '' D.K) D.isOpen_U
    (D.τ0_analytic j l) hKc hKs
  choose A hApos hA using hA
  set A₁ : ℝ := ∑ j, ∑ l, A j l with hA₁def
  set S : ℝ := ∑ i, ∑ j, ∑ l, |D.B i j l| with hSdef
  have hA_le : ∀ j l, A j l ≤ A₁ := by
    intro j l
    calc A j l ≤ ∑ l', A j l' :=
          Finset.single_le_sum (fun l' _ => (hApos j l').le) (Finset.mem_univ l)
      _ ≤ A₁ := Finset.single_le_sum (f := fun j' => ∑ l', A j' l')
          (fun j' _ => Finset.sum_nonneg fun l' _ => (hApos j' l').le) (Finset.mem_univ j)
  have hB_le : ∀ j l, ∑ i, |D.B i j l| ≤ S := by
    intro j l
    refine Finset.sum_le_sum fun i _ => ?_
    calc |D.B i j l| ≤ ∑ l', |D.B i j l'| :=
          Finset.single_le_sum (fun l' _ => abs_nonneg (D.B i j l')) (Finset.mem_univ l)
      _ ≤ ∑ j', ∑ l', |D.B i j' l'| := Finset.single_le_sum (f := fun j' => ∑ l', |D.B i j' l'|)
          (fun j' _ => Finset.sum_nonneg fun l' _ => abs_nonneg _) (Finset.mem_univ j)
  have hA₁ : 0 ≤ A₁ := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => (hApos j l).le
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun l _ => abs_nonneg _
  refine ⟨A₁ + S + 1, by linarith, ?_⟩
  intro p hp hpU j l
  have hx : p.1 ∈ Prod.fst '' D.K := ⟨p, hp, rfl⟩
  obtain ⟨hd, -, hb⟩ := hA j l p.1 hx

  set L₁ := (Complex.imCLM.comp (fderiv ℝ (fun z => D.τ0 z j l) p.1)).comp
    (ContinuousLinearMap.fst ℝ (Fin D.n → ℂ) (Fin D.m → ℂ)) with hL₁
  have h1 : HasFDerivAt (fun q : (Fin D.n → ℂ) × (Fin D.m → ℂ) => (D.τ0 q.1 j l).im) L₁ p :=
    Complex.imCLM.hasFDerivAt.comp p (hd.hasFDerivAt.comp p hasFDerivAt_fst)

  have hT := fun i => h₂ D p.1 hpU i
  set L₂ := fun i => (fderiv ℝ (fun w => cuspTime D.a_le w i) p.1).comp
    (ContinuousLinearMap.fst ℝ (Fin D.n → ℂ) (Fin D.m → ℂ)) with hL₂
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin D.a)), HasFDerivAt
      (fun q : (Fin D.n → ℂ) × (Fin D.m → ℂ) => cuspTime D.a_le q.1 i * D.B i j l)
      (D.B i j l • L₂ i) p :=
    fun i _ => ((hT i).1.hasFDerivAt.comp p hasFDerivAt_fst).mul_const (D.B i j l)
  have hfun : (fun q : (Fin D.n → ℂ) × (Fin D.m → ℂ) => D.Y q.1 j l) =
      fun q => (D.τ0 q.1 j l).im + ∑ i, cuspTime D.a_le q.1 i * D.B i j l := by
    funext q
    exact Y_apply D q.1 j l
  have hall : HasFDerivAt
      (fun q : (Fin D.n → ℂ) × (Fin D.m → ℂ) =>
        (D.τ0 q.1 j l).im + ∑ i, cuspTime D.a_le q.1 i * D.B i j l)
      (L₁ + ∑ i, D.B i j l • L₂ i) p :=
    h1.add (HasFDerivAt.fun_sum h2)
  rw [hfun]
  refine ⟨hall.differentiableAt, ?_⟩
  rw [hall.fderiv]
  have hfst : ‖ContinuousLinearMap.fst ℝ (Fin D.n → ℂ) (Fin D.m → ℂ)‖ ≤ 1 :=
    ContinuousLinearMap.norm_fst_le _ _ _
  have hE1 : 1 ≤ Real.exp (D.radius p.1 / 2) :=
    Real.one_le_exp (by linarith [MCBounds.one_le_radius D hpU.1])
  have hn1 : ‖L₁‖ ≤ A₁ := by
    calc ‖L₁‖ ≤ ‖Complex.imCLM.comp (fderiv ℝ (fun z => D.τ0 z j l) p.1)‖ *
          ‖ContinuousLinearMap.fst ℝ (Fin D.n → ℂ) (Fin D.m → ℂ)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖Complex.imCLM.comp (fderiv ℝ (fun z => D.τ0 z j l) p.1)‖ * 1 :=
          mul_le_mul_of_nonneg_left hfst (norm_nonneg _)
      _ ≤ ‖(Complex.imCLM : ℂ →L[ℝ] ℝ)‖ * ‖fderiv ℝ (fun z => D.τ0 z j l) p.1‖ := by
          rw [mul_one]; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ A₁ := by rw [Complex.imCLM_norm, one_mul]; exact hb.trans (hA_le j l)
  have hn2 : ∀ i, ‖D.B i j l • L₂ i‖ ≤ |D.B i j l| * Real.exp (D.radius p.1 / 2) := by
    intro i
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc ‖L₂ i‖ ≤ ‖fderiv ℝ (fun w => cuspTime D.a_le w i) p.1‖ *
          ‖ContinuousLinearMap.fst ℝ (Fin D.n → ℂ) (Fin D.m → ℂ)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ Real.exp (D.radius p.1 / 2) * 1 :=
          mul_le_mul (hT i).2 hfst (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (D.radius p.1 / 2) := mul_one _
  have hsum : ‖∑ i, D.B i j l • L₂ i‖ ≤ S * Real.exp (D.radius p.1 / 2) := by
    calc ‖∑ i, D.B i j l • L₂ i‖ ≤ ∑ i, ‖D.B i j l • L₂ i‖ := norm_sum_le _ _
      _ ≤ ∑ i, |D.B i j l| * Real.exp (D.radius p.1 / 2) := Finset.sum_le_sum fun i _ => hn2 i
      _ = (∑ i, |D.B i j l|) * Real.exp (D.radius p.1 / 2) := (Finset.sum_mul _ _ _).symm
      _ ≤ S * Real.exp (D.radius p.1 / 2) :=
          mul_le_mul_of_nonneg_right (hB_le j l) (Real.exp_pos _).le
  calc ‖L₁ + ∑ i, D.B i j l • L₂ i‖ ≤ ‖L₁‖ + ‖∑ i, D.B i j l • L₂ i‖ := norm_add_le _ _
    _ ≤ A₁ * Real.exp (D.radius p.1 / 2) + S * Real.exp (D.radius p.1 / 2) := by
        gcongr
        calc ‖L₁‖ ≤ A₁ := hn1
          _ = A₁ * 1 := (mul_one _).symm
          _ ≤ A₁ * Real.exp (D.radius p.1 / 2) := mul_le_mul_of_nonneg_left hE1 hA₁
    _ ≤ (A₁ + S + 1) * Real.exp (D.radius p.1 / 2) := by nlinarith [Real.exp_pos (D.radius p.1 / 2)]
end ChartImagDeriv
end GroundTheory.Heights₂.Heights
