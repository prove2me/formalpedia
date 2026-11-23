-- Prove2me | solution 1 for WeldedPath.Supplement.theorem_4_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:31:50.626805+00:00
-- url     : https://prove2.me/submissions/37238140-fefa-4078-8b0a-24006b5251f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeldedPath_Supplement_projGood
import Theorems.Thm_WeldedPath_Supplement_ordinary_factor_bounds
import Theorems.Thm_WeldedPath_Supplement_inverse_label_goodness_eta
import Theorems.Thm_WeldedPath_Supplement_edge_goodness_eta
import Theorems.Thm_WeldedPath_Supplement_exact_phase_goodness

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace WeldedPath.Supplement

private theorem etaStep_mono {n l s t : ℕ} (h : s ≤ t) : etaStep n l s ≤ etaStep n l t := by
  apply Real.sqrt_le_sqrt
  gcongr

private theorem etaStep_add_five_le (n l t : ℕ) :
    etaStep n l (t + 5) ≤ Real.sqrt 6 * etaStep n l t := by
  rw [etaStep, etaStep, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]
  apply Real.sqrt_le_sqrt
  have hdecomp :
      6 * (1 / (2 : ℝ) ^ l + (n : ℝ) * ((t : ℝ) + 1) / (2 : ℝ) ^ n) -
        (1 / (2 : ℝ) ^ l + (n : ℝ) * (((t + 5 : ℕ) : ℝ) + 1) / (2 : ℝ) ^ n) =
      5 / (2 : ℝ) ^ l + 5 * (n : ℝ) * (t : ℝ) / (2 : ℝ) ^ n := by
    push_cast
    ring
  have hnonneg : 0 ≤ 5 / (2 : ℝ) ^ l + 5 * (n : ℝ) * (t : ℝ) / (2 : ℝ) ^ n := by positivity
  linarith

private theorem final_eta_bound (Ci Ce eta : ℝ) (hCi : 0 < Ci) (hCe : 0 < Ce)
    (heta : 0 ≤ eta) :
    Ci * eta + Ce * (Real.sqrt 6 * eta) + Ce * (Real.sqrt 6 * eta) +
      Ci * (Real.sqrt 6 * eta) ≤
        (128 + 2 * Real.sqrt 6 * (Ce + Ci)) * eta := by
  have hsix : (1 : ℝ) ≤ Real.sqrt 6 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hextra : 0 ≤ (Real.sqrt 6 - 1) * Ci * eta :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hsix) hCi.le) heta
  nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 128) heta]

private theorem constant_large (Ci Ce : ℝ) (hCi : 0 < Ci) (hCe : 0 < Ce) :
    128 ≤ 128 + 2 * Real.sqrt 6 * (Ce + Ci) := by
  nlinarith [Real.sqrt_nonneg (6 : ℝ)]

private theorem one_le_of_eta {K eta : ℝ} (hK : 128 ≤ K) (heta : 1 / 128 ≤ eta) :
    1 ≤ K * eta := by
  have hK0 : 0 ≤ K := by norm_num at hK ⊢; linarith
  calc
    1 = 128 * (1 / 128 : ℝ) := by norm_num
    _ ≤ K * (1 / 128) := mul_le_mul_of_nonneg_right hK (by norm_num)
    _ ≤ K * eta := mul_le_mul_of_nonneg_left heta hK0

private theorem leakage_two {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P₀ P₁ P₂ A B : E →L[ℂ] E) (a b : ℝ)
    (hP₀ : ‖P₀‖ ≤ 1) (_hP₀c : ‖1 - P₀‖ ≤ 1)
    (hP₁c : ‖1 - P₁‖ ≤ 1) (hP₂c : ‖1 - P₂‖ ≤ 1)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hAe : ‖(1 - P₁).comp (A.comp P₀)‖ ≤ a)
    (hBe : ‖(1 - P₂).comp (B.comp P₁)‖ ≤ b) :
    ‖(1 - P₂).comp ((B.comp A).comp P₀)‖ ≤ a + b := by
  have hsplit : (1 - P₂).comp ((B.comp A).comp P₀) =
      ((1 - P₂).comp (B.comp P₁)).comp (A.comp P₀) +
        (1 - P₂).comp (B.comp ((1 - P₁).comp (A.comp P₀))) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_sub]
    abel
  have hsecond : ‖(1 - P₂).comp (B.comp ((1 - P₁).comp (A.comp P₀)))‖ ≤
      ‖1 - P₂‖ * ‖B‖ * ‖(1 - P₁).comp (A.comp P₀)‖ := by
    calc
      _ ≤ ‖1 - P₂‖ * ‖B.comp ((1 - P₁).comp (A.comp P₀))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖1 - P₂‖ * (‖B‖ * ‖(1 - P₁).comp (A.comp P₀)‖) := by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ = _ := by rw [mul_assoc]
  have hAP : ‖A.comp P₀‖ ≤ 1 := by
    calc
      ‖A.comp P₀‖ ≤ ‖A‖ * ‖P₀‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hA hP₀ (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hb0 : 0 ≤ b := le_trans (norm_nonneg _) hBe
  have ha0 : 0 ≤ a := le_trans (norm_nonneg _) hAe
  rw [hsplit]
  calc
    _ ≤ ‖((1 - P₂).comp (B.comp P₁)).comp (A.comp P₀)‖ +
        ‖(1 - P₂).comp (B.comp ((1 - P₁).comp (A.comp P₀)))‖ := norm_add_le _ _
    _ ≤ (‖(1 - P₂).comp (B.comp P₁)‖ * ‖A.comp P₀‖) +
        (‖1 - P₂‖ * ‖B‖ * ‖(1 - P₁).comp (A.comp P₀)‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ b * 1 + 1 * 1 * a := by gcongr
    _ = a + b := by ring

private theorem one_comp_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {A B : E →L[ℂ] E} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) : ‖A.comp B‖ ≤ 1 := by
  calc
    ‖A.comp B‖ ≤ ‖A‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul hA hB (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

private theorem eta_small_of_even (n l t : ℕ) (hn : Even n) (hn16 : ¬ 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) : (1 : ℝ) / 128 ≤ etaStep n l t := by
  have hn14 : n ≤ 14 := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hlN : l ≤ n := hln.trans (Nat.sub_le n 4)
  have hpowle : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ 14 := pow_le_pow_right₀ (by norm_num) hn14
  have heps : (1 : ℝ) / (2 ^ 14) ≤ 1 / (2 : ℝ) ^ n :=
    one_div_le_one_div_of_le (by positivity) hpowle
  have harg : (1 : ℝ) / (2 ^ 14) ≤
      1 / (2 : ℝ) ^ l + (n : ℝ) * ((t : ℝ) + 1) / (2 : ℝ) ^ n := by
    have hsecond : 0 ≤ (n : ℝ) * ((t : ℝ) + 1) / (2 : ℝ) ^ n := by positivity
    have hle : 1 / (2 : ℝ) ^ n ≤ 1 / (2 : ℝ) ^ l := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) hlN
    linarith
  have hs : Real.sqrt ((1 : ℝ) / (2 ^ 14)) = 1 / 128 := by
    rw [show (1 : ℝ) / (2 ^ 14) = (1 / 128) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  change 1 / 128 ≤ Real.sqrt (1 / (2 : ℝ) ^ l + (n : ℝ) * ((t : ℝ) + 1) / (2 : ℝ) ^ n)
  rw [← hs]
  exact Real.sqrt_le_sqrt harg

end WeldedPath.Supplement

open WeldedPath WeldedPath.Supplement

theorem solution :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ q t : ℕ, t ≤ 6 * q →
      C₀ * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      C₀ * (((q : ℝ) + 1) / (2 : ℝ) ^ l + ((n : ℝ) + 1) * ((q : ℝ) + 1) ^ 3 / (2 : ℝ) ^ n) ≤
        1 / 2 →
      ‖(1 - projGood l G (t + 6)).comp ((cpWT l G).comp (projGood l G t))‖ ≤
        C * etaStep n l t := by
  refine ⟨2 ^ 40, by positivity, ?_⟩
  obtain ⟨Ci, hCi, hInv⟩ := inverse_label_goodness_eta
  obtain ⟨Ce, hCe, hEdge⟩ := edge_goodness_eta
  refine ⟨128 + 2 * Real.sqrt 6 * (Ce + Ci), by positivity, ?_⟩
  intro n l hn hl hln G hG q t ht hNl hBudget
  obtain ⟨hP, hFactors⟩ := ordinary_factor_bounds n l G
  rcases hFactors with ⟨hIn, hIa, hEn, hEa, hFn, hFa, hXn⟩
  by_cases hn16 : 16 ≤ n
  · have hI (r : ℕ) (hr : r ≤ 6 * q + 6) := hInv n l hn hn16 hl hln G hG q r hr hNl hBudget
    have hE (r : ℕ) (hr : r ≤ 6 * q + 6) := hEdge n l hn hn16 hl hln G hG q r hr hNl hBudget
    have hF := exact_phase_goodness n l hn hn16 hl hln G hG
    let A₁ := (ContinuousLinearMap.adjoint (pCedge l G)).comp
      (ContinuousLinearMap.adjoint (pCinvLab l G))
    let A₂ := (ContinuousLinearMap.adjoint (pCforLab l G)).comp A₁
    let A₃ := (xorP l G).comp A₂
    let A₄ := (pCforLab l G).comp A₃
    let A₅ := (pCedge l G).comp A₄
    have hA₁ : ‖A₁‖ ≤ 1 := one_comp_le_one hEa hIa
    have hA₂ : ‖A₂‖ ≤ 1 := one_comp_le_one hFa hA₁
    have hA₃ : ‖A₃‖ ≤ 1 := one_comp_le_one hXn hA₂
    have hA₄ : ‖A₄‖ ≤ 1 := one_comp_le_one hFn hA₃
    have hA₅ : ‖A₅‖ ≤ 1 := one_comp_le_one hEn hA₄
    have hs1 := leakage_two (projGood l G t) (projGood l G (t + 1))
      (projGood l G (t + 2)) (ContinuousLinearMap.adjoint (pCinvLab l G))
      (ContinuousLinearMap.adjoint (pCedge l G)) (Ci * etaStep n l t) (Ce * etaStep n l (t + 1))
      (hP t).1 (hP t).2 (hP (t + 1)).2 (hP (t + 2)).2 hIa hEa
      ((hI t (by omega)).1) ((hE (t + 1) (by omega)).1)
    have hs1' : ‖(1 - projGood l G (t + 2)).comp (A₁.comp (projGood l G t))‖ ≤
        Ci * etaStep n l t + Ce * etaStep n l (t + 1) := hs1
    have hfadj : ‖(1 - projGood l G (t + 3)).comp
        ((ContinuousLinearMap.adjoint (pCforLab l G)).comp (projGood l G (t + 2)))‖ ≤ 0 := by
      rw [(hF (t + 2)).1.1]
      norm_num
    have hs2 := leakage_two (projGood l G t) (projGood l G (t + 2))
      (projGood l G (t + 3)) A₁ (ContinuousLinearMap.adjoint (pCforLab l G))
      (Ci * etaStep n l t + Ce * etaStep n l (t + 1)) 0
      (hP t).1 (hP t).2 (hP (t + 2)).2 (hP (t + 3)).2 hA₁ hFa hs1' hfadj
    have hs2' : ‖(1 - projGood l G (t + 3)).comp (A₂.comp (projGood l G t))‖ ≤
        Ci * etaStep n l t + Ce * etaStep n l (t + 1) := by simpa using hs2
    have hfx : ‖(1 - projGood l G (t + 3)).comp
        ((xorP l G).comp (projGood l G (t + 3)))‖ ≤ 0 := by
      rw [(hF (t + 3)).2]
      norm_num
    have hs3 := leakage_two (projGood l G t) (projGood l G (t + 3))
      (projGood l G (t + 3)) A₂ (xorP l G)
      (Ci * etaStep n l t + Ce * etaStep n l (t + 1)) 0
      (hP t).1 (hP t).2 (hP (t + 3)).2 (hP (t + 3)).2 hA₂ hXn hs2' hfx
    have hs3' : ‖(1 - projGood l G (t + 3)).comp (A₃.comp (projGood l G t))‖ ≤
        Ci * etaStep n l t + Ce * etaStep n l (t + 1) := by simpa using hs3
    have hffor : ‖(1 - projGood l G (t + 4)).comp
        ((pCforLab l G).comp (projGood l G (t + 3)))‖ ≤ 0 := by
      rw [(hF (t + 3)).1.2]
      norm_num
    have hs4 := leakage_two (projGood l G t) (projGood l G (t + 3))
      (projGood l G (t + 4)) A₃ (pCforLab l G)
      (Ci * etaStep n l t + Ce * etaStep n l (t + 1)) 0
      (hP t).1 (hP t).2 (hP (t + 3)).2 (hP (t + 4)).2 hA₃ hFn hs3' hffor
    have hs4' : ‖(1 - projGood l G (t + 4)).comp (A₄.comp (projGood l G t))‖ ≤
        Ci * etaStep n l t + Ce * etaStep n l (t + 1) := by simpa using hs4
    have hs5 := leakage_two (projGood l G t) (projGood l G (t + 4))
      (projGood l G (t + 5)) A₄ (pCedge l G)
      (Ci * etaStep n l t + Ce * etaStep n l (t + 1)) (Ce * etaStep n l (t + 4))
      (hP t).1 (hP t).2 (hP (t + 4)).2 (hP (t + 5)).2 hA₄ hEn hs4'
      ((hE (t + 4) (by omega)).2)
    have hs5' : ‖(1 - projGood l G (t + 5)).comp (A₅.comp (projGood l G t))‖ ≤
        Ci * etaStep n l t + Ce * etaStep n l (t + 1) + Ce * etaStep n l (t + 4) := hs5
    have hs6 := leakage_two (projGood l G t) (projGood l G (t + 5))
      (projGood l G (t + 6)) A₅ (pCinvLab l G)
      (Ci * etaStep n l t + Ce * etaStep n l (t + 1) + Ce * etaStep n l (t + 4))
      (Ci * etaStep n l (t + 5))
      (hP t).1 (hP t).2 (hP (t + 5)).2 (hP (t + 6)).2 hA₅ hIn hs5'
      ((hI (t + 5) (by omega)).2)
    have hmain : ‖(1 - projGood l G (t + 6)).comp ((cpWT l G).comp (projGood l G t))‖ ≤
        Ci * etaStep n l t + Ce * etaStep n l (t + 1) + Ce * etaStep n l (t + 4) +
          Ci * etaStep n l (t + 5) := by
      simpa only [cpWT, A₁, A₂, A₃, A₄, A₅] using hs6
    have heta5 := etaStep_add_five_le n l t
    have heta1 : etaStep n l (t + 1) ≤ Real.sqrt 6 * etaStep n l t :=
      (etaStep_mono (show t + 1 ≤ t + 5 by omega)).trans heta5
    have heta4 : etaStep n l (t + 4) ≤ Real.sqrt 6 * etaStep n l t :=
      (etaStep_mono (show t + 4 ≤ t + 5 by omega)).trans heta5
    have hterm1 := mul_le_mul_of_nonneg_left heta1 hCe.le
    have hterm4 := mul_le_mul_of_nonneg_left heta4 hCe.le
    have hterm5 := mul_le_mul_of_nonneg_left heta5 hCi.le
    calc
      _ ≤ Ci * etaStep n l t + Ce * etaStep n l (t + 1) + Ce * etaStep n l (t + 4) +
          Ci * etaStep n l (t + 5) := hmain
      _ ≤ Ci * etaStep n l t + Ce * (Real.sqrt 6 * etaStep n l t) +
          Ce * (Real.sqrt 6 * etaStep n l t) + Ci * (Real.sqrt 6 * etaStep n l t) := by
        linarith
      _ ≤ (128 + 2 * Real.sqrt 6 * (Ce + Ci)) * etaStep n l t :=
        final_eta_bound Ci Ce (etaStep n l t) hCi hCe (Real.sqrt_nonneg _)
  · have hcp : ‖cpWT l G‖ ≤ 1 := by
      rw [cpWT]
      exact one_comp_le_one hIn
        (one_comp_le_one hEn (one_comp_le_one hFn (one_comp_le_one hXn
          (one_comp_le_one hFa (one_comp_le_one hEa hIa)))))
    have hnproj : ‖(1 - projGood l G (t + 6)).comp ((cpWT l G).comp (projGood l G t))‖ ≤ 1 := by
      exact one_comp_le_one (hP (t + 6)).2 (one_comp_le_one hcp (hP t).1)
    have heta : (1 : ℝ) / 128 ≤ etaStep n l t := eta_small_of_even n l t hn hn16 hl hln
    exact hnproj.trans (one_le_of_eta (constant_large Ci Ce hCi hCe) heta)
