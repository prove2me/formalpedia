-- Prove2me | solution 1 for PI.RhsWLim.W.polarDecW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:53.626561+00:00
-- url     : https://prove2.me/submissions/21595ce5-36c5-4b70-b005-8a52b4bb6ad9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TransW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_UnimodS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_BallConj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PolarDec
import Theorems.Thm_PI_RhsWLim_W_uwb_emb
import Theorems.Thm_PI_RhsWLim_W_col_unitary
import Theorems.Thm_PI_RhsWLim_W_boost_herm
import Theorems.Thm_PI_RhsWLim_W_MB_Hb_conjT
import Theorems.Thm_PI_RhsWLim_W_MB_emb_conjT
import Theorems.Thm_PI_RhsWLim_W_MB_emb_mem
import Theorems.Thm_PI_RhsWLim_W_MB_emb_mem_UWb
import Theorems.Thm_PI_RhsWLim_W_MB_emb_mul
import Theorems.Thm_PI_RhsWLim_W_MB_emb_one
import Theorems.Thm_PI_RhsWLim_W_boost_mem
import Theorems.Thm_PI_RhsWLim_W_form_apply
import Theorems.Thm_PI_RhsWLim_W_hb_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix ComplexConjugate
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution : PolarDecW := by
  intro k r p hp
  set μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun i j => p (wI k r i) (wI k r j) with hμdef
  have hpμ : p = embWb k r μ := uwb_emb hp
  have hμ : μᴴ * Hb k * μ = Hb k := (MB.emb_mem μ).1 (hpμ ▸ hp.1)
  set y : Fin k → ℂ := fun l => μ l.castSucc (Fin.last k) with hy
  set c : ℂ := μ (Fin.last k) (Fin.last k) with hc
  have hform := congrFun (congrFun hμ (Fin.last k)) (Fin.last k)
  rw [form_apply] at hform
  have hS0 : ∑ l, conj (y l) * y l = conj c * c - 1 := by
    simp only [Hb, Matrix.diagonal_apply_eq, if_true] at hform
    simp only [hy, hc]; linear_combination hform
  have hA : ∑ l, conj (y l) * y l = ((∑ l, Complex.normSq (y l) : ℝ) : ℂ) := by
    push_cast [Complex.normSq_eq_conj_mul_self]; rfl
  have hA0 : 0 ≤ ∑ l, Complex.normSq (y l) := Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _
  have hcc : conj c * c = ((‖c‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul, zero_sub, hA] at hS0
    have := congrArg Complex.re hS0
    simp at this; linarith
  set n : ℝ := ‖c‖ with hn
  have hnpos : 0 < n := norm_pos_iff.2 hc0
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hnpos.ne'
  set y' : Fin k → ℂ := fun l => y l * ((n : ℂ) / c) with hy'
  have hnn : ‖((n : ℝ) : ℂ)‖ = n := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]
  have hS' : ∑ l, conj (y' l) * y' l = ((‖((n : ℝ) : ℂ)‖ : ℝ) : ℂ) ^ 2 - 1 := by
    have e : ∀ l, conj (y' l) * y' l = conj (y l) * y l * (((n : ℂ) ^ 2) / (conj c * c)) := by
      intro l; simp only [hy', map_mul, map_div₀, Complex.conj_ofReal]; field_simp
    simp only [e, ← Finset.sum_mul, hS0, hcc, hnn]
    field_simp
  set B₀ := boost y' (n : ℂ) with hB₀
  have hB : B₀ᴴ * Hb k * B₀ = Hb k := boost_mem y' (n : ℂ) hS' hn0
  have hBh : B₀ᴴ = B₀ := boost_herm y' n hnpos
  have hHbh : (Hb k)ᴴ = Hb k := MB.Hb_conjT
  set Bi := Hb k * B₀ᴴ * Hb k with hBi
  have hBiB : Bi * B₀ = 1 := by
    calc Bi * B₀ = Hb k * (B₀ᴴ * Hb k * B₀) := by simp only [hBi, Matrix.mul_assoc]
      _ = 1 := by rw [hB, hb_sq]
  have hBBi : B₀ * Bi = 1 := mul_eq_one_comm.mp hBiB
  have hBHB : B₀ * Hb k * B₀ᴴ = Hb k := by
    have : B₀ * Hb k * B₀ᴴ * Hb k = 1 := by rw [← hBBi, hBi]; simp only [Matrix.mul_assoc]
    calc B₀ * Hb k * B₀ᴴ = B₀ * Hb k * B₀ᴴ * Hb k * Hb k := by rw [Matrix.mul_assoc (B₀ * Hb k * B₀ᴴ) (Hb k) (Hb k), hb_sq, Matrix.mul_one]
      _ = Hb k := by rw [this, Matrix.one_mul]
  set μq := Bi * μ with hμq
  have hμqU : μqᴴ * Hb k * μq = Hb k := by
    have hBi' : Biᴴ * Hb k * Bi = Hb k := by
      simp only [hBi, Matrix.conjTranspose_mul, hHbh, conjTranspose_conjTranspose]
      calc Hb k * (B₀ * Hb k) * Hb k * (Hb k * B₀ᴴ * Hb k) = Hb k * (B₀ * (Hb k * Hb k) * Hb k * B₀ᴴ) * Hb k := by
            simp only [Matrix.mul_assoc]
        _ = Hb k := by rw [hb_sq, Matrix.mul_one, hBHB, hb_sq, Matrix.one_mul]
    calc μqᴴ * Hb k * μq = μᴴ * (Biᴴ * Hb k * Bi) * μ := by
          simp only [hμq, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hb k := by rw [hBi', hμ]
  set e : ℂ := c / n with he
  have hucol : ∀ l, μ l (Fin.last k) = e * B₀ l (Fin.last k) := by
    intro l
    induction l using Fin.lastCases with
    | last => simp only [hB₀, boost, Fin.lastCases_last, he, hc]; field_simp
    | cast j => simp only [hB₀, boost, Fin.lastCases_last, Fin.lastCases_castSucc, he, hy', hy]; field_simp
  have hcol : ∀ i, μq i (Fin.last k) = if i = Fin.last k then e else 0 := by
    intro i
    have : μq i (Fin.last k) = e * (Bi * B₀) i (Fin.last k) := by
      simp only [hμq, Matrix.mul_apply, hucol, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [this, hBiB, Matrix.one_apply]
    split_ifs <;> simp
  have he1 : conj e * e = 1 := by
    simp only [he, map_div₀, Complex.conj_ofReal]
    rw [div_mul_div_comm, hcc]
    field_simp
  have hqu := col_unitary μq hμqU e he1 hcol
  refine ⟨B₀, hB, hBh, embWb k r μq, MB.emb_mem_UWb hμqU, ?_, ?_⟩
  · rw [MB.emb_conjT, ← MB.emb_mul, hqu, MB.emb_one]
  · rw [← MB.emb_mul, hμq, ← Matrix.mul_assoc, hBBi, Matrix.one_mul, ← hpμ]
end PI.RhsWLim.W
