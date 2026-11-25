-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:32.157318+00:00
-- url     : https://prove2.me/submissions/d310eaf9-d56b-4ad6-bb83-ed335d8c2383

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LintegralInsertFiberLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DeZeroBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExponentConditionNeg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_exponentCondition_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_Lsq_ge_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_beta_bound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_cont_Lsq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_cont_de
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_cont_tailPt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_de_ins_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_lintegral_insertFiber_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_split_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux
private theorem lintegral_prod4_eq_iterated {A B C : Type*} [MeasureSpace A] [MeasureSpace B] [MeasureSpace C]
    [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)]
    [SigmaFinite (volume : Measure C)]
    (T : A × B × C × ℝ → ℝ≥0∞) (hT : Measurable T) :
    ∫⁻ y, T y = ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ t, T (a, b, c, t) := by
  simp only [Measure.volume_eq_prod]
  rw [lintegral_prod _ hT.aemeasurable]
  refine lintegral_congr fun a => ?_
  rw [lintegral_prod (fun w : B × C × ℝ => T (a, w))
    (hT.comp (by fun_prop : Measurable fun w : B × C × ℝ => (a, w))).aemeasurable]
  refine lintegral_congr fun b => ?_
  exact lintegral_prod (fun w : C × ℝ => T (a, b, w))
    (hT.comp (by fun_prop : Measurable fun w : C × ℝ => (a, b, w))).aemeasurable
end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution (hT : TailFin) (hC1 : C1) (hK : KER) (hL : SLOW) {p m : ℕ} (e : Fin (p + 2) → ℝ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (he : ∀ l, 0 < e l)
    (hsum : e 0 + 2 * ∑ i : Fin (p + 1), e i.succ < γ / 2) :
    ∃ C : ℝ, ∫⁻ x : Xp (p + 1) m, fS (fun l => s0N (p + 1) m l - e l) x * (‖x.2.1 0‖₊ : ℝ≥0∞) ^ (-γ) ≤
      ENNReal.ofReal C := by
  have hS0 : 0 ≤ ∑ i : Fin (p + 1), e i.succ := Finset.sum_nonneg fun i _ => (he _).le
  have he0γ : e 0 < γ := by linarith
  have hγ2 : γ < 2 := by linarith
  have hα : 0 < γ / 2 - e 0 := by linarith
  have he1 : ∀ l, e l ≤ 1 := by
    intro l
    rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨i, rfl⟩
    · linarith
    · have : e i.succ ≤ ∑ j : Fin (p + 1), e j.succ :=
        Finset.single_le_sum (f := fun j : Fin (p + 1) => e j.succ) (fun j _ => (he _).le)
          (Finset.mem_univ i)
      linarith [he 0]
  obtain ⟨CK, hCK0, hCK⟩ := lintegral_insertFiber_le hC1 hK (he 0) he0γ hγ2
  obtain ⟨CS, hCS0, hCS⟩ := beta_bound (m := m) hL e he he1 hγ2 hα
  have hec := exponentCondition_neg (α := γ / 2 - e 0) e he (by linarith)
  have hfin := hT p m (γ / 2 - e 0) (fun i => -e i.succ) hec.1 hec.2
  have hc0 : ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m 0 = 2 := by simp [ReciprocityTheory.ChartRestriction.DS.Xi.s0N]
  obtain ⟨P, hP⟩ : ∃ P : Yp p m → ℝ≥0∞, P = fun y => ∏ i : Fin (p + 1),
      ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) i.succ ^
        (-(ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m i.succ - e i.succ))) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Yp p m → ℝ≥0∞, F = fun y =>
      ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.Lsq (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 1 ^ (-1 + γ / 2)) *
        ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 0 ^ (-(γ - e 0))) * P y := ⟨_, rfl⟩
  obtain ⟨T, hTd⟩ : ∃ T : Yp p m → ℝ≥0∞, T = fun y =>
      ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.Lsq (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 1 ^ ((-2 + (γ / 2 - e 0)) / 2)) *
        ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 1 ^ (-(γ / 2 - e 0))) *
        ∏ i : Fin (p + 1), ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) i.succ ^
          (-(ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m i.succ + (fun i : Fin (p + 1) => -e i.succ) i))) := ⟨_, rfl⟩
  have hmL : ∀ l : Fin (p + 1 + 1), Measurable fun y : Yp p m => ReciprocityTheory.ChartRestriction.DS.Xi.Lsq (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) l :=
    fun l => ((cont_Lsq l).comp cont_tailPt).measurable
  have hmH : ∀ l : Fin (p + 1 + 1), Measurable fun y : Yp p m => ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) l :=
    fun l => ((cont_de l).comp cont_tailPt).measurable
  have hPm : Measurable P := by
    rw [hP]
    exact Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp ((hmH i.succ).pow_const _)
  have hFm : Measurable F := by
    rw [hF]
    exact ((ENNReal.measurable_ofReal.comp ((hmL 1).pow_const _)).mul
      (ENNReal.measurable_ofReal.comp ((hmH 0).pow_const _))).mul hPm
  have hTm : Measurable T := by
    rw [hTd]
    exact ((ENNReal.measurable_ofReal.comp ((hmL 1).pow_const _)).mul
      (ENNReal.measurable_ofReal.comp ((hmH 1).pow_const _))).mul
      (Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp ((hmH i.succ).pow_const _))
  have hPne : ∀ y, P y ≠ ∞ := fun y => by
    rw [hP]; exact ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top
  have hinner : ∀ y : Yp p m,
      ∫⁻ z : ℂ, fS (fun l => ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m l - e l) (ins y z) *
        (‖(ins y z).2.1 0‖₊ : ℝ≥0∞) ^ (-γ) ≤ ENNReal.ofReal CK * F y := by
    intro y
    have h1 : ∀ z, fS (fun l => ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m l - e l) (ins y z) =
        ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ins y z) 0 ^ (-(ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m 0 - e 0))) *
        ∏ i : Fin (p + 1), ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ins y z) i.succ ^
          (-(ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m i.succ - e i.succ))) :=
      fun z => Fin.prod_univ_succ _
    have hz : ∀ z, (ins y z).2.1 0 = z := fun z => by simp [ins]
    have hPz : ∀ z, ∏ i : Fin (p + 1), ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ins y z) i.succ ^
        (-(ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m i.succ - e i.succ))) = P y := fun z => by
      rw [hP]
      exact Finset.prod_congr rfl fun i _ => by rw [de_ins_succ]
    have hnn : 0 ≤ CK * ReciprocityTheory.ChartRestriction.DS.Xi.Lsq (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 1 ^ (-1 + γ / 2) :=
      mul_nonneg hCK0.le (Real.rpow_nonneg (zero_le_one.trans (Lsq_ge_one _ _)) _)
    calc ∫⁻ z : ℂ, fS (fun l => ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m l - e l) (ins y z) *
          (‖(ins y z).2.1 0‖₊ : ℝ≥0∞) ^ (-γ)
        = ∫⁻ z : ℂ, P y * (ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ins y z) 0 ^ (-(2 - e 0))) *
            (‖z‖₊ : ℝ≥0∞) ^ (-γ)) := by
          refine lintegral_congr fun z => ?_
          rw [h1 z, hc0, hz z, hPz z]
          ring
      _ = P y * ∫⁻ z : ℂ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ins y z) 0 ^ (-(2 - e 0))) *
            (‖z‖₊ : ℝ≥0∞) ^ (-γ) := lintegral_const_mul' _ _ (hPne y)
      _ ≤ P y * ENNReal.ofReal (CK * ReciprocityTheory.ChartRestriction.DS.Xi.Lsq (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 1 ^ (-1 + γ / 2) *
            ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 0 ^ (-(γ - e 0))) := mul_le_mul_of_nonneg_left (hCK y) zero_le
      _ = ENNReal.ofReal CK * F y := by
          simp only [hF]
          rw [ENNReal.ofReal_mul hnn, ENNReal.ofReal_mul hCK0.le]
          ring
  have hkey : ∫⁻ y, F y ≤ ENNReal.ofReal CS * ReciprocityTheory.ChartRestriction.DS.Xi.TailInt p m (γ / 2 - e 0) (fun i => -e i.succ) := by
    have htail : ReciprocityTheory.ChartRestriction.DS.Xi.TailInt p m (γ / 2 - e 0) (fun i => -e i.succ) = ∫⁻ y, T y := by
      rw [hTd]; rfl
    rw [htail, lintegral_prod4_eq_iterated F hFm, lintegral_prod4_eq_iterated T hTm]
    calc ∫⁻ a : Fin (p + 1) → ℂ, ∫⁻ b : Fin p → ℂ, ∫⁻ c : Fin m → ℂ, ∫⁻ t : ℝ, F (a, b, c, t)
        ≤ ∫⁻ a : Fin (p + 1) → ℂ, ∫⁻ b : Fin p → ℂ, ∫⁻ c : Fin m → ℂ,
            ENNReal.ofReal CS * ∫⁻ t : ℝ, T (a, b, c, t) := by
          refine lintegral_mono fun a => lintegral_mono fun b => lintegral_mono fun c => ?_
          subst hF hP hTd
          exact hCS a b c
      _ = ENNReal.ofReal CS * ∫⁻ a : Fin (p + 1) → ℂ, ∫⁻ b : Fin p → ℂ, ∫⁻ c : Fin m → ℂ,
            ∫⁻ t : ℝ, T (a, b, c, t) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun a => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun b => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ⟨CK * CS * (ReciprocityTheory.ChartRestriction.DS.Xi.TailInt p m (γ / 2 - e 0) (fun i => -e i.succ)).toReal, ?_⟩
  calc _ ≤ ∫⁻ y : Yp p m, ∫⁻ z : ℂ,
        fS (fun l => ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m l - e l) (ins y z) *
          (‖(ins y z).2.1 0‖₊ : ℝ≥0∞) ^ (-γ) := split_le _
    _ ≤ ∫⁻ y : Yp p m, ENNReal.ofReal CK * F y := lintegral_mono hinner
    _ = ENNReal.ofReal CK * ∫⁻ y, F y := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal CK * (ENNReal.ofReal CS * ReciprocityTheory.ChartRestriction.DS.Xi.TailInt p m (γ / 2 - e 0) (fun i => -e i.succ)) :=
        mul_le_mul_of_nonneg_left hkey zero_le
    _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hCK0.le hCS0.le), ENNReal.ofReal_mul hCK0.le,
          ENNReal.ofReal_toReal hfin.ne]
        ring
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
