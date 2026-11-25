-- Prove2me | solution 1 for PI.WGL.XiA.rowAct_xi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:51.08466+00:00
-- url     : https://prove2.me/submissions/f576c5e1-e0b1-4393-89d9-063f914b9695

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Theorems.Thm_PI_WGL_XiA_rowAct_initMinor
import Theorems.Thm_PI_WGL_XiA_lpMinor_eq
import Theorems.Thm_PI_WGL_XiA_rowsZ_strictMono
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiA
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.XiA
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (G : Matrix (Fin N) (Fin N) ℂ) (hG : GoodG n h G) :
    Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose (xi ℂ h lam sg) = C (xiScal h lam sg G) * xi ℂ h lam sg := by
  have hlp : ∀ i : Fin n, Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose
      (Formalism.GradedWeylDivisibility.lpMinor ℂ (r := N) (n := N) (i.1 + 1) (by omega) (by omega)) =
      C (∏ p : Fin (i.1 + 1), G (Fin.castLE (by omega) p) (Fin.castLE (by omega) p)) *
        Formalism.GradedWeylDivisibility.lpMinor ℂ (r := N) (n := N) (i.1 + 1) (by omega) (by omega) := by
    intro i
    rw [lpMinor_eq]
    apply rowAct_initMinor G _ (Fin.strictMono_castLE _) _ hG.1
    intro p b hb
    have hle : b ≤ Fin.castLE (by omega) p := by
      by_contra hlt
      push Not at hlt
      exact hb (hG.1 _ _ hlt)
    refine ⟨⟨b.1, ?_⟩, Fin.ext rfl⟩
    have := p.2
    simp only [Fin.le_def, Fin.coe_castLE] at hle
    omega
  have hrz : ∀ i : Fin n, Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose (Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) (rowsZ h i) (by omega)) =
      C (∏ p : Fin (i.1 + 1), G (rowsZ h i p) (rowsZ h i p)) *
        Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) (rowsZ h i) (by omega) := by
    intro i
    apply rowAct_initMinor G _ (rowsZ_strictMono h i) _ hG.1
    intro p b hb
    by_cases hp : p.1 = i.1
    · have e : rowsZ h i p = ⟨n, by omega⟩ := by
        simp only [rowsZ, hp, if_true]; ext; simp; omega
      rw [e] at hb
      have hbn : b.1 = n := by
        by_contra hne
        exact hb (hG.2 b hne)
      refine ⟨⟨i.1, by omega⟩, ?_⟩
      simp only [rowsZ, if_true]
      ext; simp; omega
    · have e : rowsZ h i p = ⟨p.1, by omega⟩ := by
        simp only [rowsZ, hp, if_false]
      rw [e] at hb
      have hle : b.1 ≤ p.1 := by
        by_contra hlt
        push Not at hlt
        exact hb (hG.1 _ _ (by simpa [Fin.lt_def] using hlt))
      have hpi : p.1 < i.1 := by have := p.2; omega
      refine ⟨⟨b.1, by omega⟩, ?_⟩
      have : b.1 ≠ i.1 := by omega
      simp only [rowsZ, this, if_false]
  unfold xi xiScal
  rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [map_mul, map_pow, map_pow, hlp i, hrz i, mul_pow, mul_pow, map_mul, map_pow, map_pow]
  ring
end PI.WGL.XiA
