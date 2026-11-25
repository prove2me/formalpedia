-- Prove2me | solution 1 for PI.WGL.capScalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:56:26.86715+00:00
-- url     : https://prove2.me/submissions/22026b12-ef53-4d7e-a2ff-32edea6e7687

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliShift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoExistsOfCap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_BCRowGenMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoPolDiagHw
import Theorems.Thm_PI_WGL_io_natW_anti
import Theorems.Thm_PI_WGL_io_natW_cast
import Theorems.Thm_PI_WGL_io_pol_diag_hw
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwRaise
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_REAL_qDetCentral_of
import Theorems.Thm_Formalism_REAL_quantumDetHighestWeight_holds
import Theorems.Thm_Formalism_REAL_quantumMinorColSkew_holds
import Theorems.Thm_Formalism_REAL_quantumMinorRowSkew_holds
import Theorems.Thm_PI_WGL_capE_apply
import Theorems.Thm_PI_WGL_capE_glRel
import Theorems.Thm_PI_WGL_eqv_pol
import Theorems.Thm_PI_WGL_io_extremal_mem
import Theorems.Thm_PI_WGL_pol_eq_rowDiv
import Theorems.Thm_PI_WGL_pol_mem_dualWeyl
import Theorems.Thm_PI_WGL_rowDiv_succ
import Theorems.Thm_PI_WGL_rowDiv_zero
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
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution (h3 : PI.HwIrred) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) (u : ℂ) :
    Formalism.REAL.qdet (capE h lam) u (φ s) = (∏ k : Fin n, (u - (k : ℂ) + (mu.w k : ℂ))) • φ s := by
  have hgl := capE_glRel h lam
  have hcent : ∀ a b, Formalism.REAL.qdet (capE h lam) u * capE h lam a b =
      capE h lam a b * Formalism.REAL.qdet (capE h lam) u := fun a b =>
    Formalism.REAL.qDetCentral_of Formalism.REAL.quantumMinorRowSkew_holds Formalism.REAL.quantumMinorColSkew_holds _ n (capE h lam) hgl u a b
  set Q := Formalism.REAL.qdet (capE h lam) u with hQ
  set p : ℂ := ∏ k : Fin n, (u - (k : ℂ) + (mu.w k : ℂ)) with hp
  have hφpol : ∀ a b, ∀ s ∈ nablaSq ℂ n mu, φ (pol ℂ a b s) =
      capE h lam a b (φ s) - (if a = b then (mu.detShift : ℂ) • φ s else 0) := by
    intro a b s hs
    rw [capE_apply, eq_sub_iff_add_eq, eqv_pol h mu lam φ hφ a b s hs]
  let M : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) :=
    nablaSq ℂ n mu ⊓ LinearMap.ker ((Q - p • LinearMap.id) ∘ₗ φ)
  have memM : ∀ s, s ∈ M ↔ s ∈ nablaSq ℂ n mu ∧ Q (φ s) = p • φ s := by
    intro s
    simp only [M, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  have hpolM : ∀ a b, ∀ s ∈ M, pol ℂ a b s ∈ M := by
    intro a b s hs
    rw [memM] at hs ⊢
    refine ⟨pol_mem_dualWeyl ℂ _ a b s hs.1, ?_⟩
    have hc : Q (capE h lam a b (φ s)) = capE h lam a b (Q (φ s)) := by
      have := congrArg (fun T : Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ) => T (φ s)) (hcent a b)
      simpa only [Module.End.mul_apply] using this
    rw [hφpol a b s hs.1, map_sub, hc, hs.2, map_smul, smul_sub]
    split_ifs
    · rw [map_smul, hs.2, smul_comm]
    · rw [map_zero, smul_zero]
  have hdivM : ∀ a b k, ∀ s ∈ M, rowDiv ℂ a b k s ∈ M := by
    intro a b k
    induction k with
    | zero => intro s hs; rwa [rowDiv_zero]
    | succ k ih =>
      intro s hs
      have hrec := rowDiv_succ ℂ a b k s
      have hk : ∀ (j : ℕ) (x : MvPolynomial (Fin n × Fin n) ℂ),
          x * (j : MvPolynomial (Fin n × Fin n) ℂ) = (j : ℂ) • x := by
        intro j x; rw [MvPolynomial.smul_eq_C_mul, mul_comm x, map_natCast]
      rw [← Nat.cast_succ] at hrec
      simp only [hk] at hrec
      have hc0 : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      have e1 : rowDiv ℂ a b (k + 1) s = ((k + 1 : ℕ) : ℂ)⁻¹ • (rowDiv ℂ a b k (pol ℂ a b s) -
          if a = b then (k : ℂ) • rowDiv ℂ a b k s else 0) := by
        rw [← hrec, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [e1]
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ (ih _ (hpolM a b s hs)) ?_)
      split_ifs
      · exact Submodule.smul_mem _ _ (ih s hs)
      · exact M.zero_mem
  have hext := io_extremal_mem h3 n mu
  have hextM : extremal ℂ n mu ∈ M := by
    rw [memM]
    refine ⟨hext, ?_⟩
    have hHW : Formalism.REAL.IsHW (capE h lam) (fun k => (mu.w k : ℂ)) (φ (extremal ℂ n mu)) := by
      constructor
      · intro a
        have e := hφpol a a _ hext
        rw [if_pos rfl, eq_sub_iff_add_eq] at e
        rw [← e]
        show φ (pol ℂ a a (hw ℂ le_rfl mu.natW)) + _ = _
        rw [io_pol_diag_hw _ (io_natW_anti mu), map_smul, io_natW_cast]
        change ((mu.w a - mu.detShift : ℤ) : ℂ) • φ (extremal ℂ n mu) + (mu.detShift : ℂ) • φ (extremal ℂ n mu) =
          (mu.w a : ℂ) • φ (extremal ℂ n mu)
        rw [← add_smul]
        congr 1
        push_cast
        ring
      · intro a b hab
        have e := hφpol a b _ hext
        rw [if_neg (ne_of_lt hab), sub_zero] at e
        rw [← e, pol_eq_rowDiv]
        show φ (rowDiv ℂ a b 1 (hw ℂ le_rfl mu.natW)) = 0
        rw [Formalism.GradedWeylDivisibility.hwRaise ℂ n n le_rfl mu.natW a b 1 hab le_rfl, map_zero]
    exact Formalism.REAL.quantumDetHighestWeight_holds _ n (capE h lam) _ _ hgl hHW u
  have hall : delSq ℂ n mu ≤ M := by
    show Formalism.GradedWeylDivisibility.weyl ℂ n n le_rfl mu.natW ≤ M
    unfold Formalism.GradedWeylDivisibility.weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    induction w with
    | nil => exact hextM
    | cons x w ih => exact hdivM x.1 x.2.1 x.2.2 _ ih
  rw [(h3 n mu).1] at hs
  exact ((memM s).mp (hall hs)).2
end PI.WGL
