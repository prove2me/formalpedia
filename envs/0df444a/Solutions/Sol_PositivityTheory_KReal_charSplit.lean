-- Prove2me | solution 1 for PositivityTheory.KReal.charSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:40:03.582638+00:00
-- url     : https://prove2.me/submissions/103d91de-bd38-4140-a900-36558f058b90

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSplit
import Theorems.Thm_PositivityTheory_KReal_chiTr_Eab
import Theorems.Thm_FockRL_sameBlock_symm
import Theorems.Thm_FockRaiseLowInner_fockInner_add_left
import Theorems.Thm_FockRaiseLowInner_fockInner_add_right
import Theorems.Thm_FockRaiseLowInner_fockInner_smul_left
import Theorems.Thm_FockRaiseLowInner_fockInner_smul_right
import Theorems.Thm_PI_FHS_exists_orth
import Theorems.Thm_PI_FHS_fockInner_add_left
import Theorems.Thm_PI_FHS_fockInner_add_right
import Theorems.Thm_PI_FHS_fockInner_self_eq_zero
import Theorems.Thm_PI_FHS_fockInner_smul_left
import Theorems.Thm_PI_FHS_fockInner_smul_right
import Theorems.Thm_PI_FHS_sameBlock_symm
import Theorems.Thm_PI_FockOneDegW_exists_orth
import Theorems.Thm_PI_FockOneDegW_fock_kernel_adjoint
import Theorems.Thm_PositivityTheory_KReal_mem_polChi_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {p q r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution (c : ℂ) (c0 : ℚ) (hc : c = c0) (d : ℕ) (W : Submodule ℂ (Pol p q r s))
    (hWd : W ≤ homog (Ix p q × Ix r s) d) (hW : KSt (units (fockAct1 p q r s)) W) :
    W.map (thMkC p q r s c) ≤ (W ⊓ polChi p q r s c).map (thMkC p q r s c) := by
  subst hc
  classical
  rintro _ ⟨x, hx, rfl⟩
  let D : Ix p q → Ix p q → Module.End ℂ (Pol p q r s) := fun a b =>
    fockAct1 p q r s (Eab a b) - (if a = b then ((c0 : ℚ) : ℂ) else 0) • 1
  have hDa : ∀ a b w, D a b w =
      fockAct1 p q r s (Eab a b) w + (-(if a = b then ((c0 : ℚ) : ℂ) else 0)) • w := by
    intro a b w
    rw [neg_smul, ← sub_eq_add_neg]
    rfl
  have hDW : ∀ a b, sameBlock a b → ∀ w ∈ W, D a b w ∈ W := by
    intro a b hab w hw
    rw [hDa]
    exact W.add_mem (hW a b hab w hw) (W.smul_mem _ hw)
  let K : Submodule ℂ (Pol p q r s) :=
    ⨆ ab : {ab : Ix p q × Ix p q // sameBlock ab.1 ab.2}, W.map (D ab.1.1 ab.1.2)
  have hKW : K ≤ W := iSup_le fun ab => by
    rintro _ ⟨w, hw, rfl⟩
    exact hDW _ _ ab.2 w hw
  have hKc : K ≤ coinvSub (act1 p q r s) (chiTr ((c0 : ℚ) : ℂ)) := iSup_le fun ab => by
    rintro _ ⟨w, -, rfl⟩
    refine Submodule.mem_iSup_of_mem (Eab ab.1.1 ab.1.2) ⟨w, ?_⟩
    rw [chiTr_Eab]
    rfl
  obtain ⟨y, hy, hz⟩ := PI.FHS.exists_orth K d (hKW.trans hWd) x
  have hzW : x - y ∈ W := W.sub_mem hx (hKW hy)
  refine ⟨x - y, ⟨hzW, ?_⟩, ?_⟩
  · refine (mem_polChi_iff _ _).2 fun a b hab => ?_
    have hw := hDW a b hab _ hzW
    have hba : sameBlock b a := PI.FHS.sameBlock_symm hab
    have h0 := hz (D b a (D a b (x - y)))
      (Submodule.mem_iSup_of_mem (⟨(b, a), hba⟩ : {ab : Ix p q × Ix p q // sameBlock ab.1 ab.2})
        ⟨_, hw, rfl⟩)
    have h1 : fockInner (D a b (x - y)) (D a b (x - y)) = 0 := by
      have e : ∀ w : Pol p q r s, fockInner w (D a b (x - y)) = fockInner (D b a w) (x - y) := by
        intro w
        rw [hDa, hDa, PI.FHS.fockInner_add_right, PI.FHS.fockInner_add_left, PI.FHS.fockInner_smul_right,
          PI.FHS.fockInner_smul_left, PI.FockOneDegW.fock_kernel_adjoint p q r s a b hab]
        congr 2
        by_cases h : a = b
        · subst h; simp
        · simp [h, Ne.symm h]
      rw [e, h0]
    have h2 := PI.FHS.fockInner_self_eq_zero h1
    rw [hDa, neg_smul, add_neg_eq_zero] at h2
    exact h2
  · rw [map_sub]
    have : thMkC p q r s ((c0 : ℚ) : ℂ) y = 0 := (Submodule.Quotient.mk_eq_zero _).2 (hKc hy)
    rw [this, sub_zero]
end PositivityTheory.KReal
