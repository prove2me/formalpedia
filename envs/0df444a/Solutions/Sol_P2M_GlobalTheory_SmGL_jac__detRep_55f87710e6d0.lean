-- Prove2me | solution 1 for P2M_GlobalTheory_SmGL_jac__detRep_55f87710e6d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:52:06.60509+00:00
-- url     : https://prove2.me/submissions/51dced2c-1c30-44da-9158-57a30a4c6e90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_absPow_neg
import Theorems.Thm_GlobalTheory_SmGL_jac_mk
import Theorems.Thm_GlobalTheory_SmGL_deltaHalf_two
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_P2M_GlobalTheory_SmGL_det_emb__b005fdd5e485


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {k}
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace GlobalTheory.SmGL
theorem _root_.solution (e : a ⊕ b ≃ n) (χ : kˣ →* ℂˣ) (g : GL a k × GL b k)
    (x : Jacquet (detRep n χ) (unipRad k (two e))) :
    jac₂ e (detRep n χ) g x =
      ((detChar a (χ * absPow k (-(Fintype.card b : ℂ) / 2)) g.1 *
        detChar b (χ * absPow k ((Fintype.card a : ℂ) / 2)) g.2 : ℂˣ) : ℂ) • x := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h := jac_mk (two e) (detRep n χ) (leviTwo k a b g) v
  have h2 : detRep n χ (leviEmb k (two e) (leviTwo k a b g)) v =
      ((χ (GeneralLinearGroup.det g.1) * χ (GeneralLinearGroup.det g.2) : ℂˣ) : ℂ) • v := by
    rw [← map_mul, ← det_emb₂ k e g]
    exact ofChar_apply _ _ _
  rw [h2, Submodule.Quotient.mk_smul, smul_smul, deltaHalf_two] at h
  refine h.trans ?_
  congr 1
  rw [← Units.val_mul]
  congr 1
  simp only [detChar_apply, MonoidHom.mul_apply, neg_div, absPow_neg, MonoidHom.inv_apply, mul_inv,
    inv_inv]
  simp only [mul_comm, mul_left_comm, mul_assoc]
end GlobalTheory.SmGL
