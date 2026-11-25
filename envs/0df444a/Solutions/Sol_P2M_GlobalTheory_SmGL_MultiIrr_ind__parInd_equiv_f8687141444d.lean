-- Prove2me | solution 1 for P2M_GlobalTheory_SmGL_MultiIrr_ind__parInd_equiv_f8687141444d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:55.984332+00:00
-- url     : https://prove2.me/submissions/60964524-08ef-460b-8afe-59d8a2faa6d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_smInd_stages
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_exists_parab_mul
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_modExp_zero
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_modExp_succ
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_absPow_add
import Theorems.Thm_GlobalTheory_SmGL_continuous_leviEmb
import Theorems.Thm_GlobalTheory_SmGL_continuous_leviTwo
import Theorems.Thm_GlobalTheory_SmGL_deltaHalf_apply
import Theorems.Thm_GlobalTheory_SmGL_deltaHalf_two
import Theorems.Thm_GlobalTheory_SmGL_det_parab
import Theorems.Thm_GlobalTheory_SmGL_isSmoothChar_deltaHalf
import Theorems.Thm_GlobalTheory_SmGL_mem_parab_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n a' b' n' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b'] [Fintype n'] [DecidableEq n']
  {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
variable {s : ℕ} {m : Fin (s + 1) → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
namespace GlobalTheory.SmGL.MultiIrr
theorem _root_.solution (e : (Σ i, m i) ≃ n) (σ₀ : Representation ℂ (GL (m 0) k) V)
    (ρ : Representation ℂ (Levi k fun i : Fin s => m i.succ) W) (σ : Representation ℂ (Levi k m) U)
    (κ : V ⊗[ℂ] W ≃ₗ[ℂ] U)
    (h : ∀ g x, σ g (κ x) = κ (TensorProduct.map (σ₀ (g 0)) (ρ fun i => g i.succ) x)) :
    Nonempty ((ind₂ ((headTail m).trans e) (extTensor σ₀ (parInd (Equiv.refl _) ρ))).Equiv (parInd e σ)) := by
  let e' := (headTail m).trans e
  let π := (leviTwo k (m 0) (Σ i : Fin s, m i.succ)).symm.toMonoidHom.comp (leviProj k (two e'))
  let j := ((emb₂ k e').comp (MonoidHom.inr _ _)).codRestrict (parab k (two e'))
    fun _ => leviEmb_mem_parab k _ _
  refine smInd_stages (P' := parab k (Equiv.refl (Σ i : Fin s, m i.succ))) (fun g hg => ?_) π j ?_
    (fun x => ?_) (fun q => ?_) SplitFlip.isCompact_KO (fun x => ?_)
    ((deltaHalf k _).comp (leviTwo k _ _).toMonoidHom) ?_ σ₀ _ _ κ (fun q h1 h2 x => ?_) _ fun q x => rfl
  · exact (mem_parab_two k).2 fun y x => mem_parab_iff.1 hg y.1.succ 0 y.2 x (Fin.succ_pos _)
  · exact (continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (Continuous.prodMk_right 1))
  · exact (leviTwo k _ _).symm_apply_eq.2 (leviProj_leviEmb k _ _)
  · rw [mem_parab_iff, mem_parab_iff]
    refine ⟨fun hq x y u v hxy => hq x.succ y.succ u v (Fin.succ_lt_succ_iff.2 hxy), fun hq x y u v hxy => ?_⟩
    induction x using Fin.cases with
    | zero => exact absurd hxy (Fin.not_lt_zero _)
    | succ x =>
      induction y using Fin.cases with
      | zero => exact (mem_parab_two k).1 q.2 ⟨x, u⟩ v
      | succ y => exact hq x y u v (Fin.succ_lt_succ_iff.1 hxy)
  · exact exists_parab_mul _ x
  · have h1 : IsSmoothChar (((deltaHalf k _).comp
        (leviTwo k (m 0) (Σ i : Fin s, m i.succ)).toMonoidHom).comp (MonoidHom.inr _ _)) :=
      ((isSmoothChar_deltaHalf k).comp _ (continuous_leviTwo k)).comp _ (Continuous.prodMk_right 1)
    filter_upwards [h1.mem_nhds (one_mem _)] with u hu
    exact MonoidHom.mem_ker.1 hu
  · let g := leviProj k e ⟨q, h1⟩
    have e1 : (π q).1 = g 0 := Units.ext rfl
    have e2 : leviProj k _ ⟨(π q).2, h2⟩ = fun i : Fin s => g i.succ := funext fun _ => Units.ext rfl
    have e3 : GeneralLinearGroup.det (π q).2 = ∏ i : Fin s, GeneralLinearGroup.det (g i.succ) := by
      have := det_parab k _ ⟨(π q).2, h2⟩
      rwa [e2] at this
    have e4 : deltaHalf k m g = deltaHalf k _ (leviTwo k _ _ (π q)) *
        deltaHalf k (fun i : Fin s => m i.succ) fun i => g i.succ := by
      rw [deltaHalf_two, deltaHalf_apply, deltaHalf_apply, Fin.prod_univ_succ, e1, e3, map_prod, modExp_zero,
        mul_assoc, ← Finset.prod_mul_distrib]
      refine congrArg₂ _ (by simp) (Finset.prod_congr rfl fun i _ => ?_)
      rw [modExp_succ, ← MonoidHom.mul_apply, ← absPow_add]
      congr 2
      push_cast
      ring
    show (deltaHalf k m g : ℂ) • σ g (κ x) = (deltaHalf k _ (leviTwo k _ _ (π q)) : ℂ) •
      κ (TensorProduct.map (σ₀ (π q).1) ((deltaHalf k _ (leviProj k _ ⟨(π q).2, h2⟩) : ℂ) •
        ρ (leviProj k _ ⟨(π q).2, h2⟩)) x)
    rw [h, e4, e2, e1, TensorProduct.map_smul_right, LinearMap.smul_apply, map_smul, smul_smul, Units.val_mul]
end GlobalTheory.SmGL.MultiIrr
