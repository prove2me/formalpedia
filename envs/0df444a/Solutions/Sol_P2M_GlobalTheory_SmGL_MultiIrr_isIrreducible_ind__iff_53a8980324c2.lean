-- Prove2me | solution 1 for P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind__iff_53a8980324c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:05:41.455647+00:00
-- url     : https://prove2.me/submissions/7e1ed081-0c4e-4ae9-a947-6955a0e80513

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_isIrreducible_smInd_iff
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_relabel_apply
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_continuous_relabel
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_det_relabel
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_deltaHalf_two
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
namespace GlobalTheory.SmGL.MultiIrr
theorem _root_.solution (e : a ⊕ b ≃ n) (e' : a' ⊕ b' ≃ n') (ea : a ≃ a') (eb : b ≃ b')
    {ρ : Representation ℂ (GL a k × GL b k) V} {ρ' : Representation ℂ (GL a' k × GL b' k) W} (κ : V ≃ₗ[ℂ] W)
    (h : ∀ g v, κ (ρ g v) = ρ' (relabel k ea g.1, relabel k eb g.2) (κ v)) :
    (ind₂ e ρ).IsIrreducible ↔ (ind₂ e' ρ').IsIrreducible := by
  let en : n ≃ n' := e.symm.trans ((ea.sumCongr eb).trans e')
  have hen : ∀ (g : GL n k) x y, (relabel k en g).val (e' (Sum.map ea eb x)) (e' (Sum.map ea eb y)) =
      g.val (e x) (e y) := fun g x y => by
    rw [← relabel_apply en]
    simp [en]
  have hP : ∀ g, g ∈ parab k (two e) ↔ relabel k en g ∈ parab k (two e') := fun g => by
    rw [mem_parab_two, mem_parab_two, eb.surjective.forall]
    refine forall_congr' fun j => ?_
    rw [ea.surjective.forall]
    exact forall_congr' fun i => by rw [← hen g (.inr j) (.inl i)]; rfl
  refine isIrreducible_smInd_iff (relabel k en) (continuous_relabel en) (continuous_relabel en.symm) κ hP
    fun p v => ?_
  obtain ⟨x, h1⟩ := (leviTwo k a b).surjective (leviProj k (two e) p)
  have h2 : leviProj k (two e') ⟨_, (hP p).1 p.2⟩ = leviTwo k a' b' (relabel k ea x.1, relabel k eb x.2) := by
    funext y
    cases y
    · ext i j
      obtain ⟨i, rfl⟩ := ea.surjective i
      obtain ⟨j, rfl⟩ := ea.surjective j
      exact (hen p (.inl i) (.inl j)).trans ((congrArg (fun g : Levi k (Two a b) => (g false).val i j)
        h1).symm.trans (relabel_apply ea x.1 i j).symm)
    · ext i j
      obtain ⟨i, rfl⟩ := eb.surjective i
      obtain ⟨j, rfl⟩ := eb.surjective j
      exact (hen p (.inr i) (.inr j)).trans ((congrArg (fun g : Levi k (Two a b) => (g true).val i j)
        h1).symm.trans (relabel_apply eb x.2 i j).symm)
  show κ ((deltaHalf k _ (leviProj k (two e) p) : ℂ) • ρ ((leviTwo k a b).symm (leviProj k (two e) p)) v) =
    (deltaHalf k _ (leviProj k (two e') ⟨_, (hP p).1 p.2⟩) : ℂ) •
      ρ' ((leviTwo k a' b').symm (leviProj k (two e') ⟨_, (hP p).1 p.2⟩)) (κ v)
  rw [h2, ← h1, deltaHalf_two, deltaHalf_two, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, map_smul, h,
    det_relabel, det_relabel, Fintype.card_congr ea, Fintype.card_congr eb]
end GlobalTheory.SmGL.MultiIrr
