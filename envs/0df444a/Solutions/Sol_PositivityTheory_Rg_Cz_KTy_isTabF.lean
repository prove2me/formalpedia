-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.KTy.isTabF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:37.44745+00:00
-- url     : https://prove2.me/submissions/316ed350-8aa0-4853-a9e6-fb088ea28546

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_pr_ext
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_isTabQ
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.KTy
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
variable (nu : ι → Fin n → ℕ) (H : Finset ι)
namespace PositivityTheory.Rg.Cz.KTy
theorem _root_.solution (hm : ∀ τ, Monotone (nu τ)) : IsTab (colF nu H) (bF nu H) := by
  have hQ := isTabQ nu hm
  refine ⟨fun p q h hb => ?_, fun p i hi => ?_⟩
  · rcases p with p | k | k <;> rcases q with q | k' | k' <;> simp [colF, bF] at h hb ⊢
    · exact hQ.1 p q h hb
    · exact (eP H n).injective (pr_ext H h.1 hb (congrArg Fin.val h.2))
    · exact (eP H n).injective (pr_ext H h.1 h.2 (congrArg Fin.val hb))
  · rcases p with p | k | k
    · obtain ⟨q, hq1, hq2⟩ := hQ.2 p i hi
      exact ⟨.inl q, by simp [colF, hq1], hq2⟩
    · have h0 : ((eP H n k).2.2 : ℕ) < i := by
        have := (eP H n k).2.2.isLt
        have h' : ((eP H n k).2.1 : ℕ) < i := hi
        omega
      obtain ⟨q, hq⟩ := (eP H n).surjective ⟨(eP H n k).1, i, ⟨(eP H n k).2.2, h0⟩⟩
      have hq1 : tl H q = tl H k := by show (eP H n q).1.1 = _; rw [hq]; rfl
      have hq2 : rI H q = i := by show (eP H n q).2.1 = _; rw [hq]
      have hq3 : cI H q = cI H k := Fin.ext (by show ((eP H n q).2.2 : ℕ) = _; rw [hq]; rfl)
      exact ⟨.inr (.inl q), by simp [colF, hq1, hq3], by simp [bF, hq2]⟩
    · have h0 : ((Fin.rev i : Fin n) : ℕ) < (eP H n k).2.1 := by
        have := (eP H n k).2.2.isLt
        have h' : ((Fin.rev (cI H k) : Fin n) : ℕ) < i := hi
        have := i.isLt
        simp only [Fin.val_rev, cI] at h' ⊢
        omega
      obtain ⟨q, hq⟩ := (eP H n).surjective ⟨(eP H n k).1, (eP H n k).2.1, ⟨(Fin.rev i : Fin n), h0⟩⟩
      have hq1 : tl H q = tl H k := by show (eP H n q).1.1 = _; rw [hq]; rfl
      have hq2 : rI H q = rI H k := by show (eP H n q).2.1 = _; rw [hq]; rfl
      have hq3 : cI H q = Fin.rev i := Fin.ext (by show ((eP H n q).2.2 : ℕ) = _; rw [hq])
      exact ⟨.inr (.inr q), by simp [colF, hq1, hq2], by simp [bF, hq3]⟩
end PositivityTheory.Rg.Cz.KTy
