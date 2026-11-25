-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.KTy.cnt2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:47:22.783816+00:00
-- url     : https://prove2.me/submissions/0528abb5-a402-443c-9c38-a8b8bba02436

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_card_filter_comp
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_sumFin
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_sumRange
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
theorem _root_.solution (bar : ι → ι) (hinv : ∀ τ, bar (bar τ) = τ) (τ : ι) (i : Fin n) :
    (Finset.univ.filter fun k => bar (tl H k) = τ ∧ Fin.rev (cI H k) = i).card = if bar τ ∈ H then (i : ℕ) else 0 := by
  have hc : ∀ k, (bar (tl H k) = τ ∧ Fin.rev (cI H k) = i) ↔
      ((eP H n k).1 : ι) = bar τ ∧ ((eP H n k).2.2 : ℕ) = (Fin.rev i : ℕ) := by
    intro k
    have e1 : bar (tl H k) = τ ↔ tl H k = bar τ := ⟨fun h => by rw [← h, hinv], fun h => by rw [h, hinv]⟩
    have e2 : Fin.rev (cI H k) = i ↔ cI H k = Fin.rev i :=
      ⟨fun h => by rw [← h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
    rw [e1, e2, Fin.ext_iff]
    rfl
  rw [Finset.filter_congr (fun k _ => hc k)]
  refine (card_filter_comp (eP H n) (fun x => (x.1 : ι) = bar τ ∧ (x.2.2 : ℕ) = (Fin.rev i : ℕ))).trans ?_
  rw [Finset.card_filter, Fintype.sum_sigma]
  simp only [Fintype.sum_sigma, ite_and]
  have hj : ∑ j : Fin n, (if (Fin.rev i : ℕ) < j then 1 else 0 : ℕ) = i := by
    rw [Fin.sum_univ_eq_sum_range (fun j => if (Fin.rev i : ℕ) < j then 1 else 0) n, sumRange]
    simp only [Fin.val_rev]
    omega
  rw [Finset.sum_congr rfl (g := fun x : H => if (x : ι) = bar τ then (i : ℕ) else 0) (fun x _ => ?_)]
  · rw [Finset.sum_coe_sort H (fun x => if x = bar τ then (i : ℕ) else 0), Finset.sum_ite_eq']
  · by_cases h : (x : ι) = bar τ
    · simp only [h, if_true]
      simp only [sumFin, hj]
    · simp [h]
end PositivityTheory.Rg.Cz.KTy
