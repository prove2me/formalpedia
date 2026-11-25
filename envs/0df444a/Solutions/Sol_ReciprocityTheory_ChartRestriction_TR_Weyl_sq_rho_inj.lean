-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.sq_rho_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:07.912388+00:00
-- url     : https://prove2.me/submissions/354e0cc3-15a1-414e-9949-09bccbfdd0ed

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqCharA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_intl_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution {k : ℕ} (μ : Fin (k + 1) → ℤ) : Function.Injective (sq_rho μ) := by
  intro f f' h
  have h0 : sq_restr f.1 = sq_restr f'.1 := congrArg Subtype.val h
  obtain ⟨f, hI, hs⟩ := f
  obtain ⟨f', hI', hs'⟩ := f'
  simp only at h0
  have hc : ∀ a t : Fin k, f a.castSucc t.castSucc = f' a.castSucc t.castSucc :=
    fun a t => congrFun (congrFun h0 a) t
  have hz : ∀ a : Fin k, f a.castSucc (Fin.last k) = f' a.castSucc (Fin.last k) := by
    intro a
    rw [sq_intl_zero f hI k (Fin.last k) rfl a.castSucc (by simp),
      sq_intl_zero f' hI' k (Fin.last k) rfl a.castSucc (by simp)]
  have hup : ∀ (a : Fin k) (t : Fin (k + 1)), f a.castSucc t = f' a.castSucc t := by
    intro a t
    induction t using Fin.lastCases with
    | last => exact hz a
    | cast t => exact hc a t
  apply Subtype.ext
  funext a t
  induction a using Fin.lastCases with
  | cast a => exact hup a t
  | last =>
    have h1 := hs t
    have h2 := hs' t
    rw [Fin.sum_univ_castSucc] at h1 h2
    have h3 : ∑ a : Fin k, f a.castSucc t = ∑ a : Fin k, f' a.castSucc t :=
      Finset.sum_congr rfl fun a _ => hup a t
    rw [h3] at h1
    have h4 := h1.trans h2.symm
    have h5 : (∑ a : Fin k, f' a.castSucc t) + f (Fin.last k) t =
        (∑ a : Fin k, f' a.castSucc t) + f' (Fin.last k) t := by
      exact_mod_cast h4
    exact Nat.add_left_cancel h5
end ReciprocityTheory.ChartRestriction.TR.Weyl
