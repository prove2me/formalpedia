-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.prod_ofFn_split_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:21.932095+00:00
-- url     : https://prove2.me/submissions/529d0692-ae02-49cf-bd6a-91e417b156c6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ColAnti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
omit [Algebra ℂ 𝒰]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {p : ℕ} (f : Fin (p + 1) → 𝒰) (j : Fin p) : ∃ P Q : 𝒰, ∀ g : Fin (p + 1) → 𝒰,
    (∀ m, m ≠ j.castSucc → m ≠ j.succ → g m = f m) →
      (List.ofFn g).prod = P * g j.castSucc * g j.succ * Q := by
  induction p with
  | zero => exact j.elim0
  | succ q ih =>
    cases j using Fin.cases with
    | zero =>
      refine ⟨1, (List.ofFn fun m : Fin q => f m.succ.succ).prod, fun g hg => ?_⟩
      have hr : (List.ofFn fun m : Fin q => g m.succ.succ) = List.ofFn fun m : Fin q => f m.succ.succ := by
        congr 1
        funext m
        apply hg
        · intro h; have := congrArg Fin.val h; simp at this
        · intro h; have := congrArg Fin.val h; simp at this
      simp only [List.ofFn_succ, List.prod_cons]
      rw [hr]
      simp [mul_assoc]
    | succ j' =>
      obtain ⟨P', Q', hPQ⟩ := ih (fun m => f m.succ) j'
      refine ⟨f 0 * P', Q', fun g hg => ?_⟩
      have h0 : g 0 = f 0 := hg 0
        (by intro h; have := congrArg Fin.val h; simp at this)
        (by intro h; have := congrArg Fin.val h; simp at this)
      have hc : j'.castSucc.succ = j'.succ.castSucc := Fin.ext (by simp)
      have h' := hPQ (fun m => g m.succ) (fun m hm1 hm2 =>
        hg m.succ (fun h => hm1 (Fin.succ_injective _ (h.trans hc.symm)))
          (fun h => hm2 (Fin.succ_injective _ h)))
      try dsimp only at h'
      rw [List.ofFn_succ, List.prod_cons, h', h0, hc]
      simp only [mul_assoc]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
