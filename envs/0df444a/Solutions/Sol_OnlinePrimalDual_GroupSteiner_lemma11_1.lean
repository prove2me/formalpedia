-- Prove2me | solution 1 for OnlinePrimalDual.GroupSteiner.lemma11_1
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:17:52.828986+00:00
-- url     : https://prove2.me/submissions/b1db8843-95fb-4705-b9a1-d9ffd7bf9d28

import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover
import Definitions.Def_OnlinePrimalDual_GroupSteiner_marg
import Definitions.Def_OnlinePrimalDual_GroupSteiner_condProb
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RoundedTree

namespace OnlinePrimalDual.GroupSteiner

/-- Two edges: `0` incident to the root, `1` the child of `0`. -/
def aux_gs111_tr : RoundedTree (Fin 2) where
  parent := fun e => if e = 0 then none else some 0
  cost := fun _ => 0
  hcost_nonneg := fun _ => le_refl _

/-- The uniform distribution on the four subsets of `{0, 1}` (the two edges independent,
each present with probability `1/2`). -/
noncomputable def aux_gs111_rho : RandomCover (Fin 2) where
  p := fun _ => 1 / 4
  hp_nonneg := fun _ => by norm_num
  hp_sum := by
    rw [Finset.sum_const, Finset.card_univ]
    simp [Fintype.card_finset]

theorem aux_gs111_card1 (e : Fin 2) :
    (Finset.univ.filter (fun C : Finset (Fin 2) => e ∈ C)).card = 2 := by
  fin_cases e <;> decide

theorem aux_gs111_card2 :
    (Finset.univ.filter (fun C : Finset (Fin 2) => (1 : Fin 2) ∈ C ∧ (0 : Fin 2) ∈ C)).card
      = 1 := by
  decide

theorem aux_gs111_marg (e : Fin 2) : aux_gs111_rho.marg e = 1 / 2 := by
  unfold RandomCover.marg
  simp only [aux_gs111_rho]
  rw [Finset.sum_const, aux_gs111_card1]
  norm_num

theorem aux_gs111_cond : aux_gs111_rho.condProb 1 0 = 1 / 2 := by
  unfold RandomCover.condProb
  rw [aux_gs111_marg]
  simp only [aux_gs111_rho]
  rw [Finset.sum_const, aux_gs111_card2]
  norm_num

end OnlinePrimalDual.GroupSteiner

open OnlinePrimalDual.GroupSteiner

theorem solution : ¬ (∀ {E : Type} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (ρ : RandomCover E)
    (w w' δ : E → ℝ) (hδ_def : ∀ e, w' e = w e + δ e) (hδ_nonneg : ∀ e, 0 ≤ δ e)
    (hprev : ∀ e, δ e = 0 → ρ.marg e = w e)
    (hrule1 : ∀ e, δ e > 0 → w' e > 1 → ρ.marg e = 1)
    (hrule2 : ∀ e, δ e > 0 → w' e ≤ 1 →
      (tr.parent e = none ∨ ∃ p, tr.parent e = some p ∧ w' p > 1) →
      ρ.marg e = w' e)
    (hrule3 : ∀ e p, δ e > 0 → w' e ≤ 1 → tr.parent e = some p → w' p ≤ 1 →
      ρ.condProb e p = δ e / (w' p - w e)),
    (∀ e, w' e ≤ 1 → ρ.marg e = w' e) ∧ (∀ e, w e > 1 → ρ.marg e = 1)) := by
  intro H
  let δ : Fin 2 → ℝ := ![1 / 2, 1 / 4]
  have h := H aux_gs111_tr aux_gs111_rho (fun _ => 0) δ δ
    (fun e => by simp)
    (fun e => by fin_cases e <;> simp [δ])
    (fun e he => by fin_cases e <;> simp [δ] at he)
    (fun e _ he => by fin_cases e <;> simp [δ] at he <;> norm_num at he)
    (fun e _ _ hpar => by
      fin_cases e
      · rw [aux_gs111_marg]; simp [δ]
      · exfalso
        rcases hpar with hpar | ⟨p, hp, hp1⟩
        · simp [aux_gs111_tr] at hpar
        · have : p = 0 := by simp [aux_gs111_tr] at hp; exact hp.symm
          subst this
          simp [δ] at hp1; norm_num at hp1)
    (fun e p _ _ hpar _ => by
      fin_cases e
      · simp [aux_gs111_tr] at hpar
      · have : p = 0 := by simp [aux_gs111_tr] at hpar; exact hpar.symm
        subst this
        simp only [Fin.mk_one]
        rw [aux_gs111_cond]
        simp [δ]
        norm_num)
  have h1 := h.1 1 (by simp [δ]; norm_num)
  rw [aux_gs111_marg] at h1
  simp [δ] at h1
