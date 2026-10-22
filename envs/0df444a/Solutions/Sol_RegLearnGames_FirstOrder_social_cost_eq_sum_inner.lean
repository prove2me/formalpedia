-- Prove2me | solution 1 for RegLearnGames.FirstOrder.social_cost_eq_sum_inner
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:26:13.364097+00:00
-- url     : https://prove2.me/submissions/6a37beb5-24b8-486b-ba02-b3f49180bcc7

import Mathlib
import Definitions.Def_RegLearnGames_FirstOrder_Setting

open Finset RegLearnGames.FirstOrder

/- Marginal decomposition, conditional costs, and deviation identities adapt
   carlok's accepted Theorem 23 proof, submission
   a048ba1b-9eac-472b-944a-ce1b514aca07, under Apache-2.0.
   This file exposes the exact captain-endorsed milestone conclusion. -/
namespace P2MFirstOrderSocial
open Finset
variable {n d : ℕ}
noncomputable def Pr (σ : Fin n → Fin d → ℝ) (i : Fin n) (r : {j // j ≠ i} → Fin d) : ℝ :=
  ∏ j : {j // j ≠ i}, σ j.1 (r j)

lemma decomp (σ : Fin n → Fin d → ℝ) (i : Fin n) (f : (Fin n → Fin d) → ℝ) :
    ∑ s, AGT.profileProb σ s * f s =
      ∑ a, σ i a * ∑ r, Pr σ i r * f ((Equiv.funSplitAt i (Fin d)).symm (a, r)) := by
  rw [← (Equiv.funSplitAt i (Fin d)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  unfold AGT.profileProb Pr
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  have h1 : (Equiv.funSplitAt i (Fin d)).symm (a, r) i = a := by
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have h2 : ∀ j : {j // j ≠ i}, (Equiv.funSplitAt i (Fin d)).symm (a, r) j.1 = r j := by
    intro j; simp [Equiv.funSplitAt, Equiv.piSplitAt, j.2]
  simp only [h1, h2]
  ring

lemma update_symm (i : Fin n) (a b : Fin d) (r : {j // j ≠ i} → Fin d) :
    Function.update ((Equiv.funSplitAt i (Fin d)).symm (a, r)) i b =
      (Equiv.funSplitAt i (Fin d)).symm (b, r) := by
  funext j
  by_cases h : j = i
  · subst h; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [Equiv.funSplitAt, Equiv.piSplitAt, h]

lemma Pr_update (σ : Fin n → Fin d → ℝ) (i : Fin n) (v : Fin d → ℝ) (r : {j // j ≠ i} → Fin d) :
    Pr (Function.update σ i v) i r = Pr σ i r := by
  unfold Pr
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Function.update_of_ne j.2]

noncomputable def K (c : Fin n → (Fin n → Fin d) → ℝ) (σ : Fin n → Fin d → ℝ) (i : Fin n)
    (x : Fin d) : ℝ :=
  ∑ r, Pr σ i r * c i ((Equiv.funSplitAt i (Fin d)).symm (x, r))

lemma costVec_eq (c : Fin n → (Fin n → Fin d) → ℝ) (σ : Fin n → Fin d → ℝ) (i : Fin n)
    (x : Fin d) : RegLearnGames.FirstOrder.costVec c σ i x = K c σ i x := by
  unfold RegLearnGames.FirstOrder.costVec AGT.expectedPayoff
  rw [decomp _ i]
  simp only [Function.update_self, Pr_update]
  rw [Finset.sum_eq_single x]
  · simp [K]
  · intro b _ hb; simp [hb]
  · simp

lemma dot_costVec (c : Fin n → (Fin n → Fin d) → ℝ) (σ : Fin n → Fin d → ℝ) (i : Fin n) :
    σ i ⬝ᵥ RegLearnGames.FirstOrder.costVec c σ i = AGT.expectedPayoff c σ i := by
  unfold AGT.expectedPayoff
  rw [decomp _ i]
  simp only [dotProduct, costVec_eq, K]

lemma dev_eq (c : Fin n → (Fin n → Fin d) → ℝ) (σ : Fin n → Fin d → ℝ) (i : Fin n)
    (hσ : ∑ a, σ i a = 1) (b : Fin d) :
    ∑ s, AGT.profileProb σ s * c i (Function.update s i b) =
      RegLearnGames.FirstOrder.costVec c σ i b := by
  rw [decomp _ i, costVec_eq]
  simp only [update_symm]
  rw [← Finset.sum_mul, hσ, one_mul]; rfl

end P2MFirstOrderSocial

open P2MFirstOrderSocial

theorem solution {n d : ℕ}
    (c : Fin n → (Fin n → Fin d) → ℝ)
    (w : ℕ → Fin n → Fin d → ℝ) (T : ℕ)
    (hw : ∀ t ∈ Finset.Icc 1 T, AGT.IsMixedProfile (w t)) :
    (∑ t ∈ Finset.Icc 1 T, socialCost c (w t)) =
      ∑ t ∈ Finset.Icc 1 T, ∑ i, (w t i) ⬝ᵥ (costVec c (w t) i) := by
  classical
  refine sum_congr rfl fun t _ => ?_
  simp only [dot_costVec]
  unfold socialCost socialCostPure AGT.expectedPayoff
  simp only [mul_sum]
  rw [sum_comm]
