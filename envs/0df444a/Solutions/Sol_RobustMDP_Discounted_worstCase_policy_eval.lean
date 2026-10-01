-- Prove2me | solution 1 for RobustMDP.Discounted.worstCase_policy_eval
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:16:28.584788+00:00
-- url     : https://prove2.me/submissions/48268a12-ee90-4a0b-bb5a-8a31584e8527

import Theorems.Thm_RobustMDP_Discounted_robust_bellman_recursion
import Mathlib.Tactic
open RobustMDP.Discounted

namespace CDiscounted

theorem cost_congr {n : ℕ} {A B : Type} (M : Model n A) (M' : Model n B) (i₀ : Fin n)
    (π : StationaryPolicy n A) (π' : StationaryPolicy n B)
    (P : M.StationaryNature) (P' : M'.StationaryNature)
    (hd : M.discount=M'.discount)
    (hc : ∀ i, M.cost i (π i)=M'.cost i (π' i))
    (hp : ∀ i, P.1 (π i) i=P'.1 (π' i) i) :
    M.discountedCost i₀ π P=M'.discountedCost i₀ π' P' := by
  have hs : ∀ t, stateDist π P.1 i₀ t=stateDist π' P'.1 i₀ t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      funext j
      simp only [stateDist,ih]
      exact Finset.sum_congr rfl (fun i _ => by rw [hp])
  simp only [Model.discountedCost,hs,hc,hd]
end CDiscounted

theorem solution {n : ℕ} {A : Type} (M : Model n A) (i₀ : Fin n)
    (π : StationaryPolicy n A) :
    ∃ vπ : Fin n → ℝ,
      M.policyOp π vπ=vπ ∧ (∀ w, M.policyOp π w=w → w=vπ) ∧
      IsLUB (Set.range fun P : M.StationaryNature => M.discountedCost i₀ π P) (vπ i₀) := by
  classical
  let M' : Model n Unit := {
    cost := fun i _ => M.cost i (π i)
    discount := M.discount
    rows := fun _ i => M.rows (π i) i
    cost_nonneg := fun i _ => M.cost_nonneg i (π i)
    discount_nonneg := M.discount_nonneg
    discount_lt_one := M.discount_lt_one
    rows_subset_simplex := fun _ i => M.rows_subset_simplex (π i) i
    rows_nonempty := fun _ i => M.rows_nonempty (π i) i }
  let π' : StationaryPolicy n Unit := fun _ => ()
  let r : M.StationaryNature → M'.StationaryNature := fun P =>
    ⟨fun _ i => P.1 (π i) i,fun _ i => P.2 (π i) i⟩
  let e : M'.StationaryNature → M.StationaryNature := fun P =>
    ⟨fun a i => if a=π i then P.1 () i else (M.rows_nonempty a i).choose,by
      intro a i
      dsimp only
      split_ifs with h
      · subst a
        exact P.2 () i
      · exact (M.rows_nonempty a i).choose_spec⟩
  have hr : ∀ P : M.StationaryNature, M.discountedCost i₀ π P=M'.discountedCost i₀ π' (r P) := by
    intro P
    exact CDiscounted.cost_congr M M' i₀ _ _ _ _ rfl (fun _ => rfl) (fun _ => rfl)
  have he : ∀ P : M'.StationaryNature, M.discountedCost i₀ π (e P)=M'.discountedCost i₀ π' P := by
    intro P
    apply CDiscounted.cost_congr M M' i₀ _ _ _ _ rfl (fun _ => rfl)
    intro i
    simp [e,π']
  have hop : M.policyOp π=M'.policyOp π' := rfl
  obtain ⟨v,hv⟩ := robust_bellman_recursion M' i₀
  obtain ⟨w,hw⟩ := hv.2.2.2.2.2 π'
  refine ⟨w,hop ▸ hw.1,?_,?_⟩
  · intro z hz
    exact hw.2.1 z (hop ▸ hz)
  · have hh : Set.range (fun P : M.StationaryNature => M.discountedCost i₀ π P)=
        Set.range (fun P : M'.StationaryNature => M'.discountedCost i₀ π' P) := by
      ext x
      constructor
      · rintro ⟨P,rfl⟩
        exact ⟨r P,(hr P).symm⟩
      · rintro ⟨P,rfl⟩
        exact ⟨e P,he P⟩
    rw [hh]
    exact hw.2.2
