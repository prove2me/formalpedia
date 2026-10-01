-- Prove2me | solution 1 for RobustMDP.Stationarity.stationaryPolicy_nature_stationary
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:11:10.913101+00:00
-- url     : https://prove2.me/submissions/81d3b43c-ccde-4529-8f44-d9f74e8eb44d

import Theorems.Thm_RobustMDP_Stationarity_stationary_policies_suffice
import Mathlib.Tactic
open RobustMDP.Stationarity
namespace CStationary

theorem inf_congr {n : ℕ} {A B : Type} (M : Model n A) (M' : Model n B) (ν : ℝ) (i₀ : Fin n)
    (π : Policy n A) (π' : Policy n B) (τ : M.NaturePolicy) (τ' : M'.NaturePolicy)
    (hc : ∀ t i, M.cost i (π t i)=M'.cost i (π' t i))
    (hp : ∀ t i, (τ t).1 (π t i) i=(τ' t).1 (π' t i) i) :
    M.infCost ν i₀ π τ=M'.infCost ν i₀ π' τ' := by
  have hstate : ∀ t, M.stateDist i₀ π τ t=M'.stateDist i₀ π' τ' t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      funext j
      simp only [Model.stateDist,ih]
      exact Finset.sum_congr rfl (fun i _ => by rw [hp])
  simp only [Model.infCost,Model.stageCost,hstate,hc]

theorem sup_eq_of_maps {I J : Type*} (f : I → ℝ) (g : J → ℝ)
    (r : I → J) (e : J → I) (hr : ∀ i, f i=g (r i)) (he : ∀ j, f (e j)=g j) :
    (⨆ i, f i)=⨆ j, g j := by
  have hh : Set.range f=Set.range g := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨r i,(hr i).symm⟩
    · rintro ⟨j,rfl⟩
      exact ⟨e j,he j⟩
  exact congrArg sSup hh
end CStationary

theorem solution {n : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n A) (ν : ℝ) (hν₀ : 0 < ν) (hν₁ : ν < 1) (i₀ : Fin n) :
    (∀ π : Fin n → A,
      (⨆ τ : M.NaturePolicy, M.infCost ν i₀ (fun _ => π) τ)=
        ⨆ P : M.Choice, M.infCost ν i₀ (fun _ => π) (fun _ => P)) ∧
      M.phiInf_PsT ν i₀=M.phiInf_PsTs ν i₀ := by
  classical
  refine ⟨?_,(stationary_policies_suffice M ν hν₀ hν₁ i₀).1.2.1.symm⟩
  intro π
  let M' : Model n Unit := {
    cost := fun i _ => M.cost i (π i)
    rows := fun _ i => M.rows (π i) i
    cost_nonneg := fun i _ => M.cost_nonneg i (π i)
    rows_subset_simplex := fun _ i => M.rows_subset_simplex (π i) i
    rows_nonempty := fun _ i => M.rows_nonempty (π i) i }
  let π' : Policy n Unit := fun _ _ => ()
  let r : M.Choice → M'.Choice := fun P => ⟨fun _ i => P.1 (π i) i,fun _ i => P.2 (π i) i⟩
  let e : M'.Choice → M.Choice := fun P =>
    ⟨fun a i => if a=π i then P.1 () i else (M.rows_nonempty a i).choose,by
      intro a i
      dsimp only
      split_ifs with h
      · subst a
        exact P.2 () i
      · exact (M.rows_nonempty a i).choose_spec⟩
  have hr : ∀ τ : M.NaturePolicy, M.infCost ν i₀ (fun _ => π) τ=M'.infCost ν i₀ π' (fun t => r (τ t)) := by
    intro τ
    exact CStationary.inf_congr M M' ν i₀ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)
  have he : ∀ τ : M'.NaturePolicy, M.infCost ν i₀ (fun _ => π) (fun t => e (τ t))=M'.infCost ν i₀ π' τ := by
    intro τ
    apply CStationary.inf_congr M M' ν i₀ _ _ _ _ (fun _ _ => rfl)
    intro t i
    simp [e,π']
  have htv := CStationary.sup_eq_of_maps (fun τ : M.NaturePolicy => M.infCost ν i₀ (fun _ => π) τ)
    (fun τ : M'.NaturePolicy => M'.infCost ν i₀ π' τ) (fun τ t => r (τ t)) (fun τ t => e (τ t)) hr he
  have hst := CStationary.sup_eq_of_maps (fun P : M.Choice => M.infCost ν i₀ (fun _ => π) (fun _ => P))
    (fun P : M'.Choice => M'.infCost ν i₀ π' (fun _ => P)) r e (fun P => hr (fun _ => P)) (fun P => he (fun _ => P))
  rw [htv,hst]
  have h := (stationary_policies_suffice M' ν hν₀ hν₁ i₀).1.1
  have hall : ∀ ρ : Policy n Unit, ρ=π' := fun ρ => Subsingleton.elim _ _
  have hall' : ∀ ρ : Fin n → Unit, (fun _ : ℕ => ρ)=π' := fun ρ => Subsingleton.elim _ _
  simpa only [Model.phiInf_PT,Model.phiInf_PsTs,hall,hall',ciInf_const] using h
