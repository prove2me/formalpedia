-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.force_spins_fiber_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:10:52.995348+00:00
-- url     : https://prove2.me/submissions/ed806068-ccef-412f-aa13-5b70af56d6cd

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem solution {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]
    (S : Finset V) (a₀ : A) (τ : V → A) :
    ((Finset.univ : Finset (V → A)).filter
      (fun σ => (fun v => if v ∈ S then a₀ else σ v) = τ)).card ≤
      (Fintype.card A) ^ S.card := by
  classical
  let F := (Finset.univ : Finset (V → A)).filter
      (fun σ => (fun v => if v ∈ S then a₀ else σ v) = τ)
  let r : (V → A) → (S → A) := fun σ v => σ v.1
  have hinj : Set.InjOn r F := by
    intro σ hσ σ' hσ' heq
    have hσf := (Finset.mem_filter.mp hσ).2
    have hσ'f := (Finset.mem_filter.mp hσ').2
    funext v
    by_cases hv : v ∈ S
    · exact congrFun heq ⟨v, hv⟩
    · have h1 := congrFun hσf v
      have h2 := congrFun hσ'f v
      simp only [hv, ↓reduceIte] at h1 h2
      exact h1.trans h2.symm
  have h := Finset.card_le_card_of_injOn (s := F) (t := (Finset.univ : Finset (S → A)))
      r (by intro x hx; simp) hinj
  simpa [F, Fintype.card_fun] using h
