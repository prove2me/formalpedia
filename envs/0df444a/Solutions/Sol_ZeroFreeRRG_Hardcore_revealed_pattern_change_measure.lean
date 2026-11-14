-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.revealed_pattern_change_measure
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:19:58.438971+00:00
-- url     : https://prove2.me/submissions/1630dd36-f3b6-4c55-877f-f63b218c58d5

import Theorems.Thm_ZeroFreeRRG_Hardcore_finite_observation_change_measure
import Theorems.Thm_ZeroFreeRRG_Hardcore_replica_reveal_density_bound_nonnegative
import Mathlib
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (t : ℝ) (d n : ℕ) (M : Matching n d)
    (U : Finset (Fin n)) (a₀ : m.Spin) (B : ℝ)
    (H : ({v : Fin n // v ∈ U} → m.Spin) → ({v : Fin n // v ∈ U} → m.Spin) → Prop)
    (hπ : ∀ a, 0 < m.pi t a) (hnonneg : ∀ σ, 0 ≤ gibbs m t M σ) :
    let obs := fun (σ : Fin n → m.Spin) (v : {v : Fin n // v ∈ U}) => σ v.1
    let extend := fun (y : {v : Fin n // v ∈ U} → m.Spin) (v : Fin n) =>
      if h : v ∈ U then y ⟨v,h⟩ else a₀
    let prior := fun y => ∏ v ∈ U, m.pi t (extend y v)
    (∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin,
      if H (obs σ) (obs σ') ∧ pinnedLL m t M σ U + pinnedLL m t M σ' U ≤ B then
        gibbs m t M σ * gibbs m t M σ' else 0) ≤
      Real.exp B * ∑ y, ∑ y', if H y y' then prior y * prior y' else 0 := by
  classical
  dsimp only
  let X := Fin n → m.Spin
  let Y := {v : Fin n // v ∈ U} → m.Spin
  letI : DecidableEq Y := Classical.decEq Y
  let obs : X → Y := fun σ v => σ v.1
  let extend : Y → X := fun y v => if h : v ∈ U then y ⟨v,h⟩ else a₀
  let prior : Y → ℝ := fun y => ∏ v ∈ U, m.pi t (extend y v)
  let Good : Y → Y → Prop := fun y y' =>
    pinnedLL m t M (extend y) U + pinnedLL m t M (extend y') U ≤ B
  have hext (y : Y) : obs (extend y) = y := by
    funext v
    simp [obs,extend,v.2]
  have hmatch (σ : X) (v : Fin n) (hv : v ∈ U) : extend (obs σ) v = σ v := by
    simp [extend,obs,hv]
  have hmatch' (y : Y) (v : Fin n) (hv : v ∈ U) : extend y v = y ⟨v,hv⟩ := by
    simp [extend,hv]
  have hfilters (σ : X) :
      Finset.univ.filter (fun τ : X => ∀ v ∈ U, τ v = σ v) =
        Finset.univ.filter (fun τ : X => obs τ = obs σ) := by
    ext τ
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro h
      funext v
      exact h v.1 v.2
    · intro h v hv
      exact congrFun h ⟨v,hv⟩
  have hMarg (σ : X) : gibbsMarg m t M σ U =
      ∑ τ ∈ Finset.univ.filter (fun τ : X => obs τ = obs σ), gibbs m t M τ := by
    unfold gibbsMarg
    rw [hfilters]
  have hLL (σ : X) : pinnedLL m t M σ U = pinnedLL m t M (extend (obs σ)) U := by
    unfold pinnedLL
    have hG : gibbsMarg m t M σ U = gibbsMarg m t M (extend (obs σ)) U := by
      rw [hMarg,hMarg,hext]
    have hs : (∑ v ∈ U, Real.log (m.pi t (σ v))) =
        (∑ v ∈ U, Real.log (m.pi t (extend (obs σ) v))) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [hmatch σ v hv]
    rw [hG,hs]
  have hq (y : Y) : 0 ≤ prior y := (Finset.prod_pos fun v hv => hπ (extend y v)).le
  have hdensity (y y' : Y) (hy : H y y') (hg : Good y y') :
      (∑ σ ∈ Finset.univ.filter (fun σ : X => obs σ = y), gibbs m t M σ) *
      (∑ σ ∈ Finset.univ.filter (fun σ : X => obs σ = y'), gibbs m t M σ) ≤
        Real.exp B * (prior y * prior y') := by
    have hh := replica_reveal_density_bound_nonnegative m t d n M (extend y) (extend y') U B hπ hnonneg hg
    rw [hMarg,hMarg,hext,hext] at hh
    exact hh
  have hh := finite_observation_change_measure (X := X) (Y := Y) obs (gibbs m t M) prior H Good (Real.exp B)
    (Real.exp_pos B).le hq (by
      intro y y' hy hg
      simpa only using hdensity y y' hy hg)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.sum_congr rfl
  intro σ' hσ'
  dsimp [Good]
  simp only [←hLL σ, ←hLL σ', obs]
