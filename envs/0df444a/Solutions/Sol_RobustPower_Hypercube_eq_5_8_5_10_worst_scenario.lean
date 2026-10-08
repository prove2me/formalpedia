-- Prove2me | solution 1 for RobustPower.Hypercube.eq_5_8_5_10_worst_scenario
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:56:05.830425+00:00
-- url     : https://prove2.me/submissions/fd9d75da-b9e4-49a3-ad04-9f72859e6987

import Definitions.Def_RobustPower_Hypercube_DataBox

open RobustPower.Hypercube

theorem solution
    {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Ω → Matrix (Fin m) (Fin n₁) ℝ)
    (B : Ω → Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (d : Ω → Fin n₂ → ℝ)
    (hU : IsHypercube (uncertaintySet A B b d)) :
    ∃ ωbar : Ω,
      (∀ ω i j, A ωbar i j ≤ A ω i j) ∧
      (∀ ω i j, B ωbar i j ≤ B ω i j) ∧
      (∀ ω i, b ω i ≤ b ωbar i) ∧
      (∀ ω j, d ω j ≤ d ωbar j) := by
  rcases hU with ⟨l, u, hlu, hbox⟩
  let corner : ScenarioData m n₁ n₂ := ⟨l.A, l.B, u.b, u.d⟩
  have hcorner : corner ∈ dataBox l u :=
    ⟨⟨fun _ _ => le_rfl, fun _ _ => le_rfl, hlu.2.2.1, hlu.2.2.2⟩,
      ⟨hlu.1, hlu.2.1, fun _ => le_rfl, fun _ => le_rfl⟩⟩
  rw [← hbox] at hcorner
  rcases hcorner with ⟨ωbar, hωbar⟩
  have hA : A ωbar = l.A := congrArg ScenarioData.A hωbar
  have hB : B ωbar = l.B := congrArg ScenarioData.B hωbar
  have hb : b ωbar = u.b := congrArg ScenarioData.b hωbar
  have hd : d ωbar = u.d := congrArg ScenarioData.d hωbar
  have hbounds (ω : Ω) :
      (⟨A ω, B ω, b ω, d ω⟩ : ScenarioData m n₁ n₂) ∈ dataBox l u := by
    rw [← hbox]
    exact ⟨ω, rfl⟩
  refine ⟨ωbar, ?_, ?_, ?_, ?_⟩
  · intro ω i j
    rw [hA]
    exact (hbounds ω).1.1 i j
  · intro ω i j
    rw [hB]
    exact (hbounds ω).1.2.1 i j
  · intro ω i
    rw [hb]
    exact (hbounds ω).2.2.2.1 i
  · intro ω j
    rw [hd]
    exact (hbounds ω).2.2.2.2 j
