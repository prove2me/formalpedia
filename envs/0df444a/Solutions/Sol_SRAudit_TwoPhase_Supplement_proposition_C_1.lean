-- Prove2me | solution 1 for SRAudit.TwoPhase.Supplement.proposition_C_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:35:42.341413+00:00
-- url     : https://prove2.me/submissions/ee24615e-73d9-4038-bb01-024d2ec5c9f0

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_Production

open SRAudit
open SRAudit.TwoPhase
open SRAudit.TwoPhase.Supplement

open SRAudit.TwoPhase

theorem solution (E : Demand) (hE : E.Standing) :
    (∀ p1 : ℝ, ∃! qc : ℝ, IsBuyerOptimal E p1 qc) ∧
    (∀ p1 qc : ℝ, IsBuyerOptimal E p1 qc ↔ p1 = E.α - E.v0 - 2 * E.β * qc) ∧
    (∀ qc : ℝ, invDemand1 E qc = E.α - E.v0 - 2 * E.β * qc) := by
      have hb : 0 < E.β := hE.1
      have key : ∀ p1 qc : ℝ, IsBuyerOptimal E p1 qc ↔ p1 = E.α - E.v0 - 2 * E.β * qc := by
        intro p1 qc
        constructor
        · intro h
          set d := E.α - E.v0 - p1 - 2 * E.β * qc with hd
          have h1 := h (qc + d / (2 * E.β))
          unfold buyerProfit at h1
          have e : (E.α - E.β * (qc + d / (2 * E.β)) - E.v0 - p1) * (qc + d / (2 * E.β))
              - (E.α - E.β * qc - E.v0 - p1) * qc = d ^ 2 / (4 * E.β) := by
            field_simp
            rw [hd]; ring
          have h2 : d ^ 2 / (4 * E.β) ≤ 0 := by linarith
          have h3 : d ^ 2 ≤ 0 := by
            have := (div_le_iff₀ (by positivity : (0:ℝ) < 4 * E.β)).1 h2
            linarith
          have : d = 0 := by nlinarith [sq_nonneg d]
          linarith
        · intro h q
          unfold buyerProfit
          subst h
          nlinarith [sq_nonneg (q - qc), hb]
      refine ⟨?_, key, ?_⟩
      · intro p1
        refine ⟨(E.α - E.v0 - p1) / (2 * E.β), ?_, ?_⟩
        · show IsBuyerOptimal E p1 _
          rw [key]; field_simp; ring
        · intro y hy
          rw [key] at hy
          field_simp
          linarith
      · intro qc
        have hex : ∃! p1 : ℝ, IsBuyerOptimal E p1 qc :=
          ⟨E.α - E.v0 - 2 * E.β * qc, (key _ _).2 rfl, fun y hy => (key _ _).1 hy⟩
        unfold invDemand1
        rw [dif_pos hex]
        exact (key _ _).1 hex.exists.choose_spec
