-- Prove2me | solution 1 for SRAudit.TwoPhase.Supplement.proposition_C_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:32.04998+00:00
-- url     : https://prove2.me/submissions/6ab86e07-43b7-4b05-8bd9-b643d875bb18

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_Production

open SRAudit
open SRAudit.TwoPhase
open SRAudit.TwoPhase.Supplement

open SRAudit.TwoPhase

theorem solution {ι : Type} [DecidableEq ι] (E : Demand) (hE : E.Standing) (M : ℝ)
    (hM : 0 < M) (g : Network ι) (hg : WellFormedNet g) (hnull : ¬ IsNullNet g)
    (e : ProdOutcome ι) (he : IsProdEq E g M e) :
    buyerProfit E e.p1 e.qc = E.β * e.qc ^ 2 := by
      have hβ : 0 < E.β := hE.1
      have hopt : IsBuyerOptimal E e.p1 e.qc := he.2.2.2.2.1
      let q : ℝ := (E.α - E.v0 - e.p1) / (2 * E.β)
      have hq : E.α = 2 * E.β * q + E.v0 + e.p1 := by
        dsimp [q]
        field_simp
        <;> nlinarith
      have hcomp := hopt q
      have hsq : E.β * (e.qc - q) ^ 2 ≤ 0 := by
        dsimp [buyerProfit] at hcomp
        rw [hq] at hcomp
        nlinarith [hcomp]
      have hsq' : (e.qc - q) ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hsq hβ
      have heq : e.qc = q := by
        nlinarith [sq_nonneg (e.qc - q)]
      unfold buyerProfit
      rw [hq, heq]
      ring
