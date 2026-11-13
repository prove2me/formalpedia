-- Prove2me | solution 1 for StabilityDichotomies.Solvability.nonisolated_variables_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:04:18.944668+00:00
-- url     : https://prove2.me/submissions/222cd8c6-7f8f-40da-8e45-b546101f16b5

import Definitions.Def_StabilityDichotomies_Solvability_Model
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (I : Instance Γ V) :
    (I.constraints.toFinset.biUnion fun c => Finset.univ.image c.scope).card ≤
      maxArity Γ * I.constraints.card := by
  calc
    _ ≤ ∑ c ∈ I.constraints.toFinset, (Finset.univ.image c.scope).card :=
      Finset.card_biUnion_le
    _ ≤ I.constraints.toFinset.card * maxArity Γ := by
      simpa using Finset.sum_le_card_nsmul I.constraints.toFinset
        (fun c => (Finset.univ.image c.scope).card) (maxArity Γ) (by
          intro c hc
          have h := Finset.card_image_le (s := Finset.univ) (f := c.scope)
          have hr : c.rel.val.arity ≤ maxArity Γ := Finset.le_sup c.rel.property
          simp only [Finset.card_univ, Fintype.card_fin] at h
          exact h.trans hr)
    _ ≤ I.constraints.card * maxArity Γ :=
      Nat.mul_le_mul_right _ I.constraints.toFinset_card_le
    _ = maxArity Γ * I.constraints.card := Nat.mul_comm _ _

