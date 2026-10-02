-- Prove2me | solution 1 for ProcessingNetworks.ProportionalFairness.standard_load_condition_iff_gamma_lt_a
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:38:09.302869+00:00
-- url     : https://prove2.me/submissions/9ee38d56-ef8d-4a0e-bc76-6937d86154af

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_FluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_Aggregation

set_option autoImplicit false

/-! The target's statement defines `StandardLoadCondition` inline (no Definitions bundle). A
solution may not import its own target module, and redeclaring the same name would clash with
it, so the statement below uses a local alias with an IDENTICAL body under a distinct namespace;
it is definitionally equal to the target's constant.

Counterexample: `hAtil` only pins the columns of `Atil` for groups in the range of `grp`.
Take `I = K = 1`, `L = 2`, `grp 0 = 0`, `Amat = [1]`, `b = [1]`, `Atil = [1, -10]`,
`lam = 2`, `m = 1`, `P = 0` (so `α = 2`). Then `A(α m) = 2 ≮ 1`, yet `a = (3, 1)` lies in
`Ã = {y ≥ 0 | Ãy ≤ b}` (`3 - 10 ≤ 1`) and `γ = (2, 0) < a`. -/

open ProcessingNetworks.ProportionalFairness

namespace PNPFDpSol

abbrev StandardLoadCondition {I K : ℕ} (Amat : Matrix (Fin K) (Fin I) ℝ) (bvec : Fin K → ℝ)
    (alpha m : Fin I → ℝ) : Prop :=
  ∀ k, (Amat.mulVec (fun i => alpha i * m i)) k < bvec k

/-- The reduced allocation set of the counterexample. -/
def cexAtil : Matrix (Fin 1) (Fin 2) ℝ := fun _ ℓ => if ℓ = 0 then 1 else -10

/-- The capacity consumption matrix of the counterexample. -/
def cexA : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1

/-- The capacities of the counterexample. -/
def cexB : Fin 1 → ℝ := fun _ => 1

/-- The total arrival rates of the counterexample. -/
def cexAlpha : Fin 1 → ℝ := fun _ => 2

/-- Counterexample network data. -/
noncomputable def cexDat : PFUnitaryNetworkData 1 2 where
  lam := fun _ => 2
  m := fun _ => 1
  hm := fun _ => one_pos
  P := 0
  grp := fun _ => 0
  TildeAllocSet := {y | (∀ ℓ, 0 ≤ y ℓ) ∧ ∀ k, (cexAtil.mulVec y) k ≤ (fun _ => (1 : ℝ)) k}

theorem cex_false :
    ¬ ((StandardLoadCondition cexA cexB cexAlpha cexDat.m ↔
      ∃ a ∈ cexDat.TildeAllocSet, ∀ ℓ,
        groupAggregate cexDat.grp (fun i => cexAlpha i * cexDat.m i) ℓ < a ℓ)) := by
  intro h
  have hrhs : ∃ a ∈ cexDat.TildeAllocSet, ∀ ℓ,
      groupAggregate cexDat.grp (fun i => cexAlpha i * cexDat.m i) ℓ < a ℓ := by
    refine ⟨![3, 1], ⟨?_, ?_⟩, ?_⟩
    · intro ℓ; fin_cases ℓ <;> norm_num
    · intro k
      simp [cexAtil, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      norm_num
    · intro ℓ
      fin_cases ℓ <;> simp [groupAggregate, cexDat, cexAlpha] <;> norm_num
  have hl := h.mpr hrhs 0
  simp [Matrix.mulVec, dotProduct, cexDat, cexA, cexB, cexAlpha] at hl

end PNPFDpSol

open PNPFDpSol in
theorem solution : ¬ (∀ {I L K : ℕ} (dat : PFUnitaryNetworkData I L)
    (Amat : Matrix (Fin K) (Fin I) ℝ) (bvec : Fin K → ℝ) (Atil : Matrix (Fin K) (Fin L) ℝ)
    (hA : ∀ k i, 0 ≤ Amat k i) (hb : ∀ k, 0 < bvec k)
    (hgrp : ∀ i j, dat.grp i = dat.grp j ↔ ∀ k, Amat k i = Amat k j)
    (hAtil : ∀ k i, Atil k (dat.grp i) = Amat k i)
    (hTilde : dat.TildeAllocSet = {y | (∀ ℓ, 0 ≤ y ℓ) ∧ ∀ k, (Atil.mulVec y) k ≤ bvec k})
    (alpha : Fin I → ℝ) (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 ≤ alpha i),
    StandardLoadCondition Amat bvec alpha dat.m ↔
      ∃ a ∈ dat.TildeAllocSet, ∀ ℓ, groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ < a ℓ) := by
  intro h
  refine PNPFDpSol.cex_false (h cexDat cexA cexB cexAtil
    (fun _ _ => zero_le_one) (fun _ => one_pos) ?_ ?_ rfl cexAlpha ?_
    (fun _ => zero_le_two))
  · intro i j
    exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  · intro k i
    simp [cexAtil, cexDat, cexA]
  · funext i
    norm_num [IsTotalArrivalRates, cexDat, cexAlpha]
