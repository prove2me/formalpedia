-- Prove2me | solution 1 for PebblingLean.FiniteProbability.uniformProbability_exists_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:49.124558+00:00
-- url     : https://prove2.me/submissions/d7badb5c-596b-43ed-9826-81df286a1a4b

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω ι : Type*}
namespace PebblingLean.FiniteProbability
theorem _root_.solution [Fintype Ω] [Nonempty Ω]
    [Fintype ι] (P : ι → Ω → Prop)
    [∀ i, DecidablePred (P i)]
    [DecidablePred fun ω => ∃ i : ι, P i ω] :
    uniformProbability (fun ω : Ω => ∃ i : ι, P i ω) ≤
      ∑ i : ι, uniformProbability (P i) := by
  classical
  let bad : Finset Ω := Finset.univ.filter fun ω : Ω => ∃ i : ι, P i ω
  let badAt : ι → Finset Ω := fun i => Finset.univ.filter fun ω : Ω => P i ω
  have hsubset : bad ⊆ Finset.univ.biUnion badAt := by
    intro ω hω
    have hex : ∃ i : ι, P i ω := by
      simpa [bad] using hω
    rcases hex with ⟨i, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [badAt, hi]⟩
  have hcard :
      bad.card ≤ ∑ i : ι, (badAt i).card := by
    exact (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
  have hden_nonneg : 0 ≤ (Fintype.card Ω : ℚ) := by positivity
  calc
    uniformProbability (fun ω : Ω => ∃ i : ι, P i ω)
        = (bad.card : ℚ) / (Fintype.card Ω : ℚ) := by
          rfl
    _ ≤ ((∑ i : ι, (badAt i).card : ℕ) : ℚ) / (Fintype.card Ω : ℚ) := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden_nonneg
    _ = ∑ i : ι, uniformProbability (P i) := by
          simp [uniformProbability, badAt, Finset.sum_div]
end PebblingLean.FiniteProbability
