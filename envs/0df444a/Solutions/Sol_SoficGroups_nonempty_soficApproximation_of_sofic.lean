-- Prove2me | solution 1 for SoficGroups.nonempty_soficApproximation_of_sofic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/492f36e4-6a51-48e9-b2ac-740975914385

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_nonneg
import Theorems.Thm_SoficGroups_normalizedHamming_le_one

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    (G : Type*) [Group G] [Countable G] [Sofic G] :
    Nonempty (SoficApproximation G) := by
  classical
  let K : Set.FiniteExhaustion (Set.univ : Set G) :=
    Set.countable_univ.finiteExhaustion
  let F : ℕ → Finset G := fun n => (K.finite n).toFinset
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hε_pos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  have hε_lt (n : ℕ) : ε n < 1 := by
    dsimp [ε]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_lt_one (by linarith : (0 : ℝ) < n + 2)]
    linarith
  have hε_lim : Tendsto ε atTop (𝓝 0) := by
    simpa [ε, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 1)
  have hmem (g : G) : ∀ᶠ n in atTop, g ∈ F n := by
    have hg : g ∈ ⋃ n, K n := by
      rw [K.iUnion_eq]
      exact Set.mem_univ g
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    filter_upwards [eventually_ge_atTop i] with n hn
    exact (K.finite n).mem_toFinset.mpr (K.mono hn hi)
  have hchoose (n : ℕ) : ∃ M : PermutationModel G, GoodOn M (F n) (ε n) :=
    Sofic.approximation (F n) (ε n) (hε_pos n) (hε_lt n)
  let M : ℕ → PermutationModel G := fun n => (hchoose n).choose
  have hgood (n : ℕ) : GoodOn (M n) (F n) (ε n) :=
    (hchoose n).choose_spec
  refine ⟨{
    model := M
    multiplicative := ?_
    separated := ?_
  }⟩
  · intro g h
    refine squeeze_zero' (Eventually.of_forall fun n =>
      normalizedHamming_nonneg _ _) ?_ hε_lim
    filter_upwards [hmem g, hmem h] with n hg hh
    exact (hgood n).multiplicative g hg h hh |>.le
  · intro g hg
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using (tendsto_const_nhds.sub hε_lim))
      tendsto_const_nhds
    · filter_upwards [hmem g] with n hn
      exact ((hgood n).separated g hn hg).le
    · exact Eventually.of_forall fun n =>
        normalizedHamming_le_one _ _
end SoficGroups
