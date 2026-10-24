-- Prove2me | solution 1 for ObfImpossibility.RiceSimulator.stage_answer_exists
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T10:59:50.483124+00:00
-- url     : https://prove2.me/submissions/3a0b9f92-7654-4475-80ff-d173f099d9e8

import Mathlib
import Definitions.Def_ObfImpossibility_RiceSimulator_Setting
namespace ObfImpossibility.RiceSimulator

/-- Fact (3), p. A:41: if `[M] ≢ [N]` then there is `n'` such that `N` is not
`n`-compatible with `M` for all `n > n'`. -/
theorem eventually_incompatible (M N : Machine) (h : fn M ≠ fn N) :
    ∃ n' : ℕ, ∀ n : ℕ, n' < n → ¬ Compatible n N M := by
  classical
  have hx : ∃ t x : ℕ, bounded N t x ≠ bounded M t x := by
    by_contra hnone
    push_neg at hnone
    apply h
    funext x
    apply Part.ext
    intro y
    change y ∈ M.eval x ↔ y ∈ N.eval x
    rw [Nat.Partrec.Code.evaln_complete, Nat.Partrec.Code.evaln_complete]
    have heq : ∀ t, M.evaln t x = N.evaln t x := fun t => (hnone t x).symm
    simp only [heq]
  obtain ⟨t, x, hneq⟩ := hx
  refine ⟨max t (Nat.size x), ?_⟩
  intro n hn hc
  exact hneq (hc t x (le_trans (le_max_left _ _) (Nat.le_of_lt hn))
    (le_trans (le_max_right _ _) (Nat.le_of_lt hn)))


end ObfImpossibility.RiceSimulator
open ObfImpossibility.RiceSimulator
namespace ObfImpossibility.RiceSimulator
lemma finite_size_pool (s : ℕ) : {N : Machine | size N = s}.Finite := by
  have hf : {N : Machine | Encodable.encode N < 2 ^ s}.Finite :=
    Set.Finite.preimage Encodable.encode_injective.injOn (Set.finite_Iio (2 ^ s))
  apply hf.subset
  intro N hN
  change Encodable.encode N < 2 ^ s
  rw [← hN]
  exact Nat.lt_size_self _

theorem stabilization (M : Machine) :
    ∃ b : ℕ, ∀ n : ℕ, b < n → ∀ N ∈ survivors n M, fn N = fn M := by
  classical
  have he : ∀ N : Machine, ∃ b : ℕ, ∀ n : ℕ, b < n → Compatible n N M → fn N = fn M := by
    intro N
    by_cases h : fn N = fn M
    · exact ⟨0, fun _ _ _ => h⟩
    · obtain ⟨b, hb⟩ := eventually_incompatible M N (Ne.symm h)
      exact ⟨b, fun n hn hc => False.elim (hb n hn hc)⟩
  choose b hb using he
  let pool := (finite_size_pool (size M)).toFinset
  refine ⟨pool.sup b, ?_⟩
  intro n hn N hN
  have hmem : N ∈ pool := (finite_size_pool (size M)).mem_toFinset.mpr hN.1
  exact hb N n (lt_of_le_of_lt (Finset.le_sup hmem) hn) hN.2
end ObfImpossibility.RiceSimulator
namespace ObfImpossibility.RiceSimulator

theorem stage_sound (T M : Machine) (n σ : ℕ) (h : StageAnswer T M n σ) :
    σ ∈ T.eval (Encodable.encode M) := by
  apply Nat.Partrec.Code.evaln_sound
  exact h M ⟨rfl, fun _ _ _ _ => rfl⟩

lemma stage_of_common_output (T M : Machine) (σ : ℕ)
    (hT : ∀ N : Machine, fn N = fn M → σ ∈ T.eval (Encodable.encode N)) :
    ∃ n : ℕ, StageAnswer T M n σ := by
  classical
  obtain ⟨b, hb⟩ := stabilization M
  have ht : ∀ N : Machine, ∃ t : ℕ, fn N = fn M → σ ∈ T.evaln t (Encodable.encode N) := by
    intro N
    by_cases he : fn N = fn M
    · obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp (hT N he)
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => False.elim (he h)⟩
  choose t ht using ht
  let pool := (finite_size_pool (size M)).toFinset
  let n := max (b + 1) (pool.sup t)
  have hbn : b < n := lt_of_lt_of_le (Nat.lt_succ_self b) (le_max_left _ _)
  refine ⟨n, ?_⟩
  intro N hN
  have hp : N ∈ pool := (finite_size_pool (size M)).mem_toFinset.mpr hN.1
  have he : fn N = fn M := hb n hbn N hN
  exact Nat.Partrec.Code.evaln_mono
    (le_trans (Finset.le_sup hp) (le_max_right _ _)) (ht N he)

theorem _root_.solution (P : PromiseProblem) (hclosed : P.ClosedUnderFn)
    (T : Machine) (hT : Decides T P) :
    (∀ M ∈ P.yes, ∃ n : ℕ, StageAnswer T M n 1) ∧
    (∀ M ∈ P.no, ∃ n : ℕ, StageAnswer T M n 0) := by
  constructor
  · intro M hM
    apply stage_of_common_output
    intro N he
    have hN := (hclosed M N he.symm).1.mp hM
    rw [hT.1 N hN]
    exact Part.mem_some _
  · intro M hM
    apply stage_of_common_output
    intro N he
    have hN := (hclosed M N he.symm).2.mp hM
    rw [hT.2 N hN]
    exact Part.mem_some _
end ObfImpossibility.RiceSimulator
