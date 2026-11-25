-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.sum_gs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:15:46.332124+00:00
-- url     : https://prove2.me/submissions/1fc71c26-2489-4710-b8c8-dbfc1196ca61

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsBoundedBasis
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_filter_le_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (b : Fin d → E)
    (hl : ∀ i j : Fin d, i.val = j.val + 1 → ‖gs b j‖ ^ 2 ≤ 2 * ‖gs b i‖ ^ 2) :
    ∀ (n : ℕ) (h : n < d), ∑ j ∈ univ.filter (fun j : Fin d => j.val ≤ n), ‖gs b j‖ ^ 2 ≤
      (2 ^ (n + 1) - 1) * ‖gs b ⟨n, h⟩‖ ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro h
    have hs : univ.filter (fun j : Fin d => j.val ≤ 0) = {⟨0, h⟩} := by
      ext j
      simp [Fin.ext_iff]
    rw [hs, Finset.sum_singleton]
    norm_num
  | succ n ih =>
    intro h
    rw [filter_le_succ n h, Finset.sum_insert (by simp)]
    have h1 := ih (by omega)
    have h2 := hl ⟨n + 1, h⟩ ⟨n, by omega⟩ rfl
    have hp : (0 : ℝ) ≤ 2 ^ (n + 1) - 1 := by
      have : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hp
    have e : ((2 : ℝ) ^ (n + 1 + 1) - 1) * ‖gs b ⟨n + 1, h⟩‖ ^ 2 =
        ‖gs b ⟨n + 1, h⟩‖ ^ 2 + (2 ^ (n + 1) - 1) * (2 * ‖gs b ⟨n + 1, h⟩‖ ^ 2) := by ring
    rw [e]
    linarith
end ReciprocityTheory.ReducedBases.T2
