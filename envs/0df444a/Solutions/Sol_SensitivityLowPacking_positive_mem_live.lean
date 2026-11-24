-- Prove2me | solution 1 for SensitivityLowPacking.positive_mem_live
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:20:16.456834+00:00
-- url     : https://prove2.me/submissions/a8d5d87b-66c4-42bb-bd94-987e263186aa

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_LowPackingCliqueBounds
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_LowPackingResidual
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

namespace SensitivityLowPacking
end SensitivityLowPacking
namespace SensitivityPseudoforest
end SensitivityPseudoforest

section


/-! Conditioning a low packing on a partial assignment preserves exact guard budgets. -/
namespace SensitivityLowPacking

noncomputable section
open scoped Classical BigOperators
open SensitivityPseudoforest
set_option autoImplicit false

variable {V : Type} [DecidableEq V]







theorem weightedOut_mono (D : V → V → Prop) (count : V → ℕ) (s t : Finset V)
    (hst : s ⊆ t) (v : V) : weightedOut D s count v ≤ weightedOut D t count v := by
  apply Finset.sum_le_sum_of_subset
  exact Finset.filter_subset_filter _ hst

theorem weightedOut_union (D : V → V → Prop) (count : V → ℕ) (s t : Finset V)
    (hst : Disjoint s t) (v : V) :
    weightedOut D (s ∪ t) count v = weightedOut D s count v + weightedOut D t count v := by
  unfold weightedOut
  rw [Finset.filter_union, Finset.sum_union]
  exact hst.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem residual_load_le (D : V → V → Prop) (vertices fixed remaining : Finset V)
    (count base : V → ℕ) (hf : fixed ⊆ vertices) (hr : remaining ⊆ vertices \ fixed) (v : V) :
    fixedBase D fixed count base v + weightedOut D remaining count v ≤
      base v + weightedOut D vertices count v := by
  have hd : Disjoint fixed remaining := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact (Finset.mem_sdiff.mp (hr hw')).2 hw
  have hu : fixed ∪ remaining ⊆ vertices := Finset.union_subset hf (hr.trans (Finset.sdiff_subset))
  have h := weightedOut_mono D count (fixed ∪ remaining) vertices hu v
  rw [weightedOut_union D count fixed remaining hd v] at h
  dsimp only [fixedBase]
  omega













end
end SensitivityLowPacking

end

/-! Conditioning a low packing on a partial assignment preserves exact guard budgets. -/
open SensitivityLowPacking
open scoped Classical BigOperators
open SensitivityPseudoforest
set_option autoImplicit false
variable {V : Type} [DecidableEq V]

theorem solution (D : V → V → Prop) (vertices fixed : Finset V)
    (count base : V → ℕ) (hf : fixed ⊆ vertices)
    (hbudget : ∀ v ∈ vertices, 0 < count v →
      count v + 2 * (base v + weightedOut D vertices count v) ≤ 3)
    (v : V) (hv : v ∈ vertices \ fixed) (hp : 0 < count v) :
    v ∈ liveCandidates D vertices fixed count base := by
  obtain ⟨hvV, hvf⟩ := Finset.mem_sdiff.mp hv
  refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hvV, hvf⟩, ?_, ?_⟩
  · have hm := weightedOut_mono D count fixed vertices hf v
    have hb := hbudget v hvV hp
    dsimp only [fixedBase]
    omega
  · intro w hw hwp hd
    have hb := hbudget w (hf hw) hwp
    have hl := residual_load_le D vertices fixed {v} count base hf (by
      intro u hu
      have heq : u = v := Finset.mem_singleton.mp hu
      subst u
      exact Finset.mem_sdiff.mpr ⟨hvV, hvf⟩) w
    have hone : weightedOut D {v} count w = count v := by simp [weightedOut, Finset.filter_singleton, hd]
    rw [hone] at hl
    omega
