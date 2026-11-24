-- Prove2me | solution 1 for SensitivityLowPacking.residual_zero_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:31:32.577885+00:00
-- url     : https://prove2.me/submissions/71d7674d-d811-4914-bce7-bd6e82704ef4

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
import Theorems.Thm_SensitivityLowPacking_positive_mem_live

namespace SensitivityLowPacking
end SensitivityLowPacking
namespace SensitivityPseudoforest
end SensitivityPseudoforest

section


/-! The weighted clique leaves used by the exact low-one branch certificates. -/
namespace SensitivityLowPacking

noncomputable section
open scoped Classical BigOperators
open SensitivityPseudoforest
set_option autoImplicit false

variable {V : Type} [DecidableEq V]





theorem count_le_weightedOut (D : V → V → Prop) (vertices : Finset V) (count : V → ℕ)
    (v w : V) (hw : w ∈ vertices) (hd : D v w) : count w ≤ weightedOut D vertices count v := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨hw, hd⟩)














end
end SensitivityLowPacking

end

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







theorem actual_zero_mem_fixedZeros (D : V → V → Prop) (vertices fixed zeros : Finset V)
    (count base : V → ℕ) (hf : fixed ⊆ vertices)
    (hzsub : zeros ⊆ Support vertices count) (hzsmall : ∀ v ∈ zeros, count v ≤ 2)
    (hz : ∀ v ∈ zeros, base v + weightedOut D vertices count v = 0)
    (v : V) (hv : v ∈ zeros ∩ fixed) : v ∈ fixedZeros D fixed count base := by
  obtain ⟨hvz, hvf⟩ := Finset.mem_inter.mp hv
  have hp := (Finset.mem_filter.mp (hzsub hvz)).2
  have hm := weightedOut_mono D count fixed vertices hf v
  have hh := hz v hvz
  exact Finset.mem_filter.mpr ⟨hvf, hp, hzsmall v hvz, by dsimp [fixedBase]; omega⟩









end
end SensitivityLowPacking

end

/-! Conditioning a low packing on a partial assignment preserves exact guard budgets. -/
open SensitivityLowPacking
open scoped Classical BigOperators
open SensitivityPseudoforest
set_option autoImplicit false
variable {V : Type} [DecidableEq V]

theorem solution (D : V → V → Prop) (vertices fixed zeros : Finset V)
    (count base : V → ℕ) (hf : fixed ⊆ vertices)
    (hbudget : ∀ v ∈ vertices, 0 < count v →
      count v + 2 * (base v + weightedOut D vertices count v) ≤ 3)
    (hzsub : zeros ⊆ Support vertices count) (hzsmall : ∀ v ∈ zeros, count v ≤ 2)
    (hz : ∀ v ∈ zeros, base v + weightedOut D vertices count v = 0)
    (alpha : ℕ)
    (hcap : ∀ s ⊆ (liveCandidates D vertices fixed count base).filter
        (fun v => fixedBase D fixed count base v = 0),
      (∀ v ∈ s, ∀ w ∈ s, ¬D v w) → s.card ≤ alpha) :
    zeros.card ≤ (fixedZeros D fixed count base).card + alpha := by
  have hremain : zeros \ fixed ⊆ (liveCandidates D vertices fixed count base).filter
      (fun v => fixedBase D fixed count base v = 0) := by
    intro v hv
    obtain ⟨hvz, hvf⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨hvV, hp⟩ := Finset.mem_filter.mp (hzsub hvz)
    have hm := weightedOut_mono D count fixed vertices hf v
    have hh := hz v hvz
    refine Finset.mem_filter.mpr ⟨positive_mem_live D vertices fixed count base hf hbudget v
      (Finset.mem_sdiff.mpr ⟨hvV, hvf⟩) hp, ?_⟩
    dsimp only [fixedBase]
    omega
  have hc := hcap (zeros \ fixed) hremain (by
    intro v hv w hw hd
    have hvz := (Finset.mem_sdiff.mp hv).1
    have hwz := (Finset.mem_sdiff.mp hw).1
    obtain ⟨hwV, hwp⟩ := Finset.mem_filter.mp (hzsub hwz)
    have hcount := count_le_weightedOut D vertices count v w hwV hd
    have hh := hz v hvz
    omega)
  have hzs : zeros ∩ fixed ⊆ fixedZeros D fixed count base :=
    fun v hv => actual_zero_mem_fixedZeros D vertices fixed zeros count base hf hzsub hzsmall hz v hv
  have hzc : (zeros ∩ fixed).card + (zeros \ fixed).card = zeros.card :=
    Finset.card_inter_add_card_sdiff _ _
  have hzbound := Finset.card_le_card hzs
  omega
