-- Prove2me | solution 1 for P2M_GlobalTheory_lattice_le_of_g__eq_of_g__eq_4fd8d18e060a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:34:19.266871+00:00
-- url     : https://prove2.me/submissions/d8b26463-ff6d-4a5a-af78-b915e8e13a38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Theorems.Thm_GlobalTheory_analyticAt_weierstrassP_add
import Theorems.Thm_GlobalTheory_countable_add_mem_periodLattice
import Theorems.Thm_GlobalTheory_eqOn_compl_of_countable
import Theorems.Thm_GlobalTheory_eventuallyEq_of_weierstrass_system
import Theorems.Thm_GlobalTheory_eventually_ne_notMem_periodLattice
import Theorems.Thm_GlobalTheory_eventually_notMem_periodLattice
import Theorems.Thm_GlobalTheory_exists_weierstrassP_eq_and_derivWeierstrassP_eq
import Theorems.Thm_GlobalTheory_not_eventually_weierstrassP_eq
import Theorems.Thm_GlobalTheory_weierstrass_system_add_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair
open scoped Topology Real UpperHalfPlane
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {L L' : PeriodPair} (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) : L.lattice ≤ L'.lattice := by
  have hz := L.ω₁_div_two_notMem_lattice
  set z := L.ω₁ / 2
  obtain ⟨w, hw, hw1, hw2⟩ := exists_weierstrassP_eq_and_derivWeierstrassP_eq L' (x := ℘[L] z) (y := ℘'[L] z)
    (by rw [← h₂, ← h₃]; exact L.derivWeierstrassP_sq z hz)
  obtain ⟨c, rfl⟩ : ∃ c, w = z + c := ⟨w - z, by ring⟩
  have h1 := eventuallyEq_of_weierstrass_system
    (weierstrass_system_add_const L 0 (z := z) (by simpa using hz))
    (h₂ ▸ weierstrass_system_add_const L' c hw) (by simp [hw1]) (by simp [hw2])
  have h2 := eqOn_compl_of_countable
    ((countable_add_mem_periodLattice L 0).union (countable_add_mem_periodLattice L' c))
    (fun t ht ↦ analyticAt_weierstrassP_add L 0 fun h ↦ ht (.inl h))
    (fun t ht ↦ analyticAt_weierstrassP_add L' c fun h ↦ ht (.inr h))
    (z := z) (by rintro (h | h); exacts [hz (by simpa using h), hw h]) h1
  have key : ∀ l ∈ L.lattice, l + c ∈ L'.lattice := fun l hl ↦ by
    by_contra h0
    refine not_eventually_weierstrassP_eq L hl
      (analyticAt_weierstrassP_add L' c h0).continuousAt ?_
    filter_upwards [eventually_ne_notMem_periodLattice L l, mem_nhdsWithin_of_mem_nhds
      ((continuous_add_const c).continuousAt.eventually
        (eventually_notMem_periodLattice L' h0))] with t h3 h4
    simpa using h2 (x := t) (by rintro (h | h); exacts [h3 (by simpa using h), h4 h])
  intro l hl
  simpa using sub_mem (key l hl) (key 0 (zero_mem _))
end GlobalTheory
