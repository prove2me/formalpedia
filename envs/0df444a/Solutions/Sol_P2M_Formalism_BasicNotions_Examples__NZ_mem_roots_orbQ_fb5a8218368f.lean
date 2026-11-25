-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_mem_roots_orbQ_fb5a8218368f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:32:39.519352+00:00
-- url     : https://prove2.me/submissions/27cf15c4-9794-4d3b-9e06-ba6f6625f2b8

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_orbQ_monic_0e02f754a39e
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
variable {d : ℕ} (hd : 1 ≤ d) (u : (Fbar g)ˣ) (hu : orderOf u = g ^ d - 1)
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {y : Fbar g} : y ∈ (orbQ d u).roots ↔ ∃ i < d, y = (u : Fbar g) ^ (g ^ i) := by
  have h0 := (orbQ_monic (d := d) u).ne_zero
  unfold orbQ at h0 ⊢
  rw [roots_prod _ _ h0]
  simp only [roots_X_sub_C, Multiset.mem_bind, Finset.mem_val, Finset.mem_range, Multiset.mem_singleton]
end Formalism.BasicNotions.Examples₂.NZ
