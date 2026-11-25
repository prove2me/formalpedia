-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_finOrd_56980a9f4222
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:32:35.010686+00:00
-- url     : https://prove2.me/submissions/4261f956-8e2d-4f1f-9e0a-462413f0449e

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_one_lt_pow_g_0b14e5602731
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
include hd hu
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (i : ℕ) : IsOfFinOrder ((u : Fbar g) ^ (g ^ i)) := by
  have h2 := one_lt_pow_g (g := g) hd
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨g ^ d - 1, by omega, ?_⟩
  rw [← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one]
  simp
end Formalism.BasicNotions.Examples₂.NZ
