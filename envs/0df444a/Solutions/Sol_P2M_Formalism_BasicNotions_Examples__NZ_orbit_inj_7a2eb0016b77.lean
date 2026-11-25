-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_orbit_inj_7a2eb0016b77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:32:35.257114+00:00
-- url     : https://prove2.me/submissions/0d785c28-ab1c-4edc-bd2c-f67aeb92960a

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_dvd_of_pow_eq_7b799bd31cc9
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
include hd hu
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {i j : ℕ} (hi : i < d) (hj : j < d) (h : u ^ (g ^ i) = u ^ (g ^ j)) : i = j := by
  rcases le_total i j with hij | hij
  · by_contra hne
    have hlt : i < j := lt_of_le_of_ne hij hne
    have hdv := dvd_of_pow_eq hd u hu (a := 1) hij (by simpa using h)
    rw [one_mul] at hdv
    have h1 : 1 < g ^ (j - i) := Nat.one_lt_pow (by omega) hg.out.one_lt
    have h2 : g ^ (j - i) < g ^ d := Nat.pow_lt_pow_right hg.out.one_lt (by omega)
    have := Nat.le_of_dvd (by omega) hdv
    omega
  · by_contra hne
    have hlt : j < i := lt_of_le_of_ne hij (Ne.symm hne)
    have hdv := dvd_of_pow_eq hd u hu (a := 1) hij (by simpa using h.symm)
    rw [one_mul] at hdv
    have h1 : 1 < g ^ (i - j) := Nat.one_lt_pow (by omega) hg.out.one_lt
    have h2 : g ^ (i - j) < g ^ d := Nat.pow_lt_pow_right hg.out.one_lt (by omega)
    have := Nat.le_of_dvd (by omega) hdv
    omega
end Formalism.BasicNotions.Examples₂.NZ
