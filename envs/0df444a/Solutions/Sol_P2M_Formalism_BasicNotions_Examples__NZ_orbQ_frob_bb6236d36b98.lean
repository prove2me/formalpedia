-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_orbQ_frob_bb6236d36b98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:32:31.486681+00:00
-- url     : https://prove2.me/submissions/b8f0b255-958d-4f5c-9cf0-88b9eff3a162

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_pow_gd_5940a6f3a10f
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
theorem _root_.solution : (orbQ d u).map (frobenius (Fbar g) g) = orbQ d u := by
  have hf : ∀ i, (X - C ((u : Fbar g) ^ g ^ i)).map (frobenius (Fbar g) g) =
      X - C ((u : Fbar g) ^ g ^ (i + 1)) := fun i => by
    simp only [Polynomial.map_sub, map_X, map_C, frobenius_def, ← pow_mul, pow_succ]
  have hd' : (u : Fbar g) ^ g ^ d = u := by
    have := congrArg Units.val (pow_gd hd u hu)
    simpa using this
  unfold orbQ
  rw [Polynomial.map_prod]
  simp_rw [hf]
  apply mul_right_cancel₀ (X_sub_C_ne_zero ((u : Fbar g) ^ g ^ 0))
  rw [← Finset.prod_range_succ' (fun i => X - C ((u : Fbar g) ^ g ^ i)), Finset.prod_range_succ, hd',
    pow_zero, pow_one]
end Formalism.BasicNotions.Examples₂.NZ
