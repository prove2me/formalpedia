-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_dvd_of_pow_eq_7b799bd31cc9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:22.775221+00:00
-- url     : https://prove2.me/submissions/2ef277a7-d7fa-4a95-abfc-fdad58d233ab

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_coprime_n_8914bd4d6568

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
variable {d : ℕ} (hd : 1 ≤ d) (u : (Fbar g)ˣ) (hu : orderOf u = g ^ d - 1)
include hd hu
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {i j a : ℕ} (hij : i ≤ j) (h : u ^ (g ^ i * a) = u ^ (g ^ j * a)) :
    g ^ d - 1 ∣ a * (g ^ (j - i) - 1) := by
  rw [pow_eq_pow_iff_modEq, hu] at h
  have hle : g ^ i * a ≤ g ^ j * a := Nat.mul_le_mul_right a (Nat.pow_le_pow_right hg.out.pos hij)
  have h1 : g ^ d - 1 ∣ g ^ j * a - g ^ i * a := (Nat.modEq_iff_dvd' hle).1 h
  have hp : 1 ≤ g ^ (j - i) := Nat.one_le_pow _ _ hg.out.pos
  have hgj : g ^ j = g ^ i * g ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij]
  have h2 : g ^ j * a - g ^ i * a = g ^ i * (a * (g ^ (j - i) - 1)) := by
    rw [hgj]
    have hle2 : a ≤ a * g ^ (j - i) := Nat.le_mul_of_pos_right a hp
    zify [hp, hle, hle2, hgj ▸ hle]
    ring
  rw [h2] at h1
  exact ((coprime_n d hd).pow_right i).dvd_mul_left.1 h1
end Formalism.BasicNotions.Examples₂.NZ
