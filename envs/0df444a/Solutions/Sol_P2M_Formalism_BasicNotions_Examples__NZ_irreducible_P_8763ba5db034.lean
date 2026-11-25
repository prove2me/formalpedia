-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_irreducible_P_8763ba5db034
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:29:31.731847+00:00
-- url     : https://prove2.me/submissions/9d50535b-006d-4507-b07d-ba5e6db9277c

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_le_natDegree_of_dvd_81216a4a9b35
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
variable {P : (ZMod g)[X]} (hP : P.map (algebraMap (ZMod g) (Fbar g)) = orbQ d u)
include hd hu hP
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (hPd : P.natDegree = d) : Irreducible P := by
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hPd
    omega
  refine ⟨fun h => ?_, fun a b hab => ?_⟩
  · have := natDegree_eq_zero_of_isUnit h
    omega
  · by_contra hne
    push_neg at hne
    have hab' : a * b ≠ 0 := hab ▸ hP0
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hab'
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hab'
    have ha : a.natDegree ≠ 0 := fun h =>
      hne.1 (isUnit_iff_degree_eq_zero.2 ((degree_eq_iff_natDegree_eq ha0).2 h))
    have hb : b.natDegree ≠ 0 := fun h =>
      hne.2 (isUnit_iff_degree_eq_zero.2 ((degree_eq_iff_natDegree_eq hb0).2 h))
    have h1 := le_natDegree_of_dvd hd u hu hP (Dvd.intro b hab.symm) ha
    have h2 := le_natDegree_of_dvd hd u hu hP (Dvd.intro_left a hab.symm) hb
    have h3 : P.natDegree = a.natDegree + b.natDegree := by rw [hab, natDegree_mul ha0 hb0]
    omega
end Formalism.BasicNotions.Examples₂.NZ
