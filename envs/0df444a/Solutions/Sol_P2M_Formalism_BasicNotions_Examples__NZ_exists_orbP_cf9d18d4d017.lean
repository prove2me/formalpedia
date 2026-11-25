-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_exists_orbP_cf9d18d4d017
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:41:59.227349+00:00
-- url     : https://prove2.me/submissions/44e6f174-56a1-48a3-857f-e66607ab3109

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_orbQ_monic_0e02f754a39e
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_orbQ_natDegree_1bdc5807d35c
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_orbQ_frob_bb6236d36b98
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
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
theorem _root_.solution : ∃ P : (ZMod g)[X], P.map (algebraMap (ZMod g) (Fbar g)) = orbQ d u ∧
    P.natDegree = d ∧ P.Monic := by
  have frob_fixed : ∀ y : Fbar g, y ^ g = y → y ∈ Set.range (algebraMap (ZMod g) (Fbar g)) := by
    intro y hy
    classical
    by_contra hy'
    have hf0 : (X ^ g - X : (Fbar g)[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hg.out.one_lt
    have hsub : insert y (Finset.univ.image (algebraMap (ZMod g) (Fbar g))) ⊆
        (X ^ g - X : (Fbar g)[X]).roots.toFinset := by
      intro z hz
      rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hy
      · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hz
        rw [← map_pow, ZMod.pow_card]
    have hny : y ∉ Finset.univ.image (algebraMap (ZMod g) (Fbar g)) := fun h => by
      obtain ⟨c, -, hc⟩ := Finset.mem_image.1 h
      exact hy' ⟨c, hc⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hny, Finset.card_image_of_injective _ (algebraMap (ZMod g) (Fbar g)).injective,
      Finset.card_univ, ZMod.card] at hc
    have h2 := (Multiset.toFinset_card_le _).trans (card_roots' (X ^ g - X : (Fbar g)[X]))
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hg.out.one_lt] at h2
    omega
  have hc : ∀ n, (orbQ d u).coeff n ∈ Set.range (algebraMap (ZMod g) (Fbar g)) := fun n => by
    have h := congrArg (fun p => p.coeff n) (orbQ_frob hd u hu)
    simp only [coeff_map, frobenius_def] at h
    exact frob_fixed _ h
  have hl : orbQ d u ∈ Polynomial.lifts (algebraMap (ZMod g) (Fbar g)) := (lifts_iff_coeff_lifts _).2 hc
  obtain ⟨P, hPmap, hPdeg, hPmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (orbQ_monic u)
  exact ⟨P, hPmap, hPdeg.trans (orbQ_natDegree u), hPmonic⟩
end Formalism.BasicNotions.Examples₂.NZ
