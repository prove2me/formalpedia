-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_le_natDegree_of_dvd_81216a4a9b35
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:47:59.414337+00:00
-- url     : https://prove2.me/submissions/3bf265a7-1c0b-435d-a986-bcd7eef4eea1

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_pow_g_add_980569a93c39
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_orbit_inj_7a2eb0016b77
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_orbQ_monic_0e02f754a39e
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_mem_rootsBar_P_9cb9ba47d11d
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
theorem _root_.solution {q : (ZMod g)[X]} (hq : q ∣ P) (hq0 : q.natDegree ≠ 0) : d ≤ q.natDegree := by
  classical
  have hq0' : q ≠ 0 := by
    rintro rfl
    simp at hq0
  have hqm : q.map (algebraMap (ZMod g) (Fbar g)) ≠ 0 := Polynomial.map_ne_zero hq0'
  have hPm : P.map (algebraMap (ZMod g) (Fbar g)) ≠ 0 := by
    rw [hP]; exact (orbQ_monic u).ne_zero
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (q.map (algebraMap (ZMod g) (Fbar g))) (by
    rw [degree_map]
    intro h
    exact hq0 (natDegree_eq_of_degree_eq_some h))
  have hyP : y ∈ rootsBar P := by
    rw [rootsBar, mem_roots hPm]
    exact hy.dvd (Polynomial.map_dvd _ hq)
  obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P u hP).1 hyP
  have hcomp : (frobenius (Fbar g) g).comp (algebraMap (ZMod g) (Fbar g)) = algebraMap (ZMod g) (Fbar g) :=
    RingHom.ext fun c => by simp [frobenius_def, ← map_pow, ZMod.pow_card]
  have hfrob : ∀ z, (q.map (algebraMap (ZMod g) (Fbar g))).IsRoot z →
      (q.map (algebraMap (ZMod g) (Fbar g))).IsRoot (z ^ g) := by
    intro z hz
    simp only [IsRoot, eval_map] at hz ⊢
    have h := Polynomial.hom_eval₂ q (algebraMap (ZMod g) (Fbar g)) (frobenius (Fbar g) g) z
    rw [hcomp, hz, map_zero, frobenius_def] at h
    exact h.symm
  have hiter : ∀ k, (q.map (algebraMap (ZMod g) (Fbar g))).IsRoot ((u : Fbar g) ^ g ^ (i + k)) := by
    intro k
    induction k with
    | zero => simpa using hy
    | succ k ih =>
      have h := hfrob _ ih
      rw [← pow_mul, ← pow_succ] at h
      exact h
  have hall : ∀ j < d, (q.map (algebraMap (ZMod g) (Fbar g))).IsRoot ((u : Fbar g) ^ g ^ j) := by
    intro j hj
    have h1 := hiter (d - i + j)
    have h2 : i + (d - i + j) = j + d := by omega
    rw [h2] at h1
    have h3 := congrArg Units.val (pow_g_add hd u hu j)
    simp only [Units.val_pow_eq_pow_val] at h3
    rwa [h3] at h1
  have hsub : (Finset.range d).image (fun j => (u : Fbar g) ^ g ^ j) ⊆
      (q.map (algebraMap (ZMod g) (Fbar g))).roots.toFinset := fun z hz => by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz
    rw [Multiset.mem_toFinset, mem_roots hqm]
    exact hall j (Finset.mem_range.1 hj)
  have hinj : Set.InjOn (fun j => (u : Fbar g) ^ g ^ j) (Finset.range d) := fun a ha b hb hab =>
    orbit_inj hd u hu (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) (Units.ext (by simpa using hab))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hc
  calc d ≤ _ := hc
    _ ≤ Multiset.card (q.map (algebraMap (ZMod g) (Fbar g))).roots := Multiset.toFinset_card_le _
    _ ≤ (q.map (algebraMap (ZMod g) (Fbar g))).natDegree := card_roots' _
    _ = q.natDegree := natDegree_map _
end Formalism.BasicNotions.Examples₂.NZ
