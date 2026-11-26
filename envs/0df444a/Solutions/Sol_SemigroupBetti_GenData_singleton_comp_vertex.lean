-- Prove2me | solution 1 for SemigroupBetti.GenData.singleton_comp_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:08:29.709074+00:00
-- url     : https://prove2.me/submissions/9e532365-1a54-4c05-9822-0bf88d49b00a

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
public import Theorems.Thm_SemigroupBetti_GenData_one_le_crit
public import Theorems.Thm_SemigroupBetti_GenData_exists_alt
public import Theorems.Thm_SemigroupBetti_GenData_alt_coord_eq_zero
public import Theorems.Thm_SemigroupBetti_GenData_mem_compSupp
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_pos
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_ncomp_le_one_of_reachable
public import Theorems.Thm_SemigroupBetti_GenData_nu_add
public import Theorems.Thm_SemigroupBetti_GenData_nu_single
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_pos_of_two_le_ncomp
public import Theorems.Thm_SemigroupBetti_GenData_reachable_of_sharesVar
public import Theorems.Thm_SemigroupBetti_SharesVar_symm
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.GenData.mem_fiber
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.nu_zero
attribute [local simp] SemigroupBetti.mem_supp



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} (hd : G.contributes d) {i : Fin 4}
    {C : (G.nabla d).ConnectedComponent} (hC : G.compSupp C = {i}) (z : G.fiber d)
    (hz : (G.nabla d).connectedComponentMk z = C) :
    z.1 = Pi.single i (G.crit i) ∧ d = G.crit i * G.n i := by
  have hzd := G.mem_fiber.1 z.2
  have hdpos := G.pos_of_two_le_ncomp hd
  -- `z = k eᵢ` with `k = zᵢ`
  have hzform : z.1 = Pi.single i (z.1 i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp only [Pi.single_apply, hj, ite_false]
      by_contra hzj
      have : j ∈ G.compSupp C := G.mem_compSupp.2 ⟨z, hz, Nat.pos_of_ne_zero hzj⟩
      rw [hC, mem_singleton] at this; exact hj this
  set k := z.1 i with hk
  have hdk : d = k * G.n i := by rw [← hzd, hzform, G.nu_single]
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, zero_mul] at hdk; omega
    · exact h
  rcases lt_trichotomy k (G.crit i) with hlt | heq | hgt
  · -- no alternative: the fiber is a single vertex
    exfalso
    have hall : ∀ y : G.fiber d, y = z := by
      intro y
      by_contra hyz
      have hy : y.1 ≠ Pi.single i k := by
        intro h; exact hyz (Subtype.ext (h.trans hzform.symm))
      have hcand : G.IsCritCand i k :=
        G.isCritCand_iff.2 ⟨hkpos, y.1, (G.mem_fiber.1 y.2).trans hdk, hy⟩
      exact Nat.find_min (G.crit_exists i) hlt hcand
    have := G.ncomp_le_one_of_reachable (d := d) (fun y y' => by rw [hall y, hall y'])
    unfold contributes at hd; omega
  · exact ⟨hzform.trans (by rw [heq]), by rw [hdk, heq]⟩
  · -- the bridge `b = (k - cᵢ) eᵢ + y` enlarges the support
    exfalso
    obtain ⟨y, hy, hyne⟩ := G.exists_alt i
    have hyi := G.alt_coord_eq_zero hy hyne
    have hy0 : y ≠ 0 := by
      intro h; rw [h, nu_zero] at hy
      have := Nat.mul_pos (G.one_le_crit i) (G.n_pos i); omega
    obtain ⟨j, hj⟩ : ∃ j, 0 < y j := by
      by_contra hc; push Not at hc
      exact hy0 (funext fun l => Nat.le_zero.1 (hc l))
    have hji : j ≠ i := by rintro rfl; omega
    let b := Pi.single i (k - G.crit i) + y
    have hb : G.nu b = d := by
      simp only [b]; rw [G.nu_add, G.nu_single, hy, hdk, ← Nat.add_mul, Nat.sub_add_cancel hgt.le]
    let b' : G.fiber d := ⟨b, G.mem_fiber.2 hb⟩
    have hbz : (G.nabla d).connectedComponentMk b' = C := by
      rw [← hz]
      apply SimpleGraph.ConnectedComponent.sound
      apply G.reachable_of_sharesVar
      refine ⟨i, ?_, ?_⟩
      · simp [b', b, hyi]; omega
      · rw [← hk]; exact hkpos
    have : j ∈ G.compSupp C := G.mem_compSupp.2 ⟨b', hbz, by simp [b', b, hji.symm, hj]⟩
    rw [hC, mem_singleton] at this
    exact hji this
end SemigroupBetti.GenData
