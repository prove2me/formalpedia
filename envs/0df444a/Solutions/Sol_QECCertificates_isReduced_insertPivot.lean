-- Prove2me | solution 1 for QECCertificates.isReduced_insertPivot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:21.777858+00:00
-- url     : https://prove2.me/submissions/0106cbd9-2703-43ae-84a1-067de867f24c

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Theorems.Thm_QECCertificates_IsReduced_pivot_inj
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (hD : IsReduced D) {w : Vec n} {p : Fin n}
    (hp : w p = 1) (hz : ∀ ri ∈ D, w ri.2 = 0) : IsReduced (insertPivot D w p) := by
  constructor
  · intro rj hrj
    rcases List.mem_append.mp hrj with hmap | hsingle
    · obtain ⟨ri, hri, rfl⟩ := List.mem_map.mp hmap
      change (ri.1 + (ri.1 p) • w) ri.2 = 1
      rw [Pi.add_apply, Pi.smul_apply, hz ri hri, smul_eq_mul, mul_zero, add_zero]
      exact hD.1 ri hri
    · have hw : rj = (w, p) := by simpa using hsingle
      rw [hw]; exact hp
  · intro ri hri rj hrj hne
    rcases List.mem_append.mp hri with hmi | hsi <;> rcases List.mem_append.mp hrj with hmj | hsj
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmi
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hmj
      have hab : a.2 ≠ b.2 := by
        intro hcon
        exact hne (by rw [hD.pivot_inj a ha b hb hcon])
      change (a.1 + (a.1 p) • w) b.2 = 0
      rw [Pi.add_apply, Pi.smul_apply, hz b hb, smul_eq_mul, mul_zero, add_zero]
      exact hD.2 a ha b hb (fun h => hab (by rw [h]))
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmi
      have hwj : rj = (w, p) := by simpa using hsj
      subst hwj
      change (a.1 + (a.1 p) • w) p = 0
      rw [Pi.add_apply, Pi.smul_apply, hp, smul_eq_mul, mul_one]
      exact CharTwo.add_self_eq_zero (a.1 p)
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmj
      have hwi : ri = (w, p) := by simpa using hsi
      subst hwi
      exact hz a ha
    · have hwi : ri = (w, p) := by simpa using hsi
      have hwj : rj = (w, p) := by simpa using hsj
      exact absurd (hwi.trans hwj.symm) hne
end QECCertificates
