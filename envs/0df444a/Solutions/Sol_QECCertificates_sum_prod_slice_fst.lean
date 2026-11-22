-- Prove2me | solution 1 for QECCertificates.sum_prod_slice_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:55.398021+00:00
-- url     : https://prove2.me/submissions/1cec16b8-80e1-4515-a984-9695951ed967

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support


attribute [local simp] QECCertificates.blockL_apply
attribute [local simp] QECCertificates.blockR_apply

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution {m k : ℕ} (B : Fin k → ZMod 2) (F : Fin m → Fin k → ZMod 2)
    (i : Fin m) :
    (∑ p : Fin m × Fin k, (if i = p.1 then 1 else 0) * B p.2 * F p.1 p.2)
      = ∑ b, B b * F i b := by
  rw [Fintype.sum_prod_type (f := fun p : Fin m × Fin k =>
    (if i = p.1 then 1 else 0) * B p.2 * F p.1 p.2)]
  rw [Finset.sum_eq_single (s := Finset.univ)
    (f := fun a : Fin m => ∑ b : Fin k, (if i = a then 1 else 0) * B b * F a b) i ?_ ?_]
  · simp
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg (fun h => ha h.symm), zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h
end QECCertificates
