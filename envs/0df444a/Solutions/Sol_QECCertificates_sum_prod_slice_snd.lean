-- Prove2me | solution 1 for QECCertificates.sum_prod_slice_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:51.541012+00:00
-- url     : https://prove2.me/submissions/b070f2c4-96fb-4036-bc6a-c20ce4be0753

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution {m k : ℕ} (A : Fin m → ZMod 2) (F : Fin m → Fin k → ZMod 2)
    (j : Fin k) :
    (∑ p : Fin m × Fin k, A p.1 * (if j = p.2 then 1 else 0) * F p.1 p.2)
      = ∑ a, A a * F a j := by
  rw [Fintype.sum_prod_type (f := fun p : Fin m × Fin k =>
    A p.1 * (if j = p.2 then 1 else 0) * F p.1 p.2)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (s := Finset.univ)
    (f := fun b => A a * (if j = b then 1 else 0) * F a b) j ?_ ?_]
  · rw [if_pos rfl, mul_one]
  · intro b _ hb
    rw [if_neg (fun h => hb h.symm), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h
end QECCertificates
