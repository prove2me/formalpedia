-- Prove2me | solution 1 for RiemannMasullo.adeleQuotient_nsmul_bijective
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:53:41.669188+00:00
-- url     : https://prove2.me/submissions/b3bbeb2e-5d3c-45bd-a53a-881826545599

-- Proof adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L449-L476
import Mathlib
open Function NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
local notation "Principal(" F ")" => AdeleRing.principalSubgroup (𝓞 F) F
local notation "AQuot(" F ")" => 𝔸[F] ⧸ Principal(F)

theorem solution (n : ℕ) (hn : 0 < n) :
    Bijective (fun x : AQuot(F) ↦ n • x) := by
  let P := Principal(F)
  let d := algebraMap F 𝔸[F]
  let q := QuotientAddGroup.mk' P
  have hn' : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hmul (a : 𝔸[F]) : n • (d (n : F)⁻¹ * a) = a := by
    rw [nsmul_eq_mul, ← map_natCast d, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hn', map_one,
      one_mul]
  constructor
  · intro a b hab
    induction a using QuotientAddGroup.induction_on with
    | H a =>
      induction b using QuotientAddGroup.induction_on with
      | H b =>
        change n • q a = n • q b at hab
        rw [← map_nsmul, ← map_nsmul] at hab
        obtain ⟨x, hx⟩ := QuotientAddGroup.eq_iff_sub_mem.mp hab
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        refine ⟨(n : F)⁻¹ * x, ?_⟩
        rw [map_mul, hx, ← nsmul_sub, nsmul_eq_mul, ← map_natCast d, ← mul_assoc, ← map_mul,
          inv_mul_cancel₀ hn', map_one, one_mul]
  · intro a
    induction a using QuotientAddGroup.induction_on with
    | H a =>
      refine ⟨q (d (n : F)⁻¹ * a), ?_⟩
      change n • q (d (n : F)⁻¹ * a) = q a
      rw [← map_nsmul, hmul]
