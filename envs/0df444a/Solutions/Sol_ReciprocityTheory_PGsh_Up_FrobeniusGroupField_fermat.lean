-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.fermat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:32.956837+00:00
-- url     : https://prove2.me/submissions/a8d39ba7-de2b-4471-b827-51dcc3857c0b

import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitOfNotMem
import Definitions.Def_ReciprocityTheory_DualLattices_EigPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution (p : ℕ) [Fact p.Prime] (hv : v.Integers R) (hpv : v (algebraMap R C (p : R)) < 1)
    [Algebra ℤ_[p] R] (z : ℤ_[p]) :
    res hv (algebraMap ℤ_[p] R z) ^ p = res hv (algebraMap ℤ_[p] R z) := by
  have hz : z ^ p - z ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
      ZMod.pow_card, sub_self]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hz
  have hp0 : res hv (p : R) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hpv
  have h0 : res hv (algebraMap ℤ_[p] R (z ^ p - z)) = 0 := by
    rw [← hw, map_mul, map_mul, map_natCast (algebraMap ℤ_[p] R), hp0, mul_zero]
  rw [map_sub, map_sub, map_pow, map_pow, sub_eq_zero] at h0
  exact h0
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
