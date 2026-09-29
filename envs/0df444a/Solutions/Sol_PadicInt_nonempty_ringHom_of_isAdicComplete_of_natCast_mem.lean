-- Prove2me | solution 1 for PadicInt.nonempty_ringHom_of_isAdicComplete_of_natCast_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c7a9bf70-c914-5f9f-8d56-2aa45965b572

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_nonempty_ringHom_of_isAdicComplete_of_natCast_mem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

theorem solution
    (S : Type) [CommRing S] (I : Ideal S) [IsAdicComplete I S]
    (p : ℕ) [Fact p.Prime] (hp : (p : S) ∈ I) :
    Nonempty (ℤ_[p] →+* S) := by
  classical

  let g : (n : ℕ) → ZMod (p ^ n) →+* S ⧸ I ^ n := fun n =>
    (Ideal.Quotient.lift (Ideal.span {((p ^ n : ℕ) : ℤ)})
      ((Ideal.Quotient.mk (I ^ n)).comp (Int.castRingHom S)) (by
        have h0 : (Ideal.Quotient.mk (I ^ n)) ((Int.castRingHom S) ((p ^ n : ℕ) : ℤ)) = 0 := by
          rw [eq_intCast, Int.cast_natCast, Nat.cast_pow, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.pow_mem_pow hp n
        intro a ha
        rw [Ideal.mem_span_singleton] at ha
        obtain ⟨b, rfl⟩ := ha
        simp only [RingHom.comp_apply, map_mul, h0, zero_mul])).comp
    (Int.quotientSpanNatEquivZMod (p ^ n)).symm.toRingHom
  let f : (n : ℕ) → ℤ_[p] →+* S ⧸ I ^ n := fun n => (g n).comp (PadicInt.toZModPow n)
  refine ⟨IsAdicComplete.liftRingHom I f ?_⟩
  intro m n hle
  show ((Ideal.Quotient.factorPow I hle).comp (g n)).comp (PadicInt.toZModPow n)
    = (g m).comp (PadicInt.toZModPow m)
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle]
  exact congrArg (fun φ : ZMod (p ^ n) →+* S ⧸ I ^ m => φ.comp (PadicInt.toZModPow n))
    (RingHom.ext_zmod ((Ideal.Quotient.factorPow I hle).comp (g n))
      ((g m).comp (ZMod.castHom (pow_dvd_pow p hle) (ZMod (p ^ m)))))

end S_PadicInt_nonempty_ringHom_of_isAdicComplete_of_natCast_mem
end P2MW
export P2MW.S_PadicInt_nonempty_ringHom_of_isAdicComplete_of_natCast_mem (solution)
