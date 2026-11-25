-- Prove2me | solution 1 for PI.ExpIntWProof.Key.frob_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:55:39.961518+00:00
-- url     : https://prove2.me/submissions/5d45c492-1656-4596-837a-bb411afef2a2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers
import Theorems.Thm_PI_ExpIntWProof_Key_Fx_add
import Theorems.Thm_PI_ExpIntWProof_Key_Fx_mul
import Theorems.Thm_PI_ExpIntWProof_Key_Fx_neg
import Theorems.Thm_PI_ExpIntWProof_Key_root_frob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof PI.ExpIntWProof.Key
variable {p : ℕ} [hp : Fact p.Prime]
namespace PI.ExpIntWProof.Key
theorem _root_.solution (y : ℂ_[p]) (hy : y ∈ S0 p) :
    ∃ f : ℕ, 0 < f ∧ ∃ z ∈ S0 p, y ^ p ^ f - y = (p : ℂ_[p]) * z := by
  classical
  let I : Ideal (S0 p) := Ideal.span {((p : ℕ) : S0 p)}
  suffices H : ∀ a : S0 p, Fx p (Ideal.Quotient.mk I a) by
    obtain ⟨f, hf, h⟩ := H ⟨y, hy⟩
    rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
    obtain ⟨z, hz⟩ := h
    refine ⟨f, hf, z, z.2, ?_⟩
    have := congrArg Subtype.val hz
    simpa using this
  have hp0 : ((p : ℕ) : S0 p ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I) p]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  rcases (Nat.dvd_prime hp.out).1 (ringChar.dvd hp0) with h1 | h1
  · have : CharP (S0 p ⧸ I) 1 := ringChar.of_eq h1
    have := CharP.CharOne.subsingleton (R := S0 p ⧸ I)
    exact fun a => ⟨1, one_pos, Subsingleton.elim _ _⟩
  · have : CharP (S0 p ⧸ I) p := ringChar.of_eq h1
    rintro ⟨y, hy⟩
    induction hy using Subring.closure_induction with
    | mem x hx =>
        obtain ⟨n, hn, hc, hxn⟩ := hx
        refine ⟨Nat.totient n, Nat.totient_pos.2 hn, ?_⟩
        rw [← map_pow]
        congr 1
        exact Subtype.ext (by simpa using root_frob hn hc hxn)
    | zero => exact ⟨1, one_pos, by rw [show (⟨0, _⟩ : S0 p) = 0 from rfl, map_zero, zero_pow (pow_ne_zero _ hp.out.ne_zero)]⟩
    | one => exact ⟨1, one_pos, by rw [show (⟨1, _⟩ : S0 p) = 1 from rfl, map_one, one_pow]⟩
    | add x y hx hy ihx ihy =>
        rw [show (⟨x + y, _⟩ : S0 p) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add]
        exact Fx.add p ihx ihy
    | neg x hx ih =>
        rw [show (⟨-x, _⟩ : S0 p) = -⟨x, hx⟩ from rfl, map_neg]
        exact Fx.neg p ih
    | mul x y hx hy ihx ihy =>
        rw [show (⟨x * y, _⟩ : S0 p) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]
        exact Fx.mul p ihx ihy
end PI.ExpIntWProof.Key
