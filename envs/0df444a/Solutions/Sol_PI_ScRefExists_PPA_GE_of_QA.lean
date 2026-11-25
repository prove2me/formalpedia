-- Prove2me | solution 1 for PI.ScRefExists.PPA.GE_of_QA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:57.361304+00:00
-- url     : https://prove2.me/submissions/2fb6a6fd-cbdb-4531-97cf-65fefb6ac338

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_NatCastSmulMemL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.PPA
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.PPA
theorem _root_.solution (p m : ℕ) {x : I.E} (hint : ∃ a : 𝓞 I.E, (a : I.E) = x) (h : QA I p (p ^ m) x) :
    GE I (p ^ m) x := by
  obtain ⟨b, rfl⟩ := hint
  obtain ⟨s, hs, a, ha⟩ := h
  have hcop : Nat.Coprime s (p ^ m) := Nat.Coprime.pow_right m hs
  have hz : (s : ℤ) * Nat.gcdA s (p ^ m) + ((p ^ m : ℕ) : ℤ) * Nat.gcdB s (p ^ m) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hcop]
    norm_num
  have hzE := congrArg (Int.cast : ℤ → I.E) hz
  push_cast at hzE ha
  refine ⟨(Nat.gcdA s (p ^ m) : 𝓞 I.E) * a + (Nat.gcdB s (p ^ m) : 𝓞 I.E) * b, ?_⟩
  have hA : (((Nat.gcdA s (p ^ m) : ℤ) : 𝓞 I.E) : I.E) = ((Nat.gcdA s (p ^ m) : ℤ) : I.E) :=
    map_intCast (algebraMap (𝓞 I.E) I.E) _
  have hB : (((Nat.gcdB s (p ^ m) : ℤ) : 𝓞 I.E) : I.E) = ((Nat.gcdB s (p ^ m) : ℤ) : I.E) :=
    map_intCast (algebraMap (𝓞 I.E) I.E) _
  push_cast
  linear_combination ((Nat.gcdA s (p ^ m) : ℤ) : I.E) * ha - (b : I.E) * hzE -
    (p : I.E) ^ m * (a : I.E) * hA - (b : I.E) * (p : I.E) ^ m * hB
end PI.ScRefExists.PPA
