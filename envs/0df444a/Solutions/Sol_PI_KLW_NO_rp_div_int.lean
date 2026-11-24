-- Prove2me | solution 1 for PI.KLW.NO.rp_div_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:47:18.843805+00:00
-- url     : https://prove2.me/submissions/5de90c1f-715a-443d-a490-f0ec101e3333

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.NO
variable {K : Type} [Field K] [NumberField K] {p : ℕ}
namespace PI.KLW.NO
theorem _root_.solution {y : K} (hy : y ∈ (algebraMap (𝓞 K) K).range) {m : ℤ} (hm : ¬ (p : ℤ) ∣ m)
    (hp : p.Prime) : Rp K p (y / m) := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm0
  have hcop : Nat.Coprime m.natAbs p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (by rwa [← Int.natCast_dvd])).symm
  refine ⟨m.natAbs, hcop, ?_⟩
  rcases Int.natAbs_eq m with h | h
  · have e : (m : K) = (m.natAbs : K) := by rw [← Int.cast_natCast]; exact congrArg _ h
    rw [← e, mul_div_cancel₀ _ hmK]; exact hy
  · have e : (m : K) = -(m.natAbs : K) := by rw [← Int.cast_natCast, ← Int.cast_neg]; exact congrArg _ h
    have e2 : (m.natAbs : K) = -(m : K) := by rw [e]; ring
    rw [e2, neg_mul, mul_div_cancel₀ _ hmK]; exact Subring.neg_mem _ hy
end PI.KLW.NO
