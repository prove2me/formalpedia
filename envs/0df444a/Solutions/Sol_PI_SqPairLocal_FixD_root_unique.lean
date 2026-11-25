-- Prove2me | solution 1 for PI.SqPairLocal.FixD.root_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:12.522995+00:00
-- url     : https://prove2.me/submissions/aba791db-c616-4c44-9bcb-3795e0d52eae

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnitIffSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open PI PI.SqPairLocal PI.SqPairLocal.FixD
variable {R : Type} [CommRing R] [IsDomain R] (σ : R ≃+* R)
namespace PI.SqPairLocal.FixD
theorem _root_.solution [IsLocalRing R] (g : R[X]) (a₀ b c : R) (hb : g.IsRoot b) (hc : g.IsRoot c)
    (hba : b - a₀ ∈ maximalIdeal R) (hca : c - a₀ ∈ maximalIdeal R)
    (hd : IsUnit (g.derivative.eval a₀)) : b = c := by
  obtain ⟨k, hk⟩ := g.binomExpansion c (b - c)
  have e : c + (b - c) = b := by ring
  rw [e, hb.eq_zero, hc.eq_zero, zero_add] at hk
  have hfac : (b - c) * (g.derivative.eval c + k * (b - c)) = 0 := by
    rw [hk]
    ring
  have hm : g.derivative.eval c - g.derivative.eval a₀ ∈ maximalIdeal R := by
    obtain ⟨d, hd'⟩ := Polynomial.sub_dvd_eval_sub c a₀ g.derivative
    rw [hd']
    exact Ideal.mul_mem_right _ _ hca
  have hbc : b - c ∈ maximalIdeal R := by
    have h3 := Ideal.sub_mem _ hba hca
    rwa [sub_sub_sub_cancel_right] at h3
  have hu : IsUnit (g.derivative.eval c + k * (b - c)) := by
    by_contra hnu
    have h1 : g.derivative.eval c + k * (b - c) ∈ maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).2 hnu
    have h2 : k * (b - c) ∈ maximalIdeal R := Ideal.mul_mem_left _ _ hbc
    have h3 := Ideal.sub_mem _ (Ideal.sub_mem _ h1 h2) hm
    refine (IsLocalRing.mem_maximalIdeal _).1 ?_ hd
    convert h3 using 1
    ring
  exact sub_eq_zero.1 ((hu.mul_left_eq_zero).1 hfac)
end PI.SqPairLocal.FixD
