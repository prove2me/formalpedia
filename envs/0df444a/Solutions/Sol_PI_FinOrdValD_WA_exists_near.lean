-- Prove2me | solution 1 for PI.FinOrdValD.WA.exists_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:57.169792+00:00
-- url     : https://prove2.me/submissions/1153fe17-2689-438f-bd64-1259eefc5a68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderValuation_WeakApprox
import Theorems.Thm_PI_FinOrdValD_WA_val_alg
import Theorems.Thm_PI_FinOrdValD_WA_exists_nat_small

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open PI PI.FinOrdValD PI.FinOrdValD.WA
variable {L : Type*} [Field L] [NumberField L]
namespace PI.FinOrdValD.WA
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) (x : v.adicCompletion L) {δ : ℤᵐ⁰} (hδ : δ ≠ 0) :
    ∃ b : L, Valued.v (algebraMap L (v.adicCompletion L) b - x) < δ := by
  have hd : DenseRange (algebraMap L (v.adicCompletion L)) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap L v
  have hs : {y : v.adicCompletion L | Valued.v (y - x) < δ} ∈ nhds x := by
    obtain ⟨N, hN, hNv⟩ := exists_nat_small {v} (fun _ => δ) (fun _ _ => hδ)
    have hNv' := hNv v (Finset.mem_singleton_self v)
    set z : v.adicCompletion L := algebraMap L (v.adicCompletion L) (N : L) with hz
    have hz0 : z ≠ 0 := by
      rw [hz, Ne, map_eq_zero_iff _ (algebraMap L (v.adicCompletion L)).injective]
      exact_mod_cast hN.ne'
    have hvz : Valued.v z < δ := by rw [hz, val_alg]; exact hNv'
    rw [Valued.mem_nhds]
    refine ⟨Units.mk0 (Valued.v.restrict z) ((Valuation.ne_zero_iff _).mpr hz0), fun y hy => ?_⟩
    have hy' : Valued.v.restrict (y - x) < Valued.v.restrict z := hy
    rw [Valuation.restrict_lt_iff] at hy'
    exact lt_trans hy' hvz
  obtain ⟨_, hy, ⟨b, rfl⟩⟩ := mem_closure_iff_nhds.mp (hd x) _ hs
  exact ⟨b, hy⟩
end PI.FinOrdValD.WA
