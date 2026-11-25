-- Prove2me | solution 1 for PI.Dv.GLatHermW.star_map_trace_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:49:04.226151+00:00
-- url     : https://prove2.me/submissions/4099cdeb-598a-4893-970b-8e3bc3f199ae

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_StarMapTraceOfPowEqOne
import Theorems.Thm_PI_Dv_GLatHermW_star_map_trace_of_pow_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLatHermW
open Matrix
open scoped ComplexOrder
namespace PI.Dv.GLatHermW
theorem _root_.solution {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (σ : K →+* ℂ)
    (τ : Representation K G W) (g : G) :
    star (σ (LinearMap.trace K W (τ g))) = σ (LinearMap.trace K W (τ g⁻¹)) := by
  have hn : 0 < Fintype.card G := Fintype.card_pos
  rw [star_map_trace_of_pow_eq_one σ (τ g) (Fintype.card G) hn
    (by rw [← map_pow, pow_card_eq_one, map_one])]
  congr 2
  rw [← map_pow]
  congr 1
  rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hn, pow_card_eq_one]
end PI.Dv.GLatHermW
