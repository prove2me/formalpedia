-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.exists_nonfixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:00:42.961212+00:00
-- url     : https://prove2.me/submissions/4798c100-b4a8-4dd0-8b5e-2745cec8a837

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertQRG
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_Hensel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) : ∃ θ : I.E, star θ ≠ θ := by
  by_contra h
  push_neg at h
  have htop : (⊥ : Subalgebra I.F I.E) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, ha⟩ := RingHom.mem_range.1 ((I.cm.fixed x).1 (h x))
    exact Algebra.mem_bot.2 ⟨a, ha⟩
  have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 htop
  rw [I.cm.deg2] at h1
  exact absurd h1 (by norm_num)
end PI.UnitaryGroupMassFormula.AdIndexEq
