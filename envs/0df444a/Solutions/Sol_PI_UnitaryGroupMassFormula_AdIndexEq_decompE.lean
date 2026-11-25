-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.decompE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:36:34.675596+00:00
-- url     : https://prove2.me/submissions/8b41fe15-4e91-4574-a1f1-9239f20ae194

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertQRG
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_Hensel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowD
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (θ : I.E) (hθ : star θ ≠ θ) (e : I.E) :
    ∃ f g : I.F, e = f • (1 : I.E) + g • θ := by
  have hli : LinearIndependent I.F ![(1 : I.E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hθ
      have h' : s • (1 : I.E) = -(t • θ) := eq_neg_of_add_eq_zero_left hst
      have hθeq : algebraMap I.F I.E (-(t⁻¹ * s)) = θ := by
        rw [Algebra.algebraMap_eq_smul_one, neg_smul, mul_smul, h', smul_neg, neg_neg,
          smul_smul, inv_mul_cancel₀ ht, one_smul]
      exact (I.cm.fixed θ).2 (RingHom.mem_range.2 ⟨_, hθeq⟩)
    refine ⟨?_, ht⟩
    subst ht
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact hst.resolve_right one_ne_zero
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [I.cm.deg2])
  have he : e ∈ Submodule.span I.F (Set.range ![(1 : I.E), θ]) := by
    rw [hsp]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun I.F).1 he
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp
end PI.UnitaryGroupMassFormula.AdIndexEq
