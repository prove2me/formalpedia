-- Prove2me | solution 1 for PI.Dv.Tr.exists_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:20.211469+00:00
-- url     : https://prove2.me/submissions/be8528c4-2afa-43ae-8707-4006792af731

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Theorems.Thm_PI_Dv_Tr_eS_in_ideal
import Theorems.Thm_PI_Dv_Tr_vanish
import Theorems.Thm_PI_Dv_Tr_eG_comm
import Theorems.Thm_PI_Dv_Tr_eG_idem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module NumberField
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.Tr
theorem _root_.solution (T : GoodSet K G) (P0 P : Pair K G) (hM : M1 T P0) {V : Type} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (x : V) (hx : x ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eG T)))
    (hx0 : x ≠ 0) : ∃ g, ρ.asAlgebraHom (eps P0) (ρ g x) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hx0
  have hes : ∀ s, ρ.asAlgebraHom (eS T s) x = 0 := by
    intro s
    have hY : (T.tau s).asAlgebraHom (eps P0) ≠ 0 := by
      intro h0
      have := hM s
      rw [nS, h0, LinearMap.range_zero, finrank_bot] at this
      exact zero_ne_one this
    obtain ⟨n, a, b, hab⟩ := eS_in_ideal T s P0 hY
    rw [← hab, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, Module.End.mul_apply, vanish ρ P0 x hcon, map_zero]
  obtain ⟨z, rfl⟩ := hx
  have he : ρ.asAlgebraHom (eG T) (ρ.asAlgebraHom (eps P * eG T) z) = ρ.asAlgebraHom (eps P * eG T) z := by
    rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, ← eG_comm, mul_assoc, eG_idem]
  rw [← he, eG, map_sum, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun s _ => hes s
end PI.Dv.Tr
