-- Prove2me | solution 1 for PI.Dv.Tr.trace_mul_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:56.598822+00:00
-- url     : https://prove2.me/submissions/3e500cd0-95c9-4559-8d3b-9e20e8c65d41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Theorems.Thm_PI_Dv_Tr_phiS_apply
import Theorems.Thm_PI_Dv_Tr_mul_eS
import Theorems.Thm_PI_Dv_Tr_scalar_of_comm

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
open PI.Dv
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.Tr
theorem _root_.solution (T : GoodSet K G) (s : T.S) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) :
    ∃ c : K, ∀ a : MonoidAlgebra K G,
      LinearMap.trace K V (ρ.asAlgebraHom (a * eS T s)) = c * LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom a) := by
  set Z : Module.End K (T.W s) := ∑ x : G, (cf T s * LinearMap.trace K V (ρ x)) • T.tau s x⁻¹ with hZ
  have hcomm : ∀ g, Z * T.tau s g = T.tau s g * Z := by
    intro g
    rw [hZ, Finset.sum_mul, Finset.mul_sum]
    simp_rw [smul_mul_assoc, mul_smul_comm, ← map_mul]
    refine (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ (fun x => ?_)).symm
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    have h1 : LinearMap.trace K V (ρ (g * x * g⁻¹)) = LinearMap.trace K V (ρ x) := by
      rw [ρ.map_mul, ρ.map_mul, LinearMap.trace_mul_comm, ← mul_assoc, ← ρ.map_mul, inv_mul_cancel,
        ρ.map_one, one_mul]
    have h2 : (g * x * g⁻¹)⁻¹ * g = g * x⁻¹ := by group
    rw [h1, h2]
  obtain ⟨c, hc⟩ := scalar_of_comm T s Z hcomm
  refine ⟨c, fun a => ?_⟩
  rw [mul_eS, phiS_apply, map_sum, map_sum]
  simp only [map_smul, Representation.asAlgebraHom_of, smul_eq_mul]
  have : LinearMap.trace K (T.W s) (Z * (T.tau s).asAlgebraHom a) =
      c * LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom a) := by
    rw [hc, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
  rw [← this, hZ, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]
  ring
end PI.Dv.Tr
