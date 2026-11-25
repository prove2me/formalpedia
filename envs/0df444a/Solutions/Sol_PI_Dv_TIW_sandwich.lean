-- Prove2me | solution 1 for PI.Dv.TIW.sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:24:52.850683+00:00
-- url     : https://prove2.me/submissions/27a18baf-9dc8-4ea9-8742-7a0c58479524

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TraceMemOfIntR
import Theorems.Thm_PI_Dv_TIW_epsS_eq_smul
import Theorems.Thm_PI_Dv_TIW_tau_eps_idem
import Theorems.Thm_PI_Dv_TIW_rank_one_sandwich


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv NumberField
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K G W)
namespace PI.Dv.TIW
theorem _root_.solution (P0 : Pair K G) (h1 : Module.finrank K (LinearMap.range (τ.asAlgebraHom (eps P0))) = 1)
    (z : MonoidAlgebra K G) :
    τ.asAlgebraHom (epsS P0 * z * eps P0) =
      LinearMap.trace K W (τ.asAlgebraHom (epsS P0 * z)) • τ.asAlgebraHom (eps P0) := by
  have hL : τ.asAlgebraHom (epsS P0 * z * eps P0) = ((Nat.card P0.H : ℕ) : K) •
      (τ.asAlgebraHom (eps P0) * τ.asAlgebraHom z * τ.asAlgebraHom (eps P0)) := by
    rw [epsS_eq_smul, smul_mul_assoc, smul_mul_assoc, map_smul, map_mul, map_mul]
  have hR : LinearMap.trace K W (τ.asAlgebraHom (epsS P0 * z)) = ((Nat.card P0.H : ℕ) : K) *
      LinearMap.trace K W (τ.asAlgebraHom (eps P0) * τ.asAlgebraHom z) := by
    rw [epsS_eq_smul, smul_mul_assoc, map_smul, map_smul, map_mul, smul_eq_mul]
  rw [hL, hR, rank_one_sandwich _ (tau_eps_idem τ P0) h1, smul_smul]
end PI.Dv.TIW
