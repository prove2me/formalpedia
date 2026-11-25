-- Prove2me | solution 1 for PI.Dv.RK.L_eps_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:45:23.988661+00:00
-- url     : https://prove2.me/submissions/a37b337d-08ce-44a9-a933-39a8b2555549

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_OfMulEps
import Theorems.Thm_PI_Dv_RK_of_mul_eps
import Theorems.Thm_PI_Dv_RK_L_j

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.RK
open MonoidAlgebra
variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE}
variable (M : GMap K σ G T EE ρE)
namespace PI.Dv.RK
theorem _root_.solution (P : Pair K G) (v : M.V) : L M (eps P) v ∈ eigP σ P M.rho := by
  rw [eigP, Submodule.mem_iInf]
  intro h
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  have hK : M.rhoK (h : G) * M.rhoK.asAlgebraHom (eps P) =
      ((P.chi h : Kˣ) : K) • M.rhoK.asAlgebraHom (eps P) := by
    rw [← Representation.asAlgebraHom_of, ← map_mul, of_mul_eps, map_smul]
  have hL : M.rho (h : G) * L M (eps P) = σ ((P.chi h : Kˣ) : K) • L M (eps P) := by
    refine LinearMap.ext_on_range M.j_span fun x => ?_
    have hx := LinearMap.congr_fun hK x
    rw [Module.End.mul_apply, LinearMap.smul_apply] at hx
    rw [Module.End.mul_apply, L_j, ← M.j_eq, hx, LinearMap.smul_apply, L_j, LinearMap.map_smulₛₗ]
  exact LinearMap.congr_fun hL v
end PI.Dv.RK
