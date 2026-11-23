-- Prove2me | solution 1 for PI.Dv.TIW.BlockHyp.phi_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:28.525822+00:00
-- url     : https://prove2.me/submissions/6b5b6e13-db6e-41d1-af8e-6eecc5611556

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp
import Theorems.Thm_P2M_PI_Dv_TIW__t_apply_09160b2633db

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
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {n : ℕ}
variable {X Y : Submodule K V} {Φ Ψ : Fin n → V →ₗ[K] V} {Γ : Matrix (Fin n) (Fin n) K}
namespace PI.Dv.TIW
namespace BlockHyp
theorem _root_.solution (H : BlockHyp X Y Φ Ψ Γ) (x : Fin n → V) (hx : x ∈ Submodule.pi Set.univ fun _ => X) :
    Φt Φ x ∈ Y := by
  rw [Φt_apply]
  exact Y.sum_mem fun i _ => H.h2 i _ (hx i (Set.mem_univ i))
end BlockHyp
end PI.Dv.TIW
