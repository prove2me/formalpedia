-- Prove2me | solution 1 for PI.Dv.TIW.BlockHyp.psi_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:24.062614+00:00
-- url     : https://prove2.me/submissions/cff1ae03-98de-4972-9d43-ec8dc616ca21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp

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
theorem _root_.solution (H : BlockHyp X Y Φ Ψ Γ) (y : V) (hy : y ∈ Y) :
    LinearMap.pi Ψ y ∈ Submodule.pi Set.univ fun _ : Fin n => X :=
  fun j _ => H.h3 j y hy
end BlockHyp
end PI.Dv.TIW
