-- Prove2me | solution 1 for P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_N_4814b9af5558
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:36.377735+00:00
-- url     : https://prove2.me/submissions/8a56cd7c-db06-46ad-900c-a497606a9de5

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Formalism.LIFT.CocyclePolynomialSubmodules
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
  {B : Base ℓ A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
  [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D)
namespace Formalism.LIFT.CocyclePolynomialSubmodules
theorem _root_.solution {n : D} (hn : n ∈ W.N) : W.γ n ∈ W.N := by
  obtain ⟨x', hx', h⟩ := W.γ_N n hn
  rw [← sub_add_cancel (W.γ n) n, h]
  exact W.N.add_mem (W.N.smul_mem _ hx') hn
end Formalism.LIFT.CocyclePolynomialSubmodules
