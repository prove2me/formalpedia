-- Prove2me | solution 1 for P2M_Formalism_LIFT_CocyclePolynomialSubmodules_cocyclePolynomialDivision___mem_fact_66937407d807
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:52:59.6398+00:00
-- url     : https://prove2.me/submissions/fd6fc9c6-4bb8-43d3-8516-bf960547f727

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
theorem _root_.solution {n : D} (hn : n ∈ W.N) : W.φ (B.X ^ (M + 1) • n) ∈ W.N := by
  have e : (B.X * B.Q) ^ (M + 1) = (B.X ^ (M + 1) * B.Q) * B.Q ^ M := by ring
  rw [W.φ_smul, map_pow, B.7, e, mul_smul]
  exact W.N.smul_mem _ (W.φ_N n hn)
end Formalism.LIFT.CocyclePolynomialSubmodules
