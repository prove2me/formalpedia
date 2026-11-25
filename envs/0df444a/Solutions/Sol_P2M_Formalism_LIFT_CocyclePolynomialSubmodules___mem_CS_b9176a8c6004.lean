-- Prove2me | solution 1 for P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_CS_b9176a8c6004
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:52:58.623418+00:00
-- url     : https://prove2.me/submissions/2dc79c5e-ea48-49db-aceb-dd65a09d3eba

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
import Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_mem_QS
import Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_mem_CS
import Theorems.Thm_P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_QS_a25536efd750

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
theorem _root_.solution {ω : D} (hω : ω ∈ CS W) : W.γ ω ∈ CS W := by
  rw [mem_CS] at hω ⊢
  obtain ⟨y, hy, rfl⟩ := hω
  obtain ⟨t, ht⟩ := B.8
  refine ⟨((algebraMap ℤ_[ℓ] A) ↑B.u + B.X * t) • W.γ y,
    (mem_QS W).mp ((QS W).smul_mem _ (γ_mem_QS W ((mem_QS W).mpr hy))), ?_⟩
  rw [W.γ_smul, ht, mul_smul]
end Formalism.LIFT.CocyclePolynomialSubmodules
