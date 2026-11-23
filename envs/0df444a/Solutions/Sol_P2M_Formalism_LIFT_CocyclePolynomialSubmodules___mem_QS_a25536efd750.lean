-- Prove2me | solution 1 for P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_QS_a25536efd750
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:04.167796+00:00
-- url     : https://prove2.me/submissions/18fb1505-b186-43b4-9a05-ab8336b23a8e

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
import Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_mem_QS
import Theorems.Thm_P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_N_4814b9af5558

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
theorem _root_.solution {y : D} (hy : y ∈ QS W) : W.γ y ∈ QS W := by
  rw [mem_QS] at hy ⊢
  unfold WD.QInv at hy ⊢
  obtain ⟨t, ht, hQ⟩ := B.9
  have h1 := γ_mem_N W hy
  rw [W.γ_smul, map_pow, hQ, mul_pow, mul_comm (B.Q ^ M), mul_smul] at h1
  obtain ⟨v, hv⟩ := ht.pow M
  have h2 := W.N.smul_mem (↑v⁻¹ : A) h1
  rwa [← hv, smul_smul, Units.inv_mul, one_smul] at h2
end Formalism.LIFT.CocyclePolynomialSubmodules
