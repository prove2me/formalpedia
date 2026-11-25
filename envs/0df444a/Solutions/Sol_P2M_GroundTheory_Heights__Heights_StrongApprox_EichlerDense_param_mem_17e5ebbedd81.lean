-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_param_mem_17e5ebbedd81
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:20:14.089809+00:00
-- url     : https://prove2.me/submissions/f512c57e-ae97-46e3-b7d8-e028fc3dde91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerDense
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
variable {R : Type*} [CommRing R] {N : ℕ}
variable {σ : R →+* R} (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin N) (Fin N) R} (hJ : Jᵀ = J.map σ)
  {e f : Fin N → R} {κ : R} (hκ : κ + κ = 1) (hσκ : σ κ = κ)
include hσ hJ hκ hσκ
namespace GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
theorem _root_.solution
    (hP : ∀ u, hf σ J (perpProj σ J e f u) e = 0 ∧ hf σ J (perpProj σ J e f u) f = 0)
    (p : (Fin N → R) × R) : param σ J e f κ p ∈ eichAlong σ J e f := by
  refine ⟨perpProj σ J e f p.1, _, (hP p.1).1, (hP p.1).2, ?_, rfl⟩
  have hh := hf_symm hσ hJ (perpProj σ J e f p.1) (perpProj σ J e f p.1)
  rw [map_sub, map_sub, map_mul, hσ, hσκ, hh]
  linear_combination (-(hf σ J (perpProj σ J e f p.1) (perpProj σ J e f p.1))) * hκ
end GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
