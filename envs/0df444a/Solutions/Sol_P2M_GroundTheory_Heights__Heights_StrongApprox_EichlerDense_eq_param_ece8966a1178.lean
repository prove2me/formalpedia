-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_eq_param_ece8966a1178
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:19:58.16827+00:00
-- url     : https://prove2.me/submissions/496fd64c-7178-47ef-a17d-2b9eed16e02e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerDense
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



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
omit hσ hJ
namespace GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
theorem _root_.solution
    (hfix : ∀ u, hf σ J u e = 0 → hf σ J u f = 0 → perpProj σ J e f u = u)
    {M : Matrix (Fin N) (Fin N) R} (hM : M ∈ eichAlong σ J e f) : ∃ p, M = param σ J e f κ p := by
  obtain ⟨u, c, hue, huf, hc, rfl⟩ := hM
  refine ⟨(u, κ * c), ?_⟩
  simp only [param, hfix u hue huf]
  congr 1
  rw [map_mul, hσκ]
  linear_combination κ * hc - c * hκ
end GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
