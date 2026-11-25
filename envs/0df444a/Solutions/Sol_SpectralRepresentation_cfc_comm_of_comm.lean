-- Prove2me | solution 1 for SpectralRepresentation.cfc_comm_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:58.932749+00:00
-- url     : https://prove2.me/submissions/2884e70f-e1a5-47d7-9dab-01656803e23f

module
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence
public import Definitions.Def_BasicResults_Spectral_Projection
public import Theorems.Thm_SpectralRepresentation_cfcHom_comm_of_comm

set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap
open SpectralRepresentation
open Filter Topology
open scoped InnerProductSpace
variable {H₁ H₂ : Type*}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
namespace SpectralRepresentation
theorem _root_.solution {P : H₁ →L[ℂ] H₁} (hP : IsSelfAdjoint P) (J : H₁ →L[ℝ] H₁)
    (hJP : ∀ x, J (P x) = P (J x)) {g : ℝ → ℝ} (hg : Continuous g) (x : H₁) :
    J (cfc g P x) = cfc g P (J x) := by
  rw [cfc_apply (a := P) (ha := hP) (hf := hg.continuousOn)]
  exact cfcHom_comm_of_comm hP J hJP _ x
end SpectralRepresentation
