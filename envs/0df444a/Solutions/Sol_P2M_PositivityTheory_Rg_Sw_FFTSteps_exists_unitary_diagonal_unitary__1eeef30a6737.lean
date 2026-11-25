-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_FFTSteps_exists_unitary_diagonal_unitary__1eeef30a6737
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:48:28.470542+00:00
-- url     : https://prove2.me/submissions/5d930140-a283-46ec-8b02-f4bfc40598d8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ExistsUnitaryDiagonalUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Complex Filter Topology
open scoped ComplexConjugate ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
variable {ι A B : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.Rg.Sw.FFTSteps
theorem _root_.solution (g : Matrix ι ι ℂ) (hg : IsUnit g) :
    ∃ (u₁ u₂ : Matrix ι ι ℂ) (a : ι → ℝ), u₁ ∈ Matrix.unitaryGroup ι ℂ ∧
      u₂ ∈ Matrix.unitaryGroup ι ℂ ∧ g = u₁ * diagonal (fun i => cexp (a i)) * u₂ := by
  classical
  have hinj : Function.Injective g.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hg
  have hM : (gᴴ * g).PosDef := Matrix.PosDef.conjTranspose_mul_self g hinj
  have hspec : gᴴ * g = (hM.1.eigenvectorUnitary : Matrix ι ι ℂ) *
      diagonal (fun i => (hM.1.eigenvalues i : ℂ)) * star (hM.1.eigenvectorUnitary : Matrix ι ι ℂ) := by
    have h := hM.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hVmem : (hM.1.eigenvectorUnitary : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ :=
    hM.1.eigenvectorUnitary.2
  generalize (hM.1.eigenvectorUnitary : Matrix ι ι ℂ) = V at hspec hVmem
  have hV1 : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hVmem
  have hV2 : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hVmem
  have hlpos : ∀ i, 0 < hM.1.eigenvalues i := fun i => hM.eigenvalues_pos i
  generalize hM.1.eigenvalues = l at hspec hlpos
  set a : ι → ℝ := fun i => Real.log (l i) / 2 with ha
  have hDD : diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) * diagonal (fun i => cexp (a i)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    simp
  have hDs : star (diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ))) =
      diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact Complex.conj_ofReal _
  have hreal : ∀ i, Real.exp (-(a i)) * l i * Real.exp (-(a i)) = 1 := by
    intro i
    have h2 : Real.exp (-(a i)) * Real.exp (-(a i)) = (l i)⁻¹ := by
      rw [← Real.exp_add, show -(a i) + -(a i) = -Real.log (l i) by simp only [ha]; ring,
        Real.exp_neg, Real.exp_log (hlpos i)]
    calc Real.exp (-(a i)) * l i * Real.exp (-(a i))
        = (Real.exp (-(a i)) * Real.exp (-(a i))) * l i := by ring
      _ = 1 := by rw [h2, inv_mul_cancel₀ (hlpos i).ne']
  refine ⟨g * V * diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)), star V, a, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    calc star (g * V * diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ))) *
          (g * V * diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)))
        = diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) * (star V * (gᴴ * g) * V) *
            diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) := by
          rw [star_mul, star_mul, hDs, Matrix.star_eq_conjTranspose g]
          simp only [mul_assoc]
      _ = diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) * diagonal (fun i => (l i : ℂ)) *
            diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) := by
          rw [hspec, show star V * (V * diagonal (fun i => (l i : ℂ)) * star V) * V
              = diagonal (fun i => (l i : ℂ)) by
            simp only [← mul_assoc, hV1, one_mul]
            rw [mul_assoc, hV1, mul_one]]
      _ = 1 := by
          rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
          congr 1
          funext i
          exact_mod_cast hreal i
  · exact Unitary.star_mem hVmem
  · rw [mul_assoc (g * V), hDD, mul_one, mul_assoc, hV2, mul_one]
end PositivityTheory.Rg.Sw.FFTSteps
