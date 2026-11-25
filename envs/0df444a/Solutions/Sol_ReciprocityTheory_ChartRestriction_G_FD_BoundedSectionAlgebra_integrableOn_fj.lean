-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.integrableOn_fj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:59:35.367152+00:00
-- url     : https://prove2.me/submissions/0be496b3-07fb-4e8c-9599-693b7e06dfbb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_pnorm_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_dmin_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_nfac_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_dmin_flow_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_nfac_flow_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
theorem _root_.solution {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P) {ξ : Fin r → E}
    (hξ : herm X.Gm ξ ξ = 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ν : X.Ψ → ℝ) {D : Set (X.Ψ → ℝ)}
    (hD : volume D < ⊤) :
    IntegrableOn (fun s : X.Ψ → ℝ => P (X.flow ξ (fun τ => (s τ : ℂ)) x) *
      cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)) D := by
  obtain ⟨C, hC⟩ := hP.2
  have hsub : ∀ N : Matrix (Fin r) (Fin r) ℂ,
      N.submatrix (Fin.castLE (Nat.le_of_lt_succ (Fin.last r).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (Fin.last r).isLt)) = N := by
    intro N
    ext a b
    rfl

  have hflow_dom : ∀ s : X.Ψ → ℝ, X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom := by
    intro s τ
    have hd : ∀ i, dmin X.Gm (X.flow ξ (fun τ => (s τ : ℂ)) x) τ i = dmin X.Gm x τ i :=
      fun i => dmin_flow_real X hξ s x τ i
    refine ⟨?_, fun i => by rw [hd i]; exact (hx τ).2 i⟩
    intro hdet
    have hlast : dmin X.Gm (X.flow ξ (fun τ => (s τ : ℂ)) x) τ (Fin.last r) ≠ 0 := by
      rw [hd]
      exact dmin_ne X hx τ _
    apply hlast
    unfold dmin lminor
    rw [hsub]
    have hg : gram τ.1 X.Gm (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ) =
        (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ).transpose * (X.Gm.map τ.1) *
          (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ).map (starRingEnd ℂ) := by
      ext a b
      simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.map_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [hg, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet, zero_mul, zero_mul]

  have hcont_flow : Continuous fun s : X.Ψ → ℝ => X.flow ξ (fun τ => (s τ : ℂ)) x := by
    apply continuous_pi
    intro τ
    show Continuous fun s : X.Ψ → ℝ =>
      (X.flowMat ξ τ (s τ : ℂ) * mat x τ : Matrix (Fin r) (Fin r) ℂ)
    refine Continuous.matrix_mul ?_ continuous_const
    apply continuous_pi
    intro a
    apply continuous_pi
    intro b
    show Continuous fun s : X.Ψ → ℝ => X.flowMat ξ τ (s τ : ℂ) a b
    simp only [Data.flowMat, Matrix.of_apply]
    fun_prop
  have hcont : Continuous fun s : X.Ψ → ℝ => P (X.flow ξ (fun τ => (s τ : ℂ)) x) *
      cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) :=
    (hP.1.1.continuousOn.comp_continuous hcont_flow hflow_dom).mul (by fun_prop)
  have hexp1 : ∀ s : X.Ψ → ℝ, ‖cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)‖ = 1 := by
    intro s
    have h2 : -(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ) =
        ((-(4 * Real.pi * ∑ τ, ν τ * s τ) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [h2, Complex.norm_exp_ofReal_mul_I]
  haveI : Fact (volume D < ⊤) := ⟨hD⟩
  refine Integrable.mono' (integrable_const (C / X.nfac la x)) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => ?_)
  show ‖P (X.flow ξ (fun τ => (s τ : ℂ)) x) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)‖ ≤
    C / X.nfac la x
  rw [norm_mul, hexp1 s, mul_one]
  have hnf : X.nfac la (X.flow ξ (fun τ => (s τ : ℂ)) x) = X.nfac la x := nfac_flow_real X hξ s la x
  have h1 := hC _ (hflow_dom s)
  rw [pnorm_eq, hnf] at h1
  exact (le_div_iff₀ (nfac_pos X hx la)).mpr h1
end ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
