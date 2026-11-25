-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.isOpen_OmF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:57:04.700934+00:00
-- url     : https://prove2.me/submissions/f4ec04a2-c594-4966-b663-2eacb98b0c64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_cd_cpt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
open scoped ComplexConjugate ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
theorem _root_.solution : IsOpen (OmF X x0) := by
  have hmat : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => mat x τ := fun τ =>
    continuous_matrix fun a b => (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))
  have hent : ∀ (τ : X.Ψ) (a b : Fin r), Continuous fun x : Frame X.Ψ r => x τ a b := fun τ a b =>
    (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))
  have hdmin : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor
    refine Continuous.matrix_det ?_
    refine continuous_matrix fun a b => ?_
    simp only [Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC,
      ReciprocityTheory.ChartRestriction.G.FD.col, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.of_apply]
    refine continuous_finset_sum _ fun c _ => continuous_finset_sum _ fun d _ => ?_
    exact ((hent τ c _).mul continuous_const).mul (Complex.continuous_conj.comp (hent τ d _))
  have hGG : GG X.Ψ X.Gm X.p0 = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x : Frame X.Ψ r | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x
    simp [GG]
  have hopen : IsOpen (GG X.Ψ X.Gm X.p0) := by
    rw [hGG]
    refine isOpen_iInter_of_finite fun τ => ?_
    refine IsOpen.inter (isOpen_ne_fun (hmat τ).matrix_det continuous_const)
      (isOpen_iInter_of_finite fun i => ?_)
    exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hdmin τ i)))
  exact (cd_cpt X x0).continuous.isOpen_preimage _ hopen
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
