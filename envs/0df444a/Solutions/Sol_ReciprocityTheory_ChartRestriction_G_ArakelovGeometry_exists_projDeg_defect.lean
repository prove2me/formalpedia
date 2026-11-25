-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_projDeg_defect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:42:05.141264+00:00
-- url     : https://prove2.me/submissions/5523783b-a779-498e-b8df-4017b2b517ff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HSClosing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
attribute [instance] GDatum.fieldΩ GDatum.charΩ GDatum.fintypeκ
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (I : AllFam) (D : ℕ) (hA : StepA I D) (hT : StepT D)
    (hB : StepB I D) (hN : StepN D) (hM : StepM D) (hC : StepC I D) (d : GDatum D) :
    ∃ (A : Matrix (Ix d.κ) (Ix d.κ) ℚ) (e : Fin (D + 1) → Ix d.κ), IsInvMat A ∧
      IsProjFrame (matAct A d.x) e ∧
      (fun n => defect I D d.x d.m d.μ n -
        (projDeg (matAct A d.x) e : ℝ) * hsDefect D (chiP D) (hhOf I D) n) =o[atTop] pw D := by
  obtain ⟨A, e, hAinv, hPF⟩ := hN d.Ω d.κ d.x d.m d.μ d.good
  obtain ⟨m', μ', hTr, hG'⟩ := hT d.Ω d.κ d.x d.m d.μ A e d.good hAinv hPF
  obtain ⟨m₀, hPull, hG₀⟩ := hM d.Ω d.κ (matAct A d.x) m' μ' e hG' hPF
  refine ⟨A, e, hAinv, hPF, ?_⟩
  have h1 := hC d.Ω d.κ (matAct A d.x) m₀ μ' e hG₀ hPF hPull
  have h2 := hA d.Ω d.κ (matAct A d.x) m₀ m' μ' e hPF hG₀ hG'
  have h3 := hB d.Ω d.κ d.x d.m m' d.μ μ' A e d.good hAinv hPF hTr hG'
  refine ((h1.add h2).sub h3).congr_left (fun n => ?_)
  ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
