-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.hessC_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:20.902222+00:00
-- url     : https://prove2.me/submissions/89752052-9af1-47da-a7ad-4b5c54a856b9

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff ComplexOrder Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {D : ℕ} (ψ : (Fin D → ℂ) → ℝ) (V : Set (Fin D → ℂ)) (hV : IsOpen V)
    (hψ : ContDiffOn ℝ 2 ψ V) : ContinuousOn (hessC ψ) V := by
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ ψ y) V := hψ.fderiv_of_isOpen hV (by norm_num)
  have h2 : ContinuousOn (fun y => fderiv ℝ (fderiv ℝ ψ) y) V :=
    h1.continuousOn_fderiv_of_isOpen hV le_rfl

  have ev : ∀ a b : Fin D → ℂ, ContinuousOn (fun y => fderiv ℝ (fderiv ℝ ψ) y a b) V :=
    fun a b => (h2.clm_apply continuousOn_const).clm_apply continuousOn_const
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  unfold hessC
  dsimp only
  have hre := Complex.continuous_ofReal.comp_continuousOn
    ((ev (Pi.single i 1) (Pi.single j 1)).add
      (ev (Complex.I • Pi.single i 1) (Complex.I • Pi.single j 1)))
  have him := Complex.continuous_ofReal.comp_continuousOn
    ((ev (Pi.single i 1) (Complex.I • Pi.single j 1)).sub
      (ev (Complex.I • Pi.single i 1) (Pi.single j 1)))
  exact (hre.add (continuousOn_const.mul him)).div_const 4
end ReciprocityTheory.AnForm.M
