-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.continuousOn_iteratedFDeriv_translate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:37.029678+00:00
-- url     : https://prove2.me/submissions/95c34db4-f752-49a0-a96a-3de7f80ae4fa

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_iteratedFDeriv_left_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (Kg : Type) [TopologicalSpace Kg] (ι : Kg → M2 n) (hι : Continuous ι) (c : Kg → ℂ) (hc : Continuous c) (N : ℕ) :
    ContinuousOn (fun y : Kg × M2 n => iteratedFDeriv ℂ N (fun x => F (ι y.1 * x) * c y.1) y.2)
      (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U}) := by
  let Lm : M2 n →L[ℂ] (M2 n →L[ℂ] M2 n) :=
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℂ (M2 n)).toContinuousLinearMap
  have key : ∀ y ∈ Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U},
      iteratedFDeriv ℂ N (fun x => F (ι y.1 * x) * c y.1) y.2 =
        c y.1 • ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
          (fun _ : Fin N => M2 n) (fun _ => M2 n) ℂ (fun _ => Lm (ι y.1))
          (iteratedFDeriv ℂ N F (ι y.1 * y.2)) := by
    rintro ⟨k, x⟩ ⟨-, hx⟩
    have hx' : ι k * x ∈ U := hx k
    have hcd : ContDiffAt ℂ N (fun z => F (ι k * z)) x := by
      have h1 : ContDiffAt ℂ ∞ F (Lm (ι k) x) := hF.contDiffAt (hU.mem_nhds hx')
      exact (h1.comp x (Lm (ι k)).contDiff.contDiffAt).of_le (by exact_mod_cast le_top)
    have hfun : (fun z => F (ι k * z) * c k) = c k • (fun z => F (ι k * z)) := by
      funext z
      simp [mul_comm]
    simp only
    rw [hfun, iteratedFDeriv_const_smul_apply hcd]
    congr 1
    ext v
    rw [iteratedFDeriv_left_mul F U hU hF (ι k) x hx' N v]
    rfl
  refine ContinuousOn.congr ?_ key
  refine ContinuousOn.smul (hc.comp continuous_fst).continuousOn ?_
  have hD : ContinuousOn (iteratedFDeriv ℂ N F) U := by
    have := hF.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast le_top) hU.uniqueDiffOn
    exact this.congr (fun y hy => (iteratedFDerivWithin_of_isOpen N hU hy).symm)
  have h1 : ContinuousOn (fun y : Kg × M2 n => iteratedFDeriv ℂ N F (ι y.1 * y.2))
      (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U}) :=
    hD.comp ((hι.comp continuous_fst).mul continuous_snd).continuousOn (fun y hy => hy.2 y.1)
  have h2 : Continuous (fun y : Kg × M2 n =>
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
        (fun _ : Fin N => M2 n) (fun _ => M2 n) ℂ (fun _ => Lm (ι y.1))) :=
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
        (fun _ : Fin N => M2 n) (fun _ => M2 n) ℂ).cont.comp
      (continuous_pi fun _ => Lm.continuous.comp (hι.comp continuous_fst))
  exact h2.continuousOn.clm_apply h1
end PositivityTheory.Rg.Sw.LVs
