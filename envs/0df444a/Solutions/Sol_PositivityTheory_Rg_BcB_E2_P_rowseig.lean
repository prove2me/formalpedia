-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.rowseig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:21:57.976892+00:00
-- url     : https://prove2.me/submissions/ba219b41-c0ee-4d41-8b77-ae58cf5da95a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Rowseig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
namespace PositivityTheory.Rg.BcB.E2.P
theorem _root_.solution : AeEq → Unfold → RowsEig := by
  intro hAe hUn X ι _ Φ T T₁ k u u' hΦ hT hk heq x i
  have wc : ∀ j, Continuous fun y => inner ℂ (k j y) u := fun j => (hk.cont j).inner continuous_const
  have winv : ∀ j, ∀ γ ∈ X.Γ, ∀ y, (fun y => inner ℂ (k j y) u) (γ * y) = (fun y => inner ℂ (k j y) u) y :=
    fun j γ hγ y => by simp only [hk.inv j γ hγ y]
  have hLc : Continuous fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ :=
    continuous_finsetSum _ fun j _ => (hUn X (Φ i j) _ (hΦ i j) (wc j) (winv j)).2
  have hRc : Continuous fun x => inner ℂ (k i x) u' := (hk.cont i).inner continuous_const
  have hLinv : ∀ γ ∈ X.Γ, ∀ x, (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) (γ * x)
      = (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) x := by
    intro γ hγ x
    refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [mul_assoc, hk.inv j γ hγ]
  have hRinv : ∀ γ ∈ X.Γ, ∀ x, (fun x => inner ℂ (k i x) u') (γ * x) = (fun x => inner ℂ (k i x) u') x :=
    fun γ hγ x => by simp only [hk.inv i γ hγ x]
  have h3 : (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ)
      = fun x => ∑ j, ∫ y, ker X.Γ (Φ i j) x y * (T₁ u j : X.G → ℂ) y ∂X.ν := by
    funext x
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 := (hUn X (Φ i j) _ (hΦ i j) (wc j) (winv j)).1 x
    refine e1.symm.trans (integral_congr_ae ((hk.rep u j).mono fun y hy => ?_))
    simp only [hy]
  have hae : (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) =ᵐ[X.ν]
      fun x => inner ℂ (k i x) u' := by
    rw [h3]
    have h1 := hT (T₁ u) i
    rw [heq] at h1
    exact h1.symm.trans (hk.rep u' i)
  exact congrFun (hAe X _ _ hLc hRc hLinv hRinv hae) x
end PositivityTheory.Rg.BcB.E2.P
