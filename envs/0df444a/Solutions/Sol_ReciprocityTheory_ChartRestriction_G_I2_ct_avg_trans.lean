-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ct_avg_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:09:55.402959+00:00
-- url     : https://prove2.me/submissions/1566308a-5ea7-4094-bf03-48b2ccf0976b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (Y : GT ι) (g : EuclideanSpace ℂ ι → ℝ)
    (hper : ∀ γ ∈ lat Y.b, ∀ v, g (v + γ) = g v) (a : EuclideanSpace ℂ ι) :
    (⨍ v in ZSpan.fundamentalDomain Y.b, g (v - a)) = ⨍ v in ZSpan.fundamentalDomain Y.b, g v := by
  have hD := ZSpan.isAddFundamentalDomain Y.b volume
  have hT : IsAddFundamentalDomain (Submodule.span ℤ (Set.range Y.b)).toAddSubgroup
      ((fun u => u + a) ⁻¹' ZSpan.fundamentalDomain Y.b) volume :=
    hD.preimage_of_equiv (measurePreserving_add_right volume a).quasiMeasurePreserving
      Function.bijective_id fun _ _ => add_assoc _ _ _
  have hg : ∀ (γ : (Submodule.span ℤ (Set.range Y.b)).toAddSubgroup) (x : EuclideanSpace ℂ ι),
      g (γ +ᵥ x) = g x := by
    rintro ⟨γ, hγ⟩ x
    have h := hper γ hγ x
    rw [add_comm] at h
    exact h
  simp only [MeasureTheory.setAverage_eq]
  congr 1
  have h1 := (measurePreserving_add_right volume a).setIntegral_preimage_emb
    (MeasurableEquiv.addRight a).measurableEmbedding (fun y => g (y - a)) (ZSpan.fundamentalDomain Y.b)
  simp only [add_sub_cancel_right] at h1
  rw [← h1]
  exact hT.setIntegral_eq hD hg
end ReciprocityTheory.ChartRestriction.G.I2
