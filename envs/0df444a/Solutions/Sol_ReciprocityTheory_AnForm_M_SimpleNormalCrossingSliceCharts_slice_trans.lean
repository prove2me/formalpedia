-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.slice_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:46.126938+00:00
-- url     : https://prove2.me/submissions/f547165e-b4f4-4771-8924-f9347d21c5b9

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas
import Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_sliceChart_symm_val
import Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_analyticAt_ins
import Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_analyticAt_removeNth_comp
import Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_compat_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Topology Filter Set
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
variable {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
theorem _root_.solution {e : ℕ} (A : FinHolAtlas (e + 1) X) (S : Set X)
    {ψ₁ ψ₂ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)} {i₁ i₂ : Fin (e + 1)}
    (h₁ : ∀ y ∈ ψ₁.source, y ∈ S ↔ ψ₁ y i₁ = 0) (h₂ : ∀ y ∈ ψ₂.source, y ∈ S ↔ ψ₂ y i₂ = 0)
    (w₁ w₂ : S) (hc₁ : IsCompatChart A ψ₁) (hc₂ : IsCompatChart A ψ₂) :
    AnalyticOnNhd ℂ (sliceChart ψ₂ i₂ S h₂ w₂ ∘ (sliceChart ψ₁ i₁ S h₁ w₁).symm)
      ((sliceChart ψ₁ i₁ S h₁ w₁).target ∩
        (sliceChart ψ₁ i₁ S h₁ w₁).symm ⁻¹' (sliceChart ψ₂ i₂ S h₂ w₂).source) := by
  intro z hz
  have hzt : Fin.insertNth (α := fun _ => ℂ) i₁ 0 z ∈ ψ₁.target := hz.1
  have hval := sliceChart_symm_val ψ₁ i₁ S h₁ w₁ hzt
  have hsrc : ψ₁.symm (Fin.insertNth (α := fun _ => ℂ) i₁ 0 z) ∈ ψ₂.source := by
    have h2 := hz.2
    rw [← hval]
    exact h2
  have hF : AnalyticAt ℂ
      (fun z' : Fin e → ℂ => (ψ₂ ∘ ψ₁.symm) (Fin.insertNth (α := fun _ => ℂ) i₁ 0 z')) z :=
    (compat_trans A hc₁ hc₂ hzt hsrc).comp (analyticAt_ins i₁ z)
  have hG := analyticAt_removeNth_comp i₂ hF
  apply hG.congr
  filter_upwards [(sliceChart ψ₁ i₁ S h₁ w₁).open_target.mem_nhds hz.1] with z' hz'
  show _ = i₂.removeNth (ψ₂ (((sliceChart ψ₁ i₁ S h₁ w₁).symm z' : S) : X))
  rw [sliceChart_symm_val ψ₁ i₁ S h₁ w₁ hz']
  rfl
end ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
