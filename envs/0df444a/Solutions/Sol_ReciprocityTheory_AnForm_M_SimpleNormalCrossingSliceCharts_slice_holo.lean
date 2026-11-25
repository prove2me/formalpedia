-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.slice_holo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:23.059586+00:00
-- url     : https://prove2.me/submissions/0319ebcc-912c-46f0-9f32-13e6cb7d90bf

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas
import Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_sliceChart_symm_val
import Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_analyticAt_ins

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
    {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)} {i : Fin (e + 1)}
    (hS : ∀ y ∈ ψ.source, y ∈ S ↔ ψ y i = 0) (w0 : S) (hc : IsCompatChart A ψ) (k : Fin A.n) :
    AnalyticOnNhd ℂ (A.chart k ∘ Subtype.val ∘ (sliceChart ψ i S hS w0).symm)
      ((sliceChart ψ i S hS w0).target ∩
        (sliceChart ψ i S hS w0).symm ⁻¹' (Subtype.val ⁻¹' (A.chart k).source)) := by
  intro z hz
  have hzt : Fin.insertNth (α := fun _ => ℂ) i 0 z ∈ ψ.target := hz.1
  have hval := sliceChart_symm_val ψ i S hS w0 hzt
  have hsrc : ψ.symm (Fin.insertNth (α := fun _ => ℂ) i 0 z) ∈ (A.chart k).source := by
    have h2 := hz.2
    rw [← hval]
    exact h2
  have hF : AnalyticAt ℂ
      (fun z' : Fin e → ℂ => (A.chart k ∘ ψ.symm) (Fin.insertNth (α := fun _ => ℂ) i 0 z')) z :=
    ((hc k).2 _ ⟨hzt, hsrc⟩).comp (analyticAt_ins i z)
  apply hF.congr
  filter_upwards [(sliceChart ψ i S hS w0).open_target.mem_nhds hz.1] with z' hz'
  show _ = A.chart k (((sliceChart ψ i S hS w0).symm z' : S) : X)
  rw [sliceChart_symm_val ψ i S hS w0 hz']
  rfl
end ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
