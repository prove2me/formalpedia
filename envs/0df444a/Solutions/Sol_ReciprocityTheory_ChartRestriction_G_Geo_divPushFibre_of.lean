-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.divPushFibre_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:30:25.433845+00:00
-- url     : https://prove2.me/submissions/33979abd-c9ef-4561-8754-4506c3d6daa7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_proj_ne_zero_of_snc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (h1 : DivPushResSideStatement) (h2 : DivPushPointStatement) :
    DivPushFibreStatement := by
  unfold DivPushResSideStatement at h1
  unfold DivPushPointStatement at h2
  unfold DivPushFibreStatement
  intro K _ ι _ P J n R L B B₁ s r m W BW Ψ hAr hLs hBs hB1s hB1a hsec hsnc hHolo hΨ
  have hclosed : ∀ k, IsClosed (W k) := by
    intro k
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨ψ, -, hxs, -, σ, -, hW, -⟩ := hsnc x
    refine ⟨ψ.source ∩ {y | ∀ i, σ k = some i → ψ y i ≠ 0}, ?_, ?_, ?_⟩
    · rintro y ⟨hys, hy⟩ hyW
      have hyy : y ∈ W k ∩ ψ.source := ⟨hyW, hys⟩
      rw [hW k] at hyy
      obtain ⟨-, i, hi, h0⟩ := hyy
      exact hy i hi h0
    · cases hσ : σ k with
      | none =>
        have e : ψ.source ∩ {y | ∀ i, (none : Option (Fin (n + 1))) = some i → ψ y i ≠ 0} =
            ψ.source := by
          ext y
          simp
        rw [e]
        exact ψ.open_source
      | some i0 =>
        have e : ψ.source ∩ {y | ∀ i, some i0 = some i → ψ y i ≠ 0} =
            ψ.source ∩ (fun y => ψ y i0) ⁻¹' {0}ᶜ := by
          ext y
          simp
        rw [e]
        exact ((continuous_apply i0).comp_continuousOn ψ.continuousOn).isOpen_inter_preimage
          ψ.open_source isOpen_compl_singleton
    · refine ⟨hxs, fun i hi h0 => hx ?_⟩
      have hxx : x ∈ {y ∈ ψ.source | ∃ i, σ k = some i ∧ ψ y i = 0} := ⟨hxs, i, hi, h0⟩
      rw [← hW k] at hxx
      exact hxx.1
  have hres : ∀ k, m k ≠ 0 → _ := fun k hmk =>
    h1 K ι P J n R L B₁ Ψ (W k) (BW k) hAr hLs hB1s hB1a (hclosed k) (hHolo k)
      (fun x hx => proj_ne_zero_of_snc R hsnc hΨ hmk hx)
  have hint : ∀ k ∈ Finset.univ, Integrable (fun y => (m k : ℝ) * divFib R L B₁ Ψ (BW k) y) := by
    intro k _
    by_cases hmk : m k = 0
    · simp [hmk]
    · exact ((hres k hmk).1).const_mul _
  have step : ∀ k ∈ Finset.univ, (m k : ℝ) * mInt (BW k)
      (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val)
      ((fun x => Real.log (B₁.h (R.lift x x))) ∘ Subtype.val) =
        ∫ y, (m k : ℝ) * divFib R L B₁ Ψ (BW k) y := by
    intro k _
    by_cases hmk : m k = 0
    · simp [hmk]
    · rw [integral_const_mul, (hres k hmk).2]
  rw [Finset.sum_congr rfl step,
    ← integral_finset_sum Finset.univ (f := fun k y => (m k : ℝ) * divFib R L B₁ Ψ (BW k) y) hint]
  apply integral_congr_ae
  filter_upwards [h2 K ι P J n R L B B₁ s r m W BW Ψ hAr hLs hBs hB1s hB1a hsec hsnc hHolo hΨ]
    with y hy
  simpa using hy
end ReciprocityTheory.ChartRestriction.G.Geo
