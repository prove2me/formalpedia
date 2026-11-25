-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.unwBack_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:34:32.83078+00:00
-- url     : https://prove2.me/submissions/c54af8de-c3dc-4a0b-a089-096fd5565657

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (K0 : Set M) (hK0 : IsCompact K0) (u : M → ℂ) (hu : ∀ x, x ∉ K0 → u x = 0) (x : M)
    (hx : x ∉ K0) (j : Fin n) : d n z j u x = 0 ∧ db n z j u x = 0 := by
  have key : ∀ h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source,
      fderiv ℝ (u ∘ (Classical.choose h).symm) (z x) = 0 := by
    intro h
    obtain ⟨he, hx'⟩ := Classical.choose_spec h
    set e := Classical.choose h
    have hzx : z x = e x := he hx'
    have hev : (u ∘ e.symm) =ᶠ[𝓝 (z x)] fun _ => (0 : ℂ) := by
      rw [hzx]
      have hopen : IsOpen K0ᶜ := hK0.isClosed.isOpen_compl
      have hc : ContinuousAt e.symm (e x) := e.continuousAt_symm (e.map_source hx')
      have hmem : K0ᶜ ∈ 𝓝 (e.symm (e x)) := by
        rw [e.left_inv hx']
        exact hopen.mem_nhds hx
      filter_upwards [hc.preimage_mem_nhds hmem] with y hy
      exact hu _ hy
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  unfold d db wd wdb
  constructor
  · split_ifs with h
    · rw [key h]
      simp
    · rfl
  · split_ifs with h
    · rw [key h]
      simp
    · rfl
end ReciprocityTheory.L2DbarEstimates.F
