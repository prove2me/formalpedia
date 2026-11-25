-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_partsHyp_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:45.343702+00:00
-- url     : https://prove2.me/submissions/22947e51-54b9-4c6d-a39e-28f04ea7721a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))
include hΦ hGo hG hGU
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (w ψ : X → ℝ) (hw : A.Smooth w) (hψ : A.Smooth ψ)
    (hψG : tsupport ψ ⊆ G) :
    PartsHyp (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
      ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) (w ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) := by
  have h3 : (3 : WithTop ℕ∞) ≤ ∞ := by
    first
    | exact_mod_cast (le_top : (3 : ℕ∞) ≤ ⊤)
    | exact WithTop.coe_le_coe.mpr le_top
    | norm_num
    | simp
  have hUo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) :=
    (A.chart j).isOpen_inter_preimage_symm hGo
  have hKc : IsCompact (tsupport ψ) := (isClosed_tsupport ψ).isCompact
  have hK : IsCompact ((A.chart j) '' tsupport ψ) :=
    hKc.image_of_continuousOn ((A.chart j).continuousOn.mono (hψG.trans hG))
  have hsupp : Function.support ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) ⊆
      (A.chart j) '' tsupport ψ := by
    intro y hy
    obtain ⟨ht, hs⟩ := Set.indicator_apply_ne_zero.mp hy
    exact ⟨(A.chart j).symm y, subset_tsupport _ hs, (A.chart j).right_inv ht⟩
  have htsK : tsupport ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) ⊆
      (A.chart j) '' tsupport ψ := closure_minimal hsupp hK.isClosed
  have hKU : (A.chart j) '' tsupport ψ ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G := by
    rintro _ ⟨x, hx, rfl⟩
    have hxs := hG (hψG hx)
    refine ⟨(A.chart j).map_source hxs, ?_⟩
    show (A.chart j).symm (A.chart j x) ∈ G
    rw [(A.chart j).left_inv hxs]
    exact hψG hx
  refine ⟨hUo, ?_, ?_, htsK.trans hKU, ?_, fun i => ?_⟩
  · exact (((hψ j).mono fun y hy => ⟨hy.1, Set.mem_univ _⟩).congr
      fun y hy => Set.indicator_of_mem hy.1 _).of_le h3
  · exact hK.of_isClosed_subset (isClosed_tsupport _) htsK
  · exact ((hw j).mono fun y hy => ⟨hy.1, Set.mem_univ _⟩).of_le h3
  · exact (((hΦ i).1 (x0 i) j).mono fun y hy => ⟨hy.1, hGU i hy.2⟩).of_le h3
end ReciprocityTheory.AnForm.M
