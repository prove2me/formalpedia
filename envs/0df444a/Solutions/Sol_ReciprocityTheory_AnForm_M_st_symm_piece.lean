-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_symm_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:55:21.515349+00:00
-- url     : https://prove2.me/submissions/38286d9d-dead-4d55-b3c5-3068cb856383

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_left_piece
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_right_piece
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
private lemma three_le_infty_withTop : (3 : WithTop ℕ∞) ≤ ∞ := by
  first
    | exact WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) ≤ ⊤)
    | exact_mod_cast le_top
    | simp
section Piece
variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))
end Piece
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))
include hΦ hGo hG hGU
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (hP : ReciprocityTheory.AnForm.A.PartsStatement) (w ψ : X → ℝ) (hw : A.Smooth w)
    (hψ : A.Smooth ψ) (hψG : tsupport ψ ⊆ G) :
    mInt A (Fin.cons (LocPot.ofFun w) Φ) ψ = mInt A (Fin.cons (LocPot.ofFun ψ) Φ) w := by
  rw [st_left_piece A Φ hΦ j G hGo hG x0 hGU w ψ hw hψ hψG,
    st_right_piece A Φ hΦ j G hGo hG x0 hGU w ψ hw hψ hψG]
  have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) :=
    (A.chart j).isOpen_inter_preimage_symm hGo
  have hsG : tsupport ψ ⊆ (A.chart j).source := hψG.trans hG
  have hKc : IsCompact ((A.chart j) '' tsupport ψ) :=
    (isClosed_tsupport ψ).isCompact.image_of_continuousOn ((A.chart j).continuousOn.mono hsG)
  have hsupp : Function.support ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) ⊆
      (A.chart j) '' tsupport ψ := by
    intro y hy
    have hy' := Function.mem_support.1 hy
    by_cases hyt : y ∈ (A.chart j).target
    · refine ⟨(A.chart j).symm y, subset_tsupport _ ?_, (A.chart j).right_inv hyt⟩
      rw [Set.indicator_of_mem hyt] at hy'
      exact hy'
    · exact absurd (Set.indicator_of_notMem hyt _) hy'
  have hts : tsupport ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) ⊆
      (A.chart j) '' tsupport ψ := closure_minimal hsupp hKc.isClosed
  have hKS : (A.chart j) '' tsupport ψ ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' G := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(A.chart j).map_source (hsG hx), ?_⟩
    show (A.chart j).symm ((A.chart j) x) ∈ G
    rw [(A.chart j).left_inv (hsG hx)]
    exact hψG hx
  have hH : ReciprocityTheory.AnForm.A.PartsHyp (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
      ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) (w ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) := by
    unfold ReciprocityTheory.AnForm.A.PartsHyp
    refine ⟨hSo, ?_, hKc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hKS, ?_, ?_⟩
    · exact (((hψ j).mono (fun y hy => ⟨hy.1, mem_univ _⟩)).of_le three_le_infty_withTop).congr
        (fun y hy => Set.indicator_of_mem hy.1 _)
    · exact ((hw j).mono (fun y hy => ⟨hy.1, mem_univ _⟩)).of_le three_le_infty_withTop
    · intro i
      exact (((hΦ i).1 (x0 i) j).mono (fun y hy => ⟨hy.1, hGU i hy.2⟩)).of_le three_le_infty_withTop
  have key := (hP e (fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm)
    ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm)) (w ∘ (A.chart j).symm)
    ((A.chart j).target ∩ (A.chart j).symm ⁻¹' G) hH).2.2.2.2
  exact key.symm
end ReciprocityTheory.AnForm.M
