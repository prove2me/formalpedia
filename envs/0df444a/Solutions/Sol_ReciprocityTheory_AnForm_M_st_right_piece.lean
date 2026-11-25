-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_right_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:33:54.060424+00:00
-- url     : https://prove2.me/submissions/9af4f68a-c2db-42d1-b964-9d984b94cf3f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_maDens_cons_congr
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_mInt_eq_piece
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_locDens_piece
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_isPotential_cons
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_locDens_cons_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_smooth_continuous


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
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))
include hΦ hGo hG hGU
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (w ψ : X → ℝ) (hw : A.Smooth w) (hψ : A.Smooth ψ) (hψG : tsupport ψ ⊆ G) :
    mInt A (Fin.cons (LocPot.ofFun ψ) Φ) w =
      ∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
        (w ∘ (A.chart j).symm) y *
          maDens (Fin.cons ((A.chart j).target.indicator (ψ ∘ (A.chart j).symm))
            fun i => (Φ i).φ (x0 i) ∘ (A.chart j).symm) y := by
  obtain ⟨ρ, hρs, hρ1, -⟩ := exists_tsupport_one_of_isOpen_isClosed hGo
    isClosed_closure.isCompact (isClosed_tsupport ψ) hψG
  have hpot := st_isPotential_cons A hψ hΦ

  have h1 : mInt A (Fin.cons (LocPot.ofFun ψ) Φ) w =
      mInt A (Fin.cons (LocPot.ofFun ψ) Φ) (fun x => ρ x * w x) := by
    unfold mInt
    split_ifs with hP
    · unfold integralWith
      refine Finset.sum_congr rfl fun k _ => ?_
      refine setIntegral_congr_fun (A.chart k).open_target.measurableSet ?_
      intro y hy
      by_cases hs : (A.chart k).symm y ∈ tsupport ψ
      · simp [hρ1 hs]
      · simp [st_locDens_cons_eq_zero A k ψ Φ hy hs]
    · rfl
  rw [h1, st_mInt_eq_piece A _ hpot j G hG (fun x => ρ x * w x) (ρ.continuous.mul (st_smooth_continuous A hw))
    ((tsupport_mul_subset_left).trans hρs)]
  refine setIntegral_congr_fun ((A.chart j).isOpen_inter_preimage_symm hGo).measurableSet ?_
  intro y hy
  have hV : (A.chart j).target ∩ (A.chart j).symm ⁻¹' G ∈ 𝓝 y :=
    ((A.chart j).isOpen_inter_preimage_symm hGo).mem_nhds hy
  have hev : ψ ∘ (A.chart j).symm =ᶠ[𝓝 y] (A.chart j).target.indicator (ψ ∘ (A.chart j).symm) := by
    filter_upwards [hV] with z hz
    rw [indicator_of_mem hz.1]
  simp only
  rw [st_locDens_piece A Φ hΦ j G hG x0 hGU ψ hψ hy, ← st_maDens_cons_congr _ hev]
  by_cases hs : (A.chart j).symm y ∈ tsupport ψ
  · simp [hρ1 hs]
  · have h0 := st_locDens_cons_eq_zero A j ψ Φ hy.1 hs
    rw [st_locDens_piece A Φ hΦ j G hG x0 hGU ψ hψ hy] at h0
    simp [h0]
end ReciprocityTheory.AnForm.M
