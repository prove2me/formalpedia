-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_measurable_sheetSum_0ce06e8414ea
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:45.469451+00:00
-- url     : https://prove2.me/submissions/9b596107-20ca-4b0d-9591-556248aca35a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsSheetMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_measurable_maDens_fedcbcd77e6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_term_eq_ead537038306
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_exists_sheet_nhds_e78e98ed3372
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_isClosed_zeroSet_b1e5ce62660e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_finite_20785c71949c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.SheetSumMeasurable
variable {n d : ℕ}
open Classical
namespace GroundTheory.Heights₂.Heights.SheetSumMeasurable
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) (Φ : ℝ → ℝ → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    {g : (Fin n → ℂ) → ℝ} (hg : Measurable g) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    Measurable fun y => sheetSum J A
      (fun x s => Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y)) y := by
  choose σ U W hU hW hσc hσsec hWsh hxW using
    fun x : Fin n → ℂ => exists_sheet_nhds (J := J) (A := A) x

  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  have hcover : ∀ x, (∃ s, IsSheetAt J A x s) → ∃ k, x ∈ W (e k) := by
    intro x hx
    have : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hx⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨k, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    exact ⟨k, hxi⟩

  set E : ℕ → Set (Fin n → ℂ) := fun k => zeroSet J ∩ disjointed (fun k => W (e k)) k with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (isClosed_zeroSet J).measurableSet.inter
      (MeasurableSet.disjointed (fun k => (hW (e k)).measurableSet) k)
  have hEW : ∀ k, E k ⊆ zeroSet J ∩ W (e k) := fun k x hx =>
    ⟨hx.1, disjointed_subset (fun k => W (e k)) k hx.2⟩
  have hEdisj : ∀ k k' x, x ∈ E k → x ∈ E k' → k = k' := by
    intro k k' x hk hk'
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_disjointed (fun k => W (e k)) hne) hk.2 hk'.2
  have hEcover : ∀ x, (∃ s, IsSheetAt J A x s) → ∃ k, x ∈ E k := by
    intro x hx
    obtain ⟨m, hm⟩ := hcover x hx
    have hxZ : x ∈ zeroSet J := by
      obtain ⟨s, U₀, -, hxU₀, -, hsx, hsec, -⟩ := hx
      rw [← hsx]
      exact (hsec _ hxU₀).2
    have : x ∈ ⋃ k, disjointed (fun k => W (e k)) k := by
      rw [iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hm⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, hxZ, hk⟩

  set t : (Fin n → ℂ) → ℝ := fun x => if h : ∃ s, IsSheetAt J A x s then
    Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ x)) else 0 with ht
  have htdef : ∀ x, t x = if h : ∃ s, IsSheetAt J A x s then
      Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ x)) else 0 := fun x => rfl
  have htE : ∀ k x, x ∈ E k →
      t x = Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k' => φ k' ∘ σ (e k)) (A *ᵥ x)) := by
    intro k x hx
    have hsh := (hWsh (e k) x (hEW k hx)).2
    rw [htdef, dif_pos ⟨_, hsh⟩]
    exact term_eq Φ g φ hsh _
  have htS : ∀ x, t x ≠ 0 → ∃ s, IsSheetAt J A x s := by
    intro x hx
    by_contra h
    exact hx (by rw [htdef, dif_neg h])

  set σ' : ℕ → (Fin d → ℂ) → Fin n → ℂ := fun k => (U (e k)).piecewise (σ (e k)) fun _ => 0
    with hσ'
  set f : ℕ → (Fin d → ℂ) → ℝ := fun k => (U (e k) ∩ σ' k ⁻¹' E k).indicator
    (fun y => Φ (g (σ' k y)) (ReciprocityTheory.AnForm.maDens (fun k' => φ k' ∘ σ (e k)) y)) with hf
  have hσ'm : ∀ k, Measurable (σ' k) := fun k =>
    (hσc (e k)).measurable_piecewise continuousOn_const (hU (e k)).measurableSet
  have hfm : ∀ k, Measurable (f k) := fun k =>
    (hΦ.comp ((hg.comp (hσ'm k)).prodMk (measurable_maDens _))).indicator
      ((hU (e k)).measurableSet.inter (hσ'm k (hEm k)))

  have hpiece : ∀ (k : ℕ) (y : Fin d → ℂ) (F : Finset (Fin n → ℂ)),
      (∀ x, x ∈ F ↔ x ∈ fibre J A y) → ∑ x ∈ F, (E k).indicator t x = f k y := by
    intro k y F hF
    by_cases hy : y ∈ U (e k) ∧ σ (e k) y ∈ E k
    · have hσ'y : σ' k y = σ (e k) y := by simp [hσ', Set.piecewise_eq_of_mem _ _ _ hy.1]
      have hx0 : σ (e k) y ∈ F :=
        (hF _).2 ⟨(hEW k hy.2).1, (hσsec (e k) y hy.1).1⟩
      rw [Finset.sum_eq_single_of_mem _ hx0, Set.indicator_of_mem hy.2, htE k _ hy.2,
        (hσsec (e k) y hy.1).1, hf]
      · simp only
        rw [Set.indicator_of_mem (show y ∈ U (e k) ∩ σ' k ⁻¹' E k from
          ⟨hy.1, by simp only [Set.mem_preimage, hσ'y]; exact hy.2⟩), hσ'y]
      · intro x hxF hne
        refine Set.indicator_of_notMem (fun hxE => hne ?_) _
        obtain ⟨-, hAx⟩ := (hF x).1 hxF
        obtain ⟨-, hsh⟩ := hWsh (e k) x (hEW k hxE)
        obtain ⟨-, -, -, -, hsx, -⟩ := hsh
        rw [← hsx, hAx]
    · have hfy : f k y = 0 := by
        rw [hf]
        refine Set.indicator_of_notMem (fun hmem => hy ⟨hmem.1, ?_⟩) _
        have hσ'y : σ' k y = σ (e k) y := by simp [hσ', Set.piecewise_eq_of_mem _ _ _ hmem.1]
        have := hmem.2
        simp only [Set.mem_preimage, hσ'y] at this
        exact this
      rw [hfy]
      refine Finset.sum_eq_zero fun x hxF => Set.indicator_of_notMem (fun hxE => hy ?_) _
      obtain ⟨-, hAx⟩ := (hF x).1 hxF
      obtain ⟨hAU, hsh⟩ := hWsh (e k) x (hEW k hxE)
      obtain ⟨-, -, -, -, hsx, -⟩ := hsh
      rw [hAx] at hAU hsx
      exact ⟨hAU, hsx ▸ hxE⟩

  refine measurable_of_tendsto_metrizable (f := fun N y => ∑ k ∈ Finset.range N, f k y)
    (fun N => Finset.measurable_sum _ fun k _ => hfm k) (tendsto_pi_nhds.2 fun y => ?_)
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  have hsum : sheetSum J A (fun x s => Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y)) y =
      ∑ x ∈ hfin.toFinset, t x := by
    unfold sheetSum
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    rw [htdef, hx.2]
  refine tendsto_const_nhds.congr' ?_
  have hev : ∀ x ∈ hfin.toFinset, ∀ᶠ N in atTop,
      t x = ∑ k ∈ Finset.range N, (E k).indicator t x := by
    intro x _
    by_cases hx : ∃ s, IsSheetAt J A x s
    · obtain ⟨k0, hk0⟩ := hEcover x hx
      filter_upwards [eventually_gt_atTop k0] with N hN
      rw [Finset.sum_eq_single_of_mem k0 (Finset.mem_range.2 hN), Set.indicator_of_mem hk0]
      intro k _ hk
      exact Set.indicator_of_notMem (fun hxk => hk (hEdisj k k0 x hxk hk0)) _
    · have htx : t x = 0 := by rw [htdef, dif_neg hx]
      refine Eventually.of_forall fun N => ?_
      rw [htx]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      by_cases hxk : x ∈ E k
      · rw [Set.indicator_of_mem hxk]; exact htx
      · exact Set.indicator_of_notMem hxk _
  filter_upwards [(eventually_all_finset _).2 hev] with N hN
  rw [hsum, Finset.sum_congr rfl hN, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => hpiece k y _ fun x => Set.Finite.mem_toFinset hfin
end GroundTheory.Heights₂.Heights.SheetSumMeasurable
