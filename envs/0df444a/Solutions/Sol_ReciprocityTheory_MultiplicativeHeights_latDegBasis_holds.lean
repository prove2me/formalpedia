-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.latDegBasis_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:59:26.486311+00:00
-- url     : https://prove2.me/submissions/855c0cfe-270f-4ae9-be95-0d4d737c2ee8

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBB
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_comb_diagonal
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_det_gramC_comb
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_exists_smul_le_span
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gramC_det_re_pos
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_relIndex_span_comb
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_relIndex_span_ne_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sum_log_normSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : LatDegBasisStatement := by
  intro K _ _ r k H B b b' hH hB hb hb'
  obtain ⟨hbB, hbli, hbsp⟩ := hb
  obtain ⟨hb'B, hb'li, hb'sp⟩ := hb'
  set P := Submodule.span (𝓞 K) (Set.range b) with hP
  set P' := Submodule.span (𝓞 K) (Set.range b') with hP'
  obtain ⟨D, hD, hDB⟩ := exists_smul_le_span b B hB hbsp
  have hcoef : ∀ j, ∃ c : Fin k → 𝓞 K, ∑ i, c i • b i = D • b' j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp (hDB _ (hb'B j))
  choose m hm using hcoef
  set M : Matrix (Fin k) (Fin k) (𝓞 K) := Matrix.of fun i j => m j i with hMdef
  set Dm : Matrix (Fin k) (Fin k) (𝓞 K) := Matrix.diagonal fun _ => D with hDm
  have hcM : (fun j => ∑ i, M i j • b i) = fun j => D • b' j := by
    funext j
    exact hm j
  have hcD : (fun j => ∑ i, Dm i j • b' i) = fun j => D • b' j := comb_diagonal b' D
  set NK := M.map (algebraMap (𝓞 K) K) with hNK
  set DK := Dm.map (algebraMap (𝓞 K) K) with hDK
  have hcMK : (fun j => ∑ i, NK i j • b i) = fun j => D • b' j := by
    rw [← hcM]
    funext j
    simp [NK, algebraMap_smul]
  have hcDK : (fun j => ∑ i, DK i j • b' i) = fun j => D • b' j := by
    rw [← hcD]
    funext j
    simp [DK, algebraMap_smul]
  have hNKdet : NK.det = algebraMap (𝓞 K) K M.det := (RingHom.map_det _ M).symm
  have hDKdet : DK.det = algebraMap (𝓞 K) K Dm.det := (RingHom.map_det _ Dm).symm
  have hgc : ∀ σ : K →+* ℂ, (gramC (H σ) σ (fun j => D • b' j)).det =
      ((Complex.normSq (σ NK.det) : ℝ) : ℂ) * (gramC (H σ) σ b).det := fun σ => by
    rw [← hcMK]
    exact det_gramC_comb _ _ _ _
  have hgc' : ∀ σ : K →+* ℂ, (gramC (H σ) σ (fun j => D • b' j)).det =
      ((Complex.normSq (σ DK.det) : ℝ) : ℂ) * (gramC (H σ) σ b').det := fun σ => by
    rw [← hcDK]
    exact det_gramC_comb _ _ _ _
  have hpos : ∀ σ : K →+* ℂ, 0 < (gramC (H σ) σ b).det.re := fun σ =>
    gramC_det_re_pos (H σ) σ b (hH σ) hbli
  have hpos' : ∀ σ : K →+* ℂ, 0 < (gramC (H σ) σ b').det.re := fun σ =>
    gramC_det_re_pos (H σ) σ b' (hH σ) hb'li
  have hDmdet : Dm.det ≠ 0 := by
    simp [Dm, Matrix.det_diagonal, hD]
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have hDKne : DK.det ≠ 0 := by
    rw [hDKdet, ← map_zero (algebraMap (𝓞 K) K)]
    exact hinj.ne hDmdet
  have hre : ∀ σ : K →+* ℂ, Complex.normSq (σ NK.det) * (gramC (H σ) σ b).det.re =
      Complex.normSq (σ DK.det) * (gramC (H σ) σ b').det.re := fun σ => by
    have := congrArg Complex.re ((hgc σ).symm.trans (hgc' σ))
    simpa [Complex.re_ofReal_mul] using this
  have hNKne : NK.det ≠ 0 := by
    intro h0
    have h := hre (Classical.arbitrary (K →+* ℂ))
    rw [h0, map_zero, map_zero, zero_mul] at h
    have h1 : 0 < Complex.normSq ((Classical.arbitrary (K →+* ℂ)) DK.det) :=
      Complex.normSq_pos.mpr (by simpa using hDKne)
    have h2 := hpos' (Classical.arbitrary (K →+* ℂ))
    nlinarith
  have hMdet : M.det ≠ 0 := by
    intro h0
    apply hNKne
    rw [hNKdet, h0, map_zero]
  set C := Submodule.span (𝓞 K) (Set.range (fun j => D • b' j)) with hC
  have hIdx1 := relIndex_span_comb b hbli M hMdet
  rw [hcM] at hIdx1
  have hIdx2 := relIndex_span_comb b' hb'li Dm hDmdet
  rw [hcD] at hIdx2
  have hPB : P ≤ B := Submodule.span_le.mpr (Set.range_subset_iff.mpr hbB)
  have hP'B : P' ≤ B := Submodule.span_le.mpr (Set.range_subset_iff.mpr hb'B)
  have hCP : C ≤ P := Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => hDB _ (hb'B j))
  have hCP' : C ≤ P' := Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j =>
    Submodule.smul_mem _ D (Submodule.subset_span ⟨j, rfl⟩))
  have mul1 := AddSubgroup.relIndex_mul_relIndex C.toAddSubgroup P.toAddSubgroup B.toAddSubgroup
    hCP hPB
  have mul2 := AddSubgroup.relIndex_mul_relIndex C.toAddSubgroup P'.toAddSubgroup B.toAddSubgroup
    hCP' hP'B
  have hI := relIndex_span_ne_zero b hbli B hbB D hD hDB
  have e1 : ((Algebra.norm ℤ M.det : ℤ) : ℝ) = ((Algebra.norm ℚ NK.det : ℚ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) (Algebra.coe_norm_int M.det)
    simp only [Rat.cast_intCast] at this
    rw [hNKdet]
    convert this using 3
  have e2 : ((Algebra.norm ℤ Dm.det : ℤ) : ℝ) = ((Algebra.norm ℚ DK.det : ℚ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) (Algebra.coe_norm_int Dm.det)
    simp only [Rat.cast_intCast] at this
    rw [hDKdet]
    convert this using 3
  have hcP : ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) =
      |((Algebra.norm ℚ NK.det : ℚ) : ℝ)| := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hIdx1
    simp only [Int.cast_natCast, Int.cast_abs] at this
    rw [this, e1]
  have hcP' : ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) =
      |((Algebra.norm ℚ DK.det : ℚ) : ℝ)| := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hIdx2
    simp only [Int.cast_natCast, Int.cast_abs] at this
    rw [this, e2]
  have hnM : ((Algebra.norm ℚ NK.det : ℚ) : ℝ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hNKne)
  have hnD : ((Algebra.norm ℚ DK.det : ℚ) : ℝ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hDKne)
  have hmulR : ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) *
      ((P.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) =
      ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) *
      ((P'.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) := by
    exact_mod_cast mul1.trans mul2.symm
  have hcPne : ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) ≠ 0 := by
    rw [hcP]
    exact abs_ne_zero.mpr hnM
  have hcP'ne : ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) ≠ 0 := by
    rw [hcP']
    exact abs_ne_zero.mpr hnD
  have hIne : ((P.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hI
  have hI'ne : ((P'.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmulR
    exact mul_ne_zero hcPne hIne hmulR
  have hlog : Real.log ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) +
      Real.log ((P.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) =
      Real.log ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) +
      Real.log ((P'.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) := by
    rw [← Real.log_mul hcPne hIne, ← Real.log_mul hcP'ne hI'ne, hmulR]
  rw [hcP, hcP'] at hlog
  have hsum : ∑ σ : K →+* ℂ, (Real.log (Complex.normSq (σ NK.det)) +
      Real.log (gramC (H σ) σ b).det.re) = ∑ σ : K →+* ℂ, (Real.log (Complex.normSq (σ DK.det)) +
      Real.log (gramC (H σ) σ b').det.re) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    have h1 : Complex.normSq (σ NK.det) ≠ 0 := (Complex.normSq_pos.mpr (by simpa using hNKne)).ne'
    have h2 : Complex.normSq (σ DK.det) ≠ 0 := (Complex.normSq_pos.mpr (by simpa using hDKne)).ne'
    rw [← Real.log_mul h1 (hpos σ).ne', ← Real.log_mul h2 (hpos' σ).ne', hre σ]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_log_normSq _ hNKne,
    sum_log_normSq _ hDKne] at hsum
  simp only [latDeg]
  linarith
end ReciprocityTheory.MultiplicativeHeights
