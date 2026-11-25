-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_backward_52f4b24566df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:07:10.048316+00:00
-- url     : https://prove2.me/submissions/eb537861-069d-4218-a373-3ecb5e5cfb10

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinGradedFrameIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_repr_sum_smul_c443a2f82c23
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_coeff_eq_zero_of_tri_fd257542d139
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_repr_of_sub_mem_5ce60ba3d5bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_mon_ne_zero_c2553a9ef5d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_sum_mul_pow_eq_one_1fdd236d5c86


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
universe u v w
open GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
variable {o : Type u} [CommRing o] {Ω : Type v} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K]
  {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {N : ℕ} {E : Type w}
  [AddCommGroup E] [Module Ω E] {B : ChartBundle o (segreVec y) N E}
  {w : Module.Basis (Fin N) Ω E} {b : Fin N → K → ℤ}
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
theorem _root_.solution (h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsGradedFrame o y B
      (fun i => Submodule.span Ω (w '' {j | (j : ℕ) < i})) b w) :
    IsFlagFrame y B w b := by
  refine ⟨fun c hc i => ?_⟩
  have hm := mon_ne_zero (y := y) hc
  obtain ⟨k, f, cc, hf, hcc, h1, hfr⟩ := h c hc
  choose bb hli hsp hlat hunit using hfr
  choose u hu hbu using hunit
  have htri : ∀ l q, (∀ j, q < j → w.repr (bb l q) j = 0) ∧
      w.repr (bb l q) q = u l q * IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b q) :=
    fun l q => repr_of_sub_mem w (hbu l q)
  have hA := Model.exists_sum_mul_pow_eq_one (chartRing o (segreVec y) c) f cc hf hcc h1
  ext s
  constructor
  · rintro ⟨v, hv, hvz, rfl⟩
    have hloc : ∀ l, ∃ n : ℕ, f l ^ n * (w.repr v i / IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i)) ∈
        chartRing o (segreVec y) c := by
      intro l
      obtain ⟨a, ha, hva⟩ := (hlat l v).1 ⟨0, by rw [pow_zero, one_smul]; exact hv⟩
      have hz := coeff_eq_zero_of_tri w (bb l) (fun q j hqj => (htri l q).1 j hqj)
        (fun q => by rw [(htri l q).2]; exact mul_ne_zero (hu l q).1 (hm _)) a (i + 1)
        (fun j hj => by rw [← hva]; exact hvz j (Fin.lt_def.mpr (by omega)))
      have hvi : w.repr v i = a i * (u l i * IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i)) := by
        rw [hva, repr_sum_smul, Finset.sum_eq_single i, (htri l i).2]
        · intro q _ hq
          rcases lt_or_gt_of_ne hq with hlt | hgt
          · rw [(htri l q).1 i hlt, mul_zero]
          · rw [hz q (Fin.lt_def.mp hgt), zero_mul]
        · simp
      obtain ⟨n1, hn1⟩ := ha i
      obtain ⟨n2, hn2⟩ := (hu l i).2.1
      refine ⟨n1 + n2, ?_⟩
      have hq : w.repr v i / IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i) = a i * u l i := by
        rw [hvi]; field_simp [hm (b i)]
      rw [hq, show f l ^ (n1 + n2) * (a i * u l i) = (f l ^ n1 * a i) * (f l ^ n2 * u l i) by ring]
      exact mul_mem hn1 hn2
    choose nl hnl using hloc
    obtain ⟨d, hd, hd1⟩ := hA (∑ l, nl l)
    have hmul : ∀ l, f l ^ (∑ l, nl l) *
        (w.repr v i / IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i)) ∈ chartRing o (segreVec y) c := by
      intro l
      have hle : nl l ≤ ∑ l, nl l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
      rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
      exact mul_mem (pow_mem (hf l) _) (hnl l)
    have ht : w.repr v i / IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i) ∈ chartRing o (segreVec y) c := by
      have he : w.repr v i / IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i) =
          ∑ l, d l * (f l ^ (∑ l, nl l) * (w.repr v i / IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (b i))) := by
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul, hd1, one_mul]
      rw [he]
      exact Subalgebra.sum_mem _ fun l _ => mul_mem (hd l) (hmul l)
    exact ⟨_, ht, (div_mul_cancel₀ _ (hm (b i))).symm⟩
  · rintro ⟨a, ha, rfl⟩
    have hloc : ∀ l, ∃ n : ℕ, ∃ v : E, f l ^ n • v ∈ B.lat c ∧ (∀ j, i < j → w.repr v j = 0) ∧
        w.repr v i = a * ∏ k, y ⟨k, c k⟩ ^ b i k := by
      intro l
      have hcoef : ∀ q, ∃ n : ℕ, f l ^ n * (Pi.single i (a * (u l i)⁻¹) : Fin N → Ω) q ∈
          chartRing o (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg y) c := by
        intro q
        by_cases hq : q = i
        · subst hq
          obtain ⟨n2, hn2⟩ := (hu l q).2.2
          refine ⟨n2, ?_⟩
          rw [Pi.single_eq_same, show f l ^ n2 * (a * (u l q)⁻¹) = a * (f l ^ n2 * (u l q)⁻¹) by ring]
          exact mul_mem ha hn2
        · exact ⟨0, by rw [Pi.single_eq_of_ne hq, mul_zero]; exact zero_mem _⟩
      have hsum : (a * (u l i)⁻¹) • bb l i = ∑ q, (Pi.single i (a * (u l i)⁻¹) : Fin N → Ω) q • bb l q := by
        rw [Finset.sum_eq_single i]
        · rw [Pi.single_eq_same]
        · intro q _ hq; rw [Pi.single_eq_of_ne hq, zero_smul]
        · simp
      obtain ⟨n, hn⟩ := (hlat l ((a * (u l i)⁻¹) • bb l i)).2 ⟨_, hcoef, hsum⟩
      refine ⟨n, _, hn, fun j hj => ?_, ?_⟩
      · rw [map_smul, Finsupp.smul_apply, (htri l i).1 j hj, smul_zero]
      · rw [map_smul, Finsupp.smul_apply, (htri l i).2, smul_eq_mul]
        have hu0 := (hu l i).1
        simp only [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon]
        field_simp
    choose nl v hvl hvz hvi using hloc
    obtain ⟨d, hd, hd1⟩ := hA (∑ l, nl l)
    refine ⟨∑ l, (d l * f l ^ (∑ l, nl l)) • v l, ?_, fun j hj => ?_, ?_⟩
    · refine AddSubgroup.sum_mem _ fun l _ => ?_
      have hle : nl l ≤ ∑ l, nl l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
      rw [← Nat.sub_add_cancel hle, pow_add, ← mul_assoc, mul_smul]
      exact B.stable c _ (mul_mem (hd l) (pow_mem (hf l) _)) _ (hvl l)
    · rw [repr_sum_smul]
      exact Finset.sum_eq_zero fun l _ => by rw [hvz l j hj, mul_zero]
    · rw [repr_sum_smul]
      simp_rw [hvi]
      rw [← Finset.sum_mul, hd1, one_mul]
end GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
