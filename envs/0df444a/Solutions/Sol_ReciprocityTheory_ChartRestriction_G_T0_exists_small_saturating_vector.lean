-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.exists_small_saturating_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:51:52.720469+00:00
-- url     : https://prove2.me/submissions/efe28662-bcc1-404c-ab30-1e6efc9a889d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsNeZeroMemNormSqLeGramDetDivRelIndex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsSmallSaturatingVector
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_quotDist_eq_sqrt_norm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_norm_orthProj_sq_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthProjVector_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_relIndex_orthProj_lattice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_det_gram_projectedLatticeVectors
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_exists_integral_completion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_exists_ne_zero_mem_norm_sq_le_gram_det_div_relIndex
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_latDeg_saturation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_mem_standardLattice_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_normSqSum_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthogonalProjector_mulVec_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_projectedVector_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_quotGram_det_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_standardLattice_fg
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_relIndex_ne_zero_of_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (K : Type) [Field K] [NumberField K] (r k : ℕ) (b : Fin k → Fin r → K)
    (hb : LinearIndependent K b) (hbL : ∀ j, b j ∈ hStd K r) (hk : k < r) :
    ∃ q : Fin r → 𝓞 K, (fun i => (q i : K)) ∉ Submodule.span K (Set.range b) ∧
      meanK (fun σ => Real.log (hQdist σ b (fun i => (q i : K)))) ≤
        ReciprocityTheory.MultiplicativeHeights.latDeg (fun _ => 1) (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b) b /
            ((Module.finrank ℚ K : ℝ) * ((r - k : ℕ) : ℝ)) +
          1 / 2 * Real.log ((r - k : ℕ) : ℝ) +
          1 / 2 * Real.log (|(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ))) := by
  classical
  set m := r - k with hmdef
  have hm : 0 < m := by omega
  have hkm : k + m = r := by omega
  obtain ⟨c, hc, hli, hsp⟩ := exists_integral_completion hb hk.le
  have hdeg := latDeg_saturation hkm hbL c hc hli hsp
  set n := Module.finrank ℚ K with hndef
  have hn : 0 < n := Module.finrank_pos
  have hcardI : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = n := by
    rw [hndef, Module.finrank_eq_card_basis (integralBasis K)]
  have hcardE : Fintype.card (K →+* ℂ) = n := NumberField.Embeddings.card K ℂ
  set N := m * n with hNdef
  have hN : 0 < N := Nat.mul_pos hm hn
  have hcardJ : Fintype.card (Fin m × Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = N := by
    rw [Fintype.card_prod, Fintype.card_fin, hcardI]
  let eN : Fin N ≃ (Fin m × Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :=
    (Fintype.equivFinOfCardEq hcardJ).symm
  let w := hwv b c ∘ eN
  have hgw : gram ℝ w = (gram ℝ (hwv b c)).submatrix eN eN := by
    ext i j
    simp [gram_apply, w]
  set P := ∏ σ : K →+* ℂ, (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re with hPdef
  set D := |(NumberField.discr K : ℝ)| with hDdef
  have hdetw : (gram ℝ w).det = D ^ m * P := by
    rw [hgw, det_submatrix_equiv_self, det_gram_projectedLatticeVectors b hb c]
  have hdpos : 0 < D := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hPpos : 0 < P := Finset.prod_pos fun σ _ => quotGram_det_pos σ hb c hli
  have hGpos : 0 < (gram ℝ w).det := by rw [hdetw]; positivity
  have hwli : LinearIndependent ℝ w := linearIndependent_of_det_gram_ne_zero hGpos.ne'
  set Λ := (hStd K r).toAddSubgroup.map (hpvHom b) with hΛ
  have hwmem : ∀ i, w i ∈ Λ := fun i => orthProjVector_mem b c hc (eN i)
  have hrange : Set.range w = Set.range (hwv b c) := eN.surjective.range_comp _
  set I := (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔
    Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex (hStd K r).toAddSubgroup with hIdef
  have hrel : (Submodule.span ℤ (Set.range w)).toAddSubgroup.relIndex Λ = I := by
    rw [hrange]; exact relIndex_orthProj_lattice hb c hc
  have hI0 : I ≠ 0 := by
    have h1 := ReciprocityTheory.MultiplicativeHeights.DegAdd.relIndex_ne_zero_of_fg (hStd K r) standardLattice_fg (Fin.append b c)
      (fun x _ => hsp x)
    have hle : Submodule.span (𝓞 K) (Set.range (Fin.append b c)) ≤
        ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔ Submodule.span (𝓞 K) (Set.range c) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [Fin.append_left]
        exact Submodule.mem_sup_left ⟨hbL i, Submodule.subset_span ⟨i, rfl⟩⟩
      · rw [Fin.append_right]
        exact Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)
    have hdvd := AddSubgroup.relIndex_dvd_of_le_left (hStd K r).toAddSubgroup
      (show (Submodule.span (𝓞 K) (Set.range (Fin.append b c))).toAddSubgroup ≤
        (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup
        from hle)
    intro h0
    rw [← hIdef, h0] at hdvd
    exact h1 (Nat.eq_zero_of_zero_dvd hdvd)
  obtain ⟨v, hvΛ, hv0, hvb⟩ := exists_ne_zero_mem_norm_sq_le_gram_det_div_relIndex hN w hwli Λ hwmem (by rw [hrel]; exact hI0)
  rw [hrel, hdetw] at hvb
  obtain ⟨q, hqL, rfl⟩ := AddSubgroup.mem_map.mp hvΛ
  have hq : q ∉ Submodule.span K (Set.range b) := fun h => hv0 ((projectedVector_eq_zero_iff hb q).mpr h)
  have hqL' : q ∈ hStd K r := hqL
  rw [mem_standardLattice_iff] at hqL'
  choose q' hq' using hqL'
  have hqq : (fun i => ((q' i : 𝓞 K) : K)) = q := funext hq'
  refine ⟨q', by rw [hqq]; exact hq, ?_⟩
  rw [hqq]
  set X : (K →+* ℂ) → ℝ := fun σ => hns (hPm σ b *ᵥ fun l => σ (q l)) with hX
  have hXpos : ∀ σ, 0 < X σ := fun σ => normSqSum_pos (orthogonalProjector_mulVec_ne_zero σ hb hq)
  have hdist : ∀ σ, Real.log (hQdist σ b q) = Real.log (X σ) / 2 := fun σ => by
    rw [quotDist_eq_sqrt_norm σ hb, Real.log_sqrt (hXpos σ).le]
  have hsumX : ∑ σ, X σ = ‖hpvHom b q‖ ^ 2 := by
    show _ = ‖hpv b q‖ ^ 2
    rw [norm_orthProj_sq_sum hb]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [quotDist_eq_sqrt_norm σ hb, Real.sq_sqrt (hXpos σ).le]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hamgm : ∑ σ, (1 / (n : ℝ)) * Real.log (X σ) ≤ Real.log ((1 / (n : ℝ)) * ∑ σ, X σ) := by
    have hw0 : ∀ σ ∈ (Finset.univ : Finset (K →+* ℂ)), (0 : ℝ) ≤ 1 / (n : ℝ) :=
      fun _ _ => by positivity
    have hw1 : ∑ σ ∈ (Finset.univ : Finset (K →+* ℂ)), 1 / (n : ℝ) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, hcardE, nsmul_eq_mul]
      field_simp
    have h := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ) (fun _ => 1 / (n : ℝ)) X hw0
      hw1 (fun σ _ => (hXpos σ).le)
    have hprod : 0 < ∏ σ, X σ ^ (1 / (n : ℝ)) :=
      Finset.prod_pos fun σ _ => Real.rpow_pos_of_pos (hXpos σ) _
    have hlog := Real.log_le_log hprod h
    rw [Real.log_prod (fun σ _ => (Real.rpow_pos_of_pos (hXpos σ) _).ne')] at hlog
    simp only [Real.log_rpow (hXpos _)] at hlog
    rw [Finset.mul_sum]
    exact hlog
  have hIr : (0 : ℝ) < I := by exact_mod_cast Nat.pos_of_ne_zero hI0
  have hquot : ReciprocityTheory.MultiplicativeHeights.quotDeg (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) (hStd K r) b c =
      Real.log I - 1 / 2 * Real.log P := by
    simp only [ReciprocityTheory.MultiplicativeHeights.quotDeg]
    rw [hPdef, Real.log_prod (fun σ _ => (quotGram_det_pos σ hb c hli).ne')]
  have hlogG : Real.log (D ^ m * P / (I : ℝ) ^ 2) =
      m * Real.log D + Real.log P - 2 * Real.log I := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hNr : (N : ℝ) = m * n := by rw [hNdef]; push_cast; ring
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hY : Real.log ((1 / (n : ℝ)) * ((N : ℝ) * (D ^ m * P / (I : ℝ) ^ 2) ^ (1 / (N : ℝ)))) =
      Real.log m + (1 / (N : ℝ)) * (m * Real.log D + Real.log P - 2 * Real.log I) := by
    rw [show (1 / (n : ℝ)) * ((N : ℝ) * (D ^ m * P / (I : ℝ) ^ 2) ^ (1 / (N : ℝ))) =
        (m : ℝ) * (D ^ m * P / (I : ℝ) ^ 2) ^ (1 / (N : ℝ)) by rw [hNr]; field_simp]
    rw [Real.log_mul hmr.ne' (Real.rpow_pos_of_pos (by positivity) _).ne',
      Real.log_rpow (by positivity), hlogG]
  have hmean : meanK (fun σ => Real.log (hQdist σ b q)) =
      1 / 2 * ∑ σ, (1 / (n : ℝ)) * Real.log (X σ) := by
    simp only [meanK, hdist, hcardE]
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  have hsum_pos : 0 < (1 / (n : ℝ)) * ∑ σ, X σ :=
    mul_pos (by positivity) (Finset.sum_pos (fun σ _ => hXpos σ) Finset.univ_nonempty)
  have hstep : Real.log ((1 / (n : ℝ)) * ∑ σ, X σ) ≤
      Real.log ((1 / (n : ℝ)) * ((N : ℝ) * (D ^ m * P / (I : ℝ) ^ 2) ^ (1 / (N : ℝ)))) := by
    apply Real.log_le_log hsum_pos
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hsumX]
    exact hvb
  rw [hmean, hdeg, hquot]
  have hD1 : Real.log (D ^ (1 / (n : ℝ))) = 1 / (n : ℝ) * Real.log D := Real.log_rpow hdpos _
  rw [hD1]
  have key : 1 / 2 * ∑ σ, (1 / (n : ℝ)) * Real.log (X σ) ≤
      1 / 2 * (Real.log m + (1 / (N : ℝ)) * (m * Real.log D + Real.log P - 2 * Real.log I)) := by
    rw [← hY]
    exact mul_le_mul_of_nonneg_left (hamgm.trans hstep) (by norm_num)
  refine key.trans (le_of_eq ?_)
  rw [hNr]
  field_simp
  ring
end ReciprocityTheory.ChartRestriction.G.T0
