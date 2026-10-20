-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.cgpCompactAttainment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:47:24.28001+00:00
-- url     : https://prove2.me/submissions/5e1c021a-0c78-4d75-b7fa-c85c62a97c11

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

theorem g52c_psd_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (r s : ι) :
    ‖M r s‖ ^ 2 ≤ (M r r).re * (M s s).re := by
  have h2 := (hM.submatrix ![r, s]).det_nonneg
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  have hsr : M s r = star (M r s) := (hM.1.apply s r).symm
  have hrr : (M r r).im = 0 := by
    have := hM.1.apply r r
    have h3 := congrArg Complex.im this
    simp only [Complex.star_def, Complex.conj_im] at h3
    linarith
  have hss : (M s s).im = 0 := by
    have := hM.1.apply s s
    have h3 := congrArg Complex.im this
    simp only [Complex.star_def, Complex.conj_im] at h3
    linarith
  rw [hsr] at h2
  have h4 := (Complex.nonneg_iff.mp h2).1
  simp only [Complex.sub_re, Complex.mul_re, hrr, hss, mul_zero, sub_zero, Complex.star_def,
    Complex.conj_re, Complex.conj_im] at h4
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  nlinarith [h4]

theorem g52c_isClosed_psd {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsClosed {J : Matrix ι ι ℂ | J.PosSemidef} := by
  have : {J : Matrix ι ι ℂ | J.PosSemidef} =
      {J | Jᴴ = J} ∩ ⋂ x : ι → ℂ, {J | 0 ≤ star x ⬝ᵥ (J *ᵥ x)} := by
    ext J
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact Matrix.posSemidef_iff_dotProduct_mulVec
  rw [this]
  apply IsClosed.inter
  · exact isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id
  · apply isClosed_iInter
    intro x
    exact isClosed_le continuous_const (by fun_prop)

theorem g52c_isClosed_feasible : IsClosed {J | FixedChoiFeasible J} := by
  simp only [FixedChoiFeasible, FixedPopulations, fromChoi, Set.setOf_and, Set.setOf_forall]
  refine (g52c_isClosed_psd (ι := Fin 4 × Fin 4)).inter (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)))
  · exact isClosed_iInter fun u => isClosed_iInter fun v => isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq (by fun_prop) continuous_const
  · refine isClosed_iInter fun x => isClosed_iInter fun u => isClosed_iInter fun y =>
      isClosed_iInter fun v => ?_
    exact isClosed_iInter fun _ => isClosed_eq (by fun_prop) continuous_const
  · exact (isClosed_eq (by fun_prop) continuous_const).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter (isClosed_eq (by fun_prop) continuous_const))

theorem g52c_feasible_bound (J : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) (hJ : FixedChoiFeasible J)
    (a b : Fin 4 × Fin 4) : ‖J a b‖ ≤ 4 := by
  obtain ⟨hpsd, h1, -, -, -⟩ := hJ
  have hdiag : ∀ c, 0 ≤ (J c c).re := fun c => (Complex.nonneg_iff.mp hpsd.diag_nonneg).1
  have hsum : ∑ c, (J c c).re = 4 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have : ∀ u : Fin 4, ∑ x : Fin 4, (J (x, u) (x, u)).re = 1 := by
      intro u
      have := congrArg Complex.re (h1 u u)
      simp only [if_true, Complex.one_re, Complex.re_sum] at this
      exact this
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  have hle : ∀ c, (J c c).re ≤ 4 := fun c => by
    rw [← hsum]
    exact Finset.single_le_sum (fun c _ => hdiag c) (Finset.mem_univ c)
  have h := g52c_psd_entry J hpsd a b
  have hab : (J a a).re * (J b b).re ≤ 16 := by
    nlinarith [hdiag a, hdiag b, hle a, hle b, mul_le_mul (hle a) (hle b) (hdiag b) (by norm_num)]
  nlinarith [norm_nonneg (J a b)]

end

end QAlgorithms.Papers.Independent.Information100.P44

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44 in
open scoped ComplexConjugate ComplexOrder Matrix in
theorem solution :
    IsCompact {J | FixedChoiFeasible J} ∧
    (({J | FixedChoiFeasible J} : Set (Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)).Nonempty →
      (∀ k : Fin 3, ∃ J, FixedChoiFeasible J ∧
        ∀ K, FixedChoiFeasible K → channelObjective k (fromChoi K) ≤ channelObjective k (fromChoi J)) ∧
      ∃ J, FixedChoiFeasible J ∧ ∀ K, FixedChoiFeasible K →
        (∑ k : Fin 3, channelObjective k (fromChoi K)) ≤ ∑ k : Fin 3, channelObjective k (fromChoi J)) := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin 4 × Fin 4 =>
      Set.univ.pi fun _ : Fin 4 × Fin 4 => Metric.closedBall (0 : ℂ) 4) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 4
  have hC : IsCompact {J | FixedChoiFeasible J} := by
    refine hK.of_isClosed_subset g52c_isClosed_feasible ?_
    intro J hJ
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro a b
    exact g52c_feasible_bound J hJ a b
  refine ⟨hC, fun hne => ⟨fun k => ?_, ?_⟩⟩
  · obtain ⟨J, hJ, hmax⟩ := hC.exists_isMaxOn hne
      (f := fun J => channelObjective k (fromChoi J)) (by
        apply Continuous.continuousOn
        simp only [channelObjective, fromChoi]
        fun_prop)
    exact ⟨J, hJ, fun K hK' => hmax hK'⟩
  · obtain ⟨J, hJ, hmax⟩ := hC.exists_isMaxOn hne
      (f := fun J => ∑ k : Fin 3, channelObjective k (fromChoi J)) (by
        apply Continuous.continuousOn
        simp only [channelObjective, fromChoi]
        fun_prop)
    exact ⟨J, hJ, fun K hK' => hmax hK'⟩
