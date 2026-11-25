-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:57:19.765214+00:00
-- url     : https://prove2.me/submissions/8ae1725e-eb17-44cb-a97d-7203cc104ed2

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_eq_sum_perm
import Theorems.Thm_ReciprocityTheory_AnForm_A_mixedDiscriminant_nonneg_of_gram
import Theorems.Thm_ReciprocityTheory_AnForm_A_mixedDiscriminant_re_mono_of_gram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.A
open Matrix
open scoped ComplexOrder
variable {D : ℕ}
private lemma mdiscML_apply (A : Fin D → Matrix (Fin D) (Fin D) ℂ) : mdiscML A = mdisc A := by
  rw [mdisc_eq_sum_perm, mdiscML, _root_.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [_root_.smul_apply, smul_eq_mul, MultilinearMap.domDomCongr_apply,
    MultilinearMap.compLinearMap_apply]
  congr 1
  rw [← Matrix.det_transpose]
  rfl
private lemma posSemidef_of_sub_of_add {A B : Matrix (Fin D) (Fin D) ℂ} (h1 : (B - A).PosSemidef)
    (h2 : (A + B).PosSemidef) : B.PosSemidef := by
  have h3 : ((B - A) + (A + B)).PosSemidef := h1.add h2
  have h4 : (B - A) + (A + B) = (2 : ℂ) • B := by rw [two_smul]; abel
  rw [h4] at h3
  have h5 := h3.smul (a := ((1 / 2 : ℝ) : ℂ)) (Complex.zero_le_real.2 (by norm_num))
  have h6 : ((1 / 2 : ℝ) : ℂ) • ((2 : ℂ) • B) = B := by
    rw [smul_smul]; norm_num
  rwa [h6] at h5
end ReciprocityTheory.AnForm.A
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix
open scoped ComplexOrder
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (A B : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (hle : ∀ k, (B k - A k).PosSemidef) (hge : ∀ k, (A k + B k).PosSemidef) :
    ‖mdisc A‖ ≤ (3 : ℝ) ^ D * (mdisc B).re := by
  classical
  have hB : ∀ k, (B k).PosSemidef := fun k => posSemidef_of_sub_of_add (hle k) (hge k)
  have hA : A = (fun k => A k + B k) + (fun k => (-1 : ℂ) • B k) := by
    funext k; simp
  have hexp : mdisc A = ∑ T : Finset (Fin D),
      (-1 : ℂ) ^ (D - T.card) * mdisc (T.piecewise (fun k => A k + B k) B) := by
    conv_lhs => rw [← mdiscML_apply, hA]
    rw [MultilinearMap.map_add_univ]
    refine Finset.sum_congr rfl fun T _ => ?_
    have e : T.piecewise (fun k => A k + B k) (fun k => (-1 : ℂ) • B k) =
        fun k => (if k ∈ T then (1 : ℂ) else -1) • T.piecewise (fun k => A k + B k) B k := by
      funext k; by_cases hk : k ∈ T <;> simp [Finset.piecewise, hk]
    rw [e, MultilinearMap.map_smul_univ, smul_eq_mul, mdiscML_apply, Finset.prod_ite,
      Finset.prod_const, Finset.prod_const, one_pow, one_mul]
    congr 2
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sdiff,
      Finset.card_univ, Fintype.card_fin]
    simp
  have hterm : ∀ T : Finset (Fin D),
      ‖mdisc (T.piecewise (fun k => A k + B k) B)‖ ≤ 2 ^ T.card * (mdisc B).re := by
    intro T
    have hP : ∀ k, (T.piecewise (fun k => A k + B k) B k).PosSemidef := fun k => by
      by_cases hk : k ∈ T <;> simp [Finset.piecewise, hk, hge k, hB k]
    obtain ⟨him, hre⟩ := mixedDiscriminant_nonneg_of_gram _ hP
    have hmono := mixedDiscriminant_re_mono_of_gram (T.piecewise (fun k => A k + B k) B)
      (T.piecewise (fun k => (2 : ℂ) • B k) B) hP (fun k => by
        by_cases hk : k ∈ T
        · have e : (2 : ℂ) • B k - (A k + B k) = B k - A k := by rw [two_smul]; abel
          simpa [Finset.piecewise, hk, e] using hle k
        · simpa [Finset.piecewise, hk] using Matrix.PosSemidef.zero)
    have h2 : mdisc (T.piecewise (fun k => (2 : ℂ) • B k) B) =
        (((2 : ℝ) ^ T.card : ℝ) : ℂ) * mdisc B := by
      rw [← mdiscML_apply, ← mdiscML_apply]
      have e : T.piecewise (fun k => (2 : ℂ) • B k) B =
          fun k => (if k ∈ T then (2 : ℂ) else 1) • B k := by
        funext k; by_cases hk : k ∈ T <;> simp [Finset.piecewise, hk]
      rw [e, MultilinearMap.map_smul_univ, smul_eq_mul, Finset.prod_ite, Finset.prod_const,
        Finset.prod_const, one_pow, mul_one]
      simp
    have hz : mdisc (T.piecewise (fun k => A k + B k) B) =
        ((mdisc (T.piecewise (fun k => A k + B k) B)).re : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [hz, Complex.norm_of_nonneg hre]
    rw [h2, Complex.re_ofReal_mul] at hmono
    exact hmono
  rw [hexp]
  calc ‖∑ T : Finset (Fin D), (-1 : ℂ) ^ (D - T.card) * mdisc (T.piecewise (fun k => A k + B k) B)‖
      ≤ ∑ T : Finset (Fin D),
          ‖(-1 : ℂ) ^ (D - T.card) * mdisc (T.piecewise (fun k => A k + B k) B)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ T : Finset (Fin D), 2 ^ T.card * (mdisc B).re :=
        Finset.sum_le_sum fun T _ => by
          rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          exact hterm T
    _ = 3 ^ D * (mdisc B).re := by
        rw [← Finset.sum_mul]
        congr 1
        have := Finset.sum_pow_mul_eq_add_pow (2 : ℝ) 1 (Finset.univ : Finset (Fin D))
        simp only [one_pow, mul_one, Finset.card_univ, Fintype.card_fin,
          Finset.powerset_univ] at this
        rw [this]
        norm_num
end ReciprocityTheory.AnForm.A
