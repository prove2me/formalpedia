-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Ib.ibp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:35:02.11759+00:00
-- url     : https://prove2.me/submissions/99659d47-9d0f-42d6-9aef-d84218defce8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_integrable_of_bound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_integrable_mul_chr
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_contDiff_foldr
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_ibp_list

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Ib
theorem _root_.solution : IBP := by
  intro n f t β hf ht hdet hb
  have hI : ∀ L : List (Fin n × Fin n), Integrable (L.foldr (fun kl g => Dkl kl.1 kl.2 g) f) := by
    intro L
    obtain ⟨h, hh, hbd⟩ := hb L
    exact integrable_of_bound (contDiff_foldr hf L).continuous hh hbd
  have hfold : ∀ σ : Equiv.Perm (Fin n), (List.finRange n).foldr (fun k g => Dkl k (σ k) g) f =
      ((List.finRange n).map fun k => (k, σ k)).foldr (fun kl g => Dkl kl.1 kl.2 g) f := by
    intro σ; rw [List.foldr_map]
  have hΔ : ∫ y, Delta f y * chr t β y = (Complex.I * t) ^ n * (herm β).det * ∫ y, f y * chr t β y := by
    have e : (fun y => Delta f y * chr t β y) = fun y => ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * (((List.finRange n).map fun k => (k, σ k)).foldr
          (fun kl g => Dkl kl.1 kl.2 g) f y * chr t β y) := by
      funext y
      simp only [Delta, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, hfold]
      refine Finset.sum_congr rfl fun σ _ => ?_
      ring
    rw [e, integral_finset_sum]
    swap
    · intro σ _
      exact (integrable_mul_chr (hI _) (contDiff_foldr hf _).continuous t β).const_mul _
    simp_rw [integral_const_mul, ibp_list hf t β hb, List.map_map]
    have hdet' : (herm β).det = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, herm β k (σ k) := by
      rw [← Matrix.det_transpose, Matrix.det_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Units.smul_def, zsmul_eq_mul]
      rfl
    rw [hdet', Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hp : (((List.finRange n).map ((fun kl : Fin n × Fin n => Complex.I * t * herm β kl.1 kl.2) ∘
        fun k => (k, σ k))).prod) = (Complex.I * t) ^ n * ∏ k, herm β k (σ k) := by
      rw [← Fin.prod_univ_def]
      simp only [Function.comp_apply]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hp]
    ring
  have hc : (Complex.I * t) ^ n ≠ 0 := pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ht))
  rw [hΔ]
  have e2 : (-(Complex.I * t)) ^ n = (-1) ^ n * (Complex.I * t) ^ n := by rw [neg_eq_neg_one_mul, mul_pow]
  rw [e2]
  have h1 : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by rw [← mul_pow]; norm_num
  field_simp
end PositivityTheory.Rg.Sw.WR.Ib
