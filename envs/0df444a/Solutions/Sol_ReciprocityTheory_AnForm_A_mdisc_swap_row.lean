-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_swap_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:30.54952+00:00
-- url     : https://prove2.me/submissions/2cffb9c3-13f5-416e-8327-cfd77cbddf3d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_eq_sum_perm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (p q : Fin D) (hpq : p ≠ q)
    (j k a b : Fin D) :
    mdisc (Function.update (Function.update A p (Matrix.single j k 1)) q (Matrix.single a b 1)) =
      - mdisc (Function.update (Function.update A p (Matrix.single a k 1)) q
          (Matrix.single j b 1)) := by
  have hu : ∀ (X Y : Matrix (Fin D) (Fin D) ℂ) r, Function.update (Function.update A p X) q Y r =
      if r = q then Y else if r = p then X else A r := by
    intro X Y r
    simp only [Function.update_apply]
  rw [mdisc_eq_sum_perm, mdisc_eq_sum_perm, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h1 : σ k = p
  · by_cases h2 : σ b = q
    · have hkb : k ≠ b := fun h => hpq (h1.symm.trans (h ▸ h2))
      have hM : (Matrix.of fun i c => Function.update (Function.update A p (Matrix.single a k 1)) q
          (Matrix.single j b 1) (σ c) i c) = (Matrix.of fun i c => Function.update (Function.update A p
          (Matrix.single j k 1)) q (Matrix.single a b 1) (σ c) i c).submatrix id (Equiv.swap k b) := by
        ext i c
        simp only [Matrix.of_apply, Matrix.submatrix_apply, id, hu]
        by_cases hck : c = k
        · rw [hck, Equiv.swap_apply_left, h1, h2]
          simp [hpq, Ne.symm hpq, Matrix.single_apply]
        · by_cases hcb : c = b
          · rw [hcb, Equiv.swap_apply_right, h1, h2]
            simp [hpq, Ne.symm hpq, Matrix.single_apply]
          · rw [Equiv.swap_apply_of_ne_of_ne hck hcb]
            have hp : σ c ≠ p := fun h => hck (σ.injective (h.trans h1.symm))
            have hq : σ c ≠ q := fun h => hcb (σ.injective (h.trans h2.symm))
            simp [hp, hq]
      rw [hM, Matrix.det_permute', Equiv.Perm.sign_swap hkb]
      simp
    · have hbq : b ≠ σ.symm q := fun h => h2 (by rw [h, Equiv.apply_symm_apply])
      rw [Matrix.det_eq_zero_of_column_eq_zero (σ.symm q) fun i => by
          simp [hu, Matrix.single_apply, hbq],
        Matrix.det_eq_zero_of_column_eq_zero (σ.symm q) fun i => by
          simp [hu, Matrix.single_apply, hbq], neg_zero]
  · have hkp : k ≠ σ.symm p := fun h => h1 (by rw [h, Equiv.apply_symm_apply])
    rw [Matrix.det_eq_zero_of_column_eq_zero (σ.symm p) fun i => by
        simp [hu, Matrix.single_apply, hkp, hpq],
      Matrix.det_eq_zero_of_column_eq_zero (σ.symm p) fun i => by
        simp [hu, Matrix.single_apply, hkp, hpq], neg_zero]
end ReciprocityTheory.AnForm.A
