-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_degrees_of_chowFormCycle_5abcefad6b58
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:50.905454+00:00
-- url     : https://prove2.me/submissions/fa8028ea-dff0-4629-a1b0-acf9400971e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomog_iff_4e11cc8773b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsChowForm_degrees_eq_e2d80fd5d845
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_inGroup_of_dvd_78c37585d297

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
open MvPolynomial
noncomputable section
variable {k n : ℕ} {F : Type} [Field F]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (hk : 0 < k) (Z : ProjCycle F n) (c : F)
    (g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F)
    (hg : ∀ W ∈ Z.support, IsChowForm W k (g W)) {δ : ℕ}
    (hf : IsMultiHomog δ (C c * ∏ W ∈ Z.support, g W ^ Z W)) (hf0 : C c * ∏ W ∈ Z.support, g W ^ Z W ≠ 0) :
    ∃ δW : Ideal (MvPolynomial (Fin n) F) → ℕ, (∀ W ∈ Z.support, IsMultiHomog (δW W) (g W)) ∧
      ∑ W ∈ Z.support, Z W * δW W = δ := by
  classical
  have hdeg : ∀ W ∈ Z.support, ∃ d, IsMultiHomog d (g W) := by
    intro W hW
    have hdvd : g W ∣ C c * ∏ W ∈ Z.support, g W ^ Z W := by
      apply Dvd.dvd.mul_left
      apply dvd_trans _ (Finset.dvd_prod_of_mem _ hW)
      exact dvd_pow_self _ (Finsupp.mem_support_iff.mp hW)
    have ha : ∀ i, ∃ a, IsWeightedHomogeneous (inGroup i) (g W) a := fun i =>
      isWeightedHomogeneous_inGroup_of_dvd hf hf0 hdvd i
    choose a ha using ha
    refine ⟨a ⟨0, hk⟩, (isMultiHomog_iff _ _).mpr fun i => ?_⟩
    rw [(hg W hW).degrees_eq ha ⟨0, hk⟩ i]
    exact ha i
  choose! δW hδW using hdeg
  refine ⟨δW, hδW, ?_⟩
  have hprod : IsMultiHomog (∑ W ∈ Z.support, Z W * δW W) (C c * ∏ W ∈ Z.support, g W ^ Z W) := by
    have h1 : IsWeightedHomogeneous (groupWeight k n) (∏ W ∈ Z.support, g W ^ Z W)
        (∑ W ∈ Z.support, Z W • fun _ : Fin k => δW W) :=
      IsWeightedHomogeneous.prod _ _ _ fun W hW => (hδW W hW).pow (Z W)
    have h2 := h1.C_mul c
    unfold IsMultiHomog
    convert h2 using 1
    funext i
    simp [Finset.sum_apply]
  have := hprod.inj_right hf0 hf
  exact congrFun this ⟨0, hk⟩
end GroundTheory.Heights₂.Heights
