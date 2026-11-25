-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_eq_monomial_of_isMultiHomog_point_043f9fbc675f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:53:42.258614+00:00
-- url     : https://prove2.me/submissions/f2b664de-7768-48ea-8f31-bcf2f495721c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_projIdx_e108999e94b3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {F : Type*} [Field F] (f : MRing (ProjIdx 0) F)
    (b : Unit → ℕ) (hf : IsMultiHomog f b) :
    f = monomial (Finsupp.single ⟨(), 0⟩ (b ())) (coeff (Finsupp.single ⟨(), 0⟩ (b ())) f) := by
  ext d
  rw [coeff_monomial]
  split_ifs with h
  · rw [h]
  · by_contra hne
    have hw := hf hne
    have hd : d = Finsupp.single ⟨(), 0⟩ (b ()) := by
      ext i
      obtain ⟨⟨⟩, i⟩ := i
      have hi : i = 0 := Fin.fin_one_eq_zero i
      subst hi
      rw [Finsupp.single_eq_same, ← congrFun hw (), weight_projIdx,
        Fintype.sum_eq_single ⟨(), 0⟩]
      rintro ⟨⟨⟩, j⟩ hj
      exact absurd (by rw [Fin.fin_one_eq_zero j]) hj
    exact h hd.symm
end GroundTheory.Heights₂.Heights.FieldNumbers
