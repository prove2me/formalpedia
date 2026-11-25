-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.aym_det_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:54.287502+00:00
-- url     : https://prove2.me/submissions/19476e19-3056-4ce5-aada-523b63bb754b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_TestFunctionPeriodicity
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_eN_out

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution (q k₀ r c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) (hr : n + c < r ∨ n' + c' < r) :
    (AYm q k₀ r c' n' c n x).det = 0 := by
  have hq : ∀ a b : ℕ, entB q k₀ c' n' c n 0 0 x a b
      = atN (x (eN E (n' + c') (fIdx k₀ c' n' b))) (fIdx k₀ c n a) := by
    intro a b
    simp [entB, scE]
  rcases hr with hr | hr
  · by_cases hz : ∃ s : Fin r, n + c ≤ fIdx k₀ c n s.1
    · obtain ⟨s, hs⟩ := hz
      apply Matrix.det_eq_zero_of_row_eq_zero s
      intro t
      simp only [AYm, Matrix.of_apply, hq, atN]
      rw [dif_neg (by omega)]
    · push_neg at hz
      obtain ⟨s, s', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
        (fun s : Fin r => (⟨fIdx k₀ c n s.1, hz s⟩ : Fin (n + c))) (by simp; omega)
      apply Matrix.det_zero_of_row_eq hne
      funext t
      have he : fIdx k₀ c n s.1 = fIdx k₀ c n s'.1 := congrArg Fin.val heq
      simp only [AYm, Matrix.of_apply, hq, he]
  · by_cases hz : ∃ t : Fin r, n' + c' ≤ fIdx k₀ c' n' t.1
    · obtain ⟨t, ht⟩ := hz
      apply Matrix.det_eq_zero_of_column_eq_zero t
      intro s
      simp only [AYm, Matrix.of_apply, hq, eN_out (E := E) (show ¬ fIdx k₀ c' n' t.1 < n' + c' by omega),
        map_zero]
      simp [atN]
    · push_neg at hz
      obtain ⟨t, t', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
        (fun t : Fin r => (⟨fIdx k₀ c' n' t.1, hz t⟩ : Fin (n' + c'))) (by simp; omega)
      apply Matrix.det_zero_of_column_eq hne
      intro s
      have he : fIdx k₀ c' n' t.1 = fIdx k₀ c' n' t'.1 := congrArg Fin.val heq
      simp only [AYm, Matrix.of_apply, hq, he]
end PI.TwistedEisensteinNonvanishing.W
