-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_slopeMaxExtension_ff17efa1fac9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:11:07.429388+00:00
-- url     : https://prove2.me/submissions/2d319421-e57e-40ac-990c-9744c5ff49aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DegreeTopEqArithDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_normDegree_le_rank_mul_39ef423f891f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_degree_submodule_le_fccfab8f4814
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_rank_sub_eq_155a2f330e2e


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
open NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : SlopeMaxExtension.Statement := by
  intro K _ _ E' E E'' X
  show (⨆ (F : Submodule (𝓞 K) E.carrier) (_ : F ≠ ⊥), ((E.slope F : ℝ) : EReal)) ≤ _
  refine iSup₂_le fun F hF ↦ ?_
  rcases eq_or_ne (max E'.slopeMax E''.slopeMax) ⊤ with hM | hM
  · rw [hM]
    exact le_top
  have hrank := X.rank_sub_eq F
  have hpos : 0 < E.rank F := by
    rcases Nat.eq_zero_or_pos (E.rank F) with h | h
    · exact absurd ((Submodule.finrank_eq_zero (R := 𝓞 K) (S := F)).mp h) hF
    · exact h
  have hMbot : max E'.slopeMax E''.slopeMax ≠ ⊥ := by
    have : 0 < E'.rank (F.comap X.incl) ∨ 0 < E''.rank (F.map X.proj) := by omega
    rcases this with h | h
    · have hne : F.comap X.incl ≠ ⊥ := by
        intro h0
        rw [h0] at h
        simp [HermitianBundle.rank] at h
      have h0 : ((E'.slope (F.comap X.incl) : ℝ) : EReal) ≤ E'.slopeMax :=
        le_iSup₂_of_le (F.comap X.incl) hne le_rfl
      have hle := h0.trans (le_max_left _ E''.slopeMax)
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hle
    · have hne : F.map X.proj ≠ ⊥ := by
        intro h0
        rw [h0] at h
        simp [HermitianBundle.rank] at h
      have h0 : ((E''.slope (F.map X.proj) : ℝ) : EReal) ≤ E''.slopeMax :=
        le_iSup₂_of_le (F.map X.proj) hne le_rfl
      have hle := h0.trans (le_max_right E'.slopeMax _)
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hle
  set m := (max E'.slopeMax E''.slopeMax).toReal
  have hMm : max E'.slopeMax E''.slopeMax = (m : EReal) := (EReal.coe_toReal hM hMbot).symm
  have h1 := E'.normDegree_le_rank_mul (F.comap X.incl) m ((le_max_left _ _).trans_eq hMm)
  have h2 := E''.normDegree_le_rank_mul (F.map X.proj) m ((le_max_right _ _).trans_eq hMm)
  have hdeg := X.degree_submodule_le F
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hnd : E.normDegree F ≤ E'.normDegree (F.comap X.incl) + E''.normDegree (F.map X.proj) := by
    simp only [HermitianBundle.normDegree]
    rw [← add_div]
    exact div_le_div_of_nonneg_right hdeg hd.le
  have hrpos : (0 : ℝ) < E.rank F := by exact_mod_cast hpos
  have hr : (E.rank F : ℝ) = E'.rank (F.comap X.incl) + E''.rank (F.map X.proj) := by
    exact_mod_cast hrank
  have hs : E.slope F ≤ m := by
    unfold HermitianBundle.slope
    rw [div_le_iff₀ hrpos, hr]
    calc E.normDegree F ≤ E'.rank (F.comap X.incl) * m + E''.rank (F.map X.proj) * m := by linarith
      _ = m * (E'.rank (F.comap X.incl) + E''.rank (F.map X.proj)) := by ring
  rw [hMm]
  exact EReal.coe_le_coe_iff.mpr hs
end GroundTheory.Heights₂.Heights
