-- Prove2me | solution 1 for SmartPTO.Fisher.prop5_converse
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T17:54:30.622991+00:00
-- url     : https://prove2.me/submissions/ebd5339e-712d-4894-a553-6c65bc579da3

import Init
import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SmartPTO_Fisher_Setting

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory SmartPTO.Fisher
namespace RiskSupport
variable {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
lemma oracle_exists (hSne : S.Nonempty) (hScpt : IsCompact S) :
    ∃ w, SPOBounds.Natarajan.IsOracle S w := by
  have h : ∀ c : EuclideanSpace ℝ (Fin d), ∃ w ∈ S, ∀ v ∈ S, ⟪c,w⟫_ℝ ≤ ⟪c,v⟫_ℝ := by
    intro c
    obtain ⟨w,hw,hm⟩ := hScpt.exists_isMinOn hSne
      (continuous_const.inner continuous_id : Continuous fun w : EuclideanSpace ℝ (Fin d) => ⟪c,w⟫_ℝ).continuousOn
    exact ⟨w,hw,isMinOn_iff.mp hm⟩
  choose w hw hm using h
  exact ⟨w,fun c => ⟨hw c,hm c⟩⟩
lemma zstar_eq {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hw : SPOBounds.Natarajan.IsOracle S w) (c : EuclideanSpace ℝ (Fin d)) :
    zstar S c = ⟪c,w c⟫_ℝ := by
  have hb : BddBelow ((fun v => ⟪c,v⟫_ℝ) '' S) := by
    refine ⟨⟪c,w c⟫_ℝ,?_⟩
    rintro _ ⟨v,hv,rfl⟩; exact (hw c).2 v hv
  apply le_antisymm
  · exact csInf_le hb ⟨w c,(hw c).1,rfl⟩
  · apply le_csInf (show ((fun v => ⟪c,v⟫_ℝ) '' S).Nonempty from ⟨_,w c,(hw c).1,rfl⟩)
    rintro _ ⟨v,hv,rfl⟩; exact (hw c).2 v hv
lemma norm_bound (hSne : S.Nonempty) (hScpt : IsCompact S) :
    ∃ R : NNReal, ∀ v ∈ S, ‖v‖ ≤ (R:ℝ) := by
  obtain ⟨R,hR⟩ := hScpt.isBounded.exists_norm_le
  obtain ⟨v,hv⟩ := hSne
  exact ⟨⟨R,(norm_nonneg v).trans (hR v hv)⟩,hR⟩
lemma zstar_lipschitz (hSne : S.Nonempty) (hScpt : IsCompact S) :
    ∃ R : NNReal, LipschitzWith R (zstar S) := by
  obtain ⟨w,hw⟩ := oracle_exists hSne hScpt
  obtain ⟨R,hR⟩ := norm_bound hSne hScpt
  have one : ∀ a b, zstar S a - zstar S b ≤ (R:ℝ)*‖a-b‖ := by
    intro a b
    rw [zstar_eq hw a,zstar_eq hw b]
    have hm := (hw a).2 (w b) (hw b).1
    have hi := real_inner_le_norm (a-b) (w b)
    have hn := mul_le_mul_of_nonneg_left (hR (w b) (hw b).1) (norm_nonneg (a-b))
    rw [inner_sub_left] at hi
    nlinarith
  refine ⟨R,lipschitzWith_iff_norm_sub_le.mpr ?_⟩
  intro a b
  rw [Real.norm_eq_abs,abs_le]
  have h := one b a
  rw [norm_sub_rev b a] at h
  exact ⟨by linarith,one a b⟩
lemma zstar_integrable (hSne : S.Nonempty) (hScpt : IsCompact S)
    (P : Measure (EuclideanSpace ℝ (Fin d))) (hInt : Integrable id P) :
    Integrable (zstar S) P := by
  obtain ⟨w,hw⟩ := oracle_exists hSne hScpt
  obtain ⟨R,hR⟩ := norm_bound hSne hScpt
  obtain ⟨L,hL⟩ := zstar_lipschitz hSne hScpt
  apply (hInt.norm.mul_const (R:ℝ)).mono' hL.continuous.aestronglyMeasurable
  filter_upwards [] with c
  rw [zstar_eq hw c,Real.norm_eq_abs]
  exact (abs_real_inner_le_norm c (w c)).trans
    (mul_le_mul_of_nonneg_left (hR (w c) (hw c).1) (norm_nonneg c))
end RiskSupport
#print axioms RiskSupport.zstar_integrable

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory SmartPTO.Fisher
namespace Converse
lemma gap_nonneg {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
    (hSne : S.Nonempty) (hScpt : IsCompact S) {w : EuclideanSpace ℝ (Fin d)}
    (hw : w ∈ S) (c : EuclideanSpace ℝ (Fin d)) : 0 ≤ ⟪c,w⟫_ℝ-zstar S c := by
  obtain ⟨v,hv⟩ := RiskSupport.oracle_exists hSne hScpt
  rw [RiskSupport.zstar_eq hv c]
  exact sub_nonneg.mpr ((hv c).2 w hw)
lemma gap_le_loss {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
    (hScpt : IsCompact S) {chat v : EuclideanSpace ℝ (Fin d)} (hv : v ∈ Wstar S chat)
    (c : EuclideanSpace ℝ (Fin d)) : ⟪c,v⟫_ℝ-zstar S c ≤ spoLoss S chat c := by
  apply sub_le_sub_right
  apply le_csSup
  · exact ((hScpt.image (continuous_const.inner continuous_id)).bddAbove).mono
      (Set.image_mono (fun _ h => h.1))
  · exact ⟨v,hv,rfl⟩
end Converse

theorem solution {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hInt : Integrable id P) (cstar : EuclideanSpace ℝ (Fin d))
    (hSingle : ∃ w, Wstar S cstar = {w})
    (hSub : Wstar S cstar ⊆ Wstar S (∫ c, c ∂P)) :
    ∀ chat : EuclideanSpace ℝ (Fin d), spoRisk S P cstar ≤ spoRisk S P chat := by
  obtain ⟨w,hw⟩ := hSingle
  have hwc : w ∈ Wstar S cstar := by rw [hw]; exact Set.mem_singleton w
  have hwm := hSub hwc
  have hz := RiskSupport.zstar_integrable hSne hScpt P hInt
  have hg : ∀ v : EuclideanSpace ℝ (Fin d), Integrable (fun c => ⟪c,v⟫_ℝ-zstar S c) P :=
    fun v => (hInt.inner_const v).sub hz
  have hi : ∀ v : EuclideanSpace ℝ (Fin d),
      (∫ c, (⟪c,v⟫_ℝ-zstar S c) ∂P) = ⟪(∫ c,c ∂P),v⟫_ℝ - ∫ c,zstar S c ∂P := by
    intro v
    have hiv : Integrable (fun c : EuclideanSpace ℝ (Fin d) => ⟪c,v⟫_ℝ) P := hInt.inner_const v
    rw [integral_sub hiv hz]
    simp only [real_inner_comm]
    congr 1
    simpa only [id_eq] using (integral_inner (𝕜 := ℝ) hInt v)
  intro chat
  obtain ⟨v,hv⟩ := RiskSupport.oracle_exists hSne hScpt
  have hvc : v chat ∈ Wstar S chat := hv chat
  have hsingle : ∀ c, spoLoss S cstar c = ⟪c,w⟫_ℝ-zstar S c := by
    intro c
    simp [spoLoss,hw]
  unfold spoRisk
  simp_rw [hsingle]
  rw [← ofReal_integral_eq_lintegral_ofReal (hg w)
    (Filter.Eventually.of_forall (Converse.gap_nonneg hSne hScpt hwc.1))]
  calc
    _ ≤ ENNReal.ofReal (∫ c, (⟪c,v chat⟫_ℝ-zstar S c) ∂P) := by
      apply ENNReal.ofReal_le_ofReal
      rw [hi w,hi (v chat)]
      exact sub_le_sub_right (hwm.2 (v chat) (hv chat).1) _
    _ = ∫⁻ c, ENNReal.ofReal (⟪c,v chat⟫_ℝ-zstar S c) ∂P :=
      ofReal_integral_eq_lintegral_ofReal (hg (v chat))
        (Filter.Eventually.of_forall (Converse.gap_nonneg hSne hScpt (hv chat).1))
    _ ≤ _ := lintegral_mono (fun c => ENNReal.ofReal_le_ofReal (Converse.gap_le_loss hScpt hvc c))
#print axioms solution
