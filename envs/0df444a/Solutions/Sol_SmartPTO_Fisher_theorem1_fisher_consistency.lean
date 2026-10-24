-- Prove2me | solution 1 for SmartPTO.Fisher.theorem1_fisher_consistency
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T20:22:59.146137+00:00
-- url     : https://prove2.me/submissions/7c14f5f8-cd3c-4896-9142-0c0b62bf9674

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

theorem prior_converse {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
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
#print axioms prior_converse

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory SmartPTO.Fisher
namespace RiskRegularity
variable {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}

theorem value_of_mem (hSne : S.Nonempty) (hScpt : IsCompact S)
    {c w : EuclideanSpace ℝ (Fin d)} (hw : w ∈ Wstar S c) : zstar S c = ⟪c,w⟫_ℝ := by
  obtain ⟨v,hv⟩ := RiskSupport.oracle_exists hSne hScpt
  rw [RiskSupport.zstar_eq hv c]
  exact le_antisymm ((hv c).2 w hw.1) (hw.2 (v c) (hv c).1)

theorem derivative_of_mem (hSne : S.Nonempty) (hScpt : IsCompact S)
    {c w : EuclideanSpace ℝ (Fin d)} (hw : w ∈ Wstar S c)
    (hf : DifferentiableAt ℝ (zstar S) c) : fderiv ℝ (zstar S) c = innerSL ℝ w := by
  have hm : IsLocalMax (fun x => zstar S x - ⟪w,x⟫_ℝ) c := by
    apply Filter.Eventually.of_forall
    intro x
    change zstar S x - ⟪w,x⟫_ℝ ≤ zstar S c - ⟪w,c⟫_ℝ
    rw [value_of_mem hSne hScpt hw,real_inner_comm c w,sub_self]
    have h := Converse.gap_nonneg hSne hScpt hw.1 x
    rw [real_inner_comm] at h
    linarith
  exact sub_eq_zero.mp (hm.hasFDerivAt_eq_zero (hf.hasFDerivAt.sub (innerSL ℝ w).hasFDerivAt))

theorem unique_of_differentiable (hSne : S.Nonempty) (hScpt : IsCompact S)
    {c : EuclideanSpace ℝ (Fin d)} (hf : DifferentiableAt ℝ (zstar S) c) :
    ∃ w, Wstar S c = {w} := by
  obtain ⟨v,hv⟩ := RiskSupport.oracle_exists hSne hScpt
  refine ⟨v c,?_⟩
  ext w
  constructor
  · intro hw
    apply Set.mem_singleton_iff.mpr
    have he : innerSL ℝ w = innerSL ℝ (v c) :=
      (derivative_of_mem hSne hScpt hw hf).symm.trans (derivative_of_mem hSne hScpt (hv c) hf)
    apply ext_inner_left ℝ
    intro x
    have hx := DFunLike.congr_fun he x
    change ⟪w,x⟫_ℝ = ⟪v c,x⟫_ℝ at hx
    simpa only [real_inner_comm] using hx
  · rintro rfl
    exact hv c

theorem ae_unique (hSne : S.Nonempty) (hScpt : IsCompact S) :
    ∀ᵐ c ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), ∃ w, Wstar S c = {w} := by
  obtain ⟨R,hR⟩ := RiskSupport.zstar_lipschitz hSne hScpt
  filter_upwards [hR.ae_differentiableAt (μ := volume)] with c hc
  exact unique_of_differentiable hSne hScpt hc

theorem dense_unique (hSne : S.Nonempty) (hScpt : IsCompact S) :
    Dense {c : EuclideanSpace ℝ (Fin d) | ∃ w, Wstar S c = {w}} :=
  MeasureTheory.Measure.dense_of_ae (ae_unique hSne hScpt)

#print axioms derivative_of_mem
#print axioms ae_unique
#print axioms dense_unique
end RiskRegularity

open scoped InnerProductSpace
open SmartPTO.Fisher
namespace SupportOracle
lemma maximum {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
    {wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hw : SPOBounds.Natarajan.IsOracle S wstar) (a : EuclideanSpace ℝ (Fin d)) :
    ∀ v ∈ S, ⟪a,v⟫_ℝ ≤ ⟪a,wstar (-a)⟫_ℝ := by
  intro v hv
  have h := (hw (-a)).2 v hv
  simp only [inner_neg_left] at h
  linarith
lemma bounded {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
    {wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hw : SPOBounds.Natarajan.IsOracle S wstar) (a : EuclideanSpace ℝ (Fin d)) :
    BddAbove ((fun v => ⟪a,v⟫_ℝ) '' S) := by
  refine ⟨⟪a,wstar (-a)⟫_ℝ,?_⟩
  rintro _ ⟨v,hv,rfl⟩
  exact maximum hw a v hv
lemma support_le {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
    {wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hw : SPOBounds.Natarajan.IsOracle S wstar) (a v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ S) :
    ⟪a,v⟫_ℝ ≤ xi S a := le_csSup (bounded hw a) ⟨v,hv,rfl⟩
lemma support_eq {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
    {wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hw : SPOBounds.Natarajan.IsOracle S wstar) (a : EuclideanSpace ℝ (Fin d)) :
    xi S a = ⟪a,wstar (-a)⟫_ℝ := by
  apply le_antisymm
  · change sSup ((fun v => ⟪a,v⟫_ℝ) '' S) ≤ _
    have hne : ((fun v => ⟪a,v⟫_ℝ) '' S).Nonempty :=
      ⟨⟪a,wstar (-a)⟫_ℝ, wstar (-a),(hw (-a)).1,rfl⟩
    apply csSup_le hne
    rintro _ ⟨v,hv,rfl⟩
    exact maximum hw a v hv
  · exact support_le hw a _ (hw (-a)).1
end SupportOracle

theorem prior_subgradient {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hw : SPOBounds.Natarajan.IsOracle S wstar)
    (c chat ct : EuclideanSpace ℝ (Fin d)) :
    spoPlusLoss S wstar chat c +
      ⟪(2 : ℝ) • (wstar c - wstar ((2 : ℝ) • chat - c)), ct - chat⟫_ℝ ≤
      spoPlusLoss S wstar ct c := by
  have he := SupportOracle.support_eq hw (c-(2:ℝ)•chat)
  simp only [neg_sub] at he
  have hl := SupportOracle.support_le hw (c-(2:ℝ)•ct)
    (wstar ((2:ℝ)•chat-c)) (hw ((2:ℝ)•chat-c)).1
  unfold spoPlusLoss
  rw [he]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left] at *
  simp only [real_inner_comm] at *
  linarith
#print axioms prior_subgradient

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory SmartPTO.Fisher
namespace RiskPlus
variable {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
  {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}

theorem oracle_scalar_integrable (hSne : S.Nonempty) (hScpt : IsCompact S)
    (hw : SPOBounds.Natarajan.IsOracle S w)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (ha : P ≪ volume) (v : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun c => ⟪v,w c⟫_ℝ) P := by
  obtain ⟨L,hL⟩ := RiskSupport.zstar_lipschitz hSne hScpt
  obtain ⟨R,hR⟩ := RiskSupport.norm_bound hSne hScpt
  have he : (fun c => fderiv ℝ (zstar S) c v) =ᵐ[P] (fun c => ⟪v,w c⟫_ℝ) := by
    filter_upwards [ha.ae_le (hL.ae_differentiableAt (μ := volume))] with c hc
    rw [RiskRegularity.derivative_of_mem hSne hScpt (hw c) hc]
    change ⟪w c,v⟫_ℝ = ⟪v,w c⟫_ℝ
    exact real_inner_comm _ _
  have hm := (measurable_fderiv_apply_const ℝ (zstar S) v).aestronglyMeasurable.congr he
  apply (integrable_const (‖v‖*(R:ℝ))).mono' hm
  filter_upwards [] with c
  exact (abs_real_inner_le_norm v (w c)).trans
    (mul_le_mul_of_nonneg_left (hR (w c) (hw c).1) (norm_nonneg v))

theorem support_as_min (hw : SPOBounds.Natarajan.IsOracle S w)
    (a : EuclideanSpace ℝ (Fin d)) : xi S a = -zstar S (-a) := by
  rw [SupportOracle.support_eq hw a,RiskSupport.zstar_eq hw (-a),inner_neg_left,neg_neg]

theorem loss_nonneg (hw : SPOBounds.Natarajan.IsOracle S w)
    (chat c : EuclideanSpace ℝ (Fin d)) : 0 ≤ spoPlusLoss S w chat c := by
  have h := SupportOracle.support_le hw (c-(2:ℝ)•chat) (w c) (hw c).1
  unfold spoPlusLoss
  rw [RiskSupport.zstar_eq hw c]
  simp only [inner_sub_left,real_inner_smul_left] at h
  linarith

theorem shifted_value_integrable (hSne : S.Nonempty) (hScpt : IsCompact S)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hInt : Integrable id P) (a : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun c => zstar S (a-c)) P := by
  obtain ⟨v,hv⟩ := RiskSupport.oracle_exists hSne hScpt
  obtain ⟨R,hR⟩ := RiskSupport.norm_bound hSne hScpt
  obtain ⟨L,hL⟩ := RiskSupport.zstar_lipschitz hSne hScpt
  have hi : Integrable (fun c : EuclideanSpace ℝ (Fin d) => a-c) P :=
    (integrable_const a).sub hInt
  apply (hi.norm.mul_const (R:ℝ)).mono'
    (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  filter_upwards [] with c
  change ‖zstar S (a-c)‖ ≤ ‖a-c‖*(R:ℝ)
  rw [RiskSupport.zstar_eq hv (a-c),Real.norm_eq_abs]
  exact (abs_real_inner_le_norm (a-c) (v (a-c))).trans
    (mul_le_mul_of_nonneg_left (hR (v (a-c)) (hv (a-c)).1) (norm_nonneg (a-c)))

theorem loss_integrable (hSne : S.Nonempty) (hScpt : IsCompact S)
    (hw : SPOBounds.Natarajan.IsOracle S w)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hInt : Integrable id P) (ha : P ≪ volume) (chat : EuclideanSpace ℝ (Fin d)) :
    Integrable (spoPlusLoss S w chat) P := by
  have h := ((shifted_value_integrable hSne hScpt P hInt ((2:ℝ)•chat)).neg.add
    ((oracle_scalar_integrable hSne hScpt hw P ha chat).const_mul 2)).sub
      (RiskSupport.zstar_integrable hSne hScpt P hInt)
  change Integrable (fun c => -zstar S ((2:ℝ)•chat-c) + 2*⟪chat,w c⟫_ℝ-zstar S c) P at h
  convert h using 1
  funext c
  simp only [spoPlusLoss,support_as_min hw,neg_sub]

#print axioms oracle_scalar_integrable
#print axioms loss_integrable
end RiskPlus

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory SmartPTO.Fisher
namespace RiskStrict
variable {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}

theorem positive_width (hSne : S.Nonempty) (hScpt : IsCompact S)
    (hInterior : (interior S).Nonempty) {q : EuclideanSpace ℝ (Fin d)} (hq : q ≠ 0) :
    0 < -zstar S (-q)-zstar S q := by
  obtain ⟨x,hx⟩ := hInterior
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  let t := ε/(2*‖q‖)
  have ht : 0 < t := div_pos hε (by positivity)
  have hte : t*(2*‖q‖) = ε := div_mul_cancel₀ ε (by positivity)
  have hp : x+t•q ∈ S := by
    apply hball
    rw [Metric.mem_ball,dist_eq_norm]
    have he : x+t•q-x = t•q := by abel
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    nlinarith
  have hm : x-t•q ∈ S := by
    apply hball
    rw [Metric.mem_ball,dist_eq_norm]
    have he : x-t•q-x = -(t•q) := by abel
    rw [he,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    nlinarith
  have a := Converse.gap_nonneg hSne hScpt hp (-q)
  have b := Converse.gap_nonneg hSne hScpt hm q
  simp only [inner_neg_left,inner_add_right,inner_sub_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq] at a b
  have hn2 : 0 < ‖q‖^2 := sq_pos_of_pos hn
  nlinarith [mul_pos ht hn2]

theorem slack_lower {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hw : SPOBounds.Natarajan.IsOracle S w)
    (R L : NNReal) (hR : ∀ v ∈ S, ‖v‖ ≤ (R:ℝ))
    (hL : LipschitzWith L (zstar S)) (a q : EuclideanSpace ℝ (Fin d)) :
    -zstar S (-q)-zstar S q - 2*((L:ℝ)+(R:ℝ))*‖a+q‖ ≤
      ⟪a+(2:ℝ)•q,w a⟫_ℝ-zstar S (a+(2:ℝ)•q) := by
  have h1 := hL.norm_sub_le a (-q)
  have h2 := hL.norm_sub_le (a+(2:ℝ)•q) q
  have he : a+(2:ℝ)•q-q = a+q := by module
  rw [he] at h2
  rw [sub_neg_eq_add,Real.norm_eq_abs] at h1
  rw [Real.norm_eq_abs] at h2
  have hi := abs_real_inner_le_norm (a+q) (w a)
  have hr := mul_le_mul_of_nonneg_left (hR (w a) (hw a).1) (norm_nonneg (a+q))
  have hz := RiskSupport.zstar_eq hw a
  have hc : ⟪a+(2:ℝ)•q,w a⟫_ℝ = 2*⟪a+q,w a⟫_ℝ-zstar S a := by
    rw [hz]
    simp only [inner_add_left,real_inner_smul_left]
    ring
  rw [hc]
  have h1' := (abs_le.mp h1).2
  have h2' := (abs_le.mp h2).2
  have hi' := (abs_le.mp hi).1
  nlinarith

theorem positive_slack_ball (hSne : S.Nonempty) (hScpt : IsCompact S)
    (hInterior : (interior S).Nonempty)
    {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hw : SPOBounds.Natarajan.IsOracle S w)
    {q : EuclideanSpace ℝ (Fin d)} (hq : q ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ Metric.ball (-q) δ,
      0 < ⟪a+(2:ℝ)•q,w a⟫_ℝ-zstar S (a+(2:ℝ)•q) := by
  obtain ⟨R,hR⟩ := RiskSupport.norm_bound hSne hScpt
  obtain ⟨L,hL⟩ := RiskSupport.zstar_lipschitz hSne hScpt
  let width := -zstar S (-q)-zstar S q
  have hwid : 0 < width := positive_width hSne hScpt hInterior hq
  let k := 2*((L:ℝ)+(R:ℝ))+1
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨width/k,div_pos hwid hk,?_⟩
  intro a ha
  have hn : ‖a+q‖ < width/k := by
    simpa only [Metric.mem_ball,dist_eq_norm,sub_neg_eq_add] using ha
  have hb : ‖a+q‖*k < width := (lt_div_iff₀ hk).mp hn
  have hs := slack_lower hw R L hR hL a q
  dsimp [k] at hb
  dsimp [width] at hb
  nlinarith [norm_nonneg (a+q)]

#print axioms positive_slack_ball
#print axioms positive_width
#print axioms slack_lower
end RiskStrict

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory SmartPTO.Fisher
namespace RiskStrict
variable {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
  {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}

theorem slack_identity (hw : SPOBounds.Natarajan.IsOracle S w)
    (m chat c : EuclideanSpace ℝ (Fin d)) :
    spoPlusLoss S w chat c - spoPlusLoss S w m c -
      2*(⟪chat-m,w c⟫_ℝ-⟪chat-m,w ((2:ℝ)•m-c)⟫_ℝ) =
      ⟪((2:ℝ)•m-c)+(2:ℝ)•(chat-m),w ((2:ℝ)•m-c)⟫_ℝ -
        zstar S (((2:ℝ)•m-c)+(2:ℝ)•(chat-m)) := by
  have he : ((2:ℝ)•m-c)+(2:ℝ)•(chat-m) = (2:ℝ)•chat-c := by module
  simp only [spoPlusLoss,RiskPlus.support_as_min hw,neg_sub]
  rw [← he,RiskSupport.zstar_eq hw ((2:ℝ)•m-c)]
  simp only [inner_add_left,real_inner_smul_left,inner_sub_left]
  ring

theorem strictly_larger (hSne : S.Nonempty) (hScpt : IsCompact S)
    (hScvx : Convex ℝ S) (hw : SPOBounds.Natarajan.IsOracle S w)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hInt : Integrable id P) (hCont : ContinuousOnAll P)
    (hSymm : CentrallySymmetric P) (hSinner : (interior S).Nonempty)
    (chat : EuclideanSpace ℝ (Fin d)) (hne : chat ≠ ∫ c,c ∂P) :
    spoPlusRisk S w P (∫ c,c ∂P) < spoPlusRisk S w P chat := by
  let m := ∫ c,c ∂P
  let q := chat-m
  let refl := fun c : EuclideanSpace ℝ (Fin d) => (2:ℝ)•m-c
  let g := fun c => ⟪q,w c⟫_ℝ
  let slack := fun c => spoPlusLoss S w chat c-spoPlusLoss S w m c-
    2*(g c-g (refl c))
  have hg : Integrable g P := RiskPlus.oracle_scalar_integrable hSne hScpt hw P hCont.1 q
  have hm : Measurable refl := measurable_const.sub measurable_id
  have hp : MeasurePreserving refl P P := ⟨hm,hSymm⟩
  have hgr : Integrable (fun c => g (refl c)) P := hp.integrable_comp_of_integrable hg
  have he : (∫ c,g c ∂P) = ∫ c,g (refl c) ∂P := by
    have h := integral_map hm.aemeasurable
      (show AEStronglyMeasurable g (P.map refl) from hp.map_eq.symm ▸ hg.aestronglyMeasurable)
    rw [hp.map_eq] at h
    exact h
  have hd : Integrable (fun c => 2*(g c-g (refl c))) P := (hg.sub hgr).const_mul 2
  have hdz : (∫ c,2*(g c-g (refl c)) ∂P) = 0 := by
    rw [integral_const_mul,integral_sub hg hgr,he,sub_self,mul_zero]
  have hLm := RiskPlus.loss_integrable hSne hScpt hw P hInt hCont.1 m
  have hLc := RiskPlus.loss_integrable hSne hScpt hw P hInt hCont.1 chat
  have hs : Integrable slack P := (hLc.sub hLm).sub hd
  have hseq : ∀ c, slack c = ⟪refl c+(2:ℝ)•q,w (refl c)⟫_ℝ -
      zstar S (refl c+(2:ℝ)•q) := fun c => slack_identity hw m chat c
  have hsnonneg : 0 ≤ slack := by
    intro c
    rw [hseq]
    exact Converse.gap_nonneg hSne hScpt (hw (refl c)).1 _
  have hq : q ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨δ,hδ,hball⟩ := positive_slack_ball hSne hScpt hSinner hw hq
  let U := refl ⁻¹' Metric.ball (-q) δ
  have hU : IsOpen U := Metric.isOpen_ball.preimage (continuous_const.sub continuous_id)
  have hUne : U.Nonempty := by
    refine ⟨(2:ℝ)•m+q,?_⟩
    change (2:ℝ)•m-((2:ℝ)•m+q) ∈ Metric.ball (-q) δ
    have hx : (2:ℝ)•m-((2:ℝ)•m+q) = -q := by abel
    rw [hx]
    exact Metric.mem_ball_self hδ
  have hUs : U ⊆ Function.support slack := by
    intro c hc
    change slack c ≠ 0
    rw [hseq]
    exact ne_of_gt (hball (refl c) hc)
  have hpos : 0 < ∫ c,slack c ∂P :=
    (integral_pos_iff_support_of_nonneg hsnonneg hs).mpr
      ((hCont.2 U hU hUne).trans_le (measure_mono hUs))
  have hstrict : (∫ c,spoPlusLoss S w m c ∂P) <
      ∫ c,spoPlusLoss S w chat c ∂P := by
    change 0 < ∫ c,spoPlusLoss S w chat c-spoPlusLoss S w m c-
      2*(g c-g (refl c)) ∂P at hpos
    have hdiff : Integrable (fun c => spoPlusLoss S w chat c-spoPlusLoss S w m c) P := hLc.sub hLm
    rw [integral_sub hdiff hd,integral_sub hLc hLm,hdz,sub_zero] at hpos
    exact sub_pos.mp hpos
  unfold spoPlusRisk
  rw [← ofReal_integral_eq_lintegral_ofReal hLm
    (Filter.Eventually.of_forall (RiskPlus.loss_nonneg hw m)),
    ← ofReal_integral_eq_lintegral_ofReal hLc
    (Filter.Eventually.of_forall (RiskPlus.loss_nonneg hw chat))]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (integral_nonneg (RiskPlus.loss_nonneg hw m))).mpr hstrict

end RiskStrict

 theorem prior_unique {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hw : SPOBounds.Natarajan.IsOracle S wstar)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hInt : Integrable id P) (hCont : ContinuousOnAll P)
    (hSymm : CentrallySymmetric P) (hSinner : (interior S).Nonempty)
    (chat : EuclideanSpace ℝ (Fin d))
    (hMin : spoPlusRisk S wstar P chat ≤ spoPlusRisk S wstar P (∫ c,c ∂P)) :
    chat = ∫ c,c ∂P := by
  by_contra hne
  exact (not_lt_of_ge hMin) (RiskStrict.strictly_larger hSne hScpt hScvx hw P
    hInt hCont hSymm hSinner chat hne)
#print axioms prior_unique

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory SmartPTO.Fisher

theorem prior_mean {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hw : SPOBounds.Natarajan.IsOracle S wstar)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hInt : Integrable id P) (hCont : ContinuousOnAll P)
    (hSymm : CentrallySymmetric P)
    (chat : EuclideanSpace ℝ (Fin d)) :
    spoPlusRisk S wstar P (∫ c, c ∂P) ≤ spoPlusRisk S wstar P chat := by
  let m := ∫ c,c ∂P
  let q := chat-m
  let refl := fun c : EuclideanSpace ℝ (Fin d) => (2:ℝ)•m-c
  let g := fun c => ⟪q,wstar c⟫_ℝ
  have hg : Integrable g P := RiskPlus.oracle_scalar_integrable hSne hScpt hw P hCont.1 q
  have hm : Measurable refl := measurable_const.sub measurable_id
  have hp : MeasurePreserving refl P P := ⟨hm,hSymm⟩
  have hgr : Integrable (fun c => g (refl c)) P := hp.integrable_comp_of_integrable hg
  have he : (∫ c,g c ∂P) = ∫ c,g (refl c) ∂P := by
    have h := integral_map hm.aemeasurable
      (show AEStronglyMeasurable g (P.map refl) from hp.map_eq.symm ▸ hg.aestronglyMeasurable)
    rw [hp.map_eq] at h
    exact h
  have hd : Integrable (fun c => 2*(g c-g (refl c))) P := (hg.sub hgr).const_mul 2
  have hdz : (∫ c,2*(g c-g (refl c)) ∂P) = 0 := by
    rw [integral_const_mul,integral_sub hg hgr,he,sub_self,mul_zero]
  have hLm := RiskPlus.loss_integrable hSne hScpt hw P hInt hCont.1 m
  have hLc := RiskPlus.loss_integrable hSne hScpt hw P hInt hCont.1 chat
  have hi : (∫ c,spoPlusLoss S wstar m c + 2*(g c-g (refl c)) ∂P) ≤
      ∫ c,spoPlusLoss S wstar chat c ∂P := by
    apply integral_mono (hLm.add hd) hLc
    intro c
    have h := prior_subgradient S hSne hScpt hScvx wstar hw c m chat
    simp only [real_inner_smul_left,inner_sub_left] at h
    rw [real_inner_comm (chat-m) (wstar c),
      real_inner_comm (chat-m) (wstar ((2:ℝ)•m-c))] at h
    exact h
  rw [integral_add hLm hd,hdz,add_zero] at hi
  unfold spoPlusRisk
  rw [← ofReal_integral_eq_lintegral_ofReal hLm
    (Filter.Eventually.of_forall (RiskPlus.loss_nonneg hw m)),
    ← ofReal_integral_eq_lintegral_ofReal hLc
    (Filter.Eventually.of_forall (RiskPlus.loss_nonneg hw chat))]
  exact ENNReal.ofReal_le_ofReal hi

#print axioms prior_mean

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory SmartPTO.Fisher
namespace RiskJoint
variable {d : ℕ} {X : Type*} [MeasurableSpace X]
  {S : Set (EuclideanSpace ℝ (Fin d))}
  {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}

noncomputable def regularLoss (S : Set (EuclideanSpace ℝ (Fin d)))
    (chat c : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -zstar S ((2:ℝ)•chat-c)+2*(fderiv ℝ (zstar S) c chat)-zstar S c

theorem regularLoss_measurable (hSne : S.Nonempty) (hScpt : IsCompact S)
    (f : X → EuclideanSpace ℝ (Fin d)) (hf : Measurable f) :
    Measurable (fun p : X × EuclideanSpace ℝ (Fin d) => regularLoss S (f p.1) p.2) := by
  obtain ⟨L,hL⟩ := RiskSupport.zstar_lipschitz hSne hScpt
  have happ : Continuous (fun p : ((EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ) × EuclideanSpace ℝ (Fin d) => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have heval := happ.measurable.comp (((measurable_fderiv ℝ (zstar S)).comp measurable_snd).prodMk (hf.comp measurable_fst))
  unfold regularLoss
  exact ((hL.continuous.measurable.comp ((hf.comp measurable_fst).const_smul (2:ℝ) |>.sub measurable_snd)).neg.add
    (heval.const_mul 2)).sub
      (hL.continuous.measurable.comp measurable_snd)

theorem regularLoss_eq (hSne : S.Nonempty) (hScpt : IsCompact S)
    (hw : SPOBounds.Natarajan.IsOracle S w) (chat c : EuclideanSpace ℝ (Fin d))
    (hc : DifferentiableAt ℝ (zstar S) c) :
    regularLoss S chat c = spoPlusLoss S w chat c := by
  unfold regularLoss spoPlusLoss
  rw [RiskRegularity.derivative_of_mem hSne hScpt (hw c) hc,
    RiskPlus.support_as_min hw,neg_sub]
  change -zstar S ((2:ℝ)•chat-c)+2*⟪w c,chat⟫_ℝ-zstar S c = _
  rw [real_inner_comm]

theorem regularLoss_ae (hSne : S.Nonempty) (hScpt : IsCompact S)
    (hw : SPOBounds.Natarajan.IsOracle S w)
    (P : Measure (EuclideanSpace ℝ (Fin d))) (hP : P ≪ volume)
    (chat : EuclideanSpace ℝ (Fin d)) :
    regularLoss S chat =ᵐ[P] spoPlusLoss S w chat := by
  obtain ⟨L,hL⟩ := RiskSupport.zstar_lipschitz hSne hScpt
  filter_upwards [hP.ae_le (hL.ae_differentiableAt (μ := volume))] with c hc
  exact regularLoss_eq hSne hScpt hw chat c hc

theorem regularLoss_joint_ae (hSne : S.Nonempty) (hScpt : IsCompact S)
    (hw : SPOBounds.Natarajan.IsOracle S w)
    (ν : Measure X) (κ : Kernel X (EuclideanSpace ℝ (Fin d)))
    (ha : ∀ x, κ x ≪ volume) (f : X → EuclideanSpace ℝ (Fin d)) :
    (fun p : X × EuclideanSpace ℝ (Fin d) => regularLoss S (f p.1) p.2) =ᵐ[ν ⊗ₘ κ]
      (fun p => spoPlusLoss S w (f p.1) p.2) := by
  obtain ⟨L,hL⟩ := RiskSupport.zstar_lipschitz hSne hScpt
  have hdiff : ∀ᵐ p : X × EuclideanSpace ℝ (Fin d) ∂(ν ⊗ₘ κ),
      DifferentiableAt ℝ (zstar S) p.2 := by
    apply Measure.ae_compProd_of_ae_ae
      (measurable_snd (measurableSet_of_differentiableAt ℝ (zstar S)))
    exact Filter.Eventually.of_forall fun x => (ha x).ae_le (hL.ae_differentiableAt (μ := volume))
  filter_upwards [hdiff] with p hp
  exact regularLoss_eq hSne hScpt hw (f p.1) p.2 hp

theorem risk_measurable (hSne : S.Nonempty) (hScpt : IsCompact S)
    (hw : SPOBounds.Natarajan.IsOracle S w)
    (κ : Kernel X (EuclideanSpace ℝ (Fin d))) [IsSFiniteKernel κ]
    (ha : ∀ x, κ x ≪ volume) (f : X → EuclideanSpace ℝ (Fin d)) (hf : Measurable f) :
    Measurable (fun x => spoPlusRisk S w (κ x) (f x)) := by
  have he : (fun x => spoPlusRisk S w (κ x) (f x)) =
      fun x => ∫⁻ c,ENNReal.ofReal (regularLoss S (f x) c) ∂κ x := by
    funext x
    exact lintegral_congr_ae ((regularLoss_ae hSne hScpt hw (κ x) (ha x) (f x)).symm.fun_comp ENNReal.ofReal)
  rw [he]
  exact (regularLoss_measurable hSne hScpt f hf).ennreal_ofReal.lintegral_kernel_prod_right

theorem risk_disintegration (hSne : S.Nonempty) (hScpt : IsCompact S)
    (hw : SPOBounds.Natarajan.IsOracle S w)
    (ν : Measure X) [SFinite ν] (κ : Kernel X (EuclideanSpace ℝ (Fin d))) [IsSFiniteKernel κ]
    (ha : ∀ x, κ x ≪ volume) (f : X → EuclideanSpace ℝ (Fin d)) (hf : Measurable f) :
    spoPlusRiskJoint S w (ν ⊗ₘ κ) f = ∫⁻ x,spoPlusRisk S w (κ x) (f x) ∂ν := by
  unfold spoPlusRiskJoint
  calc
    _ = ∫⁻ p,ENNReal.ofReal (regularLoss S (f p.1) p.2) ∂(ν ⊗ₘ κ) :=
      lintegral_congr_ae ((regularLoss_joint_ae hSne hScpt hw ν κ ha f).symm.fun_comp ENNReal.ofReal)
    _ = ∫⁻ x, ∫⁻ c,ENNReal.ofReal (regularLoss S (f x) c) ∂κ x ∂ν :=
      Measure.lintegral_compProd (regularLoss_measurable hSne hScpt f hf).ennreal_ofReal
    _ = _ := by
      apply lintegral_congr
      intro x
      exact lintegral_congr_ae ((regularLoss_ae hSne hScpt hw (κ x) (ha x) (f x)).fun_comp ENNReal.ofReal)

theorem mean_measurable (κ : Kernel X (EuclideanSpace ℝ (Fin d))) :
    Measurable (fun x => ∫ c,c ∂κ x) :=
  (stronglyMeasurable_id.integral_kernel (κ := κ)).measurable

#print axioms risk_disintegration
#print axioms risk_measurable
end RiskJoint

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory SmartPTO.Fisher
namespace RiskJoint
variable {d : ℕ} {X : Type*} [MeasurableSpace X]
  {S : Set (EuclideanSpace ℝ (Fin d))}
  {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}

theorem loss_bound (hw : SPOBounds.Natarajan.IsOracle S w)
    (R : NNReal) (hR : ∀ v ∈ S, ‖v‖ ≤ (R:ℝ)) (chat c : EuclideanSpace ℝ (Fin d)) :
    ‖spoPlusLoss S w chat c‖ ≤ 4*(R:ℝ)*‖chat‖+2*(R:ℝ)*‖c‖ := by
  have hz : ∀ v, |zstar S v| ≤ ‖v‖*(R:ℝ) := by
    intro v
    rw [RiskSupport.zstar_eq hw]
    exact (abs_real_inner_le_norm v (w v)).trans
      (mul_le_mul_of_nonneg_left (hR (w v) (hw v).1) (norm_nonneg v))
  have hi : |⟪chat,w c⟫_ℝ| ≤ ‖chat‖*(R:ℝ) :=
    (abs_real_inner_le_norm chat (w c)).trans
      (mul_le_mul_of_nonneg_left (hR (w c) (hw c).1) (norm_nonneg chat))
  have hn : ‖(2:ℝ)•chat-c‖ ≤ 2*‖chat‖+‖c‖ := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      using norm_sub_le ((2:ℝ)•chat) c
  have hm := mul_le_mul_of_nonneg_right hn R.coe_nonneg
  rw [Real.norm_eq_abs,abs_of_nonneg (RiskPlus.loss_nonneg hw chat c)]
  unfold spoPlusLoss
  rw [RiskPlus.support_as_min hw,neg_sub]
  have h1 := (abs_le.mp (hz ((2:ℝ)•chat-c))).1
  have h2 := (abs_le.mp (hz c)).1
  have h3 := (abs_le.mp hi).2
  nlinarith

theorem mean_integrable (ν : Measure X) [SFinite ν]
    (κ : Kernel X (EuclideanSpace ℝ (Fin d))) [IsSFiniteKernel κ]
    (hJointInt : Integrable (fun p : X × EuclideanSpace ℝ (Fin d) => p.2) (ν ⊗ₘ κ)) :
    Integrable (fun x => ∫ c,c ∂κ x) ν := by
  have h := ((Measure.integrable_compProd_iff hJointInt.aestronglyMeasurable).mp hJointInt).2
  apply h.mono' (mean_measurable κ).aestronglyMeasurable
  filter_upwards [] with x
  exact norm_integral_le_integral_norm _

theorem mean_loss_integrable (hSne : S.Nonempty) (hScpt : IsCompact S)
    (hw : SPOBounds.Natarajan.IsOracle S w)
    (ν : Measure X) [IsProbabilityMeasure ν]
    (κ : Kernel X (EuclideanSpace ℝ (Fin d))) [IsMarkovKernel κ]
    (ha : ∀ x, κ x ≪ volume)
    (hJointInt : Integrable (fun p : X × EuclideanSpace ℝ (Fin d) => p.2) (ν ⊗ₘ κ)) :
    Integrable (fun p : X × EuclideanSpace ℝ (Fin d) =>
      spoPlusLoss S w (∫ c,c ∂κ p.1) p.2) (ν ⊗ₘ κ) := by
  obtain ⟨R,hR⟩ := RiskSupport.norm_bound hSne hScpt
  have hp : MeasurePreserving (Prod.fst : X × EuclideanSpace ℝ (Fin d) → X) (ν ⊗ₘ κ) ν :=
    ⟨measurable_fst,Measure.fst_compProd ν κ⟩
  have hm := hp.integrable_comp_of_integrable (mean_integrable ν κ hJointInt)
  have hb := (hm.norm.const_mul (4*(R:ℝ))).add (hJointInt.norm.const_mul (2*(R:ℝ)))
  have hmeas := (regularLoss_measurable hSne hScpt _ (mean_measurable κ)).aestronglyMeasurable.congr
    (regularLoss_joint_ae hSne hScpt hw ν κ ha (fun x => ∫ c,c ∂κ x))
  apply hb.mono' hmeas
  exact Filter.Eventually.of_forall fun p => loss_bound hw R hR _ _

theorem mean_joint_risk_finite (hSne : S.Nonempty) (hScpt : IsCompact S)
    (hw : SPOBounds.Natarajan.IsOracle S w)
    (ν : Measure X) [IsProbabilityMeasure ν]
    (κ : Kernel X (EuclideanSpace ℝ (Fin d))) [IsMarkovKernel κ]
    (ha : ∀ x, κ x ≪ volume)
    (hJointInt : Integrable (fun p : X × EuclideanSpace ℝ (Fin d) => p.2) (ν ⊗ₘ κ)) :
    spoPlusRiskJoint S w (ν ⊗ₘ κ) (fun x => ∫ c,c ∂κ x) ≠ ⊤ := by
  have hi := mean_loss_integrable hSne hScpt hw ν κ ha hJointInt
  unfold spoPlusRiskJoint
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun p => RiskPlus.loss_nonneg hw _ _)]
  exact ENNReal.ofReal_ne_top

#print axioms mean_joint_risk_finite
end RiskJoint

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory SmartPTO.Fisher
namespace RiskJoint

theorem global_minimizer_mean {d : ℕ} {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (κ : Kernel X (EuclideanSpace ℝ (Fin d))) [IsMarkovKernel κ]
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hw : SPOBounds.Natarajan.IsOracle S wstar)
    (hCondInt : ∀ x, Integrable id (κ x))
    (hJointInt : Integrable (fun p : X × EuclideanSpace ℝ (Fin d) => p.2) (ν ⊗ₘ κ))
    (hSymm : ∀ x, CentrallySymmetric (κ x))
    (hCont : ∀ x, ContinuousOnAll (κ x))
    (hSinner : (interior S).Nonempty)
    (f : X → EuclideanSpace ℝ (Fin d)) (hf : Measurable f)
    (hMin : ∀ g : X → EuclideanSpace ℝ (Fin d), Measurable g →
      spoPlusRiskJoint S wstar (ν ⊗ₘ κ) f ≤ spoPlusRiskJoint S wstar (ν ⊗ₘ κ) g) :
    f =ᵐ[ν] fun x => ∫ c,c ∂κ x := by
  let m := fun x => ∫ c,c ∂κ x
  have hm : Measurable m := mean_measurable κ
  have hmin := hMin m hm
  have heq := risk_disintegration hSne hScpt hw ν κ (fun x => (hCont x).1)
  rw [heq f hf,heq m hm] at hmin
  have hfinite : (∫⁻ x,spoPlusRisk S wstar (κ x) (m x) ∂ν) ≠ ⊤ := by
    rw [← heq m hm]
    exact mean_joint_risk_finite hSne hScpt hw ν κ (fun x => (hCont x).1) hJointInt
  have hle : (fun x => spoPlusRisk S wstar (κ x) (m x)) ≤ᵐ[ν]
      fun x => spoPlusRisk S wstar (κ x) (f x) :=
    Filter.Eventually.of_forall fun x => prior_mean S hSne hScpt hScvx wstar hw (κ x)
      (hCondInt x) (hCont x) (hSymm x) (f x)
  have ha := ae_eq_of_ae_le_of_lintegral_le hle hfinite
    (risk_measurable hSne hScpt hw κ (fun x => (hCont x).1) f hf).aemeasurable hmin
  filter_upwards [ha] with x hx
  exact prior_unique S hSne hScpt hScvx wstar hw (κ x) (hCondInt x) (hCont x)
    (hSymm x) hSinner (f x) hx.ge

#print axioms global_minimizer_mean
end RiskJoint

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory SmartPTO.Fisher
namespace RiskJoint
variable {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}

theorem optimal_iff_value (hSne : S.Nonempty) (hScpt : IsCompact S)
    (chat v : EuclideanSpace ℝ (Fin d)) :
    v ∈ Wstar S chat ↔ v ∈ S ∧ ⟪chat,v⟫_ℝ = zstar S chat := by
  constructor
  · intro h
    exact ⟨h.1,(RiskRegularity.value_of_mem hSne hScpt h).symm⟩
  · rintro ⟨hv,he⟩
    refine ⟨hv,?_⟩
    intro u hu
    rw [he]
    exact sub_nonneg.mp (Converse.gap_nonneg hSne hScpt hu chat)

theorem optimal_compact (hSne : S.Nonempty) (hScpt : IsCompact S)
    (chat : EuclideanSpace ℝ (Fin d)) : IsCompact (Wstar S chat) := by
  have he : Wstar S chat = S ∩ {v | ⟪chat,v⟫_ℝ = zstar S chat} := by
    ext v
    exact optimal_iff_value hSne hScpt chat v
  rw [he]
  exact hScpt.inter_right (isClosed_eq (continuous_const.inner continuous_id) continuous_const)

theorem loss_attained (hSne : S.Nonempty) (hScpt : IsCompact S)
    (chat c : EuclideanSpace ℝ (Fin d)) :
    ∃ v ∈ Wstar S chat, spoLoss S chat c = ⟪c,v⟫_ℝ-zstar S c := by
  obtain ⟨w,hw⟩ := RiskSupport.oracle_exists hSne hScpt
  have hne : (Wstar S chat).Nonempty := ⟨w chat,hw chat⟩
  obtain ⟨v,hv,hm⟩ := (optimal_compact hSne hScpt chat).exists_isMaxOn hne
    (continuous_const.inner continuous_id : Continuous fun v : EuclideanSpace ℝ (Fin d) => ⟪c,v⟫_ℝ).continuousOn
  refine ⟨v,hv,?_⟩
  unfold spoLoss
  congr 1
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro _ ⟨u,hu,rfl⟩
    exact hm hu
  · apply le_csSup
    · exact ((optimal_compact hSne hScpt chat).image
        (continuous_const.inner continuous_id)).bddAbove
    · exact ⟨v,hv,rfl⟩

theorem spoLoss_measurable (hSne : S.Nonempty) (hScpt : IsCompact S) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => spoLoss S p.1 p.2) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hScpt
  obtain ⟨L,hL⟩ := RiskSupport.zstar_lipschitz hSne hScpt
  have hz := hL.continuous
  apply measurable_of_Ici
  intro r
  let D : Set ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × S) :=
    {p | ⟪p.1.1,(p.2:EuclideanSpace ℝ (Fin d))⟫_ℝ = zstar S p.1.1 ∧
      r ≤ ⟪p.1.2,(p.2:EuclideanSpace ℝ (Fin d))⟫_ℝ-zstar S p.1.2}
  have hD : IsClosed D := by
    apply IsClosed.inter
    · exact isClosed_eq (continuous_fst.fst.inner (continuous_subtype_val.comp continuous_snd))
        (hz.comp continuous_fst.fst)
    · exact isClosed_le continuous_const
        ((continuous_fst.snd.inner (continuous_subtype_val.comp continuous_snd)).sub
          (hz.comp continuous_fst.snd))
  have he : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      spoLoss S p.1 p.2) ⁻¹' Set.Ici r = Prod.fst '' D := by
    ext p
    constructor
    · intro hp
      obtain ⟨v,hv,he⟩ := loss_attained hSne hScpt p.1 p.2
      refine ⟨(p,⟨v,hv.1⟩),?_,rfl⟩
      exact ⟨((optimal_iff_value hSne hScpt p.1 v).mp hv).2,by
        change r ≤ spoLoss S p.1 p.2 at hp
        rwa [he] at hp⟩
    · rintro ⟨⟨q,v⟩,⟨hv,hr⟩,rfl⟩
      exact hr.trans (Converse.gap_le_loss hScpt
        ((optimal_iff_value hSne hScpt q.1 v).mpr ⟨v.property,hv⟩) q.2)
  rw [he]
  exact (isClosedMap_fst_of_compactSpace D hD).measurableSet

#print axioms spoLoss_measurable
end RiskJoint

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory SmartPTO.Fisher

theorem solution {d : ℕ} {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (κ : Kernel X (EuclideanSpace ℝ (Fin d))) [IsMarkovKernel κ]
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hw : SPOBounds.Natarajan.IsOracle S wstar)
    (hCondInt : ∀ x, Integrable id (κ x))
    (hJointInt : Integrable (fun p : X × EuclideanSpace ℝ (Fin d) => p.2) (ν ⊗ₘ κ))
    (hSingle : ∀ᵐ x ∂ν, ∃ w, Wstar S (∫ c,c ∂κ x) = {w})
    (hSymm : ∀ x, CentrallySymmetric (κ x))
    (hCont : ∀ x, ContinuousOnAll (κ x))
    (hSinner : (interior S).Nonempty)
    (f : X → EuclideanSpace ℝ (Fin d)) (hf : Measurable f)
    (hMin : ∀ g : X → EuclideanSpace ℝ (Fin d), Measurable g →
      spoPlusRiskJoint S wstar (ν ⊗ₘ κ) f ≤ spoPlusRiskJoint S wstar (ν ⊗ₘ κ) g) :
    (f =ᵐ[ν] fun x => ∫ c,c ∂κ x) ∧
      ∀ g : X → EuclideanSpace ℝ (Fin d), Measurable g →
        spoRiskJoint S (ν ⊗ₘ κ) f ≤ spoRiskJoint S (ν ⊗ₘ κ) g := by
  let m := fun x => ∫ c,c ∂κ x
  have hm : Measurable m := RiskJoint.mean_measurable κ
  have hfm : f =ᵐ[ν] m := RiskJoint.global_minimizer_mean ν κ S hSne hScpt hScvx
    wstar hw hCondInt hJointInt hSymm hCont hSinner f hf hMin
  refine ⟨hfm,?_⟩
  have hdis : ∀ (g : X → EuclideanSpace ℝ (Fin d)), Measurable g →
      spoRiskJoint S (ν ⊗ₘ κ) g = ∫⁻ x,spoRisk S (κ x) (g x) ∂ν := by
    intro g hg
    exact Measure.lintegral_compProd
      ((RiskJoint.spoLoss_measurable hSne hScpt).comp
        ((hg.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal
  have hfle : spoRiskJoint S (ν ⊗ₘ κ) f = spoRiskJoint S (ν ⊗ₘ κ) m := by
    apply lintegral_congr_ae
    filter_upwards [Measure.ae_eq_compProd_of_ae_eq_fst κ hf hm hfm] with p hp
    rw [hp]
  intro g hg
  rw [hfle,hdis m hm,hdis g hg]
  apply lintegral_mono_ae
  filter_upwards [hSingle] with x hx
  exact prior_converse S hSne hScpt hScvx (κ x) (hCondInt x) (m x) hx
    (fun _ h => h) (g x)

#print axioms solution
