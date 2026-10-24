-- Prove2me | solution 1 for SmartPTO.Fisher.prop6a_mean_minimizes
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T19:03:32.866853+00:00
-- url     : https://prove2.me/submissions/5f4903fe-ed48-4e6e-8731-5801653c2333

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

theorem solution {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
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

#print axioms solution
