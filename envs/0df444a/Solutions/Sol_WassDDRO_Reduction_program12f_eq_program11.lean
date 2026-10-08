-- Prove2me | solution 1 for WassDDRO.Reduction.program12f_eq_program11
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T10:19:12.795358+00:00
-- url     : https://prove2.me/submissions/470e1596-d033-4583-9f01-cee731a92aba

import Definitions.Def_WassDDRO_Reduction_Setting
set_option autoImplicit false
section
set_option autoImplicit false
namespace WassReductionCodex
 theorem dual_ball_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (lam : ℝ) (hlam : 0≤lam) :
    ∃ z : StrongDual ℝ E, ‖z‖≤lam ∧ z v=lam*‖v‖ ∧
      ∀ w : StrongDual ℝ E, ‖w‖≤lam → w v≤lam*‖v‖ := by
  obtain ⟨g,hg,hv⟩ := exists_dual_vector'' ℝ v
  refine ⟨lam • g, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]
    nlinarith [mul_le_mul_of_nonneg_left hg hlam]
  · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hv, RCLike.ofReal_real_eq_id, id_eq]
  · intro w hw
    calc
      w v ≤ |w v| := le_abs_self _
      _ ≤ ‖w‖*‖v‖ := by simpa only [Real.norm_eq_abs] using w.le_opNorm v
      _ ≤ lam*‖v‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg v)
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
 theorem pointwise_dual_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (lam : ℝ) (hlam : 0≤lam) (L : EReal) :
    L-((lam*‖v‖ : ℝ) : EReal) =
      (⨅ z ∈ {z : StrongDual ℝ E | ‖z‖≤lam}, L-((z v : ℝ) : EReal)) ∧
    ∃ z : StrongDual ℝ E, ‖z‖≤lam ∧ L-((z v : ℝ) : EReal)=L-((lam*‖v‖ : ℝ) : EReal) := by
  obtain ⟨z,hz,he,hbound⟩ := dual_ball_support v lam hlam
  refine ⟨?_,z,hz,?_⟩
  · apply le_antisymm
    · apply le_iInf
      intro w
      apply le_iInf
      intro hw
      exact EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.mpr (hbound w hw))
    · apply iInf_le_of_le z
      apply iInf_le_of_le hz
      rw [he]
  · rw [he]
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem finite_threshold_iff (L : EReal) (r d : ℝ) :
    -L ≤ ((-r-d : ℝ) : EReal) ↔ (r : EReal) ≤ L-(d : EReal) := by
  cases L using EReal.rec <;> simp only [EReal.neg_bot, EReal.neg_top,
    EReal.bot_sub, EReal.top_sub (EReal.coe_ne_top _), top_le_iff, le_bot_iff,
    EReal.coe_ne_top, EReal.coe_ne_bot, not_false_eq_true, false_iff, iff_false,
    ← EReal.coe_neg, ← EReal.coe_sub, EReal.coe_le_coe_iff, bot_le, le_top]
  constructor <;> intro h <;> linarith
 theorem shifted_quasiconcave {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {K : ℕ} (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (k : Fin K) (z : StrongDual ℝ E) (xhat : E) :
    QuasiconcaveOn ℝ Ξ (fun ξ => ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)) := by
  intro r
  cases r using EReal.rec with
  | bot => simpa using hA.convex
  | top =>
    have he : Ξ ∩ {ξ | (⊤ : EReal) ≤ ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ξ hx
      have hn : ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal) ≠ ⊤ := by
        cases h : ℓ k ξ using EReal.rec
        · simp
        · simp [← EReal.coe_sub]
        · exact False.elim (hA.ne_top k ξ h)
      exact hn (top_le_iff.mp hx.2)
    change Convex ℝ (Ξ ∩ {ξ | (⊤ : EReal) ≤ ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)})
    rw [he]
    exact convex_empty
  | coe r =>
    intro x hx y hy a b ha hb hab
    refine ⟨hA.convex hx.1 hy.1 ha hb hab, ?_⟩
    have hx' : (x,-r-z (x-xhat)) ∈ {p : E×ℝ | -ℓ k p.1 ≤ (p.2 : EReal)} :=
      (finite_threshold_iff (ℓ k x) r (z (x-xhat))).mpr hx.2
    have hy' : (y,-r-z (y-xhat)) ∈ {p : E×ℝ | -ℓ k p.1 ≤ (p.2 : EReal)} :=
      (finite_threshold_iff (ℓ k y) r (z (y-xhat))).mpr hy.2
    have hc := hA.convex_epigraph k hx' hy' ha hb hab
    change -ℓ k (a • x+b • y) ≤
      ((a*(-r-z (x-xhat))+b*(-r-z (y-xhat)) : ℝ) : EReal) at hc
    have hd : a*(-r-z (x-xhat))+b*(-r-z (y-xhat)) = -r-z (a • x+b • y-xhat) := by
      simp only [map_sub,map_add,map_smul,smul_eq_mul]
      linear_combination (-r+z xhat)*hab
    rw [hd] at hc
    exact (finite_threshold_iff (ℓ k (a • x+b • y)) r (z (a • x+b • y-xhat))).mp hc
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem ereal_neg_upper {α : Type*} [TopologicalSpace α] (f : α → EReal)
    (hf : LowerSemicontinuous f) : UpperSemicontinuous (fun x => -f x) := by
  change LowerSemicontinuous (fun x => OrderDual.toDual (-f x))
  have hg : Continuous (fun t : EReal => OrderDual.toDual (-t)) := continuous_neg
  have hm : Monotone (fun t : EReal => OrderDual.toDual (-t)) := fun x y h => EReal.neg_le_neg_iff.mpr h
  simpa only [Function.comp_def] using hg.comp_lowerSemicontinuous hf hm
 theorem shifted_upperSemicontinuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {K : ℕ} (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (k : Fin K) (z : StrongDual ℝ E) (xhat : E) :
    UpperSemicontinuous (fun ξ => ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)) := by
  have hl : UpperSemicontinuous (ℓ k) := by
    simpa only [neg_neg] using ereal_neg_upper (fun ξ => -ℓ k ξ) (hA.lsc k)
  have hc : Continuous (fun ξ => ((-z (ξ-xhat) : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp (z.continuous.comp (continuous_id.sub continuous_const)).neg
  have hs := hl.add' hc.upperSemicontinuous (fun ξ =>
    EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _)))
  simpa only [sub_eq_add_neg, EReal.coe_neg] using hs
 theorem shifted_dual_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (L : EReal) : Continuous (fun z : StrongDual ℝ E => L-((z v : ℝ) : EReal)) := by
  have hc : Continuous (fun z : StrongDual ℝ E => ((-z v : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp ((ContinuousLinearMap.apply ℝ ℝ v).continuous.neg)
  have hs : Continuous (fun z : StrongDual ℝ E => L+((-z v : ℝ) : EReal)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))).comp
      (continuousAt_const.prodMk hc.continuousAt)
  simpa only [sub_eq_add_neg,EReal.coe_neg] using hs
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem shifted_dual_quasiconvex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set (StrongDual ℝ E)) (hC : Convex ℝ C) (v : E) (L : EReal) :
    QuasiconvexOn ℝ C (fun z => L-((z v : ℝ) : EReal)) := by
  cases L using EReal.rec with
  | bot => intro r;simpa only [EReal.bot_sub,bot_le,Set.sep_true] using hC
  | top =>
    intro r
    by_cases hr : (⊤ : EReal)≤r
    · simpa only [EReal.top_sub (EReal.coe_ne_top _),hr,Set.sep_true] using hC
    · simpa only [EReal.top_sub (EReal.coe_ne_top _),hr,Set.sep_false] using
        (show Convex ℝ (∅ : Set (StrongDual ℝ E)) from convex_empty)
  | coe r =>
    have hc : ConvexOn ℝ C (fun z : StrongDual ℝ E => r-z v) := by
      refine ⟨hC, ?_⟩
      intro x hx y hy a b ha hb hab
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have hr := congrArg (fun t : ℝ => t*r) hab
      nlinarith
    have hm : Monotone (fun r : ℝ => (r : EReal)) := fun a b h => EReal.coe_le_coe_iff.mpr h
    simpa only [Function.comp_def, ← EReal.coe_sub] using hc.quasiconvexOn.monotone_comp hm

 theorem minimax_dual_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (k : Fin K) (xhat : E) (lam : ℝ) (hlam : 0≤lam) :
    (⨆ ξ ∈ Ξ, ℓ k ξ-((lam*‖ξ-xhat‖ : ℝ) : EReal)) =
      (⨅ z ∈ {z : StrongDual ℝ E | ‖z‖≤lam},
        ⨆ ξ ∈ Ξ, ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)) ∧
    ∃ z : StrongDual ℝ E, ‖z‖≤lam ∧
      (⨆ ξ ∈ Ξ, ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)) =
        (⨆ ξ ∈ Ξ, ℓ k ξ-((lam*‖ξ-xhat‖ : ℝ) : EReal)) := by
  let B := {z : StrongDual ℝ E | ‖z‖≤lam}
  let F := fun (z : StrongDual ℝ E) (ξ : E) => ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)
  have hB : B=Metric.closedBall (0 : StrongDual ℝ E) lam := by
    ext z
    simp only [B,Set.mem_setOf_eq,Metric.mem_closedBall,dist_zero_right]
  have hne : B.Nonempty := ⟨0,by simpa only [B,Set.mem_setOf_eq,norm_zero] using hlam⟩
  have hc : Convex ℝ B := by rw [hB];exact convex_closedBall 0 lam
  have hk : IsCompact B := by rw [hB];exact isCompact_closedBall 0 lam
  have hsion := Sion.minimax' (f:=F) hne hc hk
    (fun ξ _ => (shifted_dual_continuous (ξ-xhat) (ℓ k ξ)).lowerSemicontinuous.lowerSemicontinuousOn B)
    (fun ξ _ => shifted_dual_quasiconvex B hc (ξ-xhat) (ℓ k ξ)) hA.convex
    (fun z _ => (shifted_upperSemicontinuous Ξ ℓ hA k z xhat).upperSemicontinuousOn Ξ)
    (fun z _ => shifted_quasiconcave Ξ ℓ hA k z xhat)
  have hp (ξ : E) : (⨅ z ∈ B, F z ξ)=ℓ k ξ-((lam*‖ξ-xhat‖ : ℝ) : EReal) :=
    (pointwise_dual_ball (ξ-xhat) lam hlam (ℓ k ξ)).1.symm
  have he : (⨆ ξ ∈ Ξ, ℓ k ξ-((lam*‖ξ-xhat‖ : ℝ) : EReal)) = ⨅ z ∈ B, ⨆ ξ ∈ Ξ, F z ξ := by
    simpa only [hp] using hsion.symm
  have hlow : LowerSemicontinuous (fun z => ⨆ ξ ∈ Ξ, F z ξ) :=
    lowerSemicontinuous_iSup (fun ξ => lowerSemicontinuous_iSup (fun _ =>
      (shifted_dual_continuous (ξ-xhat) (ℓ k ξ)).lowerSemicontinuous))
  obtain ⟨z,hz,hmin⟩ := hlow.lowerSemicontinuousOn B |>.exists_isMinOn hne hk
  have hv : (⨅ w ∈ B, ⨆ ξ ∈ Ξ, F w ξ) = ⨆ ξ ∈ Ξ, F z ξ := by
    apply le_antisymm
    · exact iInf_le_of_le z (iInf_le_of_le hz le_rfl)
    · exact le_iInf₂ hmin
  refine ⟨he,z,hz,?_⟩
  rw [he,hv]
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction

def liftedSupport {E : Type*} (Ξ : Set E) : Set (E×E) := Set.univ ×ˢ Ξ

def liftedLoss {E : Type*} {K : ℕ} (ℓ : Fin K → E → EReal) : Fin K → (E×E) → EReal :=
  fun k p => ℓ k p.1

theorem lifted_assumption {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {K : ℕ} (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) : Assumption41 (liftedSupport Ξ) (liftedLoss ℓ) := by
  refine ⟨convex_univ.prod hA.convex,isClosed_univ.prod hA.closed,
    (fun k p => hA.ne_top k p.1),?_,?_,?_⟩
  · intro k
    exact (hA.convex_epigraph k).linear_preimage
      ((LinearMap.fst ℝ E E).prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
  · intro k
    exact (hA.lsc k).comp continuous_fst
  · intro k
    obtain ⟨x,hx,hbot⟩ := hA.not_bot_on k
    exact ⟨(x,x),⟨Set.mem_univ _,hx⟩,hbot⟩

noncomputable def pairFunctional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : StrongDual ℝ E × StrongDual ℝ E) : StrongDual ℝ (E×E) :=
  d.1.comp (ContinuousLinearMap.fst ℝ E E)+
    d.2.comp (ContinuousLinearMap.fst ℝ E E-ContinuousLinearMap.snd ℝ E E)

theorem pairFunctional_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : StrongDual ℝ E × StrongDual ℝ E) (p : E×E) (xhat : E) :
    pairFunctional d (p-(xhat,xhat))=d.1 (p.1-xhat)+d.2 (p.1-p.2) := by
  have he : (p.1-xhat)-(p.2-xhat)=p.1-p.2 := by abel
  change d.1 (p.1-xhat)+d.2 ((p.1-xhat)-(p.2-xhat))=d.1 (p.1-xhat)+d.2 (p.1-p.2)
  rw [he]

end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex

noncomputable def dualPairEval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v w : E) : (StrongDual ℝ E × StrongDual ℝ E) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ v).comp (ContinuousLinearMap.fst ℝ _ _)+
    (ContinuousLinearMap.apply ℝ ℝ w).comp (ContinuousLinearMap.snd ℝ _ _)

lemma ereal_linear_continuous {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : StrongDual ℝ V) (L : EReal) : Continuous (fun x : V => L-((P x : ℝ) : EReal)) := by
  have hc : Continuous (fun x : V => ((-P x : ℝ) : EReal)) := continuous_coe_real_ereal.comp P.continuous.neg
  have hh : Continuous (fun x : V => L+((-P x : ℝ) : EReal)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))).comp
      (continuousAt_const.prodMk hc.continuousAt)
  simpa only [sub_eq_add_neg,EReal.coe_neg] using hh

lemma ereal_linear_quasiconvex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (C : Set V) (hC : Convex ℝ C) (P : StrongDual ℝ V) (L : EReal) :
    QuasiconvexOn ℝ C (fun x : V => L-((P x : ℝ) : EReal)) := by
  cases L using EReal.rec with
  | bot => intro r;simpa only [EReal.bot_sub,bot_le,Set.sep_true] using hC
  | top =>
    intro r
    by_cases hr : (⊤ : EReal) ≤ r
    · simpa only [EReal.top_sub (EReal.coe_ne_top _),hr,Set.sep_true] using hC
    · simpa only [EReal.top_sub (EReal.coe_ne_top _),hr,Set.sep_false] using
        (show Convex ℝ (∅ : Set V) from convex_empty)
  | coe r =>
    have hc : ConvexOn ℝ C (fun x : V => r-P x) := by
      refine ⟨hC,?_⟩
      intro x hx y hy a b ha hb hab
      simp only [map_add,map_smul,smul_eq_mul]
      have hh := congrArg (fun q : ℝ => q*r) hab
      nlinarith
    have hm : Monotone (fun r : ℝ => (r : EReal)) := fun a b h => EReal.coe_le_coe_iff.mpr h
    simpa only [Function.comp_def,←EReal.coe_sub] using hc.quasiconvexOn.monotone_comp hm

def dualPairBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lam t : ℝ) : Set (StrongDual ℝ E × StrongDual ℝ E) :=
  {d | ‖d.1‖ ≤ lam ∧ ‖d.2‖ ≤ t}

noncomputable def dualPairKernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E → EReal) (xhat : E) (d : StrongDual ℝ E × StrongDual ℝ E) (p : E×E) : EReal :=
  L p.1-((d.1 (p.1-xhat)+d.2 (p.1-p.2) : ℝ) : EReal)

lemma dualPairKernel_shifted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E → EReal) (xhat : E) (d : StrongDual ℝ E × StrongDual ℝ E) :
    dualPairKernel L xhat d =
      (fun p : E×E => L p.1-((pairFunctional d (p-(xhat,xhat)) : ℝ) : EReal)) := by
  funext p
  rw [pairFunctional_shift]
  rfl

lemma dualPairKernel_pointwise_inf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E → EReal) (xhat : E) (p : E×E) (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    (⨅ d∈dualPairBall (E:=E) lam t, dualPairKernel L xhat d p) =
      L p.1-((lam*‖p.1-xhat‖+t*‖p.1-p.2‖ : ℝ) : EReal) := by
  obtain ⟨z,hz,hzv,hbz⟩ := dual_ball_support (p.1-xhat) lam hlam
  obtain ⟨ν,hν,hνv,hbν⟩ := dual_ball_support (p.1-p.2) t ht
  apply le_antisymm
  · apply iInf_le_of_le (z,ν)
    apply iInf_le_of_le ⟨hz,hν⟩
    change L p.1-((z (p.1-xhat)+ν (p.1-p.2) : ℝ) : EReal) ≤ _
    rw [hzv,hνv]
  · apply le_iInf
    intro d
    apply le_iInf
    intro hd
    exact EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.mpr
      (add_le_add (hbz d.1 hd.1) (hbν d.2 hd.2)))
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction

theorem dualPair_minimax_upper {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (k : Fin K) (xhat : E) (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t) (S : ℝ)
    (hupper : ∀ x y : E, y∈Ξ →
      ℓ k x-((lam*‖x-xhat‖+t*‖x-y‖ : ℝ) : EReal) ≤ (S : EReal)) :
    ∃ d : StrongDual ℝ E × StrongDual ℝ E, d∈dualPairBall lam t ∧
      ∀ x y : E, y∈Ξ → dualPairKernel (ℓ k) xhat d (x,y) ≤ (S : EReal) := by
  let B := dualPairBall (E:=E) lam t
  let F := dualPairKernel (ℓ k) xhat
  have hB : B=Metric.closedBall (0 : StrongDual ℝ E) lam ×ˢ Metric.closedBall (0 : StrongDual ℝ E) t := by
    ext d
    simp only [B,dualPairBall,Set.mem_setOf_eq,Set.mem_prod,Metric.mem_closedBall,dist_zero_right]
  have hne : B.Nonempty := ⟨(0,0),⟨by simpa using hlam,by simpa using ht⟩⟩
  have hc : Convex ℝ B := by rw [hB];exact (convex_closedBall 0 lam).prod (convex_closedBall 0 t)
  have hk : IsCompact B := by rw [hB];exact (isCompact_closedBall 0 lam).prod (isCompact_closedBall 0 t)
  have hLift := lifted_assumption Ξ ℓ hA
  have hsion := Sion.minimax' (f:=F) hne hc hk
    (fun p _ => (ereal_linear_continuous (dualPairEval (p.1-xhat) (p.1-p.2)) (ℓ k p.1)).lowerSemicontinuous.lowerSemicontinuousOn B)
    (fun p _ => ereal_linear_quasiconvex B hc (dualPairEval (p.1-xhat) (p.1-p.2)) (ℓ k p.1))
    hLift.convex
    (fun d _ => by
      change UpperSemicontinuousOn (dualPairKernel (ℓ k) xhat d) (liftedSupport Ξ)
      rw [dualPairKernel_shifted]
      exact (shifted_upperSemicontinuous (liftedSupport Ξ) (liftedLoss ℓ) hLift k
        (pairFunctional d) (xhat,xhat)).upperSemicontinuousOn (liftedSupport Ξ))
    (fun d _ => by
      change QuasiconcaveOn ℝ (liftedSupport Ξ) (dualPairKernel (ℓ k) xhat d)
      rw [dualPairKernel_shifted]
      exact shifted_quasiconcave (liftedSupport Ξ) (liftedLoss ℓ) hLift k (pairFunctional d) (xhat,xhat))
  have hp (p : E×E) : (⨅ d∈B, F d p)=ℓ k p.1-((lam*‖p.1-xhat‖+t*‖p.1-p.2‖ : ℝ) : EReal) :=
    dualPairKernel_pointwise_inf (ℓ k) xhat p lam t hlam ht
  have he : (⨆ p∈liftedSupport Ξ, ℓ k p.1-((lam*‖p.1-xhat‖+t*‖p.1-p.2‖ : ℝ) : EReal)) =
      ⨅ d∈B, ⨆ p∈liftedSupport Ξ, F d p := by
    simpa only [hp] using hsion.symm
  have hlow : LowerSemicontinuous (fun d => ⨆ p∈liftedSupport Ξ, F d p) :=
    lowerSemicontinuous_iSup (fun p => lowerSemicontinuous_iSup (fun _ =>
      (ereal_linear_continuous (dualPairEval (p.1-xhat) (p.1-p.2)) (ℓ k p.1)).lowerSemicontinuous))
  obtain ⟨d,hd,hmin⟩ := (hlow.lowerSemicontinuousOn B).exists_isMinOn hne hk
  have hv : (⨅ w∈B, ⨆ p∈liftedSupport Ξ, F w p)=⨆ p∈liftedSupport Ξ, F d p := by
    apply le_antisymm
    · exact iInf_le_of_le d (iInf_le_of_le hd le_rfl)
    · exact le_iInf₂ hmin
  have hsup : (⨆ p∈liftedSupport Ξ, F d p) ≤ (S : EReal) := by
    rw [←hv,←he]
    apply iSup_le
    intro p
    apply iSup_le
    intro hpΞ
    exact hupper p.1 p.2 hpΞ.2
  refine ⟨d,hd,?_⟩
  intro x y hy
  exact (le_iSup₂_of_le (x,y) ⟨Set.mem_univ _,hy⟩ le_rfl).trans hsup
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex

/-- A finite Cartesian family with a uniform sum bound has coordinatewise
finite upper bounds whose sum preserves that same bound. -/
theorem rectangular_scores_of_sum_bound {N : ℕ} (hN : 0 < N)
    (T : Fin N → Set ℝ) (hne : ∀ i, (T i).Nonempty) (B : ℝ)
    (hbound : ∀ r : Fin N → ℝ, (∀ i, r i∈T i) → (∑ i, r i) ≤ B) :
    ∃ s : Fin N → ℝ, (∀ i r, r∈T i → r ≤ s i) ∧ (∑ i, s i) ≤ B := by
  classical
  choose r0 hr0 using hne
  have hbdd : ∀ i, BddAbove (T i) := by
    intro i
    refine ⟨B-(∑ j ∈ Finset.univ.erase i, r0 j),?_⟩
    intro r hr
    have hu : ∀ j, Function.update r0 i r j ∈ T j := by
      intro j
      by_cases hji : j=i
      · subst j
        simpa using hr
      · simpa [Function.update_of_ne hji] using hr0 j
    have hh := hbound (Function.update r0 i r) hu
    rw [←Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hh
    have hs : (∑ j ∈ Finset.univ.erase i, Function.update r0 i r j) =
        ∑ j ∈ Finset.univ.erase i, r0 j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
    rw [Function.update_self,hs] at hh
    linarith
  let s : Fin N → ℝ := fun i => sSup (T i)
  refine ⟨s,fun i r hr => le_csSup (hbdd i) hr,?_⟩
  by_contra hh
  have hgap : 0 < (∑ i, s i)-B := sub_pos.mpr (lt_of_not_ge hh)
  let η := ((∑ i, s i)-B)/(2*(N : ℝ))
  have hη : 0 < η := by dsimp [η];exact div_pos hgap (by positivity)
  have happ : ∀ i, ∃ r∈T i, s i-η<r := by
    intro i
    exact exists_lt_of_lt_csSup ⟨r0 i,hr0 i⟩ (by dsimp [s];linarith)
  choose r hr hrap using happ
  have hsum : (∑ i, (s i-η)) ≤ ∑ i, r i := Finset.sum_le_sum (fun i _ => (hrap i).le)
  have hu := hbound r hr
  have hcalc : (∑ i, (s i-η)) = (∑ i, s i)-(N : ℝ)*η := by
    rw [Finset.sum_sub_distrib]
    simp
  have hηeq : (2*(N : ℝ))*η = (∑ i, s i)-B := by
    dsimp [η]
    field_simp
  rw [hcalc] at hsum
  nlinarith
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction

theorem conjugate_split_of_kernel_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (k : Fin K) (xhat : E) (d : StrongDual ℝ E × StrongDual ℝ E) (S : ℝ)
    (hbound : ∀ x y : E, y∈Ξ → dualPairKernel (ℓ k) xhat d (x,y) ≤ (S : EReal)) :
    conjOn Set.univ (fun x => -ℓ k x) (-d.1-d.2)+supportFun Ξ d.2-
      (((-d.1) xhat : ℝ) : EReal) ≤ (S : EReal) := by
  classical
  obtain ⟨x0,hx0,hbot0⟩ := hA.not_bot_on k
  let z := -d.1
  let T : Fin 2 → Set ℝ := fun i => if i=0 then
    {r | ∃ x : E, ℓ k x≠⊥ ∧ r=(ℓ k x).toReal+(z-d.2) x}
    else {r | ∃ y∈Ξ, r=d.2 y}
  have hne : ∀ i, (T i).Nonempty := by
    intro i
    fin_cases i
    · exact ⟨_,x0,hbot0,rfl⟩
    · exact ⟨_,x0,hx0,rfl⟩
  have hb : ∀ r : Fin 2 → ℝ, (∀ i, r i∈T i) → (∑ i, r i) ≤ S+z xhat := by
    intro r hr
    have h0 : ∃ x : E, ℓ k x≠⊥ ∧ r 0=(ℓ k x).toReal+(z-d.2) x := by simpa [T] using hr 0
    have h1 : ∃ y∈Ξ, r 1=d.2 y := by simpa [T] using hr 1
    obtain ⟨x,hbot,hv0⟩ := h0
    obtain ⟨y,hy,hv1⟩ := h1
    have hh := hbound x y hy
    change ℓ k x-((d.1 (x-xhat)+d.2 (x-y) : ℝ) : EReal) ≤ (S : EReal) at hh
    rw [←EReal.coe_toReal (hA.ne_top k x) hbot,←EReal.coe_sub] at hh
    have hhR := EReal.coe_le_coe_iff.mp hh
    rw [Fin.sum_univ_two,hv0,hv1]
    dsimp [z]
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply,map_sub] at hhR ⊢
    linarith
  obtain ⟨b,hbnd,hbsum⟩ := rectangular_scores_of_sum_bound (by decide : 0 < 2) T hne (S+z xhat) hb
  have hc : conjOn Set.univ (fun x => -ℓ k x) (z-d.2) ≤ (b 0 : EReal) := by
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    by_cases hbot : ℓ k x=⊥
    · simp [hbot]
    · have hmem : (ℓ k x).toReal+(z-d.2) x∈T 0 := ⟨x,hbot,rfl⟩
      have hh := EReal.coe_le_coe_iff.mpr (hbnd 0 _ hmem)
      rw [EReal.coe_add,EReal.coe_toReal (hA.ne_top k x) hbot] at hh
      simpa only [sub_eq_add_neg,neg_neg,add_comm] using hh
  have hs : supportFun Ξ d.2 ≤ (b 1 : EReal) := by
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    exact EReal.coe_le_coe_iff.mpr (hbnd 1 _ (show d.2 y∈T 1 from ⟨y,hy,rfl⟩))
  have hsum : b 0+b 1 ≤ S+z xhat := by simpa only [Fin.sum_univ_two] using hbsum
  have hh := EReal.sub_le_sub (add_le_add hc hs) (le_refl ((z xhat : ℝ) : EReal))
  rw [←EReal.coe_add,←EReal.coe_sub] at hh
  exact hh.trans (EReal.coe_le_coe_iff.mpr (by linarith))
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex

/-- A concave upper semicontinuous extended-real function bounded on a closed
convex set admits an arbitrarily small norm-slack spatial penalty. -/
theorem norm_slack_spatial_penalty {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] (Ξ : Set E) (hΞ : IsClosed Ξ) (hcv : Convex ℝ Ξ)
    (φ : E → EReal) (husc : UpperSemicontinuous φ)
    (hconc : ∀ x y : E, ∀ u v a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      (u : EReal) ≤ φ x → (v : EReal) ≤ φ y →
      ((a*u+b*v : ℝ) : EReal) ≤ φ (a • x+b • y))
    (x0 : E) (hx0 : x0∈Ξ) (r0 : ℝ) (hr0 : φ x0=(r0 : EReal))
    (C A s : ℝ) (hA : 0 ≤ A)
    (hupper : ∀ x, φ x ≤ ((C+A*‖x-x0‖ : ℝ) : EReal))
    (hs : ∀ x∈Ξ, φ x ≤ (s : EReal))
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ t : ℝ, 0 ≤ t ∧ ∀ x y : E, y∈Ξ →
      φ x-((η*‖x-x0‖+t*‖x-y‖ : ℝ) : EReal) ≤ ((s+δ : ℝ) : EReal) := by
  have hr0s : r0 ≤ s := EReal.coe_le_coe_iff.mp (by simpa only [hr0] using hs x0 hx0)
  let R : ℝ := 1+(s+δ-r0)/η
  have hR : 0 < R := by
    have hh : 0 < s+δ-r0 := by linarith
    dsimp [R]
    exact add_pos zero_lt_one (div_pos hh hη)
  have hηR : η*R=η+s+δ-r0 := by dsimp [R];field_simp;ring
  let K : Set E := Metric.closedBall x0 R ∩ {x | ((s+δ/2 : ℝ) : EReal) ≤ φ x}
  have hK : IsCompact K := (isCompact_closedBall x0 R).inter_right (husc.isClosed_preimage ((s+δ/2 : ℝ) : EReal))
  have hdisj : Disjoint K Ξ := Set.disjoint_left.mpr (by
    intro x hx hxΞ
    have hh := hx.2.trans (hs x hxΞ)
    have hhR := EReal.coe_le_coe_iff.mp hh
    linarith)
  obtain ⟨ρ,hρ,hsep⟩ := Metric.exists_pos_forall_lt_edist hK hΞ hdisj
  have hρR : 0 < (ρ : ℝ) := hρ
  have hsepR : ∀ x∈K, ∀ y∈Ξ, (ρ : ℝ) < ‖x-y‖ := by
    intro x hx y hy
    have hh := (ENNReal.toReal_lt_toReal (by finiteness) (edist_ne_top x y)).mpr (hsep x hx y hy)
    simpa only [ENNReal.coe_toReal,←dist_edist,dist_eq_norm] using hh
  let B : ℝ := |C-s|
  have hB : 0 ≤ B := abs_nonneg _
  let t : ℝ := 1+(B+A*R)/(ρ : ℝ)
  have ht : 0 < t := by dsimp [t];positivity
  have htρ : t*(ρ : ℝ)=B+A*R+(ρ : ℝ) := by dsimp [t];field_simp;ring
  refine ⟨t,ht.le,?_⟩
  intro x y hy
  cases hx : φ x using EReal.rec with
  | bot => simp
  | top =>
    have hh := hupper x
    rw [hx] at hh
    exact False.elim ((EReal.coe_ne_top _) (top_le_iff.mp hh))
  | coe u =>
    rw [←EReal.coe_sub]
    apply EReal.coe_le_coe_iff.mpr
    by_contra hviol
    have hu : u ≤ C+A*‖x-x0‖ := EReal.coe_le_coe_iff.mp (by simpa only [hx] using hupper x)
    have hxy : t*‖x-y‖ < B+A*‖x-x0‖ := by
      have hηx : 0 ≤ η*‖x-x0‖ := mul_nonneg hη.le (norm_nonneg _)
      have hCs : C-s ≤ B := le_abs_self _
      nlinarith
    by_cases hd : ‖x-x0‖ ≤ R
    · have hxK : x∈K := by
        refine ⟨?_,?_⟩
        · change dist x x0 ≤ R
          simpa only [dist_eq_norm] using hd
        · change ((s+δ/2 : ℝ) : EReal) ≤ φ x
          rw [hx]
          apply EReal.coe_le_coe_iff.mpr
          nlinarith [mul_nonneg hη.le (norm_nonneg (x-x0)),mul_nonneg ht.le (norm_nonneg (x-y))]
      have hsepX := mul_lt_mul_of_pos_left (hsepR x hxK y hy) ht
      have hAR := mul_le_mul_of_nonneg_left hd hA
      nlinarith
    · have hdR : R < ‖x-x0‖ := lt_of_not_ge hd
      have hd0 : 0 < ‖x-x0‖ := hR.trans hdR
      let τ : ℝ := R/‖x-x0‖
      have hτ : 0 < τ := div_pos hR hd0
      have hτ1 : τ ≤ 1 := (div_le_iff₀ hd0).mpr (by simpa using hdR.le)
      have hτd : τ*‖x-x0‖=R := by dsimp [τ];field_simp
      let w := (1-τ) • x0+τ • x
      let z := (1-τ) • x0+τ • y
      have hz : z∈Ξ := hcv hx0 hy (sub_nonneg.mpr hτ1) hτ.le (by ring)
      have hnormw : ‖w-x0‖=R := by
        have he : w-x0=τ • (x-x0) := by dsimp [w];module
        rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hτ,hτd]
      have hnormwz : ‖w-z‖=τ*‖x-y‖ := by
        have he : w-z=τ • (x-y) := by dsimp [w,z];module
        rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hτ]
      have hφw := hconc x0 x r0 u (1-τ) τ (sub_nonneg.mpr hτ1) hτ.le (by ring)
        (by rw [hr0]) (by rw [hx])
      have hheight : s+δ/2 ≤ (1-τ)*r0+τ*u := by
        have hηnorm : 0 ≤ t*‖x-y‖ := mul_nonneg ht.le (norm_nonneg _)
        have huL : s+δ+η*‖x-x0‖ ≤ u := by linarith
        have hmul := mul_le_mul_of_nonneg_left huL hτ.le
        have hpos := mul_nonneg hτ.le (show 0 ≤ s+δ-r0 by linarith)
        have hητ := congrArg (fun q : ℝ => η*q) hτd
        nlinarith
      have hwK : w∈K := by
        refine ⟨?_,(EReal.coe_le_coe_iff.mpr hheight).trans hφw⟩
        change dist w x0 ≤ R
        rw [dist_eq_norm,hnormw]
      have hsepW := mul_lt_mul_of_pos_left (hsepR w hwK z hz) ht
      rw [hnormwz] at hsepW
      have hcost := mul_lt_mul_of_pos_left hxy hτ
      have hτB := mul_le_mul_of_nonneg_right hτ1 hB
      have he : τ*(B+A*‖x-x0‖)=τ*B+A*R := by rw [←hτd];ring
      rw [he] at hcost
      nlinarith
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction

theorem penalized_finite_concavity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {K : ℕ} (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (k : Fin K) (xhat : E) (lam : ℝ) (hlam : 0 ≤ lam)
    (x y : E) (u v a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (hu : (u : EReal) ≤ ℓ k x-((lam*‖x-xhat‖ : ℝ) : EReal))
    (hv : (v : EReal) ≤ ℓ k y-((lam*‖y-xhat‖ : ℝ) : EReal)) :
    ((a*u+b*v : ℝ) : EReal) ≤ ℓ k (a • x+b • y)-((lam*‖a • x+b • y-xhat‖ : ℝ) : EReal) := by
  have hx : (x,-u-lam*‖x-xhat‖)∈{p : E×ℝ | -ℓ k p.1 ≤ (p.2 : EReal)} :=
    (finite_threshold_iff (ℓ k x) u (lam*‖x-xhat‖)).mpr hu
  have hy : (y,-v-lam*‖y-xhat‖)∈{p : E×ℝ | -ℓ k p.1 ≤ (p.2 : EReal)} :=
    (finite_threshold_iff (ℓ k y) v (lam*‖y-xhat‖)).mpr hv
  have hc := hA.convex_epigraph k hx hy ha hb hab
  change -ℓ k (a • x+b • y) ≤ ((a*(-u-lam*‖x-xhat‖)+b*(-v-lam*‖y-xhat‖) : ℝ) : EReal) at hc
  have he : a • (x-xhat)+b • (y-xhat)=a • x+b • y-xhat := by
    rw [smul_sub,smul_sub,sub_add_sub_comm,←add_smul,hab,one_smul]
  have hn : ‖a • x+b • y-xhat‖ ≤ a*‖x-xhat‖+b*‖y-xhat‖ := by
    rw [←he]
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb] using
      norm_add_le (a • (x-xhat)) (b • (y-xhat))
  apply (finite_threshold_iff (ℓ k (a • x+b • y)) (a*u+b*v) (lam*‖a • x+b • y-xhat‖)).mp
  apply hc.trans
  apply EReal.coe_le_coe_iff.mpr
  nlinarith [mul_le_mul_of_nonneg_left hn hlam]

theorem penalized_upperSemicontinuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {K : ℕ} (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (k : Fin K) (xhat : E) (lam : ℝ) :
    UpperSemicontinuous (fun x => ℓ k x-((lam*‖x-xhat‖ : ℝ) : EReal)) := by
  have hl : UpperSemicontinuous (ℓ k) := by
    simpa only [neg_neg] using ereal_neg_upper (fun x => -ℓ k x) (hA.lsc k)
  have hc : Continuous (fun x => ((-lam*‖x-xhat‖ : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp (continuous_const.mul (continuous_id.sub continuous_const).norm)
  have hh := hl.add' hc.upperSemicontinuous (fun x =>
    EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _)))
  convert hh using 1
  ext x
  simp only [sub_eq_add_neg,←EReal.coe_neg,neg_mul]
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex

theorem linear_upper_of_convex_epigraph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E → EReal)
    (hne_top : ∀ x, L x ≠ ⊤)
    (hconvex : Convex ℝ {p : E×ℝ | -L p.1 ≤ (p.2 : EReal)})
    (x0 : E) (a : ℝ) (ha : L x0=(a : EReal))
    (husc : UpperSemicontinuousAt L x0) :
    ∃ C A : ℝ, 0 ≤ A ∧ ∀ x, L x ≤ ((C+A*‖x-x0‖ : ℝ) : EReal) := by
  have hn : ∀ᶠ x in 𝓝 x0, L x < ((a+1 : ℝ) : EReal) := by
    apply husc
    rw [ha]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨δ,hδ,hlocal⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨a+1,2/δ,by positivity,?_⟩
  intro x
  cases hx : L x using EReal.rec with
  | bot => exact bot_le
  | top => exact False.elim (hne_top x hx)
  | coe b =>
    by_cases hd : ‖x-x0‖ < δ
    · have hb : b < a+1 := EReal.coe_lt_coe_iff.mp (by
        rw [←hx]
        exact hlocal (by simpa [dist_eq_norm] using hd))
      apply EReal.coe_le_coe_iff.mpr
      have hp : 0 ≤ (2/δ)*‖x-x0‖ := by positivity
      linarith
    · have hd0 : 0 < ‖x-x0‖ := lt_of_lt_of_le hδ (le_of_not_gt hd)
      let t : ℝ := δ/(2*‖x-x0‖)
      have ht : 0 < t := by dsimp [t];positivity
      have ht1 : t ≤ 1 := by
        dsimp [t]
        apply (div_le_iff₀ (by positivity)).mpr
        linarith [le_of_not_gt hd]
      have hp0 : (x0,-a) ∈ {p : E×ℝ | -L p.1 ≤ (p.2 : EReal)} := by
        change -L x0 ≤ ((-a : ℝ) : EReal)
        simp [ha, EReal.coe_neg]
      have hpx : (x,-b) ∈ {p : E×ℝ | -L p.1 ≤ (p.2 : EReal)} := by
        change -L x ≤ ((-b : ℝ) : EReal)
        simp [hx, EReal.coe_neg]
      have hc := hconvex hp0 hpx (sub_nonneg.mpr ht1) ht.le (by ring : (1-t)+t=1)
      change -L ((1-t) • x0+t • x) ≤ (((1-t)*(-a)+t*(-b) : ℝ) : EReal) at hc
      have hvec : (1-t) • x0+t • x-x0 = t • (x-x0) := by module
      have hnorm : ‖(1-t) • x0+t • x-x0‖ = δ/2 := by
        rw [hvec,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
        dsimp [t]
        field_simp
      have hu := (hlocal (y:=(1-t) • x0+t • x) (by
        rw [dist_eq_norm,hnorm];linarith)).le
      have hlow : (((1-t)*a+t*b : ℝ) : EReal) ≤ L ((1-t) • x0+t • x) := by
        have hc' : -L ((1-t) • x0+t • x) ≤ -(((1-t)*a+t*b : ℝ) : EReal) := by
          convert hc using 1 <;> simp only [←EReal.coe_neg] <;> congr 1 <;> ring
        exact EReal.neg_le_neg_iff.mp hc'
      have hb : (1-t)*a+t*b ≤ a+1 := by
        have hh := hlow.trans hu
        exact EReal.coe_le_coe_iff.mp hh
      have htd : t*((2/δ)*‖x-x0‖)=1 := by dsimp [t];field_simp <;> ring
      apply EReal.coe_le_coe_iff.mpr
      have hbx : b ≤ a+(2/δ)*‖x-x0‖ := by nlinarith
      linarith
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction

theorem spatial_penalty_at_anchor {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (k : Fin K) (xhat : E) (lam s : ℝ) (hlam : 0 ≤ lam)
    (hs : ∀ x∈Ξ, ℓ k x-((lam*‖x-xhat‖ : ℝ) : EReal) ≤ (s : EReal))
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ)
    (x0 : E) (hx0 : x0∈Ξ) (hbot : ℓ k x0≠⊥) :
    ∃ t : ℝ, 0 ≤ t ∧ ∀ x y : E, y∈Ξ →
      ℓ k x-(((lam+η)*‖x-xhat‖+t*‖x-y‖ : ℝ) : EReal) ≤
        ((s+δ+η*‖xhat-x0‖ : ℝ) : EReal) := by
  have hfinite := EReal.coe_toReal (hA.ne_top k x0) hbot
  have husc : UpperSemicontinuous (ℓ k) := by
    simpa only [neg_neg] using ereal_neg_upper (fun x => -ℓ k x) (hA.lsc k)
  obtain ⟨C,A,hA0,hupper⟩ := linear_upper_of_convex_epigraph (ℓ k) (hA.ne_top k)
    (hA.convex_epigraph k) x0 (ℓ k x0).toReal hfinite.symm (husc x0)
  let φ : E → EReal := fun x => ℓ k x-((lam*‖x-xhat‖ : ℝ) : EReal)
  let r0 : ℝ := (ℓ k x0).toReal-lam*‖x0-xhat‖
  have hr0 : φ x0=(r0 : EReal) := by
    change ℓ k x0-((lam*‖x0-xhat‖ : ℝ) : EReal) = (((ℓ k x0).toReal-lam*‖x0-xhat‖ : ℝ) : EReal)
    rw [EReal.coe_sub,hfinite]
  have hφupper : ∀ x, φ x ≤ ((C+A*‖x-x0‖ : ℝ) : EReal) := by
    intro x
    have hh := EReal.sub_le_sub (le_refl (ℓ k x))
      (EReal.coe_nonneg.mpr (mul_nonneg hlam (norm_nonneg (x-xhat))))
    have hle : φ x ≤ ℓ k x := by
      change ℓ k x-((lam*‖x-xhat‖ : ℝ) : EReal) ≤ ℓ k x
      simpa only [sub_zero] using hh
    exact hle.trans (hupper x)
  obtain ⟨t,ht,hpen⟩ := norm_slack_spatial_penalty Ξ hA.closed hA.convex φ
    (penalized_upperSemicontinuous Ξ ℓ hA k xhat lam)
    (fun x y u v a b ha hb hab hu hv => penalized_finite_concavity Ξ ℓ hA k xhat lam hlam x y u v a b ha hb hab hu hv)
    x0 hx0 r0 hr0 C A s hA0 hφupper hs η δ hη hδ
  refine ⟨t,ht,?_⟩
  intro x y hy
  have hh := hpen x y hy
  cases hx : ℓ k x using EReal.rec with
  | bot => simp
  | top => exact False.elim (hA.ne_top k x hx)
  | coe u =>
    change (ℓ k x-((lam*‖x-xhat‖ : ℝ) : EReal))-((η*‖x-x0‖+t*‖x-y‖ : ℝ) : EReal) ≤ ((s+δ : ℝ) : EReal) at hh
    rw [hx,←EReal.coe_sub,←EReal.coe_sub] at hh
    have hr := EReal.coe_le_coe_iff.mp hh
    rw [←EReal.coe_sub]
    apply EReal.coe_le_coe_iff.mpr
    have hd := norm_sub_le_norm_sub_add_norm_sub x xhat x0
    nlinarith [mul_le_mul_of_nonneg_left hd hη.le]
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction

theorem approximate_split_at_anchor {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (k : Fin K) (xhat : E) (lam s : ℝ) (hlam : 0 ≤ lam)
    (hs : ∀ x∈Ξ, ℓ k x-((lam*‖x-xhat‖ : ℝ) : EReal) ≤ (s : EReal))
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) (x0 : E) (hx0 : x0∈Ξ) (hbot : ℓ k x0≠⊥) :
    ∃ z ν : StrongDual ℝ E, ‖z‖ ≤ lam+η ∧
      conjOn Set.univ (fun x => -ℓ k x) (z-ν)+supportFun Ξ ν-((z xhat : ℝ) : EReal) ≤
        ((s+δ+η*‖xhat-x0‖ : ℝ) : EReal) := by
  obtain ⟨t,ht,hpen⟩ := spatial_penalty_at_anchor Ξ ℓ hA k xhat lam s hlam hs η δ hη hδ x0 hx0 hbot
  obtain ⟨d,hd,hkernel⟩ := dualPair_minimax_upper Ξ ℓ hA k xhat (lam+η) t
    (add_nonneg hlam hη.le) ht (s+δ+η*‖xhat-x0‖) hpen
  refine ⟨-d.1,d.2,?_,?_⟩
  · simpa only [norm_neg] using hd.1
  · exact conjugate_split_of_kernel_bound Ξ ℓ hA k xhat d (s+δ+η*‖xhat-x0‖) hkernel
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem iSup_sub_real {α : Sort*} (f : α → EReal) (c : ℝ) :
    (⨆ i, f i)-(c : EReal) = ⨆ i, f i-(c : EReal) := by
  have hs {a b : EReal} : a-(c : EReal)≤b ↔ a≤b+(c : EReal) :=
    EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot c)) (.inl (EReal.coe_ne_top c))
  apply le_antisymm
  · apply hs.mpr
    apply iSup_le
    intro i
    exact hs.mp (le_iSup (fun i => f i-(c : EReal)) i)
  · apply iSup_le
    intro i
    exact EReal.sub_le_sub (le_iSup f i) le_rfl
 theorem conjugate_neg_sign {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (Ξ : Set E) (ℓ : E → EReal) (z : StrongDual ℝ E) (xhat : E) :
    conjOn Ξ (fun ξ => -ℓ ξ) (-z) - (((-z) xhat : ℝ) : EReal) =
      ⨆ ξ ∈ Ξ, ℓ ξ-((z (ξ-xhat) : ℝ) : EReal) := by
  rw [conjOn,iSup_sub_real]
  congr 1
  funext ξ
  rw [iSup_sub_real]
  congr 1
  funext hξ
  cases h : ℓ ξ using EReal.rec <;>
    simp only [neg_apply, map_sub, EReal.neg_bot, EReal.neg_top,
      EReal.sub_top, EReal.sub_bot (EReal.coe_ne_bot _), EReal.top_sub (EReal.coe_ne_top _), EReal.bot_sub,
      ← EReal.coe_neg, ← EReal.coe_sub]
  congr 1
  ring
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem envelope_to_conjugate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] {K N : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (lam : ℝ) (hlam : 0≤lam) (s : Fin N → ℝ)
    (h : ∀ i, (⨆ ξ ∈ Ξ, maxLoss ℓ ξ-((lam*‖ξ-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal)) :
    ∃ z : Fin N → Fin K → StrongDual ℝ E,
      (∀ i k, conjOn Ξ (fun ξ => -ℓ k ξ) (z i k)-((z i k (ξhat i) : ℝ) : EReal) ≤ (s i : EReal)) ∧
      ∀ i k, ‖z i k‖≤lam := by
  classical
  choose z hz he using (fun (i : Fin N) (k : Fin K) => (minimax_dual_ball Ξ ℓ hA k (ξhat i) lam hlam).2)
  refine ⟨fun i k => -z i k, ?_, ?_⟩
  · intro i k
    rw [conjugate_neg_sign,he i k]
    apply iSup_le
    intro ξ
    apply iSup_le
    intro hξ
    have hp : ℓ k ξ ≤ maxLoss ℓ ξ := le_iSup (fun j => ℓ j ξ) k
    exact le_trans (EReal.sub_le_sub hp le_rfl)
      (le_trans (le_iSup₂_of_le ξ hξ le_rfl) (h i))
  · intro i k
    simpa only [norm_neg] using hz i k
 theorem conjugate_to_envelope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {K N : ℕ} (hK : 0<K) (hN : 0<N)
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (ξhat : Fin N → E) (lam : ℝ) (s : Fin N → ℝ)
    (z : Fin N → Fin K → StrongDual ℝ E)
    (hc : ∀ i k, conjOn Ξ (fun ξ => -ℓ k ξ) (z i k)-((z i k (ξhat i) : ℝ) : EReal) ≤ (s i : EReal))
    (hn : ∀ i k, ‖z i k‖≤lam) :
    0≤lam ∧ ∀ i, (⨆ ξ ∈ Ξ, maxLoss ℓ ξ-((lam*‖ξ-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal) := by
  have hlam : 0≤lam := le_trans (norm_nonneg (z ⟨0,hN⟩ ⟨0,hK⟩)) (hn _ _)
  refine ⟨hlam, ?_⟩
  intro i
  apply iSup_le
  intro ξ
  apply iSup_le
  intro hξ
  rw [maxLoss,iSup_sub_real]
  apply iSup_le
  intro k
  have hb : ‖-z i k‖≤lam := by simpa only [norm_neg] using hn i k
  have hp := (pointwise_dual_ball (ξ-ξhat i) lam hlam (ℓ k ξ)).1
  rw [hp]
  apply le_trans (iInf_le_of_le (-z i k) (iInf_le_of_le hb le_rfl))
  have he := conjugate_neg_sign Ξ (ℓ k) (-z i k) (ξhat i)
  simp only [neg_neg] at he
  have hci := hc i k
  rw [he] at hci
  exact le_trans (le_iSup₂_of_le ξ hξ le_rfl) hci
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem program12c_eq_program12f {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] {K N : ℕ} (hK : 0<K) (hN : 0<N)
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (ε : ℝ) :
    program12cValue ε Ξ ξhat (maxLoss ℓ)=program12fValue ε Ξ ξhat ℓ := by
  unfold program12cValue program12fValue
  apply le_antisymm
  · apply le_iInf
    intro lam
    apply le_iInf
    intro s
    apply le_iInf
    intro z
    apply le_iInf
    intro hc
    apply le_iInf
    intro hn
    obtain ⟨hlam,he⟩ := conjugate_to_envelope hK hN Ξ ℓ ξhat lam s z hc hn
    exact iInf_le_of_le lam (iInf_le_of_le s (iInf_le_of_le he (iInf_le_of_le hlam le_rfl)))
  · apply le_iInf
    intro lam
    apply le_iInf
    intro s
    apply le_iInf
    intro he
    apply le_iInf
    intro hlam
    obtain ⟨z,hc,hn⟩ := envelope_to_conjugate Ξ ℓ hA ξhat lam hlam s he
    exact iInf_le_of_le lam (iInf_le_of_le s (iInf_le_of_le z
      (iInf_le_of_le hc (iInf_le_of_le hn le_rfl))))
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction

theorem conjOn_le_conj_add_support {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E]
    (Ξ : Set E) (L : E → EReal) (z ν : StrongDual ℝ E) :
    conjOn Ξ (fun x => -L x) z ≤
      conjOn Set.univ (fun x => -L x) (z-ν)+supportFun Ξ ν := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  have hl : (((z-ν) x : ℝ) : EReal)-(-L x) ≤ conjOn Set.univ (fun x => -L x) (z-ν) :=
    le_iSup₂_of_le x (Set.mem_univ x) le_rfl
  have hs : ((ν x : ℝ) : EReal) ≤ supportFun Ξ ν := le_iSup₂_of_le x hx le_rfl
  have hu := add_le_add hl hs
  have he : (((z-ν) x : ℝ) : EReal)-(-L x)+((ν x : ℝ) : EReal) =
      ((z x : ℝ) : EReal)-(-L x) := by
    rw [ContinuousLinearMap.sub_apply]
    simp only [sub_eq_add_neg,neg_neg]
    rw [add_right_comm,←EReal.coe_add]
    have hn : z x + -ν x + ν x = z x := by ring
    rw [hn]
  rwa [he] at hu

theorem program12f_le_program11 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K N : ℕ}
    (ε : ℝ) (Ξ : Set E) (ξhat : Fin N → E) (ℓ : Fin K → E → EReal) :
    program12fValue ε Ξ ξhat ℓ ≤ program11Value ε Ξ ξhat ℓ := by
  unfold program11Value
  apply le_iInf
  intro lam
  apply le_iInf
  intro s
  apply le_iInf
  intro z
  apply le_iInf
  intro ν
  apply le_iInf
  intro hc
  apply le_iInf
  intro hn
  have hf : ∀ i k, conjOn Ξ (fun x => -ℓ k x) (z i k)-((z i k (ξhat i) : ℝ) : EReal) ≤ (s i : EReal) := by
    intro i k
    exact (EReal.sub_le_sub (conjOn_le_conj_add_support Ξ (ℓ k) (z i k) (ν i k)) le_rfl).trans (hc i k)
  unfold program12fValue
  exact iInf_le_of_le lam (iInf_le_of_le s (iInf_le_of_le z
    (iInf_le_of_le hf (iInf_le_of_le hn le_rfl))))
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex
open WassDDRO.Reduction

theorem program11_le_epigraph_objective {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] {K N : ℕ}
    (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (ε lam : ℝ) (s : Fin N → ℝ) (hlam : 0 ≤ lam)
    (he : ∀ i, (⨆ x∈Ξ, maxLoss ℓ x-((lam*‖x-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal)) :
    program11Value ε Ξ ξhat ℓ ≤ ((lam*ε+(1/(N : ℝ))*(∑ i, s i) : ℝ) : EReal) := by
  classical
  have ha : ∀ k, ∃ x∈Ξ, ℓ k x≠⊥ := hA.not_bot_on
  choose a haΞ habot using ha
  let B : ℝ := ∑ i, ∑ k, ‖ξhat i-a k‖
  have hB : ∀ i k, ‖ξhat i-a k‖ ≤ B := by
    intro i k
    apply le_trans (Finset.single_le_sum (fun j _ => norm_nonneg (ξhat i-a j)) (Finset.mem_univ k))
    exact Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun k _ => norm_nonneg (ξhat j-a k))) (Finset.mem_univ i)
  let obj : ℝ := lam*ε+(1/(N : ℝ))*(∑ i, s i)
  have hb (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
      program11Value ε Ξ ξhat ℓ ≤ ((obj+η*ε+δ+η*B : ℝ) : EReal) := by
    have hp : ∀ i k, ∃ z ν : StrongDual ℝ E, ‖z‖ ≤ lam+η ∧
        conjOn Set.univ (fun x => -ℓ k x) (z-ν)+supportFun Ξ ν-((z (ξhat i) : ℝ) : EReal) ≤
          ((s i+δ+η*‖ξhat i-a k‖ : ℝ) : EReal) := by
      intro i k
      apply approximate_split_at_anchor Ξ ℓ hA k (ξhat i) lam (s i) hlam _ η δ hη hδ (a k) (haΞ k) (habot k)
      intro x hx
      have hmax : maxLoss ℓ x-((lam*‖x-ξhat i‖ : ℝ) : EReal) ≤ (s i : EReal) :=
        (le_iSup₂_of_le x hx le_rfl).trans (he i)
      exact (EReal.sub_le_sub (le_iSup (fun k => ℓ k x) k) le_rfl).trans hmax
    choose z ν hz hconj using hp
    let R : Fin N → ℝ := fun i => s i+δ+η*B
    have hc : ∀ i k, conjOn Set.univ (fun x => -ℓ k x) (z i k-ν i k)+supportFun Ξ (ν i k)-
        ((z i k (ξhat i) : ℝ) : EReal) ≤ (R i : EReal) := by
      intro i k
      apply (hconj i k).trans
      apply EReal.coe_le_coe_iff.mpr
      exact add_le_add (le_refl (s i+δ)) (mul_le_mul_of_nonneg_left (hB i k) hη.le)
    have hn : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
    have hsum : (∑ i, R i)=(∑ i, s i)+(N : ℝ)*(δ+η*B) := by
      dsimp [R]
      simp_rw [add_assoc]
      rw [Finset.sum_add_distrib]
      simp
      ring
    have hobj : (lam+η)*ε+(1/(N : ℝ))*(∑ i, R i)=obj+η*ε+δ+η*B := by
      rw [hsum]
      dsimp [obj]
      field_simp [hn]
      ring
    have hprog : program11Value ε Ξ ξhat ℓ ≤ (((lam+η)*ε+(1/(N : ℝ))*(∑ i, R i) : ℝ) : EReal) := by
      unfold program11Value
      exact iInf_le_of_le (lam+η) (iInf_le_of_le R (iInf_le_of_le z
        (iInf_le_of_le ν (iInf_le_of_le hc (iInf_le_of_le hz le_rfl)))))
    rwa [hobj] at hprog
  have hη : Tendsto (fun n : ℕ => (1 : ℝ)/(n+1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hreal : Tendsto (fun n : ℕ => obj+((1 : ℝ)/(n+1))*ε+(1 : ℝ)/(n+1)+((1 : ℝ)/(n+1))*B)
      atTop (𝓝 obj) := by
    simpa using ((tendsto_const_nhds.add (hη.mul_const ε)).add hη).add (hη.mul_const B)
  have ht := (continuous_coe_real_ereal.tendsto obj).comp hreal
  exact isClosed_Ici.mem_of_tendsto ht (Eventually.of_forall fun n =>
    hb ((1 : ℝ)/(n+1)) ((1 : ℝ)/(n+1)) (by positivity) (by positivity))

theorem program11_le_program12c {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] {K N : ℕ}
    (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (ε : ℝ) :
    program11Value ε Ξ ξhat ℓ ≤ program12cValue ε Ξ ξhat (maxLoss ℓ) := by
  unfold program12cValue
  apply le_iInf
  intro lam
  apply le_iInf
  intro s
  apply le_iInf
  intro he
  apply le_iInf
  intro hlam
  exact program11_le_epigraph_objective hN Ξ ℓ hA ξhat ε lam s hlam he

theorem program12f_eq_program11_full {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] {K N : ℕ}
    (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (ε : ℝ) : program12fValue ε Ξ ξhat ℓ=program11Value ε Ξ ξhat ℓ := by
  have hh := program11_le_program12c hN Ξ ℓ hA ξhat ε
  rw [program12c_eq_program12f hK hN Ξ ℓ hA ξhat ε] at hh
  exact le_antisymm (program12f_le_program11 ε Ξ ξhat ℓ) hh
end WassReductionCodex

end

set_option autoImplicit false
open WassDDRO.Reduction
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (ε : ℝ) (hε : 0 ≤ ε) (hA : Assumption41 Ξ ℓ) :
    program12fValue ε Ξ ξhat ℓ = program11Value ε Ξ ξhat ℓ := by
  exact WassReductionCodex.program12f_eq_program11_full hK hN Ξ ℓ hA ξhat ε



#print axioms solution
