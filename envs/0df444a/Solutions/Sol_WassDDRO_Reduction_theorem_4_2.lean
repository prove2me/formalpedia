-- Prove2me | solution 1 for WassDDRO.Reduction.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T10:23:54.531226+00:00
-- url     : https://prove2.me/submissions/6e4986f7-2b7e-4a8d-97e1-f19f9c2537ac

import Definitions.Def_WassDDRO_Reduction_Setting
import Mathlib
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

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open DupacovaWets.Consistency

lemma expect_mono {Z : Type*} [MeasurableSpace Z] (Q : Measure Z)
    (f g : Z → EReal) (hfg : f ≤ᵐ[Q] g) :
    expect Q f ≤ expect Q g := by
  have hpos : (∫⁻ z, (f z).toENNReal ∂Q) ≤ ∫⁻ z, (g z).toENNReal ∂Q :=
    lintegral_mono_ae (hfg.mono fun z hz => EReal.toENNReal_le_toENNReal hz)
  have hneg : (∫⁻ z, (-g z).toENNReal ∂Q) ≤ ∫⁻ z, (-f z).toENNReal ∂Q :=
    lintegral_mono_ae (hfg.mono fun z hz => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr hz))
  unfold expect
  by_cases hgtop : (∫⁻ z, (g z).toENNReal ∂Q) = ⊤
  · rw [if_pos hgtop]
    exact le_top
  · have hftop : (∫⁻ z, (f z).toENNReal ∂Q) ≠ ⊤ :=
      (lt_of_le_of_lt hpos (lt_top_iff_ne_top.mpr hgtop)).ne
    rw [if_neg hgtop, if_neg hftop]
    exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hpos)
      (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hneg)

end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open DupacovaWets.Consistency
lemma expect_eq_integral {E : Type*} [MeasurableSpace E]
    (Q : Measure E) (l : E → ℝ) (hl : Integrable l Q) :
    expect Q (fun x => (l x : EReal)) = (∫ x, l x ∂Q : ℝ) := by
  have hp : (∫⁻ x, ENNReal.ofReal (l x) ∂Q) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm l).trans_lt hl.2).ne
  have hn : (∫⁻ x, ENNReal.ofReal (-l x) ∂Q) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm (fun x => -l x)).trans_lt hl.neg.2).ne
  unfold expect
  rw [if_neg (show (∫⁻ x, ((l x : EReal)).toENNReal ∂Q) ≠ ⊤ from hp)]
  simp only [EReal.real_coe_toENNReal, ← EReal.coe_neg]
  rw [ ← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn,
    ← EReal.coe_sub, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hl]


end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open DupacovaWets.Consistency
 theorem expect_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Q : Measure α) (g : α → β) (f : β → EReal) (hg : Measurable g) (hf : Measurable f) :
    expect (Q.map g) f=expect Q (fun x => f (g x)) := by
  have hp : (∫⁻ y, (f y).toENNReal ∂Q.map g) = ∫⁻ x, (f (g x)).toENNReal ∂Q :=
    lintegral_map (by fun_prop) hg
  have hn : (∫⁻ y, (-f y).toENNReal ∂Q.map g) = ∫⁻ x, (-f (g x)).toENNReal ∂Q :=
    lintegral_map (by fun_prop) hg
  unfold expect
  rw [hp,hn]
 theorem expect_le_integrable_upper {α : Type*} [MeasurableSpace α]
    (Q : Measure α) (f : α → EReal) (g : α → ℝ) (hg : Integrable g Q)
    (hfg : f ≤ᵐ[Q] fun x => (g x : EReal)) :
    expect Q f ≤ ((∫ x, g x ∂Q : ℝ) : EReal) := by
  rw [← expect_eq_integral Q g hg]
  exact expect_mono Q f _ hfg
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassersteinDRO.Duality
 theorem wasserstein_one_eq {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (Q P : Measure E) : wassersteinDistance 1 Q P =
      ⨅ (π : Measure (E×E)) (_ : π.map Prod.fst=Q ∧ π.map Prod.snd=P),
        ∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π := by simp [wassersteinDistance]
 theorem exists_coupling_lt_budget_add {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (Q P : Measure E) (ε η : ℝ) (hε : 0≤ε) (hη : 0<η)
    (hbudget : wassersteinDistance 1 Q P≤ENNReal.ofReal ε) :
    ∃ π : Measure (E×E), (π.map Prod.fst=Q ∧ π.map Prod.snd=P) ∧
      (∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π)<ENNReal.ofReal (ε+η) := by
  have hlt : wassersteinDistance 1 Q P<ENNReal.ofReal (ε+η) :=
    lt_of_le_of_lt hbudget ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε).mpr (by linarith))
  rw [wasserstein_one_eq,iInf_lt_iff] at hlt
  obtain ⟨π,hπ⟩ := hlt
  rw [iInf_lt_iff] at hπ
  obtain ⟨hm,hc⟩ := hπ
  exact ⟨π,hm,hc⟩
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex

lemma finite_probability_mixture {Z : Type*} [MeasurableSpace Z]
    (π ρ : Measure Z) (hπ : IsProbabilityMeasure π) (hρ : IsProbabilityMeasure ρ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    IsProbabilityMeasure (ENNReal.ofReal a • π+ENNReal.ofReal b • ρ) := by
  letI := hπ
  letI := hρ
  constructor
  simp only [Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_add ha hb,hab]
  norm_num

lemma finite_mixture_second_marginal {E : Type*} [MeasurableSpace E]
    (π ρ : Measure (E×E)) (P : Measure E) (hπ : π.map Prod.snd=P)
    (hρ : ρ.map Prod.snd=P) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    (ENNReal.ofReal a • π+ENNReal.ofReal b • ρ).map Prod.snd=P := by
  rw [Measure.map_add _ _ measurable_snd,Measure.map_smul,Measure.map_smul,
    hπ,hρ,←add_smul,←ENNReal.ofReal_add ha hb,hab]
  simp

lemma finite_mixture_integral {Z : Type*} [MeasurableSpace Z]
    (π ρ : Measure Z) (f : Z → ℝ) (hπ : Integrable f π) (hρ : Integrable f ρ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ z, f z ∂(ENNReal.ofReal a • π+ENNReal.ofReal b • ρ)) =
      a*(∫ z, f z ∂π)+b*(∫ z, f z ∂ρ) := by
  rw [integral_add_measure (hπ.smul_measure ENNReal.ofReal_ne_top)
    (hρ.smul_measure ENNReal.ofReal_ne_top),integral_smul_measure,integral_smul_measure]
  simp only [ENNReal.toReal_ofReal ha,ENNReal.toReal_ofReal hb,smul_eq_mul]

/-- Cost/reward pairs from couplings on the finite-loss domain; no condition is
imposed on loss values outside the coupling's almost-everywhere support. -/
def finiteCouplingValues {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (Ξ : Set E) (P : Measure E) (L : E → EReal) : Set (ℝ×ℝ) :=
  {v | ∃ π : Measure (E×E), IsProbabilityMeasure π ∧ π.map Prod.snd=P ∧
    (∀ᵐ w ∂π, w.1∈Ξ ∧ L w.1≠⊤ ∧ L w.1≠⊥) ∧
    Integrable (fun w : E×E => ‖w.1-w.2‖) π ∧
    Integrable (fun w : E×E => (L w.1).toReal) π ∧
    v=((∫ w, ‖w.1-w.2‖ ∂π),(∫ w, (L w.1).toReal ∂π))}

theorem finiteCouplingValues_convex {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (Ξ : Set E) (P : Measure E) (L : E → EReal) : Convex ℝ (finiteCouplingValues Ξ P L) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨π,hπ,hπP,hπae,hπc,hπL,rfl⟩ := hx
  obtain ⟨ρ,hρ,hρP,hρae,hρc,hρL,rfl⟩ := hy
  refine ⟨ENNReal.ofReal a • π+ENNReal.ofReal b • ρ,
    finite_probability_mixture π ρ hπ hρ a b ha hb hab,
    finite_mixture_second_marginal π ρ P hπP hρP a b ha hb hab,
    ae_add_measure_iff.mpr ⟨Measure.ae_smul_measure hπae _,Measure.ae_smul_measure hρae _⟩,
    (hπc.smul_measure ENNReal.ofReal_ne_top).add_measure (hρc.smul_measure ENNReal.ofReal_ne_top),
    (hπL.smul_measure ENNReal.ofReal_ne_top).add_measure (hρL.smul_measure ENNReal.ofReal_ne_top),?_⟩
  rw [finite_mixture_integral π ρ _ hπc hρc a b ha hb,
    finite_mixture_integral π ρ _ hπL hρL a b ha hb]
  rfl

theorem finiteCouplingValues_cost_nonneg {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (Ξ : Set E) (P : Measure E) (L : E → EReal) (v : ℝ×ℝ)
    (hv : v∈finiteCouplingValues Ξ P L) : 0 ≤ v.1 := by
  obtain ⟨π,_,_,_,_,_,rfl⟩ := hv
  exact integral_nonneg (fun w => norm_nonneg _)
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction WassersteinDRO.Duality DupacovaWets.Consistency

theorem expect_eq_integral_toReal_of_finite_ae {Z : Type*} [MeasurableSpace Z]
    (π : Measure Z) (L : Z → EReal) (hi : Integrable (fun z => (L z).toReal) π)
    (hf : ∀ᵐ z ∂π, L z≠⊤ ∧ L z≠⊥) :
    expect π L = ((∫ z, (L z).toReal ∂π : ℝ) : EReal) := by
  have hae : L =ᵐ[π] (fun z => ((L z).toReal : EReal)) :=
    hf.mono (fun z hz => (EReal.coe_toReal hz.1 hz.2).symm)
  have he : expect π L=expect π (fun z => ((L z).toReal : EReal)) := by
    apply le_antisymm
    · exact expect_mono π _ _ (hae.mono fun z hz => hz.le)
    · exact expect_mono π _ _ (hae.mono fun z hz => hz.ge)
  rw [he,expect_eq_integral π _ hi]

theorem finite_coupling_project_budget {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (P : Measure E) (L : E → EReal)
    (hL : Measurable L) (v : ℝ×ℝ) (hv : v∈finiteCouplingValues Ξ P L)
    (ε : ℝ) (hvε : v.1 ≤ ε) :
    ∃ Q : Measure E, Q∈ambiguitySet ε 1 Ξ P ∧ expect Q L=(v.2 : EReal) := by
  obtain ⟨π,hπ,hπP,hπae,hπc,hπL,rfl⟩ := hv
  letI := hπ
  let Q : Measure E := π.map Prod.fst
  have hQ : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI := hQ
  have hs : Q Ξᶜ=0 := by
    change (π.map Prod.fst) Ξᶜ=0
    rw [Measure.map_apply measurable_fst hΞ.compl]
    have hax : ∀ᵐ w ∂π, w.1∈Ξ := hπae.mono (fun w hw => hw.1)
    rw [ae_iff] at hax
    exact hax
  have hc : wassersteinDistance 1 Q P ≤ ENNReal.ofReal ε := by
    rw [wasserstein_one_eq]
    apply le_trans (iInf_le _ π)
    apply le_trans (iInf_le _ ⟨rfl,hπP⟩)
    rw [←ofReal_integral_eq_lintegral_ofReal hπc (Filter.Eventually.of_forall fun w => norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hvε
  refine ⟨Q,⟨measure_univ,hs,hc⟩,?_⟩
  have he := expect_map π Prod.fst L measurable_fst hL
  rw [he]
  exact expect_eq_integral_toReal_of_finite_ae π (fun w => L w.1) hπL
    (hπae.mono (fun w hw => hw.2))

theorem finiteCouplingValues_le_worstCase {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {N : ℕ} (Ξ : Set E) (hΞ : MeasurableSet Ξ) (L : E → EReal) (hL : Measurable L)
    (ξhat : Fin N → E) (v : ℝ×ℝ)
    (hv : v∈finiteCouplingValues Ξ (empiricalDistribution ξhat) L)
    (ε : ℝ) (hvε : v.1 ≤ ε) : (v.2 : EReal) ≤ worstCaseExpectation ε Ξ ξhat L := by
  obtain ⟨Q,hQ,he⟩ := finite_coupling_project_budget Ξ hΞ (empiricalDistribution ξhat) L hL v hv ε hvε
  rw [←he]
  exact le_iSup₂_of_le Q hQ le_rfl
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
theorem finite_supporting_multiplier (C : Set (ℝ × ℝ)) (hC : Convex ℝ C)
    (δ V c0 L : ℝ) (hδ : c0 < δ) (hbase : (c0, L) ∈ C)
    (hbudget : ∀ z ∈ C, z.1 < δ → z.2 ≤ V) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ z ∈ C, z.2 ≤ V + γ * (z.1 - δ) := by
  let D : Set (ℝ × ℝ) := Set.Iio δ ×ˢ Set.Ioi V
  have hDconv : Convex ℝ D := (convex_Iio δ).prod (convex_Ioi V)
  have hDopen : IsOpen D := isOpen_Iio.prod isOpen_Ioi
  have hdisj : Disjoint D C := Set.disjoint_left.mpr (by
    intro z hzD hzC
    exact not_lt_of_ge (hbudget z hzC hzD.1) hzD.2)
  obtain ⟨f, k, hD, hCbound⟩ := geometric_hahn_banach_open hDconv hDopen hC hdisj
  let a := f (1, 0)
  let b := f (0, 1)
  have hf (x y : ℝ) : f (x, y) = a * x + b * y := by
    have he : (x, y) = x • (1, 0) + y • (0, 1) := by ext <;> simp
    rw [he, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    dsimp [a, b]
    ring
  have ha : 0 ≤ a := by
    by_contra ha
    have han : 0 < -a := neg_pos.mpr (lt_of_not_ge ha)
    let t := (|k - (a * δ + b * (V + 1))| + 1) / (-a)
    have ht : 0 < t := div_pos (by positivity) han
    have hm : (-a) * t = |k - (a * δ + b * (V + 1))| + 1 := by
      dsimp [t]
      exact mul_div_cancel₀ _ han.ne'
    have hd := hD (δ - t, V + 1) (show (δ - t, V + 1) ∈ D from ⟨by change δ - t < δ; linarith, by change V < V + 1; linarith⟩)
    rw [hf] at hd
    nlinarith [le_abs_self (k - (a * δ + b * (V + 1)))]
  have hb : b ≤ 0 := by
    by_contra hb
    have hbp : 0 < b := lt_of_not_ge hb
    let t := (|k - (a * (δ - 1) + b * V)| + 1) / b
    have ht : 0 < t := div_pos (by positivity) hbp
    have hm : b * t = |k - (a * (δ - 1) + b * V)| + 1 := by
      dsimp [t]
      exact mul_div_cancel₀ _ hbp.ne'
    have hd := hD (δ - 1, V + t) (show (δ - 1, V + t) ∈ D from ⟨by change δ - 1 < δ; linarith, by change V < V + t; linarith⟩)
    rw [hf] at hd
    nlinarith [le_abs_self (k - (a * (δ - 1) + b * V))]
  have hbneg : b < 0 := by
    by_contra hbneg
    have hbzero : b = 0 := le_antisymm hb (le_of_not_gt hbneg)
    have hd := hD ((δ+c0) / 2, V + 1) (show ((δ+c0) / 2, V + 1) ∈ D from ⟨by change (δ+c0) / 2 < δ; linarith, by change V < V + 1; linarith⟩)
    have hc := hCbound (c0, L) hbase
    rw [hf, hbzero] at hd hc
    nlinarith
  have hboundary : a * δ + b * V ≤ k := by
    by_contra hle
    have hgap : 0 < a * δ + b * V - k := sub_pos.mpr (lt_of_not_ge hle)
    obtain ⟨ε, hε, hsmall⟩ := exists_pos_mul_lt hgap (a - b)
    have hd := hD (δ - ε, V + ε) (show (δ - ε, V + ε) ∈ D from ⟨by change δ - ε < δ; linarith, by change V < V + ε; linarith⟩)
    rw [hf] at hd
    nlinarith
  refine ⟨a / (-b), div_nonneg ha (neg_nonneg.mpr hb), ?_⟩
  intro z hz
  have hc := hboundary.trans (hCbound z hz)
  have hzeta : (z.1, z.2) = z := Prod.mk.eta
  rw [← hzeta, hf] at hc
  have hn : 0 < -b := neg_pos.mpr hbneg
  have he : V + a / (-b) * (z.1 - δ) = (a * (z.1 - δ) + (-b) * V) / (-b) := by
    field_simp [ne_of_lt hbneg]
    ring
  rw [he]
  apply (le_div_iff₀ hn).mpr
  nlinarith

end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open MeasureTheory WassersteinDRO.Duality
lemma empirical_probability {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (hn : 0 < n) (X : Fin n → Z) : IsProbabilityMeasure (empiricalDistribution X) := by
  constructor
  simp [empiricalDistribution, Measure.smul_apply, Measure.finsetSum_apply]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)

lemma empirical_map {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W] {n : ℕ}
    (X : Fin n → Z) (f : Z → W) (hf : Measurable f) :
    (empiricalDistribution X).map f = empiricalDistribution (fun i => f (X i)) := by
  unfold empiricalDistribution
  rw [Measure.map_smul, Measure.map_finset_sum' hf.aemeasurable]
  simp only [Measure.map_dirac' hf]

lemma empirical_lintegral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (X : Fin n → Z) (f : Z → ENNReal) :
    (∫⁻ z, f z ∂empiricalDistribution X) = (n : ENNReal)⁻¹ * ∑ i, f (X i) := by
  unfold empiricalDistribution
  rw [lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac]
  rfl

lemma empirical_coupling {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Z) (Y : Fin n → W) :
    IsProbabilityMeasure (empiricalDistribution (fun i => (X i, Y i))) ∧
    (empiricalDistribution (fun i => (X i, Y i))).map Prod.fst = empiricalDistribution X ∧
    (empiricalDistribution (fun i => (X i, Y i))).map Prod.snd = empiricalDistribution Y := by
  refine ⟨empirical_probability hn _, ?_, ?_⟩
  · exact empirical_map _ Prod.fst measurable_fst
  · exact empirical_map _ Prod.snd measurable_snd

lemma empirical_integrable {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Z) (l : Z → ℝ) :
    Integrable l (empiricalDistribution X) := by
  unfold empiricalDistribution
  apply Integrable.smul_measure
  · apply integrable_finsetSum_measure.mpr
    intro i hi
    exact integrable_dirac (by simp)
  · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hn.ne')

lemma empirical_integral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (X : Fin n → Z) (l : Z → ℝ) :
    (∫ z, l z ∂empiricalDistribution X) = (n : ℝ)⁻¹ * ∑ i, l (X i) := by
  unfold empiricalDistribution
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  · intro i hi
    exact integrable_dirac (by simp)


end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassersteinDRO.Duality DupacovaWets.Consistency

theorem empirical_ae_of_samples {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] {N : ℕ} (ξhat : Fin N → E)
    (p : E → Prop) (hp : ∀ i, p (ξhat i)) : ∀ᵐ x ∂empiricalDistribution ξhat, p x := by
  unfold empiricalDistribution
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro i hi
  rw [ae_dirac_eq]
  exact hp i

theorem empirical_expect_eq_of_finite_samples {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (L : E → EReal) (htop : ∀ i, L (ξhat i) ≠ ⊤) (hbot : ∀ i, L (ξhat i) ≠ ⊥) :
    expect (empiricalDistribution ξhat) L =
      ((1 / (N : ℝ) : ℝ) : EReal) * (∑ i, L (ξhat i)) := by
  let f : E → ℝ := fun x => (L x).toReal
  have hae : L =ᵐ[empiricalDistribution ξhat] (fun x => (f x : EReal)) := by
    apply empirical_ae_of_samples
    intro i
    exact (EReal.coe_toReal (htop i) (hbot i)).symm
  have he : expect (empiricalDistribution ξhat) L =
      expect (empiricalDistribution ξhat) (fun x => (f x : EReal)) := by
    apply le_antisymm
    · exact expect_mono _ _ _ (hae.mono fun x hx => hx.le)
    · exact expect_mono _ _ _ (hae.mono fun x hx => hx.ge)
  rw [he, expect_eq_integral _ f (empirical_integrable hN ξhat f),empirical_integral]
  have hs : (∑ i, L (ξhat i)) = ((∑ i, f (ξhat i) : ℝ) : EReal) := by
    have hh : ∀ i, L (ξhat i) = (f (ξhat i) : EReal) :=
      fun i => (EReal.coe_toReal (htop i) (hbot i)).symm
    simp only [hh]
    exact (map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) _ _).symm
  rw [hs,←EReal.coe_mul,one_div]
theorem empirical_expect_eq_of_ne_top_samples {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (L : E → EReal) (htop : ∀ i, L (ξhat i) ≠ ⊤) :
    expect (empiricalDistribution ξhat) L =
      ((1 / (N : ℝ) : ℝ) : EReal) * (∑ i, L (ξhat i)) := by
  by_cases hb : ∃ i, L (ξhat i) = ⊥
  · obtain ⟨i,hi⟩ := hb
    have hpos : (∫⁻ x, (L x).toENNReal ∂empiricalDistribution ξhat) ≠ ⊤ := by
      rw [empirical_lintegral]
      apply ENNReal.mul_ne_top
      · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hN.ne')
      · exact ENNReal.sum_ne_top.mpr (fun j _ => EReal.toENNReal_ne_top_iff.mpr (htop j))
    have hneg : (∫⁻ x, (-L x).toENNReal ∂empiricalDistribution ξhat) = ⊤ := by
      rw [empirical_lintegral]
      have hs : (∑ j : Fin N, (-L (ξhat j)).toENNReal) = ⊤ := by
        apply top_le_iff.mp
        have hh := Finset.single_le_sum (f:=fun j : Fin N => (-L (ξhat j)).toENNReal) (fun j _ => (bot_le : (0 : ENNReal) ≤ (-L (ξhat j)).toENNReal)) (Finset.mem_univ i)
        simpa [hi] using hh
      rw [hs,ENNReal.mul_top]
      simp
    have hs : (∑ j : Fin N, L (ξhat j)) = ⊥ := by
      rw [←Finset.add_sum_erase _ _ (Finset.mem_univ i),hi,EReal.bot_add]
    rw [expect,if_neg hpos,hneg,EReal.coe_ennreal_top,EReal.sub_top,hs]
    symm
    exact EReal.mul_bot_of_pos (by exact_mod_cast (one_div_pos.mpr (Nat.cast_pos.mpr hN)))
  · apply empirical_expect_eq_of_finite_samples hN ξhat L htop
    intro i hi
    exact hb ⟨i,hi⟩

end WassReductionCodex


end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassersteinDRO.Duality

theorem finite_empirical_coupling_mem {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N)
    (Ξ : Set E) (L : E → EReal) (ξhat x : Fin N → E)
    (hx : ∀ i, x i∈Ξ ∧ L (x i)≠⊤ ∧ L (x i)≠⊥) :
    (((1/(N : ℝ))*∑ i, ‖x i-ξhat i‖),((1/(N : ℝ))*∑ i, (L (x i)).toReal)) ∈
      finiteCouplingValues Ξ (empiricalDistribution ξhat) L := by
  let π := empiricalDistribution (fun i => (x i,ξhat i))
  refine ⟨π,empirical_probability hN _,?_,?_,empirical_integrable hN _ _,empirical_integrable hN _ _,?_⟩
  · exact empirical_map _ Prod.snd measurable_snd
  · exact empirical_ae_of_samples _ _ hx
  · dsimp [π]
    rw [empirical_integral,empirical_integral]
    simp only [one_div]

theorem finiteCouplingValues_nonempty_of_finite_point {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N)
    (Ξ : Set E) (L : E → EReal) (ξhat : Fin N → E) (x0 : E)
    (hx0 : x0∈Ξ ∧ L x0≠⊤ ∧ L x0≠⊥) :
    (finiteCouplingValues Ξ (empiricalDistribution ξhat) L).Nonempty :=
  ⟨_,finite_empirical_coupling_mem hN Ξ L ξhat (fun _ => x0) (fun _ => hx0)⟩
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction WassersteinDRO.Duality

theorem exists_multiplier_of_strict_finite_coupling {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {N : ℕ} (Ξ : Set E) (hΞ : MeasurableSet Ξ) (L : E → EReal) (hL : Measurable L)
    (ξhat : Fin N → E) (ε V : ℝ)
    (hupper : worstCaseExpectation ε Ξ ξhat L ≤ (V : EReal))
    (v0 : ℝ×ℝ) (hv0 : v0∈finiteCouplingValues Ξ (empiricalDistribution ξhat) L)
    (hstrict : v0.1 < ε) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ v∈finiteCouplingValues Ξ (empiricalDistribution ξhat) L,
      v.2 ≤ V+lam*(v.1-ε) := by
  apply finite_supporting_multiplier _ (finiteCouplingValues_convex Ξ _ L) ε V v0.1 v0.2 hstrict
  · simpa using hv0
  · intro v hv hc
    have hh := (finiteCouplingValues_le_worstCase Ξ hΞ L hL ξhat v hv ε hc.le).trans hupper
    exact EReal.coe_le_coe_iff.mp hh

theorem finite_tuple_bound_of_multiplier {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N)
    (Ξ : Set E) (L : E → EReal) (ξhat : Fin N → E) (ε V lam : ℝ)
    (hsupport : ∀ v∈finiteCouplingValues Ξ (empiricalDistribution ξhat) L,
      v.2 ≤ V+lam*(v.1-ε))
    (x : Fin N → E) (hx : ∀ i, x i∈Ξ ∧ L (x i)≠⊤ ∧ L (x i)≠⊥) :
    (∑ i, ((L (x i)).toReal-lam*‖x i-ξhat i‖)) ≤ (N : ℝ)*(V-lam*ε) := by
  have hv := finite_empirical_coupling_mem hN Ξ L ξhat x hx
  have hh := hsupport _ hv
  dsimp only at hh
  have hsum : (∑ i, ((L (x i)).toReal-lam*‖x i-ξhat i‖)) =
      (∑ i, (L (x i)).toReal)-lam*(∑ i, ‖x i-ξhat i‖) := by
    rw [Finset.sum_sub_distrib,Finset.mul_sum]
  rw [hsum]
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hc := mul_le_mul_of_nonneg_left hh hn.le
  have hcalc : (N : ℝ)*((1/(N : ℝ))*∑ i, (L (x i)).toReal) = ∑ i, (L (x i)).toReal := by
    field_simp
  have hcalc2 : (N : ℝ)*(V+lam*((1/(N : ℝ))*∑ i, ‖x i-ξhat i‖-ε)) =
      (N : ℝ)*(V-lam*ε)+lam*∑ i, ‖x i-ξhat i‖ := by
    field_simp
    ring
  rw [hcalc,hcalc2] at hc
  linarith
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction WassersteinDRO.Duality

theorem program12c_le_of_finite_multiplier {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N)
    (Ξ : Set E) (L : E → EReal) (ξhat : Fin N → E) (ε V lam : ℝ)
    (hlam : 0 ≤ lam) (hne_top : ∀ x∈Ξ, L x≠⊤)
    (hfinite : ∃ x∈Ξ, L x≠⊥)
    (hsupport : ∀ v∈finiteCouplingValues Ξ (empiricalDistribution ξhat) L,
      v.2 ≤ V+lam*(v.1-ε)) :
    program12cValue ε Ξ ξhat L ≤ (V : EReal) := by
  classical
  let T : Fin N → Set ℝ := fun i =>
    {r | ∃ x∈Ξ, L x≠⊥ ∧ r=(L x).toReal-lam*‖x-ξhat i‖}
  obtain ⟨x0,hx0,hL0⟩ := hfinite
  have hne : ∀ i, (T i).Nonempty := by
    intro i
    exact ⟨_,x0,hx0,hL0,rfl⟩
  have hb : ∀ r : Fin N → ℝ, (∀ i, r i∈T i) →
      (∑ i, r i) ≤ (N : ℝ)*(V-lam*ε) := by
    intro r hr
    choose x hx hbot hval using hr
    have hh := finite_tuple_bound_of_multiplier hN Ξ L ξhat ε V lam hsupport x
      (fun i => ⟨hx i,hne_top (x i) (hx i),hbot i⟩)
    simpa only [hval] using hh
  obtain ⟨s,hupper,hsum⟩ := rectangular_scores_of_sum_bound hN T hne _ hb
  have he : ∀ i, (⨆ x∈Ξ, L x-((lam*‖x-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal) := by
    intro i
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    by_cases hbot : L x=⊥
    · simp [hbot]
    · have hm : (L x).toReal-lam*‖x-ξhat i‖∈T i := ⟨x,hx,hbot,rfl⟩
      have hh := EReal.coe_le_coe_iff.mpr (hupper i _ hm)
      rw [EReal.coe_sub,EReal.coe_toReal (hne_top x hx) hbot] at hh
      exact hh
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hobj : lam*ε+(1/(N : ℝ))*∑ i, s i ≤ V := by
    have hh := mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr hn.le)
    have hc : (1/(N : ℝ))*((N : ℝ)*(V-lam*ε))=V-lam*ε := by field_simp
    rw [hc] at hh
    linarith
  unfold program12cValue
  exact iInf_le_of_le lam (iInf_le_of_le s (iInf_le_of_le he
    (iInf_le_of_le hlam (EReal.coe_le_coe_iff.mpr hobj))))
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex

/-- A linearly bounded upper semicontinuous extended-real loss has exact
zero-radius penalized envelopes, including value minus infinity at the sample. -/
theorem envelope_small_of_linear_upper {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (L : E → EReal) (xhat : E) (C A r : ℝ)
    (husc : UpperSemicontinuousAt L xhat)
    (hupper : ∀ x ∈ Ξ, L x ≤ ((C+A*‖x-xhat‖ : ℝ) : EReal))
    (hr : L xhat < (r : EReal)) :
    ∃ lam : ℝ, 0 ≤ lam ∧
      (⨆ x ∈ Ξ, L x-((lam*‖x-xhat‖ : ℝ) : EReal)) ≤ (r : EReal) := by
  have hn : ∀ᶠ x in 𝓝 xhat, L x < (r : EReal) := husc r hr
  obtain ⟨δ,hδ,hlocal⟩ := Metric.eventually_nhds_iff.mp hn
  let B := max 0 ((C-r)/δ)
  let lam := max 0 A+B
  have hB : 0 ≤ B := le_max_left _ _
  have hlam : 0 ≤ lam := add_nonneg (le_max_left _ _) hB
  refine ⟨lam,hlam,?_⟩
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  by_cases hd : ‖x-xhat‖ < δ
  · have hl : L x ≤ (r : EReal) := (hlocal (by simpa [dist_eq_norm] using hd)).le
    have hp : (0 : EReal) ≤ ((lam*‖x-xhat‖ : ℝ) : EReal) := by
      exact EReal.coe_nonneg.mpr (mul_nonneg hlam (norm_nonneg _))
    exact le_trans (by simpa using EReal.sub_le_sub le_rfl hp) hl
  · have hdist : δ ≤ ‖x-xhat‖ := le_of_not_gt hd
    have hfrac : (C-r)/δ ≤ B := le_max_right _ _
    have hCd : C-r ≤ B*δ := (div_le_iff₀ hδ).mp hfrac
    have hBd : B*δ ≤ B*‖x-xhat‖ := mul_le_mul_of_nonneg_left hdist hB
    have hAd : A*‖x-xhat‖ ≤ max 0 A*‖x-xhat‖ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    have hb : C+A*‖x-xhat‖-lam*‖x-xhat‖ ≤ r := by
      dsimp [lam]
      nlinarith
    have hh := EReal.sub_le_sub (hupper x hx) (le_refl ((lam*‖x-xhat‖ : ℝ) : EReal))
    rw [←EReal.coe_sub] at hh
    exact hh.trans (EReal.coe_le_coe_iff.mpr hb)

theorem envelope_limit_of_linear_upper {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (L : E → EReal) (xhat : E) (hxhat : xhat ∈ Ξ) (C A : ℝ)
    (husc : UpperSemicontinuousAt L xhat)
    (hupper : ∀ x ∈ Ξ, L x ≤ ((C+A*‖x-xhat‖ : ℝ) : EReal)) :
    Tendsto (fun lam : ℝ => ⨆ x ∈ Ξ, L x-((lam*‖x-xhat‖ : ℝ) : EReal))
      atTop (𝓝 (L xhat)) := by
  let F : ℝ → EReal := fun lam => ⨆ x ∈ Ξ, L x-((lam*‖x-xhat‖ : ℝ) : EReal)
  have hanti : Antitone F := by
    intro a b hab
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply le_trans _ (le_iSup₂_of_le x hx le_rfl)
    apply EReal.sub_le_sub le_rfl
    exact EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hab (norm_nonneg _))
  have hle : L xhat ≤ ⨅ lam, F lam := by
    apply le_iInf
    intro lam
    have hh : L xhat-((lam*‖xhat-xhat‖ : ℝ) : EReal) ≤ F lam :=
      le_iSup₂_of_le xhat hxhat le_rfl
    simpa [F] using hh
  have hge : (⨅ lam, F lam) ≤ L xhat := by
    by_contra hh
    obtain ⟨r,hr,hri⟩ := EReal.exists_between_coe_real (lt_of_not_ge hh)
    obtain ⟨lam,_,hlam⟩ := envelope_small_of_linear_upper Ξ L xhat C A r husc hupper hr
    exact (not_le_of_gt hri) ((iInf_le F lam).trans hlam)
  have he : (⨅ lam, F lam)=L xhat := le_antisymm hge hle
  rw [←he]
  exact tendsto_atTop_iInf hanti
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex
open WassDDRO.Reduction

theorem maxLoss_upperSemicontinuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ) :
    UpperSemicontinuous (maxLoss ℓ) := by
  intro x r hr
  obtain ⟨q,hq,hqr⟩ := exists_between hr
  have he : ∀ k, ∀ᶠ y in 𝓝 x, ℓ k y < q := by
    intro k
    have hu : UpperSemicontinuous (ℓ k) := by
      simpa only [neg_neg] using ereal_neg_upper (fun y => -ℓ k y) (hA.lsc k)
    exact hu x q (lt_of_le_of_lt (le_iSup (fun k => ℓ k x) k) hq)
  filter_upwards [eventually_all.mpr he] with y hy
  exact lt_of_le_of_lt (iSup_le (fun k => (hy k).le)) hqr

theorem maxLoss_linear_upper {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ) (xhat : E) :
    ∃ C A : ℝ, 0 ≤ A ∧ ∀ x, maxLoss ℓ x ≤ ((C+A*‖x-xhat‖ : ℝ) : EReal) := by
  classical
  have hp : ∀ k, ∃ C A : ℝ, 0 ≤ A ∧ ∀ x, ℓ k x ≤ ((C+A*‖x-xhat‖ : ℝ) : EReal) := by
    intro k
    obtain ⟨x0,_,hx0⟩ := hA.not_bot_on k
    have ha := EReal.coe_toReal (hA.ne_top k x0) hx0
    have hu : UpperSemicontinuous (ℓ k) := by
      simpa only [neg_neg] using ereal_neg_upper (fun y => -ℓ k y) (hA.lsc k)
    obtain ⟨C,A,hA0,hbound⟩ := linear_upper_of_convex_epigraph (ℓ k) (hA.ne_top k)
      (hA.convex_epigraph k) x0 (ℓ k x0).toReal ha.symm (hu x0)
    refine ⟨C+A*‖xhat-x0‖,A,hA0,?_⟩
    intro x
    have hd : ‖x-x0‖ ≤ ‖x-xhat‖+‖xhat-x0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    apply (hbound x).trans
    apply EReal.coe_le_coe_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_left hd hA0]
  choose C A hA0 hbound using hp
  refine ⟨∑ k, |C k|, ∑ k, A k,Finset.sum_nonneg (fun k _ => hA0 k),?_⟩
  intro x
  apply iSup_le
  intro k
  have hc : C k ≤ ∑ j, |C j| := (le_abs_self _).trans
    (Finset.single_le_sum (f:=fun j : Fin K => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_univ k))
  have ha : A k ≤ ∑ j, A j := Finset.single_le_sum (fun j _ => hA0 j) (Finset.mem_univ k)
  apply (hbound k x).trans
  exact EReal.coe_le_coe_iff.mpr (add_le_add hc (mul_le_mul_of_nonneg_right ha (norm_nonneg _)))

theorem maxLoss_envelope_limit {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (xhat : E) (hxhat : xhat ∈ Ξ) :
    Tendsto (fun lam : ℝ => ⨆ x ∈ Ξ, maxLoss ℓ x-((lam*‖x-xhat‖ : ℝ) : EReal))
      atTop (𝓝 (maxLoss ℓ xhat)) := by
  obtain ⟨C,A,_,hupper⟩ := maxLoss_linear_upper Ξ ℓ hA xhat
  exact envelope_limit_of_linear_upper Ξ (maxLoss ℓ) xhat hxhat C A
    (maxLoss_upperSemicontinuous Ξ ℓ hA xhat) (fun x _ => hupper x)
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open DupacovaWets.Consistency
 theorem coupling_upper {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (Q P : Measure E) (π : Measure (E×E)) (L : E → EReal) (ψ : E → ℝ) (lam : ℝ)
    (hL : Measurable L) (hψ : Integrable ψ P)
    (hm : π.map Prod.fst=Q ∧ π.map Prod.snd=P)
    (hcost : (∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π) ≠ ⊤)
    (hbound : ∀ᵐ w ∂π, L w.1 ≤ ((lam*‖w.1-w.2‖+ψ w.2 : ℝ) : EReal)) :
    expect Q L ≤ ((lam*(∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π).toReal+
      ∫ y, ψ y ∂P : ℝ) : EReal) := by
  have hc : Measurable (fun w : E×E => ‖w.1-w.2‖) := (measurable_fst.sub measurable_snd).norm
  have hi : Integrable (fun w : E×E => ‖w.1-w.2‖) π :=
    (lintegral_ofReal_ne_top_iff_integrable hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => norm_nonneg (w.1-w.2))).mp hcost
  have hp : Integrable ψ (π.map Prod.snd) := by rw [hm.2];exact hψ
  have hs : Integrable (fun w : E×E => ψ w.2) π := hp.comp_measurable measurable_snd
  have hb : Integrable (fun w : E×E => lam*‖w.1-w.2‖+ψ w.2) π := (hi.const_mul lam).add hs
  have he : expect Q L=expect π (fun w => L w.1) := by
    rw [←hm.1]
    exact expect_map π Prod.fst L measurable_fst hL
  rw [he]
  have hup := expect_le_integrable_upper π (fun w => L w.1) _ hb hbound
  have hsnd : (∫ w : E×E, ψ w.2 ∂π) = ∫ y, ψ y ∂P := by
    rw [←hm.2]
    symm
    exact integral_map measurable_snd.aemeasurable hp.aestronglyMeasurable
  have hreal : (∫ w : E×E, lam*‖w.1-w.2‖+ψ w.2 ∂π) =
      lam*(∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π).toReal+∫ y, ψ y ∂P := by
    rw [integral_add (hi.const_mul lam) hs, integral_const_mul, hsnd,
      integral_eq_lintegral_of_nonneg_ae (f:=fun w : E×E => ‖w.1-w.2‖)
        (Filter.Eventually.of_forall fun w => norm_nonneg (w.1-w.2)) hc.aestronglyMeasurable]
  rwa [hreal] at hup
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
 theorem exists_sample_barrier {E : Type*} {N : ℕ} (ξhat : Fin N → E) (s : Fin N → ℝ) :
    ∃ ψ : E → ℝ, (∀ i, ψ (ξhat i)≤ s i) ∧
      ∀ y ∈ Set.range ξhat, ∃ i, ξhat i=y ∧ ψ y=s i := by
  classical
  have hchoose (y : E) (hy : y ∈ Set.range ξhat) :
      ∃ i, ξhat i=y ∧ ∀ j, ξhat j=y → s i≤ s j := by
    obtain ⟨j,hj⟩ := hy
    have hn : (Finset.univ.filter (fun i => ξhat i=y)).Nonempty := ⟨j,by simp [hj]⟩
    obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun i => ξhat i=y)) s hn
    refine ⟨i,(Finset.mem_filter.mp hi).2,?_⟩
    intro j hj
    exact hmin j (by simp [hj])
  choose idx hi hmin using hchoose
  let ψ := fun y => if hy : y ∈ Set.range ξhat then s (idx y hy) else 0
  refine ⟨ψ,?_,?_⟩
  · intro i
    have hy : ξhat i ∈ Set.range ξhat := Set.mem_range_self i
    simp only [ψ,dif_pos hy]
    exact hmin (ξhat i) hy i rfl
  · intro y hy
    refine ⟨idx y hy,hi y hy,?_⟩
    simp only [ψ,dif_pos hy]
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace WassReductionCodex
open WassDDRO.Reduction WassersteinDRO.Duality DupacovaWets.Consistency
 theorem transport_epigraph_upper {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {N : ℕ} (hN : 0<N)
    (Ξ : Set E) (L : E → EReal) (hL : Measurable L) (ξhat : Fin N → E)
    (ε lam : ℝ) (hε : 0≤ε) (hlam : 0≤lam) (s : Fin N → ℝ)
    (he : ∀ i, (⨆ ξ ∈ Ξ, L ξ-((lam*‖ξ-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal))
    (Q : Measure E) (hQ : Q Ξᶜ=0)
    (hbudget : wassersteinDistance 1 Q (empiricalDistribution ξhat)≤ENNReal.ofReal ε) :
    expect Q L ≤ ((lam*ε+(1/(N : ℝ))*∑ i, s i : ℝ) : EReal) := by
  obtain ⟨ψ,hψ,hsel⟩ := exists_sample_barrier ξhat s
  have hiψ := empirical_integrable hN ξhat ψ
  have hav : (∫ y, ψ y ∂empiricalDistribution ξhat) ≤ (1/(N : ℝ))*∑ i, s i := by
    rw [empirical_integral,one_div]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hψ i)) (by positivity)
  have hsupport : (empiricalDistribution ξhat) (Set.range ξhat)ᶜ=0 := by
    simp [empiricalDistribution,Measure.smul_apply,Measure.finsetSum_apply,Measure.dirac_apply',Set.mem_range_self]
  have hupper (η : ℝ) (hη : 0<η) :
      expect Q L ≤ ((lam*(ε+η)+(1/(N : ℝ))*∑ i, s i : ℝ) : EReal) := by
    obtain ⟨π,hm,hc⟩ := exists_coupling_lt_budget_add Q (empiricalDistribution ξhat) ε η hε hη hbudget
    have hcfin : (∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π) ≠ ⊤ := (lt_of_lt_of_le hc le_top).ne
    have hx : ∀ᵐ w ∂π, w.1∈Ξ := by
      rw [ae_iff]
      change π (Prod.fst ⁻¹' Ξᶜ)=0
      have ht := π.le_map_apply measurable_fst.aemeasurable Ξᶜ
      rw [hm.1,hQ] at ht
      exact le_antisymm ht bot_le
    have hy : ∀ᵐ w ∂π, w.2∈Set.range ξhat := by
      rw [ae_iff]
      change π (Prod.snd ⁻¹' (Set.range ξhat)ᶜ)=0
      have ht := π.le_map_apply measurable_snd.aemeasurable (Set.range ξhat)ᶜ
      rw [hm.2,hsupport] at ht
      exact le_antisymm ht bot_le
    have hb : ∀ᵐ w ∂π, L w.1≤((lam*‖w.1-w.2‖+ψ w.2 : ℝ) : EReal) := by
      filter_upwards [hx,hy] with w hwx hwy
      obtain ⟨i,hiy,hψy⟩ := hsel w.2 hwy
      have hp : L w.1-((lam*‖w.1-ξhat i‖ : ℝ) : EReal) ≤ (s i : EReal) :=
        le_trans (le_iSup₂_of_le w.1 hwx le_rfl) (he i)
      rw [hiy] at hp
      have hu := (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).mp hp
      simpa only [hψy,← EReal.coe_add,add_comm] using hu
    have hg := coupling_upper Q (empiricalDistribution ξhat) π L ψ lam hL hiψ hm hcfin hb
    have hr := mul_le_mul_of_nonneg_left (ENNReal.toReal_lt_of_lt_ofReal hc).le hlam
    exact le_trans hg (EReal.coe_le_coe_iff.mpr (add_le_add hr hav))
  have hη : Tendsto (fun n : ℕ => (1 : ℝ)/(n+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have htR : Tendsto (fun n : ℕ => lam*(ε+(1 : ℝ)/(n+1))+(1/(N : ℝ))*∑ i, s i)
      atTop (𝓝 (lam*ε+(1/(N : ℝ))*∑ i, s i)) := by
    have heR : Tendsto (fun n : ℕ => ε+(1 : ℝ)/(n+1)) atTop (𝓝 ε) := by
      simpa using tendsto_const_nhds.add hη
    exact (tendsto_const_nhds.mul heR).add tendsto_const_nhds
  have ht := (continuous_coe_real_ereal.tendsto (lam*ε+(1/(N : ℝ))*∑ i, s i)).comp htR
  exact isClosed_Ici.mem_of_tendsto ht
    (Eventually.of_forall fun n => hupper ((1 : ℝ)/(n+1)) (by positivity))

end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem worstCase_le_program12c {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hN : 0<N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (ε : ℝ) (hε : 0≤ε) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)≤program12cValue ε Ξ ξhat (maxLoss ℓ) := by
  have hL : Measurable (maxLoss ℓ) := by
    unfold maxLoss
    exact Measurable.iSup hmeas
  unfold worstCaseExpectation program12cValue
  apply le_iInf
  intro lam
  apply le_iInf
  intro s
  apply le_iInf
  intro he
  apply le_iInf
  intro hlam
  apply iSup_le
  intro Q
  apply iSup_le
  intro hQ
  exact transport_epigraph_upper hN Ξ (maxLoss ℓ) hL ξhat ε lam hε hlam s he Q hQ.2.1 hQ.2.2
 theorem program12c_le_program12f {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {K N : ℕ} (hK : 0<K) (hN : 0<N)
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (ξhat : Fin N → E) (ε : ℝ) :
    program12cValue ε Ξ ξhat (maxLoss ℓ)≤program12fValue ε Ξ ξhat ℓ := by
  unfold program12cValue program12fValue
  apply le_iInf
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
 theorem approximate_reduction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0<K) (hN : 0<N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (ε : ℝ) (hε : 0≤ε) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)≤program12fValue ε Ξ ξhat ℓ :=
  le_trans (worstCase_le_program12c hN Ξ ℓ hmeas ξhat ε hε)
    (program12c_le_program12f hK hN Ξ ℓ ξhat ε)
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction

theorem exists_program12c_finite_upper {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K N : ℕ} (hN : 0 < N)
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (ε : ℝ) :
    ∃ r : ℝ, program12cValue ε Ξ ξhat (maxLoss ℓ) ≤ (r : EReal) := by
  let j : Fin N := ⟨0,hN⟩
  obtain ⟨C,A,hA0,hbound⟩ := maxLoss_linear_upper Ξ ℓ hA (ξhat j)
  let s : Fin N → ℝ := fun i => C+A*‖ξhat i-ξhat j‖
  have he : ∀ i, (⨆ x ∈ Ξ, maxLoss ℓ x-((A*‖x-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal) := by
    intro i
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    have hh := EReal.sub_le_sub (hbound x) (le_refl ((A*‖x-ξhat i‖ : ℝ) : EReal))
    rw [←EReal.coe_sub] at hh
    apply hh.trans
    apply EReal.coe_le_coe_iff.mpr
    have hd := norm_sub_le_norm_sub_add_norm_sub x (ξhat i) (ξhat j)
    dsimp [s]
    nlinarith [mul_le_mul_of_nonneg_left hd hA0]
  refine ⟨A*ε+(1/(N : ℝ))*∑ i, s i,?_⟩
  unfold program12cValue
  exact iInf_le_of_le A (iInf_le_of_le s (iInf_le_of_le he (iInf_le_of_le hA0 le_rfl)))

theorem program12c_ne_top {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K N : ℕ} (hN : 0 < N)
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (ε : ℝ) : program12cValue ε Ξ ξhat (maxLoss ℓ) ≠ ⊤ := by
  obtain ⟨r,hr⟩ := exists_program12c_finite_upper hN Ξ ℓ hA ξhat ε
  exact (lt_of_le_of_lt hr (EReal.coe_lt_top r)).ne

theorem worstCase_ne_top {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (hmeas : ∀ k, Measurable (ℓ k))
    (ξhat : Fin N → E) (ε : ℝ) (hε : 0 ≤ ε) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ) ≠ ⊤ := by
  obtain ⟨r,hr⟩ := exists_program12c_finite_upper hN Ξ ℓ hA ξhat ε
  exact (lt_of_le_of_lt ((worstCase_le_program12c hN Ξ ℓ hmeas ξhat ε hε).trans hr)
    (EReal.coe_lt_top r)).ne
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction WassersteinDRO.Duality

/-- The strict-feasibility case of the original positive-radius equality.
The extra finite-coupling hypothesis is explicit and is not claimed to follow
from Assumption41 for every radius. -/
theorem worstCase_eq_program12c_of_strict_finite_coupling {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {K N : ℕ} (hK : 0 < K) (hN : 0 < N)
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hmeas : ∀ k, Measurable (ℓ k))
    (ξhat : Fin N → E) (ε : ℝ) (hε : 0 ≤ ε) (hA : Assumption41 Ξ ℓ)
    (v0 : ℝ×ℝ) (hv0 : v0∈finiteCouplingValues Ξ (empiricalDistribution ξhat) (maxLoss ℓ))
    (hstrict : v0.1 < ε) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)=program12cValue ε Ξ ξhat (maxLoss ℓ) := by
  have hL : Measurable (maxLoss ℓ) := Measurable.iSup hmeas
  have htop := worstCase_ne_top hN Ξ ℓ hA hmeas ξhat ε hε
  have hbot : worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)≠⊥ := by
    intro hh
    have hv := finiteCouplingValues_le_worstCase Ξ hA.closed.measurableSet (maxLoss ℓ)
      hL ξhat v0 hv0 ε hstrict.le
    rw [hh] at hv
    exact (EReal.coe_ne_bot _) (le_bot_iff.mp hv)
  have hreal := EReal.coe_toReal htop hbot
  let V : ℝ := (worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)).toReal
  have hupper : worstCaseExpectation ε Ξ ξhat (maxLoss ℓ) ≤ (V : EReal) := hreal.symm.le
  obtain ⟨lam,hlam,hsupport⟩ := exists_multiplier_of_strict_finite_coupling Ξ
    hA.closed.measurableSet (maxLoss ℓ) hL ξhat ε V hupper v0 hv0 hstrict
  let k0 : Fin K := ⟨0,hK⟩
  obtain ⟨x0,hx0,hL0⟩ := hA.not_bot_on k0
  have hn0 : maxLoss ℓ x0≠⊥ := by
    intro hh
    have hl := le_iSup (fun k => ℓ k x0) k0
    change ℓ k0 x0 ≤ maxLoss ℓ x0 at hl
    rw [hh] at hl
    exact hL0 (le_bot_iff.mp hl)
  have hp := program12c_le_of_finite_multiplier hN Ξ (maxLoss ℓ) ξhat ε V lam hlam
    (fun x _ => iSup_ne_top (fun k => hA.ne_top k x)) ⟨x0,hx0,hn0⟩ hsupport
  exact le_antisymm (worstCase_le_program12c hN Ξ ℓ hmeas ξhat ε hε) (hp.trans hreal.le)
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction

theorem program12c_eq_bot_of_cost_gap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K N : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (ε : ℝ) (d : Fin N → ℝ)
    (hd : ∀ i x, x∈Ξ → maxLoss ℓ x≠⊥ → d i≤‖x-ξhat i‖)
    (hgap : ε < (1/(N : ℝ))*∑ i, d i) :
    program12cValue ε Ξ ξhat (maxLoss ℓ)=⊥ := by
  classical
  have hg : ∀ i, ∃ C A : ℝ, 0 ≤ A ∧
      ∀ x, maxLoss ℓ x ≤ ((C+A*‖x-ξhat i‖ : ℝ) : EReal) :=
    fun i => maxLoss_linear_upper Ξ ℓ hA (ξhat i)
  choose C A hA0 hupper using hg
  let a : ℝ := ∑ i, A i
  have ha : 0 ≤ a := Finset.sum_nonneg (fun i _ => hA0 i)
  have hai : ∀ i, A i≤a := fun i => Finset.single_le_sum (fun j _ => hA0 j) (Finset.mem_univ i)
  have hb (r : ℝ) : program12cValue ε Ξ ξhat (maxLoss ℓ) ≤ (r : EReal) := by
    let D : ℝ := (1/(N : ℝ))*∑ i, d i-ε
    have hD : 0 < D := sub_pos.mpr hgap
    let B : ℝ := a*ε+(1/(N : ℝ))*∑ i, C i
    let t : ℝ := max 0 ((B-r)/D)
    have ht : 0 ≤ t := le_max_left _ _
    have htr : B-r≤t*D := (div_le_iff₀ hD).mp (le_max_right _ _)
    let lam := a+t
    let s : Fin N → ℝ := fun i => C i-t*d i
    have he : ∀ i, (⨆ x∈Ξ, maxLoss ℓ x-((lam*‖x-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal) := by
      intro i
      apply iSup_le
      intro x
      apply iSup_le
      intro hx
      by_cases hbot : maxLoss ℓ x=⊥
      · simp [hbot]
      · have hh := EReal.sub_le_sub (hupper i x) (le_refl ((lam*‖x-ξhat i‖ : ℝ) : EReal))
        rw [←EReal.coe_sub] at hh
        apply hh.trans
        apply EReal.coe_le_coe_iff.mpr
        have hnorm := norm_nonneg (x-ξhat i)
        have hcost := mul_le_mul_of_nonneg_left (hd i x hx hbot) ht
        have hAi := mul_le_mul_of_nonneg_right (hai i) hnorm
        dsimp [lam,s]
        nlinarith
    have hobj : lam*ε+(1/(N : ℝ))*∑ i, s i ≤ r := by
      have hs : (∑ i, s i)=(∑ i, C i)-t*(∑ i, d i) := by
        dsimp [s]
        rw [Finset.sum_sub_distrib,Finset.mul_sum]
      rw [hs]
      have heq : lam*ε+(1/(N : ℝ))*((∑ i, C i)-t*(∑ i, d i)) = B-t*D := by
        dsimp [lam,B,D]
        ring
      rw [heq]
      nlinarith
    unfold program12cValue
    exact iInf_le_of_le lam (iInf_le_of_le s (iInf_le_of_le he
      (iInf_le_of_le (add_nonneg ha ht) (EReal.coe_le_coe_iff.mpr hobj))))
  apply le_antisymm _ bot_le
  by_contra hh
  obtain ⟨r,_,hr⟩ := EReal.exists_between_coe_real (lt_of_not_ge hh)
  exact (not_le_of_gt hr) (hb r)

theorem worstCase_and_program_eq_bot_of_cost_gap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (ε : ℝ) (hε : 0 ≤ ε) (d : Fin N → ℝ)
    (hd : ∀ i x, x∈Ξ → maxLoss ℓ x≠⊥ → d i≤‖x-ξhat i‖)
    (hgap : ε < (1/(N : ℝ))*∑ i, d i) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)=⊥ ∧ program12cValue ε Ξ ξhat (maxLoss ℓ)=⊥ := by
  have hp := program12c_eq_bot_of_cost_gap Ξ ℓ hA ξhat ε d hd hgap
  have hw := worstCase_le_program12c hN Ξ ℓ hmeas ξhat ε hε
  rw [hp] at hw
  exact ⟨le_bot_iff.mp hw,hp⟩
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction WassersteinDRO.Duality

def finiteLossDomain {E : Type*} (Ξ : Set E) (L : E → EReal) : Set E :=
  Ξ ∩ {x | L x≠⊥}

noncomputable def finiteDomainCost {E : Type*} [NormedAddCommGroup E] {N : ℕ}
    (Ξ : Set E) (L : E → EReal) (ξhat : Fin N → E) : ℝ :=
  (1/(N : ℝ))*∑ i, Metric.infDist (ξhat i) (finiteLossDomain Ξ L)

theorem finite_domain_distance_lower {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (L : E → EReal) (xhat x : E) (hx : x∈Ξ) (hLx : L x≠⊥) :
    Metric.infDist xhat (finiteLossDomain Ξ L) ≤ ‖x-xhat‖ := by
  have hh := Metric.infDist_le_dist_of_mem (x:=xhat) (show x∈finiteLossDomain Ξ L from ⟨hx,hLx⟩)
  rw [dist_comm,dist_eq_norm] at hh
  exact hh

theorem strict_finite_coupling_of_gt_domain_cost {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N)
    (Ξ : Set E) (L : E → EReal) (ξhat : Fin N → E) (ε : ℝ)
    (hne_top : ∀ x∈Ξ, L x≠⊤) (hfinite : (finiteLossDomain Ξ L).Nonempty)
    (hε : finiteDomainCost Ξ L ξhat < ε) :
    ∃ v∈finiteCouplingValues Ξ (empiricalDistribution ξhat) L, v.1 < ε := by
  classical
  let D := finiteDomainCost Ξ L ξhat
  let η : ℝ := (ε-D)/2
  have hη : 0 < η := by dsimp [η,D];linarith
  have hp : ∀ i, ∃ x∈finiteLossDomain Ξ L,
      ‖x-ξhat i‖ < Metric.infDist (ξhat i) (finiteLossDomain Ξ L)+η := by
    intro i
    obtain ⟨x,hx,hd⟩ := (Metric.infDist_lt_iff hfinite).mp
      (show Metric.infDist (ξhat i) (finiteLossDomain Ξ L) <
        Metric.infDist (ξhat i) (finiteLossDomain Ξ L)+η by linarith)
    refine ⟨x,hx,?_⟩
    simpa [dist_comm,dist_eq_norm] using hd
  choose x hx hdist using hp
  have hv := finite_empirical_coupling_mem hN Ξ L ξhat x
    (fun i => ⟨(hx i).1,hne_top (x i) (hx i).1,(hx i).2⟩)
  refine ⟨_,hv,?_⟩
  dsimp only
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hh : (1/(N : ℝ))*(∑ i, ‖x i-ξhat i‖) ≤
      (1/(N : ℝ))*(∑ i, (Metric.infDist (ξhat i) (finiteLossDomain Ξ L)+η)) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => (hdist i).le))
    (one_div_nonneg.mpr hn.le)
  have he : (1/(N : ℝ))*(∑ i, (Metric.infDist (ξhat i) (finiteLossDomain Ξ L)+η)) = D+η := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    dsimp [D,finiteDomainCost]
    field_simp
  rw [he] at hh
  exact lt_of_le_of_lt hh (by dsimp [η];dsimp [D] at hε ⊢;linarith)

theorem positive_reduction_except_domain_boundary {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E)
    (ε : ℝ) (hε : 0 ≤ ε) (hA : Assumption41 Ξ ℓ)
    (hne : ε≠finiteDomainCost Ξ (maxLoss ℓ) ξhat) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)=program12cValue ε Ξ ξhat (maxLoss ℓ) := by
  by_cases hlt : ε < finiteDomainCost Ξ (maxLoss ℓ) ξhat
  · have hh := worstCase_and_program_eq_bot_of_cost_gap hN Ξ ℓ hmeas hA ξhat ε hε
      (fun i => Metric.infDist (ξhat i) (finiteLossDomain Ξ (maxLoss ℓ)))
      (fun i x hx hn => finite_domain_distance_lower Ξ (maxLoss ℓ) (ξhat i) x hx hn) hlt
    rw [hh.1,hh.2]
  · have hgt : finiteDomainCost Ξ (maxLoss ℓ) ξhat < ε := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
    let k0 : Fin K := ⟨0,hK⟩
    obtain ⟨x0,hx0,hL0⟩ := hA.not_bot_on k0
    have hn0 : maxLoss ℓ x0≠⊥ := by
      intro hh
      have hl := le_iSup (fun k => ℓ k x0) k0
      change ℓ k0 x0 ≤ maxLoss ℓ x0 at hl
      rw [hh] at hl
      exact hL0 (le_bot_iff.mp hl)
    obtain ⟨v,hv,hvε⟩ := strict_finite_coupling_of_gt_domain_cost hN Ξ (maxLoss ℓ) ξhat ε
      (fun x _ => iSup_ne_top (fun k => hA.ne_top k x)) ⟨x0,hx0,hn0⟩ hgt
    exact worstCase_eq_program12c_of_strict_finite_coupling hK hN Ξ ℓ hmeas ξhat ε hε hA v hv hvε
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex

/-- An upper semicontinuous loss attains its maximum on the compact nearest
face of the closure of its finite domain. The maximizing value may be bottom. -/
theorem nearest_finite_domain_max {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (Ξ : Set E) (hΞ : IsClosed Ξ) (L : E → EReal) (hL : UpperSemicontinuous L)
    (hne : (finiteLossDomain Ξ L).Nonempty) (xhat : E) :
    ∃ y∈Ξ, ‖y-xhat‖=Metric.infDist xhat (finiteLossDomain Ξ L) ∧
      y∈closure (finiteLossDomain Ξ L) ∧
      ∀ x∈closure (finiteLossDomain Ξ L),
        ‖x-xhat‖=Metric.infDist xhat (finiteLossDomain Ξ L) → L x≤L y := by
  let S := closure (finiteLossDomain Ξ L)
  let d := Metric.infDist xhat (finiteLossDomain Ξ L)
  let K := S ∩ Metric.sphere xhat d
  have hc : IsCompact K := (isCompact_sphere xhat d).inter_left isClosed_closure
  obtain ⟨z,hz,hdz⟩ := Metric.exists_mem_closure_infDist_eq_dist hne xhat
  have hnK : K.Nonempty := by
    refine ⟨z,hz,?_⟩
    change dist z xhat=d
    dsimp [d]
    rw [dist_comm]
    exact hdz.symm
  obtain ⟨y,hy,hmax⟩ := (hL.upperSemicontinuousOn K).exists_isMaxOn hnK hc
  have hSΞ : S⊆Ξ := closure_minimal (fun x hx => hx.1) hΞ
  refine ⟨y,hSΞ hy.1,?_,hy.1,?_⟩
  · have hs : dist y xhat=d := hy.2
    simpa only [dist_eq_norm] using hs
  · intro x hx hd
    apply hmax
    exact ⟨hx,by change dist x xhat=d;simpa only [dist_eq_norm] using hd⟩
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex

theorem critical_envelope_small {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (Ξ : Set E) (hΞ : IsClosed Ξ) (L : E → EReal) (hL : UpperSemicontinuous L)
    (xhat y : E) (C A : ℝ) (hA : 0 ≤ A)
    (hupper : ∀ x∈Ξ, L x≤((C+A*‖x-xhat‖ : ℝ) : EReal))
    (hmax : ∀ x∈closure (finiteLossDomain Ξ L),
      ‖x-xhat‖=Metric.infDist xhat (finiteLossDomain Ξ L) → L x≤L y)
    (r : ℝ) (hr : L y < (r : EReal)) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ lam' : ℝ, lam≤lam' →
      (⨆ x∈Ξ, L x-((lam'*‖x-xhat‖ : ℝ) : EReal)) ≤
        ((r-lam'*Metric.infDist xhat (finiteLossDomain Ξ L) : ℝ) : EReal) := by
  classical
  let d := Metric.infDist xhat (finiteLossDomain Ξ L)
  let T := Ξ ∩ {x | (r : EReal)≤L x}
  have hcost (x : E) (hx : x∈Ξ) (hb : L x≠⊥) : d≤‖x-xhat‖ :=
    finite_domain_distance_lower Ξ L xhat x hx hb
  have hlow (lam' : ℝ) (hlam : 0 ≤ lam') (x : E) (hx : x∈Ξ)
      (hb : L x≠⊥) (hl : L x≤(r : EReal)) :
      L x-((lam'*‖x-xhat‖ : ℝ) : EReal) ≤ ((r-lam'*d : ℝ) : EReal) := by
    have hh := EReal.sub_le_sub hl (EReal.coe_le_coe_iff.mpr
      (mul_le_mul_of_nonneg_left (hcost x hx hb) hlam))
    simpa only [←EReal.coe_sub] using hh
  by_cases hn : T.Nonempty
  · have hTc : IsClosed T := hΞ.inter (hL.isClosed_preimage (r : EReal))
    obtain ⟨z,hz,hzdist⟩ := hTc.exists_infDist_eq_dist hn xhat
    let q := Metric.infDist xhat T
    have hzbot : L z≠⊥ := by
      intro hh
      have hrz : (r : EReal)≤L z := hz.2
      rw [hh] at hrz
      exact (EReal.coe_ne_bot r) (le_bot_iff.mp hrz)
    have hzq : ‖z-xhat‖=q := by
      have hh := hzdist.symm
      rw [dist_comm,dist_eq_norm] at hh
      exact hh
    have hq : d<q := by
      have hdq : d≤q := by rw [←hzq];exact hcost z hz.1 hzbot
      by_contra hh
      have he : q=d := le_antisymm (le_of_not_gt hh) hdq
      have hzS : z∈closure (finiteLossDomain Ξ L) := subset_closure ⟨hz.1,hzbot⟩
      have hl := hmax z hzS (by rw [hzq,he])
      exact (not_le_of_gt hr) ((show (r : EReal)≤L z from hz.2).trans hl)
    let t : ℝ := max 0 ((C+A*d-r)/(q-d))
    have ht : 0 ≤ t := le_max_left _ _
    have htr : C+A*d-r≤t*(q-d) := (div_le_iff₀ (sub_pos.mpr hq)).mp (le_max_right _ _)
    refine ⟨A+t,add_nonneg hA ht,?_⟩
    intro lam' hlam
    have hlam0 : 0 ≤ lam' := le_trans (add_nonneg hA ht) hlam
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    by_cases hb : L x=⊥
    · simp [hb]
    · by_cases hl : L x≤(r : EReal)
      · exact hlow lam' hlam0 x hx hb hl
      · have hxT : x∈T := ⟨hx,(lt_of_not_ge hl).le⟩
        have hqx : q≤‖x-xhat‖ := by
          have hh := Metric.infDist_le_dist_of_mem (x:=xhat) hxT
          rw [dist_comm,dist_eq_norm] at hh
          exact hh
        have hg := le_trans hq.le hqx
        have htlam : t≤lam'-A := by linarith
        have hp1 := mul_le_mul_of_nonneg_left (sub_le_sub_right hqx d) ht
        have hp2 := mul_le_mul_of_nonneg_right htlam (sub_nonneg.mpr hg)
        have hh := EReal.sub_le_sub (hupper x hx) (le_refl ((lam'*‖x-xhat‖ : ℝ) : EReal))
        rw [←EReal.coe_sub] at hh
        apply hh.trans
        apply EReal.coe_le_coe_iff.mpr
        nlinarith
  · refine ⟨0,le_rfl,?_⟩
    intro lam' hlam
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    by_cases hb : L x=⊥
    · simp [hb]
    · have hl : L x≤(r : EReal) := by
        by_contra hh
        exact hn ⟨x,hx,(lt_of_not_ge hh).le⟩
      exact hlow lam' hlam x hx hb hl
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex
open WassDDRO.Reduction

lemma ereal_sum_ne_top {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊤) : (∑ i ∈ s, f i) ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact EReal.add_ne_top (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma tendsto_ereal_finset_sum {α ι : Type*} (F : Filter α) (s : Finset ι)
    (f : ι → α → EReal) (a : ι → EReal)
    (ha : ∀ i ∈ s, a i ≠ ⊤) (hf : ∀ i ∈ s, Tendsto (f i) F (𝓝 (a i))) :
    Tendsto (fun x => ∑ i ∈ s, f i x) F (𝓝 (∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : EReal)) F (𝓝 0))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hs := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hc := EReal.continuousAt_add (p:=(a i, ∑ j ∈ s, a j)) (.inl (ha i (Finset.mem_insert_self _ _)))
      (.inr (ereal_sum_ne_top s a (fun j hj => ha j (Finset.mem_insert_of_mem hj))))
    exact hc.tendsto.comp ((hf i (Finset.mem_insert_self _ _)).prodMk_nhds hs)

theorem envelope_average_limit {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K N : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ) :
    Tendsto (fun lam : ℝ => ((1 / (N : ℝ) : ℝ) : EReal) *
      ∑ i, (⨆ x ∈ Ξ, maxLoss ℓ x-((lam*‖x-ξhat i‖ : ℝ) : EReal)))
      atTop (𝓝 (((1 / (N : ℝ) : ℝ) : EReal) * (∑ i, maxLoss ℓ (ξhat i)))) := by
  have ht := tendsto_ereal_finset_sum atTop Finset.univ
    (fun i (lam : ℝ) => ⨆ x ∈ Ξ, maxLoss ℓ x-((lam*‖x-ξhat i‖ : ℝ) : EReal))
    (fun i => maxLoss ℓ (ξhat i))
    (fun i _ => iSup_ne_top (fun k => hA.ne_top k (ξhat i)))
    (fun i _ => maxLoss_envelope_limit Ξ ℓ hA (ξhat i) (hξ i))
  exact EReal.Tendsto.const_mul ht (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex

theorem exists_real_scores_lt_average {N : ℕ} (a : Fin N → EReal)
    (hne_top : ∀ i, a i ≠ ⊤) (r : ℝ)
    (hr : ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, a i) < (r : EReal)) :
    ∃ s : Fin N → ℝ, (∀ i, a i < (s i : EReal)) ∧ (1/(N : ℝ))*∑ i, s i < r := by
  classical
  let s : Fin N → ℕ → ℝ := fun i n => if a i=⊥ then -(n : ℝ) else (a i).toReal+1/(n+1)
  have hscore : ∀ i n, a i < (s i n : EReal) := by
    intro i n
    by_cases hb : a i=⊥
    · simpa only [s,if_pos hb,hb] using EReal.bot_lt_coe (-(n : ℝ))
    · dsimp only [s]
      rw [if_neg hb,←EReal.coe_toReal (hne_top i) hb]
      apply EReal.coe_lt_coe_iff.mpr
      simpa using (Nat.one_div_pos_of_nat (n:=n) : (0 : ℝ)<1/(n+1))
  have ht : ∀ i, Tendsto (fun n => (s i n : EReal)) atTop (𝓝 (a i)) := by
    intro i
    by_cases hb : a i=⊥
    · simp only [s,hb,if_pos]
      exact EReal.tendsto_coe_nhds_bot_iff.mpr
        (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
    · simp only [s,if_neg hb]
      rw [←EReal.coe_toReal (hne_top i) hb]
      apply continuous_coe_real_ereal.continuousAt.tendsto.comp
      simpa using (tendsto_const_nhds (x:=(a i).toReal)).add
        tendsto_one_div_add_atTop_nhds_zero_nat
  have hsum := tendsto_ereal_finset_sum atTop Finset.univ
    (fun i n => (s i n : EReal)) a (fun i _ => hne_top i) (fun i _ => ht i)
  have hav := EReal.Tendsto.const_mul (a:=((1/(N : ℝ) : ℝ) : EReal)) hsum
    (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))
  have hev : ∀ᶠ n : ℕ in atTop,
      ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, (s i n : EReal)) < (r : EReal) :=
    hav.eventually (isOpen_Iio.mem_nhds hr)
  obtain ⟨n,hn⟩ := hev.exists
  refine ⟨fun i => s i n,fun i => hscore i n,?_⟩
  have hs : (∑ i, (s i n : EReal)) = ((∑ i, s i n : ℝ) : EReal) :=
    (map_sum (⟨⟨Real.toEReal,EReal.coe_zero⟩,EReal.coe_add⟩ : ℝ →+ EReal) _ _).symm
  rw [hs,←EReal.coe_mul] at hn
  exact EReal.coe_lt_coe_iff.mp hn
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction

theorem critical_program_le_nearest_average {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    {K N : ℕ} (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat y : Fin N → E)
    (hmax : ∀ i, ∀ x∈closure (finiteLossDomain Ξ (maxLoss ℓ)),
      ‖x-ξhat i‖=Metric.infDist (ξhat i) (finiteLossDomain Ξ (maxLoss ℓ)) →
      maxLoss ℓ x ≤ maxLoss ℓ (y i)) :
    program12cValue (finiteDomainCost Ξ (maxLoss ℓ) ξhat) Ξ ξhat (maxLoss ℓ) ≤
      ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, maxLoss ℓ (y i)) := by
  classical
  by_contra hh
  obtain ⟨r,hr,hrp⟩ := EReal.exists_between_coe_real (lt_of_not_ge hh)
  obtain ⟨R,hR,havg⟩ := exists_real_scores_lt_average (fun i => maxLoss ℓ (y i))
    (fun i => iSup_ne_top (fun k => hA.ne_top k (y i))) r hr
  have hp : ∀ i, ∃ lam : ℝ, 0 ≤ lam ∧ ∀ lam' : ℝ, lam≤lam' →
      (⨆ x∈Ξ, maxLoss ℓ x-((lam'*‖x-ξhat i‖ : ℝ) : EReal)) ≤
        ((R i-lam'*Metric.infDist (ξhat i) (finiteLossDomain Ξ (maxLoss ℓ)) : ℝ) : EReal) := by
    intro i
    obtain ⟨C,A,hA0,hupper⟩ := maxLoss_linear_upper Ξ ℓ hA (ξhat i)
    exact critical_envelope_small Ξ hA.closed (maxLoss ℓ)
      (maxLoss_upperSemicontinuous Ξ ℓ hA) (ξhat i) (y i) C A hA0
      (fun x _ => hupper x) (hmax i) (R i) (hR i)
  choose lam hnonneg hbound using hp
  let Λ : ℝ := ∑ i, lam i
  let s : Fin N → ℝ := fun i => R i-Λ*Metric.infDist (ξhat i) (finiteLossDomain Ξ (maxLoss ℓ))
  have hΛ : 0 ≤ Λ := Finset.sum_nonneg (fun i _ => hnonneg i)
  have he : ∀ i, (⨆ x∈Ξ, maxLoss ℓ x-((Λ*‖x-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal) :=
    fun i => hbound i Λ (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i))
  have hobj : Λ*finiteDomainCost Ξ (maxLoss ℓ) ξhat+(1/(N : ℝ))*∑ i, s i =
      (1/(N : ℝ))*∑ i, R i := by
    dsimp [s,finiteDomainCost]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum]
    ring
  have hprog : program12cValue (finiteDomainCost Ξ (maxLoss ℓ) ξhat) Ξ ξhat (maxLoss ℓ) ≤
      (((1/(N : ℝ))*∑ i, R i : ℝ) : EReal) := by
    unfold program12cValue
    apply iInf_le_of_le Λ
    apply iInf_le_of_le s
    apply iInf_le_of_le he
    apply iInf_le_of_le hΛ
    rw [hobj]
  exact (not_le_of_gt hrp) (hprog.trans (EReal.coe_le_coe_iff.mpr havg.le))
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction WassersteinDRO.Duality DupacovaWets.Consistency

theorem empirical_law_budget {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {N : ℕ} (hN : 0 < N) (Ξ : Set E) (ξhat y : Fin N → E)
    (hy : ∀ i, y i∈Ξ) (ε : ℝ)
    (hc : (1/(N : ℝ))*∑ i, ‖y i-ξhat i‖ ≤ ε) :
    empiricalDistribution y∈ambiguitySet ε 1 Ξ (empiricalDistribution ξhat) := by
  have hQ := empirical_probability hN y
  letI := hQ
  have hs : (empiricalDistribution y) Ξᶜ=0 := by
    simp [empiricalDistribution,Measure.smul_apply,Measure.finsetSum_apply,hy]
  obtain ⟨_,hfst,hsnd⟩ := empirical_coupling hN y ξhat
  have hb : wassersteinDistance 1 (empiricalDistribution y) (empiricalDistribution ξhat) ≤ ENNReal.ofReal ε := by
    rw [wasserstein_one_eq]
    apply le_trans (iInf_le _ (empiricalDistribution (fun i => (y i,ξhat i))))
    apply le_trans (iInf_le _ ⟨hfst,hsnd⟩)
    rw [←ofReal_integral_eq_lintegral_ofReal (empirical_integrable hN _ _)
      (Filter.Eventually.of_forall fun w => norm_nonneg _),empirical_integral]
    apply ENNReal.ofReal_le_ofReal
    simpa only [one_div] using hc
  exact ⟨measure_univ,hs,hb⟩

theorem empirical_law_value_le_worstCase {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {N : ℕ} (hN : 0 < N) (Ξ : Set E) (L : E → EReal) (ξhat y : Fin N → E)
    (hy : ∀ i, y i∈Ξ) (hne_top : ∀ i, L (y i)≠⊤) (ε : ℝ)
    (hc : (1/(N : ℝ))*∑ i, ‖y i-ξhat i‖ ≤ ε) :
    ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, L (y i)) ≤ worstCaseExpectation ε Ξ ξhat L := by
  have hmem := empirical_law_budget hN Ξ ξhat y hy ε hc
  have he := empirical_expect_eq_of_ne_top_samples hN y L hne_top
  rw [←he]
  exact le_iSup₂_of_le (empiricalDistribution y) hmem le_rfl
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction

theorem worstCase_eq_program12c_full {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E)
    (ε : ℝ) (hε : 0 ≤ ε) (hA : Assumption41 Ξ ℓ) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)=program12cValue ε Ξ ξhat (maxLoss ℓ) := by
  classical
  by_cases hne : ε≠finiteDomainCost Ξ (maxLoss ℓ) ξhat
  · exact positive_reduction_except_domain_boundary hK hN Ξ ℓ hmeas ξhat ε hε hA hne
  · have he : ε=finiteDomainCost Ξ (maxLoss ℓ) ξhat := not_ne_iff.mp hne
    let k0 : Fin K := ⟨0,hK⟩
    obtain ⟨x0,hx0,hL0⟩ := hA.not_bot_on k0
    have hn0 : maxLoss ℓ x0≠⊥ := by
      intro hh
      have hl := le_iSup (fun k => ℓ k x0) k0
      change ℓ k0 x0 ≤ maxLoss ℓ x0 at hl
      rw [hh] at hl
      exact hL0 (le_bot_iff.mp hl)
    have hp : ∀ i, ∃ y∈Ξ, ‖y-ξhat i‖=Metric.infDist (ξhat i) (finiteLossDomain Ξ (maxLoss ℓ)) ∧
        y∈closure (finiteLossDomain Ξ (maxLoss ℓ)) ∧
        ∀ x∈closure (finiteLossDomain Ξ (maxLoss ℓ)),
          ‖x-ξhat i‖=Metric.infDist (ξhat i) (finiteLossDomain Ξ (maxLoss ℓ)) →
          maxLoss ℓ x ≤ maxLoss ℓ y := by
      intro i
      exact nearest_finite_domain_max Ξ hA.closed (maxLoss ℓ)
        (maxLoss_upperSemicontinuous Ξ ℓ hA) ⟨x0,hx0,hn0⟩ (ξhat i)
    choose y hy hdist hcl hmax using hp
    have hav := empirical_law_value_le_worstCase hN Ξ (maxLoss ℓ) ξhat y hy
      (fun i => iSup_ne_top (fun k => hA.ne_top k (y i))) ε (by
        rw [he]
        simp only [hdist,finiteDomainCost]
        exact le_rfl)
    have hprog := critical_program_le_nearest_average Ξ ℓ hA ξhat y hmax
    rw [←he] at hprog
    exact le_antisymm (worstCase_le_program12c hN Ξ ℓ hmeas ξhat ε hε) (hprog.trans hav)
end WassReductionCodex

end

set_option autoImplicit false
open WassDDRO.Reduction
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (ε : ℝ) (hε : 0 ≤ ε) (hA : Assumption41 Ξ ℓ) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ) = program11Value ε Ξ ξhat ℓ := by
  calc
    _ = program12cValue ε Ξ ξhat (maxLoss ℓ) := WassReductionCodex.worstCase_eq_program12c_full hK hN Ξ ℓ hmeas ξhat ε hε hA
    _ = program12fValue ε Ξ ξhat ℓ := WassReductionCodex.program12c_eq_program12f hK hN Ξ ℓ hA ξhat ε
    _ = program11Value ε Ξ ξhat ℓ := WassReductionCodex.program12f_eq_program11_full hK hN Ξ ℓ hA ξhat ε



#print axioms solution
