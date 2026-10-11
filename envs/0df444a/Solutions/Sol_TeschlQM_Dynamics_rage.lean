-- Prove2me | solution 1 for TeschlQM.Dynamics.rage
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T01:47:24.30071+00:00
-- url     : https://prove2.me/submissions/6dc4acd7-3c92-40f9-9349-2a80dbeacd97

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Shared_IsSpectralIntegral
import Definitions.Def_TeschlQM_Shared_timeEvolution
import Definitions.Def_TeschlQM_Dynamics_spectralSubspaces
import Definitions.Def_TeschlQM_Dynamics_IsRelativelyCompact

open Filter Topology
open scoped ENNReal

-- BEGIN COMPLETE MODULE GramExtension
section

open scoped InnerProductSpace

namespace TeschlQM.Dynamics.Proof

variable {I E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma linearCombination_inner (e : I → E) (f : I → F)
    (h : ∀ i j, ⟪f i,f j⟫_ℂ = ⟪e i,e j⟫_ℂ) (a b : I →₀ ℂ) :
    ⟪Finsupp.linearCombination ℂ f a,Finsupp.linearCombination ℂ f b⟫_ℂ =
      ⟪Finsupp.linearCombination ℂ e a,Finsupp.linearCombination ℂ e b⟫_ℂ := by
  classical
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,sum_inner,inner_sum,
    inner_smul_left,inner_smul_right,h]

omit [CompleteSpace F] in
lemma linearCombination_norm (e : I → E) (f : I → F)
    (h : ∀ i j, ⟪f i,f j⟫_ℂ = ⟪e i,e j⟫_ℂ) (a : I →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ f a‖ = ‖Finsupp.linearCombination ℂ e a‖ := by
  have hi := congrArg Complex.re (linearCombination_inner e f h a a)
  simp only [inner_self_eq_norm_sq_to_K] at hi
  change ((‖Finsupp.linearCombination ℂ f a‖ : ℂ)^2).re =
    ((‖Finsupp.linearCombination ℂ e a‖ : ℂ)^2).re at hi
  simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hi
  nlinarith [norm_nonneg (Finsupp.linearCombination ℂ f a),norm_nonneg (Finsupp.linearCombination ℂ e a)]

noncomputable def gramExtension (e : I → E) (f : I → F) : E →L[ℂ] F :=
  (Finsupp.linearCombination ℂ f).extendOfNorm (Finsupp.linearCombination ℂ e)

lemma gramExtension_apply (e : I → E) (f : I → F)
    (hd : DenseRange (Finsupp.linearCombination ℂ e))
    (h : ∀ i j, ⟪f i,f j⟫_ℂ = ⟪e i,e j⟫_ℂ) (i : I) :
    gramExtension e f (e i) = f i := by
  have hb : ∃ C : ℝ, ∀ a, ‖Finsupp.linearCombination ℂ f a‖ ≤ C * ‖Finsupp.linearCombination ℂ e a‖ :=
    ⟨1,fun a => by rw [linearCombination_norm e f h a,one_mul]⟩
  simpa [gramExtension] using (LinearMap.extendOfNorm_eq hd hb (Finsupp.single i (1 : ℂ)))

lemma gramExtension_norm (e : I → E) (f : I → F)
    (hd : DenseRange (Finsupp.linearCombination ℂ e))
    (h : ∀ i j, ⟪f i,f j⟫_ℂ = ⟪e i,e j⟫_ℂ) (x : E) :
    ‖gramExtension e f x‖ = ‖x‖ := by
  have hb : ∃ C : ℝ, ∀ a, ‖Finsupp.linearCombination ℂ f a‖ ≤ C * ‖Finsupp.linearCombination ℂ e a‖ :=
    ⟨1,fun a => by rw [linearCombination_norm e f h a,one_mul]⟩
  refine hd.induction_on x (isClosed_eq (by fun_prop) continuous_norm) ?_
  intro a
  rw [gramExtension,LinearMap.extendOfNorm_eq hd hb]
  exact linearCombination_norm e f h a

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE GramExtension

-- BEGIN COMPLETE MODULE L2IndicatorSpan
section

open MeasureTheory
open scoped ENNReal

namespace TeschlQM.Dynamics.Proof

abbrev BorelSet := {S : Set ℝ // MeasurableSet S}

noncomputable def indicatorL2 (μ : Measure ℝ) [IsFiniteMeasure μ] (S : BorelSet) : Lp ℂ 2 μ :=
  indicatorConstLp 2 S.property (measure_ne_top μ S.val) (1 : ℂ)

lemma indicatorL2_smul (μ : Measure ℝ) [IsFiniteMeasure μ] (S : BorelSet) (c : ℂ) :
    c • indicatorL2 μ S = indicatorConstLp 2 S.property (measure_ne_top μ S.val) c := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul c (indicatorL2 μ S),indicatorConstLp_coeFn (p := 2) (hs := S.property)
    (hμs := measure_ne_top μ S.val) (c := (1 : ℂ)),indicatorConstLp_coeFn (p := 2) (hs := S.property)
    (hμs := measure_ne_top μ S.val) (c := c)] with x h1 h2 h3
  rw [h1,h3]
  change c * (indicatorL2 μ S) x = _
  change c * (indicatorConstLp 2 S.property (measure_ne_top μ S.val) (1 : ℂ)) x = _
  rw [h2]
  by_cases hx : x ∈ S.val <;> simp [Set.indicator,hx]

lemma indicatorL2_dense (μ : Measure ℝ) [IsFiniteMeasure μ] :
    DenseRange (Finsupp.linearCombination ℂ (indicatorL2 μ)) := by
  let V := LinearMap.range (Finsupp.linearCombination ℂ (indicatorL2 μ))
  have hall : ∀ x : Lp ℂ 2 μ, x ∈ V.topologicalClosure := by
    apply Lp.induction (by norm_num) (fun x => x ∈ V.topologicalClosure)
    · intro c S hS hμS
      have hm : indicatorL2 μ ⟨S,hS⟩ ∈ V := by
        exact ⟨Finsupp.single ⟨S,hS⟩ 1,by simp⟩
      have hs := V.topologicalClosure.smul_mem c (V.le_topologicalClosure hm)
      simpa only [indicatorL2_smul, Lp.simpleFunc.coe_indicatorConst] using hs
    · intro f g hf hg hfg hfm hgm
      exact V.topologicalClosure.add_mem hfm hgm
    · exact V.isClosed_topologicalClosure
  change Dense (Set.range (Finsupp.linearCombination ℂ (indicatorL2 μ)))
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_iff_forall.mpr
  exact hall

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE L2IndicatorSpan

-- BEGIN COMPLETE MODULE PVMBasic
section

open Filter Topology
open scoped InnerProductSpace

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma pvm_empty (hP : TeschlQM.Shared.IsProjValuedMeasure P) : P ∅ = 0 := by
  ext ψ
  have h := hP.2.2 (fun _ => ∅) (fun _ => MeasurableSet.empty)
    (fun _ _ _ => by simp) ψ
  simp only [Set.iUnion_empty] at h
  have hs := (h.comp (tendsto_add_atTop_nat 1)).sub h
  have he : (fun N : ℕ => (∑ k ∈ Finset.range (N+1), P ∅ ψ) -
      ∑ k ∈ Finset.range N, P ∅ ψ) = fun _ => P ∅ ψ := by
    funext N
    rw [Finset.sum_range_succ]
    abel
  simp only [Function.comp_apply, sub_self] at hs
  rw [he] at hs
  exact tendsto_nhds_unique tendsto_const_nhds hs

lemma pvm_projection (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {S : Set ℝ} (hS : MeasurableSet S) : IsStarProjection (P S) :=
  ⟨(hP.1 S hS).2,(hP.1 S hS).1⟩

lemma pvm_norm_le (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {S : Set ℝ} (hS : MeasurableSet S) (ψ : H) : ‖P S ψ‖ ≤ ‖ψ‖ := by
  calc
    ‖P S ψ‖ ≤ ‖P S‖ * ‖ψ‖ := (P S).le_opNorm ψ
    _ ≤ 1 * ‖ψ‖ := mul_le_mul_of_nonneg_right (pvm_projection hP hS).norm_le (norm_nonneg ψ)
    _ = ‖ψ‖ := one_mul _

lemma pvm_union (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hd : Disjoint S T) :
    P (S ∪ T) = P S + P T := by
  classical
  let E : ℕ → Set ℝ := fun k => if k = 0 then S else if k = 1 then T else ∅
  have hE : ∀ k, MeasurableSet (E k) := by intro k; dsimp [E]; split_ifs <;> first | assumption | exact MeasurableSet.empty
  have hdis : Pairwise (Function.onFun Disjoint E) := by
    intro i j hij
    dsimp [E,Function.onFun]
    split_ifs <;> simp_all [hd.symm]
  have hU : (⋃ k, E k) = S ∪ T := by
    ext x
    simp only [Set.mem_iUnion,Set.mem_union]
    constructor
    · rintro ⟨k,hk⟩
      dsimp [E] at hk
      split_ifs at hk <;> simp_all
    · rintro (hx | hx)
      · exact ⟨0,by simpa [E] using hx⟩
      · exact ⟨1,by simpa [E] using hx⟩
  ext ψ
  have hlim := hP.2.2 E hE hdis ψ
  rw [hU] at hlim
  have ht : ∀ k, P (E k) ψ = (if k=0 then P S ψ else 0) + (if k=1 then P T ψ else 0) := by
    intro k
    dsimp [E]
    split_ifs <;> simp_all [pvm_empty hP]
  have he : (fun N : ℕ => ∑ k ∈ Finset.range N, P (E k) ψ) =ᶠ[atTop]
      (fun _ => P S ψ + P T ψ) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp only [ht,Finset.sum_add_distrib]
    simp [show 0<N by omega,show 1<N by omega]

  exact (tendsto_nhds_unique hlim (tendsto_const_nhds.congr' he.symm))

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE PVMBasic

-- BEGIN COMPLETE MODULE ProjectionAlgebra
section

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma idempotent_add_mul_zero {p q : H →L[ℂ] H}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hs : IsIdempotentElem (p+q)) : p*q = 0 := by
  have he : p*q+q*p = 0 := by
    have hx : (p+q)+(p*q+q*p) = p+q := by
      calc
        _ = (p+q)*(p+q) := by
          simp only [add_mul,mul_add,hp.eq,hq.eq]
          abel
        _ = _ := hs.eq
    exact add_left_cancel (show (p+q)+(p*q+q*p) = (p+q)+0 by simpa using hx)
  have hl := congrArg (fun x => p*x) he
  have hr := congrArg (fun x => x*p) he
  simp only [mul_add,mul_zero,← mul_assoc,hp.eq] at hl
  simp only [add_mul,zero_mul,mul_assoc,hp.eq] at hr
  have hc : p*q = q*p := by
    calc
      p*q = -(p*q*p) := eq_neg_of_add_eq_zero_left hl
      _ = q*p := by
        apply neg_eq_of_add_eq_zero_left
        simpa [mul_assoc,add_comm] using hr
  rw [← hc] at he
  have h2 : (2 : ℂ) • (p*q) = 0 := by simpa [two_smul] using he
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE ProjectionAlgebra

-- BEGIN COMPLETE MODULE PVMIntersection
section

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma pvm_disjoint_mul (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hd : Disjoint S T) :
    P S * P T = 0 := by
  apply idempotent_add_mul_zero (hP.1 S hS).2 (hP.1 T hT).2
  rw [← pvm_union hP hS hT hd]
  exact (hP.1 (S ∪ T) (hS.union hT)).2

lemma pvm_subset_mul (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : S ⊆ T) :
    P S * P T = P S := by
  have hd : Disjoint S (T \ S) := Set.disjoint_sdiff_right
  have hu : S ∪ (T \ S) = T := Set.union_sdiff_cancel hST
  have hp := pvm_union hP hS (hT.diff hS) hd
  rw [hu] at hp
  rw [hp,mul_add,(hP.1 S hS).2.eq,pvm_disjoint_mul hP hS (hT.diff hS) hd,add_zero]

lemma pvm_inter (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    P S * P T = P (S ∩ T) := by
  have hd : Disjoint (S ∩ T) (S \ T) := by exact Set.disjoint_left.mpr (by intro x hx hy; exact hy.2 hx.2)
  have hu : (S ∩ T) ∪ (S \ T) = S := by ext x; simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_sdiff]; tauto
  have hp := pvm_union hP (hS.inter hT) (hS.diff hT) hd
  rw [hu] at hp
  conv_lhs => rw [hp]
  rw [add_mul,pvm_subset_mul hP (hS.inter hT) hT Set.inter_subset_right,
    pvm_disjoint_mul hP (hS.diff hT) hT Set.disjoint_sdiff_left,add_zero]

lemma pvm_commute (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) : Commute (P S) (P T) := by
  show P S * P T = P T * P S
  rw [pvm_inter hP hS hT,pvm_inter hP hT hS,Set.inter_comm]

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE PVMIntersection

-- BEGIN COMPLETE MODULE SpectralMeasureBasic
section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma pvm_inner_self (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {S : Set ℝ} (hS : MeasurableSet S) (ψ : H) :
    ⟪ψ,P S ψ⟫_ℂ = (‖P S ψ‖ : ℂ)^2 := by
  have ha : (P S).adjoint = P S := (hP.1 S hS).1
  calc
    ⟪ψ,P S ψ⟫_ℂ = ⟪ψ,(P S).adjoint (P S ψ)⟫_ℂ := by
      rw [ha]
      congr 1
      exact (congrArg (fun T : H →L[ℂ] H => T ψ) (hP.1 S hS).2.eq).symm
    _ = ⟪P S ψ,P S ψ⟫_ℂ := (P S).adjoint_inner_right ψ (P S ψ)
    _ = _ := inner_self_eq_norm_sq_to_K _

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma pvm_mass_ofReal (ψ : H) : ENNReal.ofReal (‖ψ‖^2) = (‖ψ‖₊ : ℝ≥0∞)^2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _)]
  simp only [← coe_nnnorm,ENNReal.ofReal_coe_nnreal]

lemma pvm_mass_additive (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H)
    (E : ℕ → Set ℝ) (hE : ∀ k, MeasurableSet (E k))
    (hd : Pairwise (Function.onFun Disjoint E)) :
    (‖P (⋃ k,E k) ψ‖₊ : ℝ≥0∞)^2 = ∑' k, (‖P (E k) ψ‖₊ : ℝ≥0∞)^2 := by
  have h := hP.2.2 E hE hd ψ
  have hr := ((Complex.continuous_re.comp
    (continuous_const.inner continuous_id : Continuous fun x : H => ⟪ψ,x⟫_ℂ)).tendsto _).comp h
  have hi : ∀ S, MeasurableSet S → (⟪ψ,P S ψ⟫_ℂ).re = ‖P S ψ‖^2 := by
    intro S hS
    rw [pvm_inner_self hP hS,← Complex.ofReal_pow,Complex.ofReal_re]
  have hs : Tendsto (fun N => ∑ k ∈ Finset.range N, ‖P (E k) ψ‖^2) atTop
      (𝓝 (‖P (⋃ k,E k) ψ‖^2)) := by
    simpa only [Function.comp_def,inner_sum,Complex.re_sum,hi _ (MeasurableSet.iUnion hE),hi _ (hE _)] using hr
  have hen := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hs
  have hsum : ∀ N, ENNReal.ofReal (∑ k ∈ Finset.range N, ‖P (E k) ψ‖^2) =
      ∑ k ∈ Finset.range N, (‖P (E k) ψ‖₊ : ℝ≥0∞)^2 := by
    intro N
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    simp only [pvm_mass_ofReal]
  simp only [Function.comp_def,hsum,pvm_mass_ofReal] at hen
  exact ((ENNReal.hasSum_iff_tendsto_nat _).mpr hen).tsum_eq.symm

lemma spectralMeasure_apply (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H)
    {S : Set ℝ} (hS : MeasurableSet S) :
    TeschlQM.Shared.spectralMeasure P ψ S = (‖P S ψ‖₊ : ℝ≥0∞)^2 := by
  have hgood : (‖P ∅ ψ‖₊ : ℝ≥0∞)^2 = 0 ∧
      ∀ ⦃E : ℕ → Set ℝ⦄, (∀ k,MeasurableSet (E k)) → Pairwise (Function.onFun Disjoint E) →
        (‖P (⋃ k,E k) ψ‖₊ : ℝ≥0∞)^2 = ∑' k,(‖P (E k) ψ‖₊ : ℝ≥0∞)^2 :=
    ⟨by simp [pvm_empty hP],by intro E hE hd; exact pvm_mass_additive hP ψ E hE hd⟩
  simp only [TeschlQM.Shared.spectralMeasure,dif_pos hgood]
  exact Measure.ofMeasurable_apply S hS

lemma spectralMeasure_univ (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) :
    TeschlQM.Shared.spectralMeasure P ψ Set.univ = (‖ψ‖₊ : ℝ≥0∞)^2 := by
  rw [spectralMeasure_apply hP ψ MeasurableSet.univ,hP.2.1]
  rfl

lemma spectralMeasure_finite (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) :
    IsFiniteMeasure (TeschlQM.Shared.spectralMeasure P ψ) := by
  constructor
  rw [spectralMeasure_univ hP]
  finiteness

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE SpectralMeasureBasic

-- BEGIN COMPLETE MODULE SpectralMeasureRestriction
section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma spectralMeasure_restrict (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H)
    {T : Set ℝ} (hT : MeasurableSet T) :
    TeschlQM.Shared.spectralMeasure P (P T ψ) = (TeschlQM.Shared.spectralMeasure P ψ).restrict T := by
  apply Measure.ext
  intro S hS
  rw [spectralMeasure_apply hP _ hS,Measure.restrict_apply hS,spectralMeasure_apply hP ψ (hS.inter hT)]
  have hi := congrArg (fun A : H →L[ℂ] H => A ψ) (pvm_inter hP hS hT)
  change P S (P T ψ) = P (S ∩ T) ψ at hi
  rw [hi]

lemma pvm_inner_pair (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ⟪P S ψ,P T ψ⟫_ℂ = ((TeschlQM.Shared.spectralMeasure P ψ).real (S ∩ T) : ℂ) := by
  have ha : (P S).adjoint = P S := (hP.1 S hS).1
  rw [← (P S).adjoint_inner_right,ha]
  have hi : P S (P T ψ) = P (S ∩ T) ψ := congrArg (fun A : H →L[ℂ] H => A ψ) (pvm_inter hP hS hT)
  rw [hi,pvm_inner_self hP (hS.inter hT)]
  rw [Measure.real,spectralMeasure_apply hP ψ (hS.inter hT),← pvm_mass_ofReal,
    ENNReal.toReal_ofReal (sq_nonneg _),Complex.ofReal_pow]

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE SpectralMeasureRestriction

-- BEGIN COMPLETE MODULE CyclicIsometry
section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

noncomputable def cyclicMap (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) :
    Lp ℂ 2 (TeschlQM.Shared.spectralMeasure P ψ) →L[ℂ] H := by
  letI := spectralMeasure_finite hP ψ
  exact gramExtension (indicatorL2 (TeschlQM.Shared.spectralMeasure P ψ))
    (fun S : BorelSet => P S.val ψ)

lemma cyclic_gram (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) (S T : BorelSet) :
    let := spectralMeasure_finite hP ψ
    ⟪P S.val ψ,P T.val ψ⟫_ℂ =
      ⟪indicatorL2 (TeschlQM.Shared.spectralMeasure P ψ) S,
       indicatorL2 (TeschlQM.Shared.spectralMeasure P ψ) T⟫_ℂ := by
  let := spectralMeasure_finite hP ψ
  rw [pvm_inner_pair hP ψ S.property T.property]
  exact (L2.inner_indicatorConstLp_one_indicatorConstLp_one S.property T.property).symm

lemma cyclicMap_indicator (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) (S : BorelSet) :
    let := spectralMeasure_finite hP ψ
    cyclicMap hP ψ (indicatorL2 (TeschlQM.Shared.spectralMeasure P ψ) S) = P S.val ψ := by
  let := spectralMeasure_finite hP ψ
  exact gramExtension_apply _ _ (indicatorL2_dense _) (cyclic_gram hP ψ) S

lemma cyclicMap_norm (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H)
    (f : Lp ℂ 2 (TeschlQM.Shared.spectralMeasure P ψ)) :
    ‖cyclicMap hP ψ f‖ = ‖f‖ := by
  let := spectralMeasure_finite hP ψ
  exact gramExtension_norm _ _ (indicatorL2_dense _) (cyclic_gram hP ψ) f

noncomputable def cyclicIsometry (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) :
    Lp ℂ 2 (TeschlQM.Shared.spectralMeasure P ψ) →ₗᵢ[ℂ] H :=
  ⟨(cyclicMap hP ψ).toLinearMap, cyclicMap_norm hP ψ⟩

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE CyclicIsometry

-- BEGIN COMPLETE MODULE SimpleCyclic
section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace TeschlQM.Dynamics.Proof

local infixr:25 " →ₛ " => SimpleFunc

lemma lp_sum_coe {I : Type*} (μ : Measure ℝ) (s : Finset I) (f : I → Lp ℂ 2 μ) :
    (fun x => (∑ i ∈ s, f i) x) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 μ
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s,f i),ih] with x h1 h2
    simp only [Pi.add_apply] at h1
    rw [h1,h2]

lemma simple_toLp_sum (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ →ₛ ℂ) :
    (f.memLp_of_isFiniteMeasure 2 μ).toLp f =
      ∑ c ∈ f.range, indicatorConstLp 2 (f.measurableSet_fiber c)
        (measure_ne_top μ _) c := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (f.memLp_of_isFiniteMeasure 2 μ),
    lp_sum_coe μ f.range (fun c => indicatorConstLp 2 (f.measurableSet_fiber c)
      (measure_ne_top μ _) c),
    (Filter.eventually_all_finset f.range).mpr (fun c hc => indicatorConstLp_coeFn (p := 2)
      (hs := f.measurableSet_fiber c) (hμs := measure_ne_top μ _) (c := c))] with x h1 h2 h3
  rw [h1,h2]
  have hh : (∑ c ∈ f.range, (indicatorConstLp 2 (f.measurableSet_fiber c) (measure_ne_top μ _) c) x) =
    ∑ c ∈ f.range, (f ⁻¹' {c}).indicator (fun _ => c) x :=
      Finset.sum_congr rfl (fun c hc => h3 c hc)
  rw [hh]
  classical
  rw [Finset.sum_eq_single (f x)]
  · simp
  · intro b hb hbx
    simp [Set.indicator, Ne.symm hbx]
  · exact fun h => (h (f.mem_range_self x)).elim

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

noncomputable def simplePvm (P : Set ℝ → (H →L[ℂ] H)) (f : ℝ →ₛ ℂ) : H →L[ℂ] H :=
  ∑ c ∈ f.range, c • P (f ⁻¹' {c})

lemma cyclicMap_simple (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) (f : ℝ →ₛ ℂ) :
    letI := spectralMeasure_finite hP ψ
    cyclicMap hP ψ ((f.memLp_of_isFiniteMeasure 2 _).toLp f) = simplePvm P f ψ := by
  let := spectralMeasure_finite hP ψ
  rw [simple_toLp_sum,map_sum]
  simp only [simplePvm,sum_apply,smul_apply]
  apply Finset.sum_congr rfl
  intro c hc
  rw [← indicatorL2_smul _ ⟨f ⁻¹' {c}, f.measurableSet_fiber c⟩ c,map_smul,cyclicMap_indicator]

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE SimpleCyclic

-- BEGIN COMPLETE MODULE CyclicApproximation
section

open MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology

namespace TeschlQM.Dynamics.Proof

noncomputable def simpleApprox (f : ℝ → ℂ) (hf : Measurable f) (n : ℕ) : SimpleFunc ℝ ℂ :=
  SimpleFunc.approxOn f hf Set.univ 0 (Set.mem_univ _) n

lemma simpleApprox_tendsto (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ → ℂ)
    (hf : Measurable f) (hm : MemLp f 2 μ) :
    Tendsto (fun n => ((simpleApprox f hf n).memLp_of_isFiniteMeasure 2 μ).toLp
      (simpleApprox f hf n)) atTop (𝓝 (hm.toLp f)) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
  apply SimpleFunc.tendsto_approxOn_Lp_eLpNorm hf (Set.mem_univ (0 : ℂ)) (by norm_num)
  · simp
  · simpa using hm.2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

noncomputable def cyclicEval (hP : TeschlQM.Shared.IsProjValuedMeasure P) (f : ℝ → ℂ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (ψ : H) : H := by
  letI := spectralMeasure_finite hP ψ
  exact cyclicMap hP ψ ((MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)).toLp f)

lemma simplePvm_tendsto (hP : TeschlQM.Shared.IsProjValuedMeasure P) (f : ℝ → ℂ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (ψ : H) :
    Tendsto (fun n => simplePvm P (simpleApprox f hf n) ψ) atTop
      (𝓝 (cyclicEval hP f hf C hC ψ)) := by
  let := spectralMeasure_finite hP ψ
  have hm : MemLp f 2 (TeschlQM.Shared.spectralMeasure P ψ) :=
    MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have ht := (cyclicMap hP ψ).continuous.tendsto (hm.toLp f) |>.comp
    (simpleApprox_tendsto _ f hf hm)
  simpa only [cyclicEval,Function.comp_def,cyclicMap_simple] using ht

lemma cyclicEval_bound (hP : TeschlQM.Shared.IsProjValuedMeasure P) (f : ℝ → ℂ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (ψ : H) :
    ‖cyclicEval hP f hf C hC ψ‖ ≤ C * ‖ψ‖ := by
  let := spectralMeasure_finite hP ψ
  have hm : MemLp f 2 (TeschlQM.Shared.spectralMeasure P ψ) :=
    MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  let e := indicatorL2 (TeschlQM.Shared.spectralMeasure P ψ) ⟨Set.univ,MeasurableSet.univ⟩
  have he : ‖e‖ = ‖ψ‖ := by
    rw [← cyclicMap_norm hP ψ e,cyclicMap_indicator,hP.2.1]
    rfl
  change ‖cyclicMap hP ψ (hm.toLp f)‖ ≤ _
  rw [cyclicMap_norm]
  rw [← he]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hm.coeFn_toLp,indicatorConstLp_coeFn (p := 2)
    (hs := MeasurableSet.univ) (hμs := measure_ne_top (TeschlQM.Shared.spectralMeasure P ψ) _)
    (c := (1 : ℂ))] with x hx he
  change ‖(hm.toLp f) x‖ ≤ C * ‖(indicatorConstLp 2 MeasurableSet.univ
    (measure_ne_top (TeschlQM.Shared.spectralMeasure P ψ) _) (1 : ℂ)) x‖
  rw [hx,he]
  simpa using hC x

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE CyclicApproximation

-- BEGIN COMPLETE MODULE BoundedCyclicOperator
section

open MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma cyclicEval_add (hP : TeschlQM.Shared.IsProjValuedMeasure P) (f : ℝ → ℂ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (ψ φ : H) :
    cyclicEval hP f hf C hC (ψ + φ) = cyclicEval hP f hf C hC ψ + cyclicEval hP f hf C hC φ := by
  apply tendsto_nhds_unique (simplePvm_tendsto hP f hf C hC (ψ+φ))
  simpa only [map_add] using (simplePvm_tendsto hP f hf C hC ψ).add
    (simplePvm_tendsto hP f hf C hC φ)

lemma cyclicEval_smul (hP : TeschlQM.Shared.IsProjValuedMeasure P) (f : ℝ → ℂ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (c : ℂ) (ψ : H) :
    cyclicEval hP f hf C hC (c • ψ) = c • cyclicEval hP f hf C hC ψ := by
  apply tendsto_nhds_unique (simplePvm_tendsto hP f hf C hC (c • ψ))
  simpa only [map_smul] using (simplePvm_tendsto hP f hf C hC ψ).const_smul c

noncomputable def boundedCyclicOperator (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := cyclicEval hP f hf C hC
      map_add' := cyclicEval_add hP f hf C hC
      map_smul' := cyclicEval_smul hP f hf C hC }
    C (cyclicEval_bound hP f hf C hC)

lemma cyclicMap_one (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) :
    letI := spectralMeasure_finite hP ψ
    cyclicMap hP ψ (indicatorL2 (TeschlQM.Shared.spectralMeasure P ψ)
      ⟨Set.univ,MeasurableSet.univ⟩) = ψ := by
  let := spectralMeasure_finite hP ψ
  rw [cyclicMap_indicator,hP.2.1]
  rfl

lemma boundedCyclicOperator_quadratic (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (ψ : H) :
    ⟪ψ,boundedCyclicOperator hP f hf C hC ψ⟫_ℂ =
      ∫ x, f x ∂TeschlQM.Shared.spectralMeasure P ψ := by
  let := spectralMeasure_finite hP ψ
  let e := indicatorL2 (TeschlQM.Shared.spectralMeasure P ψ) ⟨Set.univ,MeasurableSet.univ⟩
  have hm : MemLp f 2 (TeschlQM.Shared.spectralMeasure P ψ) :=
    MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  change ⟪ψ,cyclicMap hP ψ (hm.toLp f)⟫_ℂ = _
  nth_rw 1 [← cyclicMap_one hP ψ]
  change ⟪cyclicIsometry hP ψ e,cyclicIsometry hP ψ (hm.toLp f)⟫_ℂ = _
  rw [LinearIsometry.inner_map_map,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hm.coeFn_toLp,indicatorConstLp_coeFn (p := 2)
    (hs := MeasurableSet.univ) (hμs := measure_ne_top (TeschlQM.Shared.spectralMeasure P ψ) _)
    (c := (1 : ℂ))] with x hx he
  change ⟪(indicatorConstLp 2 MeasurableSet.univ
    (measure_ne_top (TeschlQM.Shared.spectralMeasure P ψ) _) (1 : ℂ)) x,(hm.toLp f) x⟫_ℂ = f x
  rw [hx,he]
  simp

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE BoundedCyclicOperator

-- BEGIN COMPLETE MODULE NativeBoundedIntegral
section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

omit [CompleteSpace H] in
lemma clm_quadratic_ext (A B : H →L[ℂ] H) (h : ∀ ψ, ⟪ψ,A ψ⟫_ℂ = ⟪ψ,B ψ⟫_ℂ) : A = B := by
  have he : A.toLinearMap = B.toLinearMap := (ext_inner_map _ _).mp (fun ψ => by
    change ⟪A ψ,ψ⟫_ℂ = ⟪B ψ,ψ⟫_ℂ
    simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) (h ψ))
  exact ContinuousLinearMap.coe_injective he

lemma boundedSpectralIntegral_eq (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    TeschlQM.Shared.boundedSpectralIntegral P f = boundedCyclicOperator hP f hf C hC := by
  classical
  have hex : ∃ T : H →L[ℂ] H, ∀ ψ, ⟪ψ,T ψ⟫_ℂ = ∫ x,f x ∂TeschlQM.Shared.spectralMeasure P ψ :=
    ⟨boundedCyclicOperator hP f hf C hC,boundedCyclicOperator_quadratic hP f hf C hC⟩
  rw [TeschlQM.Shared.boundedSpectralIntegral,dif_pos hex]
  apply clm_quadratic_ext
  intro ψ
  rw [hex.choose_spec ψ,boundedCyclicOperator_quadratic]

lemma boundedSpectralIntegral_apply (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (ψ : H) :
    TeschlQM.Shared.boundedSpectralIntegral P f ψ = cyclicEval hP f hf C hC ψ := by
  rw [boundedSpectralIntegral_eq hP f hf C hC]
  rfl

lemma boundedSpectralIntegral_bound (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (ψ : H) :
    ‖TeschlQM.Shared.boundedSpectralIntegral P f ψ‖ ≤ C * ‖ψ‖ := by
  rw [boundedSpectralIntegral_apply hP f hf C hC]
  exact cyclicEval_bound hP f hf C hC ψ

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE NativeBoundedIntegral

-- BEGIN COMPLETE MODULE CyclicPairing
section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma cyclic_pairing_density (hP : TeschlQM.Shared.IsProjValuedMeasure P) (φ ψ : H) :
    ∃ g : ℝ → ℂ, Integrable g (TeschlQM.Shared.spectralMeasure P ψ) ∧
      ∀ (f : ℝ → ℂ) (_hf : Measurable f) (C : ℝ) (_hC : ∀ x, ‖f x‖ ≤ C),
        ⟪φ,TeschlQM.Shared.boundedSpectralIntegral P f ψ⟫_ℂ =
          ∫ x,g x * f x ∂TeschlQM.Shared.spectralMeasure P ψ := by
  let := spectralMeasure_finite hP ψ
  let a := (cyclicMap hP ψ).adjoint φ
  let g : ℝ → ℂ := fun x => star (a x)
  have ha : Integrable (fun x => a x) (TeschlQM.Shared.spectralMeasure P ψ) :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp a)
  have hg : Integrable g (TeschlQM.Shared.spectralMeasure P ψ) := by
    apply ha.norm.mono' ?_ (ae_of_all _ (fun x => le_of_eq (norm_star (a x))))
    exact (continuous_star.comp_aestronglyMeasurable (Lp.aestronglyMeasurable a))
  refine ⟨g,hg,?_⟩
  intro f hf C hC
  rw [boundedSpectralIntegral_apply hP f hf C hC]
  have hm : MemLp f 2 (TeschlQM.Shared.spectralMeasure P ψ) :=
    MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  change ⟪φ,cyclicMap hP ψ (hm.toLp f)⟫_ℂ = _
  rw [← (cyclicMap hP ψ).adjoint_inner_left,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hm.coeFn_toLp] with x hx
  rw [hx]
  simp [a,g, RCLike.inner_apply, mul_comm]

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE CyclicPairing

-- BEGIN COMPLETE MODULE BoundedIntegralInner
section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma boundedIntegral_inner (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖g x‖ ≤ D) (ψ : H) :
    ⟪TeschlQM.Shared.boundedSpectralIntegral P f ψ,
      TeschlQM.Shared.boundedSpectralIntegral P g ψ⟫_ℂ =
      ∫ x, star (f x) * g x ∂TeschlQM.Shared.spectralMeasure P ψ := by
  let := spectralMeasure_finite hP ψ
  have hmf : MemLp f 2 (TeschlQM.Shared.spectralMeasure P ψ) :=
    MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have hmg : MemLp g 2 (TeschlQM.Shared.spectralMeasure P ψ) :=
    MemLp.of_bound hg.aestronglyMeasurable D (ae_of_all _ hD)
  rw [boundedSpectralIntegral_apply hP f hf C hC,boundedSpectralIntegral_apply hP g hg D hD]
  change ⟪cyclicIsometry hP ψ (hmf.toLp f),cyclicIsometry hP ψ (hmg.toLp g)⟫_ℂ = _
  rw [LinearIsometry.inner_map_map,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hmf.coeFn_toLp,hmg.coeFn_toLp] with x hx hy
  rw [hx,hy]
  simp only [RCLike.inner_apply, mul_comm]
  rfl

lemma boundedIntegral_quadratic (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (ψ : H) :
    ⟪ψ,TeschlQM.Shared.boundedSpectralIntegral P f ψ⟫_ℂ =
      ∫ x,f x ∂TeschlQM.Shared.spectralMeasure P ψ := by
  rw [boundedSpectralIntegral_eq hP f hf C hC]
  exact boundedCyclicOperator_quadratic hP f hf C hC ψ

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE BoundedIntegralInner

-- BEGIN COMPLETE MODULE BoundedIntegralAlgebra
section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma boundedIntegral_adjoint (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    (TeschlQM.Shared.boundedSpectralIntegral P f).adjoint =
      TeschlQM.Shared.boundedSpectralIntegral P (fun x => star (f x)) := by
  apply clm_quadratic_ext
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_right,← inner_conj_symm,
    boundedIntegral_quadratic hP f hf C hC,
    boundedIntegral_quadratic hP (fun x => star (f x)) (by fun_prop) C (fun x => by simpa using hC x)]
  exact (integral_conj (f := f)).symm

lemma boundedIntegral_mul (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖g x‖ ≤ D) :
    TeschlQM.Shared.boundedSpectralIntegral P (fun x => f x * g x) =
      TeschlQM.Shared.boundedSpectralIntegral P f * TeschlQM.Shared.boundedSpectralIntegral P g := by
  have hC0 := le_trans (norm_nonneg (f 0)) (hC 0)
  have hD0 := le_trans (norm_nonneg (g 0)) (hD 0)
  have hfg (x : ℝ) : ‖f x * g x‖ ≤ C * D := by
    rw [norm_mul]
    exact mul_le_mul (hC x) (hD x) (norm_nonneg _) hC0
  apply clm_quadratic_ext
  intro ψ
  rw [boundedIntegral_quadratic hP (fun x => f x * g x) (by fun_prop) (C*D) hfg]
  change _ = ⟪ψ,TeschlQM.Shared.boundedSpectralIntegral P f
    (TeschlQM.Shared.boundedSpectralIntegral P g ψ)⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left,boundedIntegral_adjoint hP f hf C hC,
    boundedIntegral_inner hP _ g (by fun_prop) hg C D (fun x => by simpa using hC x) hD]
  simp only [star_star]

lemma boundedIntegral_one (hP : TeschlQM.Shared.IsProjValuedMeasure P) :
    TeschlQM.Shared.boundedSpectralIntegral P (fun _ => (1 : ℂ)) = 1 := by
  apply clm_quadratic_ext
  intro ψ
  let := spectralMeasure_finite hP ψ
  rw [boundedIntegral_quadratic hP _ measurable_const 1 (fun _ => by simp)]
  change (∫ x, (1 : ℂ) ∂TeschlQM.Shared.spectralMeasure P ψ) = ⟪ψ,ψ⟫_ℂ
  rw [integral_const,inner_self_eq_norm_sq_to_K]
  simp only [Measure.real,spectralMeasure_univ hP ψ,← pvm_mass_ofReal,
    ENNReal.toReal_ofReal (sq_nonneg _)]
  simp [Complex.ofReal_pow]

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE BoundedIntegralAlgebra

-- BEGIN COMPLETE MODULE BoundedIntegralIndicator
section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma indicator_one_measurable {S : Set ℝ} (hS : MeasurableSet S) :
    Measurable (S.indicator (fun _ => (1 : ℂ))) := measurable_const.indicator hS

lemma indicator_one_bound (S : Set ℝ) (x : ℝ) :
    ‖S.indicator (fun _ => (1 : ℂ)) x‖ ≤ 1 := by
  classical
  by_cases hx : x ∈ S <;> simp [Set.indicator,hx]

lemma boundedIntegral_indicator (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {S : Set ℝ} (hS : MeasurableSet S) :
    TeschlQM.Shared.boundedSpectralIntegral P (S.indicator (fun _ => (1 : ℂ))) = P S := by
  apply clm_quadratic_ext
  intro ψ
  let := spectralMeasure_finite hP ψ
  rw [boundedIntegral_quadratic hP _ (indicator_one_measurable hS) 1 (indicator_one_bound S),
    integral_indicator hS,integral_const,pvm_inner_self hP hS]
  simp only [Measure.real,Measure.restrict_apply_univ,spectralMeasure_apply hP ψ hS,
    ← pvm_mass_ofReal,ENNReal.toReal_ofReal (sq_nonneg _)]
  simp [Complex.ofReal_pow]

lemma boundedIntegral_commute_projection (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    {S : Set ℝ} (hS : MeasurableSet S) :
    TeschlQM.Shared.boundedSpectralIntegral P f * P S =
      P S * TeschlQM.Shared.boundedSpectralIntegral P f := by
  rw [← boundedIntegral_indicator hP hS,
    ← boundedIntegral_mul hP _ _ hf (indicator_one_measurable hS) C 1 hC (indicator_one_bound S),
    ← boundedIntegral_mul hP _ _ (indicator_one_measurable hS) hf 1 C (indicator_one_bound S) hC]
  congr 1
  funext x
  exact mul_comm _ _

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE BoundedIntegralIndicator

-- BEGIN COMPLETE MODULE CesaroKernel
section

open MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace TeschlQM.Dynamics.Proof

noncomputable def cesaroKernel (T x : ℝ) : ℂ :=
  (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))

lemma oscillation_norm (x t : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

lemma cesaroKernel_norm_le (T x : ℝ) : ‖cesaroKernel T x‖ ≤ 1 := by
  by_cases hT : T = 0
  · simp [cesaroKernel, hT]
  have hb : ‖∫ t in (0 : ℝ)..T, Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))‖ ≤ |T| := by
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := T) (C := (1 : ℝ)) (fun t _ => (oscillation_norm x t).le)
  rw [cesaroKernel, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  calc
    |T|⁻¹ * ‖∫ t in (0 : ℝ)..T, Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))‖
      ≤ |T|⁻¹ * |T| := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 1 := inv_mul_cancel₀ (abs_ne_zero.mpr hT)

lemma cesaroKernel_zero {T : ℝ} (hT : T ≠ 0) : cesaroKernel T 0 = 1 := by
  simp [cesaroKernel, hT]

lemma cesaroKernel_formula {x : ℝ} (hx : x ≠ 0) (T : ℝ) :
    cesaroKernel T x = (T : ℂ)⁻¹ *
      ((Complex.exp (Complex.I * (x : ℂ) * (T : ℂ)) - 1) / (Complex.I * (x : ℂ))) := by
  unfold cesaroKernel
  rw [integral_exp_mul_complex (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hx))]
  simp

lemma cesaroKernel_norm_decay {x : ℝ} (hx : x ≠ 0) {T : ℝ} (hT : 0 < T) :
    ‖cesaroKernel T x‖ ≤ (2 / |x|) / T := by
  rw [cesaroKernel_formula hx, norm_mul, norm_inv, norm_div, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hT]
  have hb : ‖Complex.exp (Complex.I * (x : ℂ) * (T : ℂ)) - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖Complex.exp (Complex.I * (x : ℂ) * (T : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [oscillation_norm]; norm_num
  calc
    T⁻¹ * (‖Complex.exp (Complex.I * (x : ℂ) * (T : ℂ)) - 1‖ / |x|)
      ≤ T⁻¹ * (2 / |x|) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hb (abs_nonneg _)) (by positivity)
    _ = (2 / |x|) / T := by ring

lemma cesaroKernel_tendsto {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun T : ℝ => cesaroKernel T x) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    ((eventually_gt_atTop (0 : ℝ)).mono fun _ hT => cesaroKernel_norm_decay hx hT)
  simpa only [mul_zero, div_eq_mul_inv] using
    (tendsto_inv_atTop_zero.const_mul (2 / |x|))

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE CesaroKernel

-- BEGIN COMPLETE MODULE CesaroProduct
section

open MeasureTheory Filter Topology

namespace TeschlQM.Dynamics.Proof

lemma cesaroKernel_measurable (T : ℝ) : Measurable (cesaroKernel T) := by
  by_cases hT : T = 0
  · subst T
    change Measurable (fun x => cesaroKernel 0 x)
    simpa only [cesaroKernel, Complex.ofReal_zero, inv_zero, zero_mul] using
      (measurable_const : Measurable (fun _ : ℝ => (0 : ℂ)))
  have he : cesaroKernel T = fun x : ℝ => if x = 0 then 1 else
      (T : ℂ)⁻¹ * ((Complex.exp (Complex.I * (x : ℂ) * (T : ℂ)) - 1) /
        (Complex.I * (x : ℂ))) := by
    funext x
    split_ifs with hx
    · subst x
      exact cesaroKernel_zero hT
    · exact cesaroKernel_formula hx T
  rw [he]
  apply Measurable.ite (measurableSet_singleton 0) measurable_const
  fun_prop

lemma ae_prod_ne (μ : Measure ℝ) [SFinite μ] (hμ : ∀ x : ℝ, μ {x} = 0) :
    ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, p.1 ≠ p.2 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
  exact Eventually.of_forall fun x => by simpa [ae_iff] using hμ x

lemma cesaro_product_tendsto (μ : Measure ℝ) [SFinite μ]
    (hμ : ∀ x : ℝ, μ {x} = 0) (F : ℝ × ℝ → ℂ)
    (hF : Integrable F (μ.prod μ)) :
    Tendsto (fun T : ℝ => ∫ p, F p * cesaroKernel T (p.1 - p.2) ∂μ.prod μ)
      atTop (𝓝 0) := by
  have hd := tendsto_integral_filter_of_dominated_convergence
    (μ := μ.prod μ) (l := atTop) (F := fun T p => F p * cesaroKernel T (p.1 - p.2))
    (f := fun _ => (0 : ℂ)) (fun p => ‖F p‖)
  have hm : ∀ T : ℝ, AEStronglyMeasurable
      (fun p : ℝ × ℝ => F p * cesaroKernel T (p.1 - p.2)) (μ.prod μ) := by
    intro T
    exact hF.aestronglyMeasurable.mul
      ((cesaroKernel_measurable T).comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  have hb : ∀ T p, ‖F p * cesaroKernel T (p.1 - p.2)‖ ≤ ‖F p‖ := by
    intro T p
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (cesaroKernel_norm_le _ _)
  have hl : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ,
      Tendsto (fun T : ℝ => F p * cesaroKernel T (p.1 - p.2)) atTop (𝓝 0) := by
    filter_upwards [ae_prod_ne μ hμ] with p hp
    simpa using (cesaroKernel_tendsto (sub_ne_zero.mpr hp)).const_mul (F p)
  simpa using hd (Eventually.of_forall hm)
    (Eventually.of_forall fun T => Eventually.of_forall (hb T)) hF.norm hl

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE CesaroProduct

-- BEGIN COMPLETE MODULE CesaroFubini
section

open MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace TeschlQM.Dynamics.Proof

lemma oscillation_product (t x y : ℝ) :
    Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) *
      conj (Complex.exp (Complex.I * (y : ℂ) * (t : ℂ))) =
        Complex.exp (Complex.I * ((x - y : ℝ) : ℂ) * (t : ℂ)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub]
  ring

lemma fourier_square_product (μ : Measure ℝ) [SFinite μ] (g : ℝ → ℂ) (t : ℝ) :
    ((‖∫ x, g x * Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) ∂μ‖ ^ 2 : ℝ) : ℂ) =
      ∫ p : ℝ × ℝ, (g p.1 * conj (g p.2)) *
        Complex.exp (Complex.I * ((p.1 - p.2 : ℝ) : ℂ) * (t : ℂ)) ∂μ.prod μ := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', ← integral_conj, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [map_mul]
  rw [← oscillation_product]
  ring

lemma cesaro_fubini (μ : Measure ℝ) [SFinite μ] (F : ℝ × ℝ → ℂ)
    (hF : Integrable F (μ.prod μ)) {T : ℝ} (hT : 0 ≤ T) :
    (T : ℂ)⁻¹ * (∫ t in (0 : ℝ)..T, ∫ p : ℝ × ℝ,
      F p * Complex.exp (Complex.I * ((p.1 - p.2 : ℝ) : ℂ) * (t : ℂ)) ∂μ.prod μ) =
      ∫ p : ℝ × ℝ, F p * cesaroKernel T (p.1 - p.2) ∂μ.prod μ := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 T)
  have hb : Integrable (fun z : ℝ × (ℝ × ℝ) => ‖F z.2‖) (ν.prod (μ.prod μ)) := by
    simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) ν).mul_prod hF.norm
  have hm : AEStronglyMeasurable (fun z : ℝ × (ℝ × ℝ) => F z.2 *
      Complex.exp (Complex.I * ((z.2.1 - z.2.2 : ℝ) : ℂ) * (z.1 : ℂ))) (ν.prod (μ.prod μ)) := by
    apply hF.aestronglyMeasurable.comp_snd.mul
    exact (by fun_prop : Continuous (fun z : ℝ × (ℝ × ℝ) =>
      Complex.exp (Complex.I * ((z.2.1 - z.2.2 : ℝ) : ℂ) * (z.1 : ℂ)))).aestronglyMeasurable
  have hi := hb.mono' hm (Eventually.of_forall fun z => by
    rw [norm_mul, oscillation_norm, mul_one])
  simp only [intervalIntegral.integral_of_le hT]
  rw [integral_integral_swap hi, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [integral_const_mul]
  simp only [cesaroKernel, intervalIntegral.integral_of_le hT]
  ring

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE CesaroFubini

-- BEGIN COMPLETE MODULE WienerAtomless
section

open MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace TeschlQM.Dynamics.Proof

lemma wiener_atomless (μ : Measure ℝ) [SFinite μ]
    (hμ : ∀ x : ℝ, μ {x} = 0) (g : ℝ → ℂ) (hg : Integrable g μ) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T,
      ‖∫ x, g x * Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) ∂μ‖ ^ 2)
      atTop (𝓝 0) := by
  have hgc : Integrable (fun x => conj (g x)) μ := by
    apply hg.norm.mono'
    · exact Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable
    · filter_upwards [] with x
      simp
  have hd := cesaro_product_tendsto μ hμ (fun p => g p.1 * conj (g p.2))
    (hg.mul_prod hgc)
  have he : ∀ T : ℝ, 0 ≤ T →
      ∫ p : ℝ × ℝ, (g p.1 * conj (g p.2)) * cesaroKernel T (p.1 - p.2) ∂μ.prod μ =
        (((1 / T) * ∫ t in (0 : ℝ)..T,
          ‖∫ x, g x * Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) ∂μ‖ ^ 2 : ℝ) : ℂ) := by
    intro T hT
    rw [← cesaro_fubini μ _ (hg.mul_prod hgc) hT]
    simp_rw [← fourier_square_product]
    simp only [intervalIntegral.integral_of_le hT, integral_complex_ofReal,
      Complex.ofReal_mul, one_div, Complex.ofReal_inv]
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hd
  simp only [Complex.zero_re] at hreal
  apply hreal.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  simp only [Function.comp_apply]
  rw [he T hT]
  rfl

lemma wiener_atomless_neg (μ : Measure ℝ) [SFinite μ]
    (hμ : ∀ x : ℝ, μ {x} = 0) (g : ℝ → ℂ) (hg : Integrable g μ) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T,
      ‖∫ x, g x * Complex.exp (-(Complex.I * (t : ℂ) * (x : ℂ))) ∂μ‖ ^ 2)
      atTop (𝓝 0) := by
  have hgc : Integrable (fun x => conj (g x)) μ := by
    apply hg.norm.mono'
    · exact Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable
    · filter_upwards [] with x
      simp
  have he : ∀ t : ℝ,
      (∫ x, g x * Complex.exp (-(Complex.I * (t : ℂ) * (x : ℂ))) ∂μ) =
        conj (∫ x, conj (g x) * Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) ∂μ) := by
    intro t
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [map_mul, starRingEnd_self_apply, ← Complex.exp_conj,
      Complex.conj_I, Complex.conj_ofReal]
    congr 2
    ring
  simp_rw [he, RCLike.norm_conj]
  exact wiener_atomless μ hμ _ hgc

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE WienerAtomless

-- BEGIN COMPLETE MODULE CesaroAtom
section

open MeasureTheory Filter Topology

namespace TeschlQM.Dynamics.Proof

lemma cesaroKernel_tendsto_zero_frequency :
    Tendsto (fun T : ℝ => cesaroKernel T 0) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact (cesaroKernel_zero hT.ne').symm

lemma cesaro_atom_tendsto (μ : Measure ℝ) (g : ℝ → ℂ) (hg : Integrable g μ) (a : ℝ) :
    Tendsto (fun T : ℝ => ∫ x, g x * cesaroKernel T (a-x) ∂μ)
      atTop (𝓝 (∫ x in {a}, g x ∂μ)) := by
  have hd := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := atTop) (F := fun T x => g x * cesaroKernel T (a-x))
    (f := Set.indicator {a} g) (fun x => ‖g x‖)
  have hm : ∀ T : ℝ, AEStronglyMeasurable (fun x => g x * cesaroKernel T (a-x)) μ := by
    intro T
    exact hg.aestronglyMeasurable.mul
      ((cesaroKernel_measurable T).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hb : ∀ T x, ‖g x * cesaroKernel T (a-x)‖ ≤ ‖g x‖ := by
    intro T x
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (cesaroKernel_norm_le _ _)
  have hl : ∀ x : ℝ, Tendsto (fun T : ℝ => g x * cesaroKernel T (a-x))
      atTop (𝓝 (Set.indicator {a} g x)) := by
    intro x
    by_cases hx : x = a
    · subst x
      simpa using cesaroKernel_tendsto_zero_frequency.const_mul (g a)
    · simpa [Set.indicator_of_notMem, hx] using
        (cesaroKernel_tendsto (sub_ne_zero.mpr (Ne.symm hx))).const_mul (g x)
  simpa only [integral_indicator (measurableSet_singleton a)] using
    hd (Eventually.of_forall hm) (Eventually.of_forall fun T => Eventually.of_forall (hb T))
      hg.norm (Eventually.of_forall hl)

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE CesaroAtom

-- BEGIN COMPLETE MODULE AtomPairingMean
section

open MeasureTheory Filter Topology

namespace TeschlQM.Dynamics.Proof

lemma cesaro_frequency_fubini (μ : Measure ℝ) [SFinite μ] (g : ℝ → ℂ)
    (hg : Integrable g μ) (a : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (T : ℂ)⁻¹ * (∫ t in (0 : ℝ)..T, ∫ x,
      g x * Complex.exp (Complex.I * ((a-x : ℝ) : ℂ) * (t : ℂ)) ∂μ) =
      ∫ x, g x * cesaroKernel T (a-x) ∂μ := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 T)
  have hb : Integrable (fun z : ℝ × ℝ => ‖g z.2‖) (ν.prod μ) := by
    simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) ν).mul_prod hg.norm
  have hm : AEStronglyMeasurable (fun z : ℝ × ℝ => g z.2 *
      Complex.exp (Complex.I * ((a-z.2 : ℝ) : ℂ) * (z.1 : ℂ))) (ν.prod μ) := by
    apply hg.aestronglyMeasurable.comp_snd.mul
    exact (by fun_prop : Continuous (fun z : ℝ × ℝ =>
      Complex.exp (Complex.I * ((a-z.2 : ℝ) : ℂ) * (z.1 : ℂ)))).aestronglyMeasurable
  have hi := hb.mono' hm (Eventually.of_forall fun z => by
    rw [norm_mul, oscillation_norm, mul_one])
  simp only [intervalIntegral.integral_of_le hT]
  rw [integral_integral_swap hi, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [integral_const_mul]
  simp only [cesaroKernel, intervalIntegral.integral_of_le hT]
  ring

lemma atom_pairing_mean (μ : Measure ℝ) [SFinite μ] (g : ℝ → ℂ)
    (hg : Integrable g μ) (a : ℝ) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
      Complex.exp (Complex.I * (a : ℂ) * (t : ℂ)) *
        (∫ x, g x * Complex.exp (-(Complex.I * (t : ℂ) * (x : ℂ))) ∂μ))
      atTop (𝓝 (∫ x in {a}, g x ∂μ)) := by
  apply (cesaro_atom_tendsto μ g hg a).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [← cesaro_frequency_fubini μ g hg a hT]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  calc
    g x * Complex.exp (Complex.I * ((a-x : ℝ) : ℂ) * (t : ℂ)) =
      g x * (Complex.exp (Complex.I * (a : ℂ) * (t : ℂ)) *
        Complex.exp (-(Complex.I * (t : ℂ) * (x : ℂ)))) := by
          rw [← Complex.exp_add]
          congr 2
          push_cast
          ring
    _ = _ := by ring

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE AtomPairingMean

-- BEGIN COMPLETE MODULE TimeMean
section

open MeasureTheory Filter Topology

namespace TeschlQM.Dynamics.Proof

noncomputable def timeMean (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  T⁻¹ * ∫ t in (0 : ℝ)..T, f t

lemma timeMean_nonneg {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ timeMean f T := by
  exact mul_nonneg (inv_nonneg.mpr hT) (intervalIntegral.integral_nonneg_of_forall hT hf)

lemma timeMean_const (c : ℝ) {T : ℝ} (hT : T ≠ 0) : timeMean (fun _ => c) T = c := by
  simp [timeMean, hT]

lemma timeMean_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ t, f t ≤ g t) {T : ℝ} (hT : 0 ≤ T) : timeMean f T ≤ timeMean g T := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hT)
  exact intervalIntegral.integral_mono_on hT (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _) (fun t _ => hfg t)

lemma timeMean_sq_control (f : ℝ → ℝ) (hf : Continuous f) {ε T : ℝ}
    (hε : 0 < ε) (hT : 0 < T) :
    timeMean f T ≤ ε / 2 + timeMean (fun t => (f t)^2) T / (2 * ε) := by
  have hb : ∀ t, f t ≤ ε / 2 + (f t)^2 / (2 * ε) := by
    intro t
    have hs := sq_nonneg (f t - ε)
    have hh : f t ≤ (ε^2 + (f t)^2) / (2*ε) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith)
    convert hh using 1
    field_simp
  have hi := timeMean_mono hf (by fun_prop) hb hT.le
  unfold timeMean at *
  have h0 : IntervalIntegrable (fun _ : ℝ => ε / 2) volume 0 T := continuous_const.intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun t : ℝ => (f t)^2 / (2*ε)) volume 0 T :=
    (by fun_prop : Continuous (fun t : ℝ => (f t)^2 / (2*ε))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h0 h1,
    intervalIntegral.integral_const, intervalIntegral.integral_div] at hi
  simp only [sub_zero, smul_eq_mul] at hi
  convert hi using 1
  field_simp

lemma timeMean_tendsto_of_sq (f : ℝ → ℝ) (hf : Continuous f) (hn : ∀ t, 0 ≤ f t)
    (hs : Tendsto (fun T => timeMean (fun t => (f t)^2) T) atTop (𝓝 0)) :
    Tendsto (timeMean f) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact ha.trans_le (timeMean_nonneg hn hT)
  · intro b hb
    have hs' := hs.eventually (gt_mem_nhds (sq_pos_of_pos hb))
    filter_upwards [eventually_gt_atTop (0 : ℝ), hs'] with T hT hsT
    have hc := timeMean_sq_control f hf hb hT
    have hd : timeMean (fun t => (f t)^2) T / (2*b) < b/2 := by
      apply (div_lt_iff₀ (by positivity : 0 < 2*b)).mpr
      nlinarith
    linarith

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE TimeMean

-- BEGIN COMPLETE MODULE NativePairings
section

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma native_phase_norm (t x : ℝ) :
    ‖Complex.exp (-(Complex.I*(t : ℂ)*(x : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

lemma native_wiener (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ φ : H)
    (hψ : ∀ x : ℝ, TeschlQM.Shared.spectralMeasure P ψ {x} = 0) :
    Tendsto (timeMean (fun t => ‖⟪φ,TeschlQM.Shared.timeEvolution P t ψ⟫_ℂ‖^2)) atTop (𝓝 0) := by
  let := spectralMeasure_finite hP ψ
  obtain ⟨g,hg,hpair⟩ := cyclic_pairing_density hP φ ψ
  have he : ∀ t : ℝ, ⟪φ,TeschlQM.Shared.timeEvolution P t ψ⟫_ℂ =
      ∫ x, g x * Complex.exp (-(Complex.I*(t : ℂ)*(x : ℂ))) ∂TeschlQM.Shared.spectralMeasure P ψ := by
    intro t
    exact hpair _ (by fun_prop) 1 (fun x => (native_phase_norm t x).le)
  unfold timeMean
  simpa only [he, one_div] using wiener_atomless_neg _ hψ g hg

lemma native_atom_mean (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ φ : H) (a : ℝ) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
      Complex.exp (Complex.I*(a : ℂ)*(t : ℂ)) * ⟪φ,TeschlQM.Shared.timeEvolution P t ψ⟫_ℂ)
      atTop (𝓝 ⟪φ,P {a} ψ⟫_ℂ) := by
  let := spectralMeasure_finite hP ψ
  obtain ⟨g,hg,hpair⟩ := cyclic_pairing_density hP φ ψ
  have he : ∀ t : ℝ, ⟪φ,TeschlQM.Shared.timeEvolution P t ψ⟫_ℂ =
      ∫ x, g x * Complex.exp (-(Complex.I*(t : ℂ)*(x : ℂ))) ∂TeschlQM.Shared.spectralMeasure P ψ := by
    intro t
    exact hpair _ (by fun_prop) 1 (fun x => (native_phase_norm t x).le)
  have hp := hpair (Set.indicator {a} (fun _ => (1 : ℂ)))
    (indicator_one_measurable (measurableSet_singleton a)) 1 (indicator_one_bound {a})
  rw [boundedIntegral_indicator hP (measurableSet_singleton a)] at hp
  have hi : (∫ x, g x * Set.indicator {a} (fun _ => (1 : ℂ)) x ∂TeschlQM.Shared.spectralMeasure P ψ) =
      ∫ x in {a}, g x ∂TeschlQM.Shared.spectralMeasure P ψ := by
    rw [← integral_indicator (measurableSet_singleton a)]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x = a <;> simp [Set.indicator,hx]
  rw [hi] at hp
  simpa only [he,hp] using atom_pairing_mean _ g hg a

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE NativePairings

-- BEGIN COMPLETE MODULE PairingMeanBound
section

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma pairing_mean_norm_bound (f : ℝ → H) (hf : Continuous f) (φ : H) (a : ℝ)
    {T : ℝ} (hT : 0 < T) :
    ‖(T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
      Complex.exp (Complex.I*(a : ℂ)*(t : ℂ)) * ⟪φ,f t⟫_ℂ‖ ≤
        ‖φ‖ * timeMean (fun t => ‖f t‖) T := by
  have hi : ‖∫ t in (0 : ℝ)..T,
      Complex.exp (Complex.I*(a : ℂ)*(t : ℂ)) * ⟪φ,f t⟫_ℂ‖ ≤
        ∫ t in (0 : ℝ)..T, ‖φ‖*‖f t‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le hT.le
    · filter_upwards [] with t _
      rw [norm_mul,oscillation_norm,one_mul]
      exact norm_inner_le_norm _ _
    · exact (continuous_const.mul hf.norm).intervalIntegrable _ _
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  calc
    _ ≤ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖φ‖*‖f t‖ :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by rw [intervalIntegral.integral_const_mul]; unfold timeMean; ring

lemma norm_le_mean_limit (f : ℝ → H) (hf : Continuous f) (v : H) (a L : ℝ)
    (hL : Tendsto (timeMean (fun t => ‖f t‖)) atTop (𝓝 L))
    (hv : ∀ φ : H, Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
      Complex.exp (Complex.I*(a : ℂ)*(t : ℂ)) * ⟪φ,f t⟫_ℂ) atTop (𝓝 ⟪φ,v⟫_ℂ)) :
    ‖v‖ ≤ L := by
  have hL0 : 0 ≤ L := ge_of_tendsto hL
    ((eventually_ge_atTop (0 : ℝ)).mono fun T hT => timeMean_nonneg (fun _ => norm_nonneg _) hT)
  have hh := le_of_tendsto_of_tendsto (hv v).norm (hL.const_mul ‖v‖)
    ((eventually_gt_atTop (0 : ℝ)).mono fun T hT => pairing_mean_norm_bound f hf v a hT)
  have he : ‖⟪v,v⟫_ℂ‖ = ‖v‖^2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [he] at hh
  by_cases hz : v = 0
  · simpa [hz] using hL0
  · have hp := norm_pos_iff.mpr hz
    nlinarith

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE PairingMeanBound

-- BEGIN COMPLETE MODULE ContinuousSubspace
section

open MeasureTheory
open scoped ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma spectralMeasure_zero_iff (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H)
    {S : Set ℝ} (hS : MeasurableSet S) :
    TeschlQM.Shared.spectralMeasure P ψ S = 0 ↔ P S ψ = 0 := by
  rw [spectralMeasure_apply hP ψ hS]
  simp

lemma pvm_complement_sum (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H)
    {S : Set ℝ} (hS : MeasurableSet S) : P S ψ + P Sᶜ ψ = ψ := by
  have hh := congrArg (fun T : H →L[ℂ] H => T ψ)
    (pvm_union hP hS hS.compl disjoint_compl_right)
  simpa [hP.2.1] using hh.symm

lemma hc_iff_atomless (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) :
    ψ ∈ TeschlQM.Dynamics.hc P ↔
      ∀ x : ℝ, TeschlQM.Shared.spectralMeasure P ψ {x} = 0 := by
  constructor
  · rintro ⟨a, ha, s, hs, rfl⟩ x
    apply (spectralMeasure_zero_iff hP _ (measurableSet_singleton x)).mpr
    have ha0 : P {x} a = 0 := (spectralMeasure_zero_iff hP _ (measurableSet_singleton x)).mp
      (ha (measure_singleton x))
    have hs0 : P {x} s = 0 := (spectralMeasure_zero_iff hP _ (measurableSet_singleton x)).mp (hs.2 x)
    simp [ha0, hs0]
  · intro hψ
    let μ := TeschlQM.Shared.spectralMeasure P ψ
    let : IsFiniteMeasure μ := spectralMeasure_finite hP ψ
    obtain ⟨S,hS,hSing,hVol⟩ := Measure.mutuallySingular_singularPart μ volume
    have hac : μ.restrict S ≪ volume := by
      rw [← Measure.singularPart_add_rnDeriv μ volume, Measure.restrict_add,
        Measure.restrict_eq_zero.mpr hSing, zero_add]
      exact Measure.restrict_le_self.absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
    have hsc : μ.restrict Sᶜ ⟂ₘ volume := by
      rw [← Measure.singularPart_eq_restrict (by simpa using hSing) hVol]
      exact Measure.mutuallySingular_singularPart μ volume
    refine ⟨P S ψ, ?_, P Sᶜ ψ, ?_, (pvm_complement_sum hP ψ hS).symm⟩
    · change TeschlQM.Shared.spectralMeasure P (P S ψ) ≪ volume
      rw [spectralMeasure_restrict hP ψ hS]
      exact hac
    · constructor
      · rw [spectralMeasure_restrict hP ψ hS.compl]
        exact hsc
      · intro x
        rw [spectralMeasure_restrict hP ψ hS.compl]
        exact le_antisymm ((Measure.restrict_le_self _).trans_eq (hψ x)) (by positivity)

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE ContinuousSubspace

-- BEGIN COMPLETE MODULE PointContinuousSplit
section

open MeasureTheory

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma spectral_atoms_countable (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) :
    Set.Countable {x : ℝ | TeschlQM.Shared.spectralMeasure P ψ {x} ≠ 0} := by
  let : IsFiniteMeasure (TeschlQM.Shared.spectralMeasure P ψ) := spectralMeasure_finite hP ψ
  have h := Measure.countable_meas_level_set_pos
    (μ := TeschlQM.Shared.spectralMeasure P ψ) (g := (id : ℝ → ℝ)) measurable_id
  simpa [pos_iff_ne_zero] using h

lemma point_continuous_split (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) :
    ∃ p ∈ TeschlQM.Dynamics.hpp P, ∃ c ∈ TeschlQM.Dynamics.hc P, ψ = p+c := by
  let D := {x : ℝ | TeschlQM.Shared.spectralMeasure P ψ {x} ≠ 0}
  have hDc : D.Countable := spectral_atoms_countable hP ψ
  have hD : MeasurableSet D := hDc.measurableSet
  refine ⟨P D ψ, ?_, P Dᶜ ψ, ?_, (pvm_complement_sum hP ψ hD).symm⟩
  · refine ⟨D,hDc,?_⟩
    rw [spectralMeasure_restrict hP ψ hD, Measure.restrict_apply hD.compl]
    simp
  · apply (hc_iff_atomless hP _).mpr
    intro x
    rw [spectralMeasure_restrict hP ψ hD.compl]
    by_cases hx : x ∈ D
    · rw [Measure.restrict_apply (measurableSet_singleton x)]
      have he : ({x} : Set ℝ) ∩ Dᶜ = ∅ := by simp [hx]
      rw [he, measure_empty]
    · have hz : TeschlQM.Shared.spectralMeasure P ψ {x} = 0 := by simpa [D] using hx
      exact le_antisymm ((Measure.restrict_le_self _).trans_eq hz) (by positivity)

lemma hc_sub (hP : TeschlQM.Shared.IsProjValuedMeasure P) {u v : H}
    (hu : u ∈ TeschlQM.Dynamics.hc P) (hv : v ∈ TeschlQM.Dynamics.hc P) :
    u-v ∈ TeschlQM.Dynamics.hc P := by
  apply (hc_iff_atomless hP _).mpr
  intro x
  have hu0 := (spectralMeasure_zero_iff hP u (measurableSet_singleton x)).mp ((hc_iff_atomless hP u).mp hu x)
  have hv0 := (spectralMeasure_zero_iff hP v (measurableSet_singleton x)).mp ((hc_iff_atomless hP v).mp hv x)
  apply (spectralMeasure_zero_iff hP _ (measurableSet_singleton x)).mpr
  simp [hu0,hv0]

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE PointContinuousSplit

-- BEGIN COMPLETE MODULE OrbitLocalization
section

open Filter Topology
open scoped ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def OrbitLocalized (K : ℕ → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H) (ψ : H) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 0 ≤ t → ‖U t ψ - K n (U t ψ)‖ < ε

lemma orbitLocalized_zero (K : ℕ → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H) :
    OrbitLocalized K U 0 := by
  intro ε hε
  filter_upwards [] with n t _
  simpa using hε

lemma orbitLocalized_add {K : ℕ → H →L[ℂ] H} {U : ℝ → H →L[ℂ] H} {ψ φ : H}
    (hψ : OrbitLocalized K U ψ) (hφ : OrbitLocalized K U φ) : OrbitLocalized K U (ψ+φ) := by
  intro ε hε
  filter_upwards [hψ (ε/2) (by positivity), hφ (ε/2) (by positivity)] with n hn hm t ht
  have h1 := hn t ht
  have h2 := hm t ht
  have he : U t (ψ+φ)-K n (U t (ψ+φ)) =
      (U t ψ-K n (U t ψ)) + (U t φ-K n (U t φ)) := by simp; abel
  rw [he]
  exact (norm_add_le _ _).trans_lt (by linarith)

lemma orbitLocalized_sub {K : ℕ → H →L[ℂ] H} {U : ℝ → H →L[ℂ] H} {ψ φ : H}
    (hψ : OrbitLocalized K U ψ) (hφ : OrbitLocalized K U φ) : OrbitLocalized K U (ψ-φ) := by
  intro ε hε
  filter_upwards [hψ (ε/2) (by positivity), hφ (ε/2) (by positivity)] with n hn hm t ht
  have h1 := hn t ht
  have h2 := hm t ht
  have he : U t (ψ-φ)-K n (U t (ψ-φ)) =
      (U t ψ-K n (U t ψ)) - (U t φ-K n (U t φ)) := by simp; abel
  rw [he]
  exact (norm_sub_le _ _).trans_lt (by linarith)

lemma strong_operator_uniform_bound [CompleteSpace H] (K : ℕ → H →L[ℂ] H)
    (hK : ∀ ψ, Tendsto (fun n => K n ψ) atTop (𝓝 ψ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖K n‖ ≤ B := by
  obtain ⟨B,hB⟩ := banach_steinhaus (g := K) (fun ψ => by
    obtain ⟨C,hC⟩ := (Metric.isBounded_range_of_tendsto _ (hK ψ)).exists_norm_le
    exact ⟨C,fun n => hC _ ⟨n,rfl⟩⟩)
  exact ⟨max B 0,le_max_right _ _,fun n => (hB n).trans (le_max_left _ _)⟩

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE OrbitLocalization

-- BEGIN COMPLETE MODULE OrbitSupremum
section

open Filter Topology
open scoped ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma orbitLocalized_iff_sup (K : ℕ → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H) (ψ : H) :
    OrbitLocalized K U ψ ↔
      Tendsto (fun n => ⨆ t : Set.Ici (0 : ℝ), ‖U t ψ - K n (U t ψ)‖ₑ) atTop (𝓝 0) := by
  constructor
  · intro h
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    by_cases he : ε = ⊤
    · simp [he]
    have hr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' he
    filter_upwards [h ε.toReal hr] with n hn
    apply iSup_le
    intro t
    rw [← ENNReal.ofReal_toReal he, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hn t t.property).le
  · intro h ε hε
    have he := (ENNReal.tendsto_nhds_zero.mp h) (ENNReal.ofReal (ε/2)) (by positivity)
    filter_upwards [he] with n hn t ht
    have hb : ‖U t ψ-K n (U t ψ)‖ₑ ≤ ENNReal.ofReal (ε/2) :=
      (le_iSup (fun s : Set.Ici (0 : ℝ) => ‖U s ψ-K n (U s ψ)‖ₑ) ⟨t,ht⟩).trans hn
    rw [← ofReal_norm] at hb
    have hreal : ‖U t ψ-K n (U t ψ)‖ ≤ ε/2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
    linarith

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE OrbitSupremum

-- BEGIN COMPLETE MODULE TimeMeanLinear
section

open MeasureTheory Filter Topology

namespace TeschlQM.Dynamics.Proof

lemma timeMean_add (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (T : ℝ) :
    timeMean (fun t => f t + g t) T = timeMean f T + timeMean g T := by
  unfold timeMean
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

lemma timeMean_const_mul (f : ℝ → ℝ) (c T : ℝ) :
    timeMean (fun t => c * f t) T = c * timeMean f T := by
  unfold timeMean
  rw [intervalIntegral.integral_const_mul]
  ring

lemma timeMean_add_const (f : ℝ → ℝ) (hf : Continuous f) (c : ℝ) {T : ℝ} (hT : T ≠ 0) :
    timeMean (fun t => f t + c) T = timeMean f T + c := by
  rw [timeMean_add _ _ hf continuous_const, timeMean_const _ hT]

lemma timeMean_le_of_le_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {c T : ℝ} (hfg : ∀ t, f t ≤ g t + c) (hT : 0 < T) :
    timeMean f T ≤ timeMean g T + c := by
  exact (timeMean_mono hf (hg.add continuous_const) hfg hT.le).trans_eq
    (timeMean_add_const _ hg _ hT.ne')

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE TimeMeanLinear

-- BEGIN COMPLETE MODULE LocalizationConverse
section

open MeasureTheory Filter Topology

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma localized_continuous_zero (K : ℕ → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H)
    (ψ : H) (hu : Continuous (fun t => U t ψ)) (hnorm : ∀ t, ‖U t ψ‖ = ‖ψ‖)
    (hdecay : ∀ n, Tendsto (timeMean (fun t => ‖K n (U t ψ)‖)) atTop (𝓝 0))
    (hloc : OrbitLocalized K U ψ) : ψ = 0 := by
  by_contra hψ
  have hp : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  obtain ⟨n,hn⟩ := (hloc (‖ψ‖/2) (by positivity)).exists
  have hc : Continuous (fun t => ‖K n (U t ψ)‖) := ((K n).continuous.comp hu).norm
  have hb : ∀ T : ℝ, 0 < T → ‖ψ‖ ≤
      timeMean (fun t => ‖K n (U t ψ)‖) T + ‖ψ‖/2 := by
    intro T hT
    have hi : ∫ t in (0 : ℝ)..T, ‖ψ‖ ≤
        ∫ t in (0 : ℝ)..T, ‖K n (U t ψ)‖ + ‖ψ‖/2 := by
      apply intervalIntegral.integral_mono_on hT.le
        (continuous_const.intervalIntegrable _ _)
        ((hc.add continuous_const).intervalIntegrable _ _)
      intro t ht
      have he := norm_le_insert' (U t ψ) (K n (U t ψ))
      rw [hnorm t] at he
      exact he.trans (add_le_add le_rfl (hn t ht.1).le)
    have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hT.le)
    change timeMean (fun _ => ‖ψ‖) T ≤
      timeMean (fun t => ‖K n (U t ψ)‖ + ‖ψ‖/2) T at hh
    rw [timeMean_const _ hT.ne',timeMean_add_const _ hc _ hT.ne'] at hh
    exact hh
  have hh : ‖ψ‖ ≤ ‖ψ‖/2 := by
    have ht := (hdecay n).add_const (‖ψ‖/2)
    simp only [zero_add] at ht
    exact ge_of_tendsto ht ((eventually_gt_atTop (0 : ℝ)).mono fun T hT => hb T hT)
  linarith

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE LocalizationConverse

-- BEGIN COMPLETE MODULE RAGECharacterizations
section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma hc_of_mean_limits (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (hU : ∀ ψ : H, Continuous (fun t => TeschlQM.Shared.timeEvolution P t ψ))
    (K : ℕ → H →L[ℂ] H) (hKI : ∀ ψ, Tendsto (fun n => K n ψ) atTop (𝓝 ψ))
    (ψ : H) (L : ℕ → ℝ)
    (hL : ∀ n, Tendsto (timeMean (fun t => ‖K n (TeschlQM.Shared.timeEvolution P t ψ)‖)) atTop (𝓝 (L n)))
    (hL0 : Tendsto L atTop (𝓝 0)) : ψ ∈ TeschlQM.Dynamics.hc P := by
  apply (hc_iff_atomless hP ψ).mpr
  intro a
  have hb : ∀ n, ‖K n (P {a} ψ)‖ ≤ L n := by
    intro n
    apply norm_le_mean_limit _ ((K n).continuous.comp (hU ψ)) _ a _ (hL n)
    intro φ
    have hh := native_atom_mean hP ψ ((K n).adjoint φ) a
    simpa only [Function.comp_apply, ContinuousLinearMap.adjoint_inner_left] using hh
  have hh := le_of_tendsto_of_tendsto (hKI (P {a} ψ)).norm hL0 (Eventually.of_forall hb)
  apply (spectralMeasure_zero_iff hP ψ (measurableSet_singleton a)).mpr
  exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))

lemma hpp_of_localized (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (hU : ∀ ψ : H, Continuous (fun t => TeschlQM.Shared.timeEvolution P t ψ))
    (hUnorm : ∀ t ψ, ‖TeschlQM.Shared.timeEvolution P t ψ‖ = ‖ψ‖)
    (K : ℕ → H →L[ℂ] H)
    (hcdecay : ∀ ψ ∈ TeschlQM.Dynamics.hc P, ∀ n,
      Tendsto (timeMean (fun t => ‖K n (TeschlQM.Shared.timeEvolution P t ψ)‖)) atTop (𝓝 0))
    (hpploc : ∀ ψ ∈ TeschlQM.Dynamics.hpp P,
      OrbitLocalized K (TeschlQM.Shared.timeEvolution P) ψ)
    (ψ : H) (hloc : OrbitLocalized K (TeschlQM.Shared.timeEvolution P) ψ) :
    ψ ∈ TeschlQM.Dynamics.hpp P := by
  obtain ⟨p,hp,c,hc,he⟩ := point_continuous_split hP ψ
  have hcEq : c = ψ-p := by rw [he]; abel
  have hcloc : OrbitLocalized K (TeschlQM.Shared.timeEvolution P) c := by
    rw [hcEq]
    exact orbitLocalized_sub hloc (hpploc p hp)
  have hc0 := localized_continuous_zero K (TeschlQM.Shared.timeEvolution P) c
    (hU c) (fun t => hUnorm t c) (hcdecay c hc) hcloc
  rw [he,hc0,add_zero]
  exact hp

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE RAGECharacterizations

-- BEGIN COMPLETE MODULE PurePointApproximation
section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma projection_residual_norm (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H)
    {S : Set ℝ} (hS : MeasurableSet S) :
    ‖ψ - P S ψ‖ = Real.sqrt ((TeschlQM.Shared.spectralMeasure P ψ Sᶜ).toReal) := by
  have he : ψ - P S ψ = P Sᶜ ψ := by
    have hh := pvm_complement_sum hP ψ hS
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hh.symm)
  rw [he,spectralMeasure_apply hP ψ hS.compl,← pvm_mass_ofReal,
    ENNReal.toReal_ofReal (sq_nonneg _),Real.sqrt_sq (norm_nonneg _)]

lemma pure_point_finite_approx (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H)
    (hψ : ψ ∈ TeschlQM.Dynamics.hpp P) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℝ, ‖ψ - P (S : Set ℝ) ψ‖ < ε := by
  classical
  obtain ⟨D,hD,hnull⟩ := hψ
  by_cases hne : D.Nonempty
  · obtain ⟨f,hf⟩ := hD.exists_eq_range hne
    let S (n : ℕ) : Finset ℝ := (Finset.range n).image f
    have hmono : Monotone (fun n => (S n : Set ℝ)) := by
      intro n m hnm
      exact Finset.coe_subset.mpr (Finset.image_subset_image (Finset.range_mono hnm))
    have hUnion : (⋃ n, (S n : Set ℝ)) = D := by
      rw [hf]
      ext x
      simp only [Set.mem_iUnion,Finset.mem_coe, S, Finset.mem_image, Finset.mem_range,Set.mem_range]
      constructor
      · rintro ⟨n,k,_,hk⟩
        exact ⟨k,hk⟩
      · rintro ⟨k,rfl⟩
        exact ⟨k+1,k,by omega,rfl⟩
    let μ := TeschlQM.Shared.spectralMeasure P ψ
    let : IsFiniteMeasure μ := spectralMeasure_finite hP ψ
    have ht := tendsto_measure_iInter_atTop (μ := μ)
      (s := fun n => (S n : Set ℝ)ᶜ)
      (fun n => (S n).measurableSet.compl.nullMeasurableSet)
      (fun n m hnm => Set.compl_subset_compl.mpr (hmono hnm))
      ⟨0,measure_ne_top _ _⟩
    have hInter : (⋂ n, (S n : Set ℝ)ᶜ) = Dᶜ := by rw [← Set.compl_iUnion,hUnion]
    rw [hInter,hnull] at ht
    have hr := Real.continuous_sqrt.continuousAt.tendsto.comp
      ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht)
    have hnorm : Tendsto (fun n => ‖ψ-P (S n : Set ℝ) ψ‖) atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.toReal_zero, Real.sqrt_zero,
        projection_residual_norm hP ψ (S _).measurableSet] using hr
    obtain ⟨n,hn⟩ := (hnorm.eventually (gt_mem_nhds hε)).exists
    exact ⟨S n,hn⟩
  · have hD0 : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hzero : ψ = 0 := by
      have hp := (spectralMeasure_zero_iff hP ψ MeasurableSet.univ).mp (by simpa [hD0] using hnull)
      simpa [hP.2.1] using hp
    exact ⟨∅,by simpa [hzero] using hε⟩

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE PurePointApproximation

-- BEGIN COMPLETE MODULE PVMFiniteSum
section

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma pvm_finset (hP : TeschlQM.Shared.IsProjValuedMeasure P) (S : Finset ℝ) (ψ : H) :
    P (S : Set ℝ) ψ = ∑ x ∈ S, P {x} ψ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [pvm_empty hP]
  | @insert a S ha ih =>
    have hd : Disjoint ({a} : Set ℝ) (S : Set ℝ) := by simpa using ha
    rw [Finset.coe_insert,Set.insert_eq, pvm_union hP (measurableSet_singleton a) S.measurableSet hd]
    simp only [add_apply, ih, Finset.sum_insert ha]

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE PVMFiniteSum

-- BEGIN COMPLETE MODULE OrbitApproximation
section

open Filter Topology

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma orbitLocalized_finset_sum {ι : Type*} (s : Finset ι) (v : ι → H)
    {K : ℕ → H →L[ℂ] H} {U : ℝ → H →L[ℂ] H}
    (hv : ∀ i ∈ s, OrbitLocalized K U (v i)) : OrbitLocalized K U (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using orbitLocalized_zero K U
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact orbitLocalized_add (hv a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hv i (Finset.mem_insert_of_mem hi)))

lemma orbitLocalized_phase {K : ℕ → H →L[ℂ] H} {U : ℝ → H →L[ℂ] H} (ψ : H)
    (hK : Tendsto (fun n => K n ψ) atTop (𝓝 ψ))
    (c : ℝ → ℂ) (hc : ∀ t, ‖c t‖ = 1) (hU : ∀ t, U t ψ = c t • ψ) :
    OrbitLocalized K U ψ := by
  have he : Tendsto (fun n => ‖ψ-K n ψ‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ψ) atTop (𝓝 ψ)).sub hK).norm
  intro ε hε
  filter_upwards [he.eventually (gt_mem_nhds hε)] with n hn t _
  simpa only [hU, map_smul, ← smul_sub, norm_smul, hc, one_mul] using hn

lemma residual_difference_bound {K U : H →L[ℂ] H} {B : ℝ}
    (hK : ‖K‖ ≤ B) (hU : ∀ x, ‖U x‖ = ‖x‖) (ψ φ : H) :
    ‖(U ψ-K (U ψ))-(U φ-K (U φ))‖ ≤ (1+B)*‖ψ-φ‖ := by
  have he : (U ψ-K (U ψ))-(U φ-K (U φ)) = U (ψ-φ)-K (U (ψ-φ)) := by simp; abel
  rw [he]
  calc
    _ ≤ ‖U (ψ-φ)‖ + ‖K (U (ψ-φ))‖ := norm_sub_le _ _
    _ ≤ ‖U (ψ-φ)‖ + ‖K‖*‖U (ψ-φ)‖ := add_le_add le_rfl (K.le_opNorm _)
    _ ≤ ‖ψ-φ‖ + B*‖ψ-φ‖ := by rw [hU]; gcongr
    _ = _ := by ring

lemma orbitLocalized_of_approx [CompleteSpace H]
    (K : ℕ → H →L[ℂ] H) (hK : ∀ ψ, Tendsto (fun n => K n ψ) atTop (𝓝 ψ))
    (U : ℝ → H →L[ℂ] H) (hU : ∀ t ψ, ‖U t ψ‖ = ‖ψ‖) (ψ : H)
    (ha : ∀ ε > 0, ∃ φ, OrbitLocalized K U φ ∧ ‖ψ-φ‖ < ε) : OrbitLocalized K U ψ := by
  obtain ⟨B,hB0,hB⟩ := strong_operator_uniform_bound K hK
  intro ε hε
  obtain ⟨φ,hφ,hclose⟩ := ha (ε/(2*(1+B))) (by positivity)
  have herror : (1+B)*‖ψ-φ‖ < ε/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*(1+B))).mp hclose
    nlinarith
  filter_upwards [hφ (ε/2) (by positivity)] with n hn t ht
  have hr := residual_difference_bound (hB n) (hU t) ψ φ
  have hh := norm_le_insert' (U t ψ-K n (U t ψ)) (U t φ-K n (U t φ))
  have hp := hn t ht
  linarith

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE OrbitApproximation

-- BEGIN COMPLETE MODULE PurePointLocalization
section

open Filter Topology

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma pure_point_localized (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (K : ℕ → H →L[ℂ] H) (hKI : ∀ ψ, Tendsto (fun n => K n ψ) atTop (𝓝 ψ))
    (U : ℝ → H →L[ℂ] H) (hU : ∀ t ψ, ‖U t ψ‖ = ‖ψ‖)
    (hphase : ∀ t a ψ, U t (P {a} ψ) = Complex.exp (-(Complex.I*(t : ℂ)*(a : ℂ))) • P {a} ψ)
    (ψ : H) (hψ : ψ ∈ TeschlQM.Dynamics.hpp P) : OrbitLocalized K U ψ := by
  apply orbitLocalized_of_approx K hKI U hU ψ
  intro ε hε
  obtain ⟨S,hS⟩ := pure_point_finite_approx hP ψ hψ hε
  refine ⟨P (S : Set ℝ) ψ,?_,hS⟩
  rw [pvm_finset hP]
  apply orbitLocalized_finset_sum
  intro a _
  apply orbitLocalized_phase (P {a} ψ) (hKI _) (fun t => Complex.exp (-(Complex.I*(t : ℂ)*(a : ℂ))))
  · intro t
    rw [Complex.norm_exp]
    simp
  · intro t
    exact hphase t a ψ

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE PurePointLocalization

-- BEGIN COMPLETE MODULE TimeEvolutionAlgebra
section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

noncomputable def spectralPhase (t x : ℝ) : ℂ := Complex.exp (-(Complex.I * (t : ℂ) * (x : ℂ)))

lemma spectralPhase_measurable (t : ℝ) : Measurable (spectralPhase t) := by
  unfold spectralPhase
  fun_prop

lemma spectralPhase_norm (t x : ℝ) : ‖spectralPhase t x‖ = 1 := by
  simp [spectralPhase,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

lemma spectralPhase_add (s t x : ℝ) : spectralPhase (s+t) x = spectralPhase s x * spectralPhase t x := by
  unfold spectralPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma timeEvolution_mul (hP : TeschlQM.Shared.IsProjValuedMeasure P) (s t : ℝ) :
    TeschlQM.Shared.timeEvolution P s * TeschlQM.Shared.timeEvolution P t =
      TeschlQM.Shared.timeEvolution P (s+t) := by
  change TeschlQM.Shared.boundedSpectralIntegral P (spectralPhase s) *
    TeschlQM.Shared.boundedSpectralIntegral P (spectralPhase t) = _
  rw [← boundedIntegral_mul hP _ _ (spectralPhase_measurable s) (spectralPhase_measurable t)
    1 1 (fun x => le_of_eq (spectralPhase_norm s x)) (fun x => le_of_eq (spectralPhase_norm t x))]
  congr 1
  funext x
  exact (spectralPhase_add s t x).symm

lemma timeEvolution_zero (hP : TeschlQM.Shared.IsProjValuedMeasure P) :
    TeschlQM.Shared.timeEvolution P 0 = 1 := by
  simpa [TeschlQM.Shared.timeEvolution] using boundedIntegral_one hP

lemma timeEvolution_norm_le (hP : TeschlQM.Shared.IsProjValuedMeasure P) (t : ℝ) (ψ : H) :
    ‖TeschlQM.Shared.timeEvolution P t ψ‖ ≤ ‖ψ‖ := by
  change ‖TeschlQM.Shared.boundedSpectralIntegral P (spectralPhase t) ψ‖ ≤ ‖ψ‖
  simpa only [one_mul] using boundedSpectralIntegral_bound hP (spectralPhase t)
    (spectralPhase_measurable t) 1 (fun x => le_of_eq (spectralPhase_norm t x)) ψ

lemma timeEvolution_norm (hP : TeschlQM.Shared.IsProjValuedMeasure P) (t : ℝ) (ψ : H) :
    ‖TeschlQM.Shared.timeEvolution P t ψ‖ = ‖ψ‖ := by
  apply le_antisymm (timeEvolution_norm_le hP t ψ)
  have h := timeEvolution_norm_le hP (-t) (TeschlQM.Shared.timeEvolution P t ψ)
  have hi : TeschlQM.Shared.timeEvolution P (-t) (TeschlQM.Shared.timeEvolution P t ψ) = ψ := by
    change (TeschlQM.Shared.timeEvolution P (-t) * TeschlQM.Shared.timeEvolution P t) ψ = ψ
    rw [timeEvolution_mul hP,neg_add_cancel,timeEvolution_zero hP]
    rfl
  rwa [hi] at h

lemma timeEvolution_commute_projection (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (t : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (ψ : H) :
    TeschlQM.Shared.timeEvolution P t (P S ψ) = P S (TeschlQM.Shared.timeEvolution P t ψ) := by
  exact congrArg (fun A : H →L[ℂ] H => A ψ)
    (boundedIntegral_commute_projection hP (spectralPhase t) (spectralPhase_measurable t)
      1 (fun x => le_of_eq (spectralPhase_norm t x)) hS)

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE TimeEvolutionAlgebra

-- BEGIN COMPLETE MODULE TimeEvolutionAtoms
section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma boundedIntegral_smul (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (c : ℂ) :
    TeschlQM.Shared.boundedSpectralIntegral P (fun x => c * f x) =
      c • TeschlQM.Shared.boundedSpectralIntegral P f := by
  apply clm_quadratic_ext
  intro ψ
  have hb (x : ℝ) : ‖c*f x‖ ≤ ‖c‖*C := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)
  rw [boundedIntegral_quadratic hP (fun x => c*f x) (by fun_prop) (‖c‖*C) hb]
  change _ = ⟪ψ,c • TeschlQM.Shared.boundedSpectralIntegral P f ψ⟫_ℂ
  rw [inner_smul_right,boundedIntegral_quadratic hP f hf C hC,integral_const_mul]

lemma timeEvolution_projection_singleton (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (t a : ℝ) (ψ : H) :
    TeschlQM.Shared.timeEvolution P t (P {a} ψ) = spectralPhase t a • P {a} ψ := by
  have hs : MeasurableSet ({a} : Set ℝ) := measurableSet_singleton a
  have he : (fun x => spectralPhase t x * ({a} : Set ℝ).indicator (fun _ => (1 : ℂ)) x) =
      (fun x => spectralPhase t a * ({a} : Set ℝ).indicator (fun _ => (1 : ℂ)) x) := by
    funext x
    by_cases hx : x = a
    · subst x; rfl
    · simp [Set.indicator,hx]
  have hi := boundedIntegral_mul hP (spectralPhase t) (({a} : Set ℝ).indicator (fun _ => (1 : ℂ)))
    (spectralPhase_measurable t) (indicator_one_measurable hs) 1 1
    (fun x => le_of_eq (spectralPhase_norm t x)) (indicator_one_bound _)
  rw [he,boundedIntegral_smul hP _ (indicator_one_measurable hs) 1 (indicator_one_bound _),
    boundedIntegral_indicator hP hs] at hi
  exact (congrArg (fun A : H →L[ℂ] H => A ψ) hi).symm

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE TimeEvolutionAtoms

-- BEGIN COMPLETE MODULE NativePurePoint
section

open Filter Topology

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma native_pure_point_localized (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (K : ℕ → H →L[ℂ] H) (hKI : ∀ ψ, Tendsto (fun n => K n ψ) atTop (𝓝 ψ))
    (ψ : H) (hψ : ψ ∈ TeschlQM.Dynamics.hpp P) :
    OrbitLocalized K (TeschlQM.Shared.timeEvolution P) ψ := by
  apply pure_point_localized hP K hKI _ (timeEvolution_norm hP) _ ψ hψ
  intro t a φ
  exact timeEvolution_projection_singleton hP t a φ

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE NativePurePoint

-- BEGIN COMPLETE MODULE PhaseL2Continuity
section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace TeschlQM.Dynamics.Proof

lemma phase_eLpNorm_tendsto (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Tendsto (fun s => eLpNorm (spectralPhase s - spectralPhase t) 2 μ) (𝓝 t) (𝓝 0) := by
  have hb (s x : ℝ) : ‖spectralPhase s x - spectralPhase t x‖ₑ ≤ 2 := by
    rw [← ofReal_norm]
    apply le_trans (ENNReal.ofReal_le_ofReal (show ‖spectralPhase s x - spectralPhase t x‖ ≤ (2 : ℝ) from ?_)) (by norm_num)
    calc
      ‖spectralPhase s x - spectralPhase t x‖ ≤ ‖spectralPhase s x‖ + ‖spectralPhase t x‖ := norm_sub_le _ _
      _ = 2 := by rw [spectralPhase_norm,spectralPhase_norm]; norm_num
  have ht : Tendsto (fun s => ∫⁻ x, ‖spectralPhase s x - spectralPhase t x‖ₑ ^ (2 : ℝ) ∂μ)
      (𝓝 t) (𝓝 0) := by
    have hh := tendsto_lintegral_filter_of_dominated_convergence (μ := μ)
      (F := fun s x => ‖spectralPhase s x - spectralPhase t x‖ₑ ^ (2 : ℝ))
      (f := fun _ => 0) (fun _ => (4 : ℝ≥0∞))
      (Eventually.of_forall (fun s => by unfold spectralPhase; fun_prop))
      (Eventually.of_forall (fun s => ae_of_all _ (fun x => by
        calc
          ‖spectralPhase s x - spectralPhase t x‖ₑ ^ (2 : ℝ) ≤ (2 : ℝ≥0∞)^ (2 : ℝ) :=
            ENNReal.rpow_le_rpow (hb s x) (by norm_num)
          _ = 4 := by norm_num)))
      (by simp only [lintegral_const]; finiteness)
      (ae_of_all _ (fun x => by
        have hc : Continuous (fun s : ℝ => ‖spectralPhase s x - spectralPhase t x‖ₑ ^ (2 : ℝ)) := by
          unfold spectralPhase
          fun_prop
        simpa using hc.continuousAt.tendsto (x := t)))
    simpa using hh
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),ENNReal.toReal_ofNat]
  simpa [Function.comp_def] using (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).continuousAt.tendsto.comp ht

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE PhaseL2Continuity

-- BEGIN COMPLETE MODULE TimeEvolutionContinuity
section

open MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma timeEvolution_continuous_apply (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) :
    Continuous (fun t => TeschlQM.Shared.timeEvolution P t ψ) := by
  let := spectralMeasure_finite hP ψ
  let hm (t : ℝ) : MemLp (spectralPhase t) 2 (TeschlQM.Shared.spectralMeasure P ψ) :=
    MemLp.of_bound (spectralPhase_measurable t).aestronglyMeasurable 1
      (ae_of_all _ (fun x => le_of_eq (spectralPhase_norm t x)))
  rw [continuous_iff_continuousAt]
  intro t
  have ht : Tendsto (fun s => (hm s).toLp (spectralPhase s)) (𝓝 t)
      (𝓝 ((hm t).toLp (spectralPhase t))) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
    exact phase_eLpNorm_tendsto _ t
  have hh := (cyclicMap hP ψ).continuous.tendsto ((hm t).toLp (spectralPhase t)) |>.comp ht
  have he (s : ℝ) : TeschlQM.Shared.timeEvolution P s ψ =
      cyclicMap hP ψ ((hm s).toLp (spectralPhase s)) := by
    change TeschlQM.Shared.boundedSpectralIntegral P (spectralPhase s) ψ = _
    rw [boundedSpectralIntegral_apply hP _ (spectralPhase_measurable s) 1
      (fun x => le_of_eq (spectralPhase_norm s x))]
    rfl
  change Tendsto (fun s => TeschlQM.Shared.timeEvolution P s ψ) (𝓝 t)
    (𝓝 (TeschlQM.Shared.timeEvolution P t ψ))
  simpa only [Function.comp_def,← he] using hh

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE TimeEvolutionContinuity

-- BEGIN COMPLETE MODULE RAGECore
section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma rage_of_continuous_decay (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (K : ℕ → H →L[ℂ] H) (hKI : ∀ ψ, Tendsto (fun n => K n ψ) atTop (𝓝 ψ))
    (hdecay : ∀ ψ ∈ TeschlQM.Dynamics.hc P, ∀ n,
      Tendsto (timeMean (fun t => ‖K n (TeschlQM.Shared.timeEvolution P t ψ)‖)) atTop (𝓝 0)) :
    TeschlQM.Dynamics.hc P = {ψ | ∃ L : ℕ → ℝ,
      (∀ n, Tendsto (timeMean (fun t => ‖K n (TeschlQM.Shared.timeEvolution P t ψ)‖)) atTop (𝓝 (L n))) ∧
      Tendsto L atTop (𝓝 0)} ∧
    TeschlQM.Dynamics.hpp P = {ψ | Tendsto (fun n => ⨆ t : Set.Ici (0 : ℝ),
      ‖TeschlQM.Shared.timeEvolution P t ψ-K n (TeschlQM.Shared.timeEvolution P t ψ)‖ₑ) atTop (𝓝 0)} := by
  constructor
  · ext ψ
    constructor
    · intro hψ
      exact ⟨fun _ => 0,hdecay ψ hψ,tendsto_const_nhds⟩
    · rintro ⟨L,hL,hL0⟩
      exact hc_of_mean_limits hP (timeEvolution_continuous_apply hP) K hKI ψ L hL hL0
  · ext ψ
    constructor
    · intro hψ
      exact (orbitLocalized_iff_sup K _ ψ).mp (native_pure_point_localized hP K hKI ψ hψ)
    · intro hψ
      exact hpp_of_localized hP (timeEvolution_continuous_apply hP) (timeEvolution_norm hP)
        K hdecay (native_pure_point_localized hP K hKI) ψ ((orbitLocalized_iff_sup K _ ψ).mpr hψ)

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE RAGECore

-- BEGIN COMPLETE MODULE SpectralProjectionLimit
section

open MeasureTheory Filter Topology

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma pvm_tendsto_univ (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (S : ℕ → Set ℝ) (hS : ∀ n, MeasurableSet (S n)) (hm : Monotone S)
    (hcover : (⋃ n, S n) = Set.univ) (ψ : H) :
    Tendsto (fun n => P (S n) ψ) atTop (𝓝 ψ) := by
  let μ := TeschlQM.Shared.spectralMeasure P ψ
  let : IsFiniteMeasure μ := spectralMeasure_finite hP ψ
  have ht := tendsto_measure_iInter_atTop (μ := μ) (s := fun n => (S n)ᶜ)
    (fun n => (hS n).compl.nullMeasurableSet)
    (fun n m hnm => Set.compl_subset_compl.mpr (hm hnm)) ⟨0,measure_ne_top _ _⟩
  have hInter : (⋂ n, (S n)ᶜ) = ∅ := by rw [← Set.compl_iUnion,hcover,Set.compl_univ]
  rw [hInter,measure_empty] at ht
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,ENNReal.toReal_zero,Real.sqrt_zero,norm_sub_rev,
    projection_residual_norm hP ψ (hS _)] using hr

lemma pvm_cutoff_tendsto (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H) :
    Tendsto (fun n : ℕ => P (Set.Icc (-(n : ℝ)) (n : ℝ)) ψ) atTop (𝓝 ψ) := by
  apply pvm_tendsto_univ hP _ (fun _ => measurableSet_Icc) _ _ ψ
  · intro n m hnm x hx
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    constructor <;> linarith [hx.1,hx.2]
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n,hn⟩ := exists_nat_gt |x|
    exact Set.mem_iUnion.mpr ⟨n,⟨by linarith [neg_abs_le x],by linarith [le_abs_self x]⟩⟩

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE SpectralProjectionLimit

-- BEGIN COMPLETE MODULE SpectralCutoffDomain
section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

noncomputable def cutoffFunction (N : ℕ) : ℝ → ℂ :=
  (Set.Icc (-(N : ℝ)) N).indicator (fun x => (x : ℂ))

lemma cutoffFunction_measurable (N : ℕ) : Measurable (cutoffFunction N) := by
  exact Complex.measurable_ofReal.indicator measurableSet_Icc

lemma cutoffFunction_bound (N : ℕ) (x : ℝ) : ‖cutoffFunction N x‖ ≤ N := by
  classical
  by_cases hx : x ∈ Set.Icc (-(N : ℝ)) N
  · simp only [cutoffFunction,Set.indicator_of_mem hx,Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr hx
  · simp [cutoffFunction,Set.indicator_of_notMem hx]

lemma cutoff_mem_domain (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {A : H →ₗ.[ℂ] H} (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x => (x : ℂ)) A)
    (N : ℕ) (ψ : H) : P (Set.Icc (-(N : ℝ)) N) ψ ∈ A.domain := by
  rw [← SetLike.mem_coe,hAP.1]
  change (∫⁻ x, (‖(x : ℂ)‖₊ : ℝ≥0∞)^2 ∂TeschlQM.Shared.spectralMeasure P
    (P (Set.Icc (-(N : ℝ)) N) ψ)) < ⊤
  rw [spectralMeasure_restrict hP ψ measurableSet_Icc]
  let := spectralMeasure_finite hP ψ
  apply lt_of_le_of_lt (lintegral_mono_ae ?_) (show (∫⁻ _ : ℝ, (N : ℝ≥0∞)^2
    ∂(TeschlQM.Shared.spectralMeasure P ψ).restrict (Set.Icc (-(N : ℝ)) N)) < ⊤ by
      simp only [lintegral_const]; finiteness)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  apply pow_le_pow_left₀ (by positivity)
  change (‖(x : ℂ)‖₊ : ℝ≥0∞) ≤ (N : ℝ≥0∞)
  exact_mod_cast (show ‖(x : ℂ)‖ ≤ (N : ℝ) by
    rw [Complex.norm_real,Real.norm_eq_abs]; exact abs_le.mpr hx)

noncomputable def cutoffDomainMap (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {A : H →ₗ.[ℂ] H} (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x => (x : ℂ)) A)
    (N : ℕ) : H →ₗ[ℂ] A.domain where
  toFun ψ := ⟨P (Set.Icc (-(N : ℝ)) N) ψ,cutoff_mem_domain hP hAP N ψ⟩
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' c x := Subtype.ext (map_smul _ c x)

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE SpectralCutoffDomain

-- BEGIN COMPLETE MODULE SpectralCutoffCompression
section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

noncomputable def compressedSpectralOperator (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {A : H →ₗ.[ℂ] H} (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x => (x : ℂ)) A)
    (N : ℕ) : H →ₗ[ℂ] H :=
  (P (Set.Icc (-(N : ℝ)) N)).toLinearMap.comp (A.toFun.comp (cutoffDomainMap hP hAP N))

lemma cutoff_compression (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {A : H →ₗ.[ℂ] H} (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x => (x : ℂ)) A)
    (N : ℕ) (ψ : H) :
    P (Set.Icc (-(N : ℝ)) N) (A (cutoffDomainMap hP hAP N ψ)) =
      TeschlQM.Shared.boundedSpectralIntegral P (cutoffFunction N) ψ := by
  have hq (φ : H) : ⟪φ,compressedSpectralOperator hP hAP N φ⟫_ℂ =
      ⟪φ,TeschlQM.Shared.boundedSpectralIntegral P (cutoffFunction N) φ⟫_ℂ := by
    change ⟪φ,P (Set.Icc (-(N : ℝ)) N) (A (cutoffDomainMap hP hAP N φ))⟫_ℂ = _
    have ha : (P (Set.Icc (-(N : ℝ)) N)).adjoint = P (Set.Icc (-(N : ℝ)) N) :=
      (hP.1 _ measurableSet_Icc).1
    rw [← ContinuousLinearMap.adjoint_inner_left,ha]
    change ⟪((cutoffDomainMap hP hAP N φ) : H),A (cutoffDomainMap hP hAP N φ)⟫_ℂ = _
    rw [hAP.2,boundedIntegral_quadratic hP (cutoffFunction N) (cutoffFunction_measurable N)
      (N : ℝ) (cutoffFunction_bound N)]
    change (∫ x,(x : ℂ) ∂TeschlQM.Shared.spectralMeasure P (P (Set.Icc (-(N : ℝ)) N) φ)) = _
    rw [spectralMeasure_restrict hP φ measurableSet_Icc]
    exact (integral_indicator measurableSet_Icc).symm
  have he : compressedSpectralOperator hP hAP N =
      (TeschlQM.Shared.boundedSpectralIntegral P (cutoffFunction N)).toLinearMap := by
    apply (ext_inner_map _ _).mp
    intro φ
    change ⟪compressedSpectralOperator hP hAP N φ,φ⟫_ℂ =
      ⟪TeschlQM.Shared.boundedSpectralIntegral P (cutoffFunction N) φ,φ⟫_ℂ
    simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) (hq φ)
  exact LinearMap.congr_fun he ψ

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE SpectralCutoffCompression

-- BEGIN COMPLETE MODULE SpectralCutoffAction
section

open MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma cutoff_set_mono {N M : ℕ} (h : N ≤ M) :
    Set.Icc (-(N : ℝ)) N ⊆ Set.Icc (-(M : ℝ)) M := by
  intro x hx
  have hh : (N : ℝ) ≤ M := by exact_mod_cast h
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

lemma cutoff_function_mul {N M : ℕ} (h : N ≤ M) :
    (fun x => cutoffFunction M x * (Set.Icc (-(N : ℝ)) N).indicator (fun _ => (1 : ℂ)) x) =
      cutoffFunction N := by
  funext x
  by_cases hx : x ∈ Set.Icc (-(N : ℝ)) N
  · simp [cutoffFunction,Set.indicator_of_mem hx,Set.indicator_of_mem (cutoff_set_mono h hx)]
  · simp [cutoffFunction,Set.indicator_of_notMem hx]

lemma cutoff_cross_compression (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {A : H →ₗ.[ℂ] H} (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x => (x : ℂ)) A)
    {N M : ℕ} (hNM : N ≤ M) (ψ : H) :
    P (Set.Icc (-(M : ℝ)) M) (A (cutoffDomainMap hP hAP N ψ)) =
      TeschlQM.Shared.boundedSpectralIntegral P (cutoffFunction N) ψ := by
  have hp : P (Set.Icc (-(M : ℝ)) M) (P (Set.Icc (-(N : ℝ)) N) ψ) =
      P (Set.Icc (-(N : ℝ)) N) ψ := by
    have he := pvm_subset_mul hP measurableSet_Icc measurableSet_Icc (cutoff_set_mono hNM)
    rw [pvm_commute hP measurableSet_Icc measurableSet_Icc] at he
    exact congrArg (fun T : H →L[ℂ] H => T ψ) he
  have hd : cutoffDomainMap hP hAP M (P (Set.Icc (-(N : ℝ)) N) ψ) =
      cutoffDomainMap hP hAP N ψ := Subtype.ext hp
  have hc := cutoff_compression hP hAP M (P (Set.Icc (-(N : ℝ)) N) ψ)
  rw [hd] at hc
  rw [hc]
  have hi := boundedIntegral_mul hP (cutoffFunction M)
    ((Set.Icc (-(N : ℝ)) N).indicator (fun _ => (1 : ℂ)))
    (cutoffFunction_measurable M) (indicator_one_measurable measurableSet_Icc) M 1
    (cutoffFunction_bound M) (indicator_one_bound _)
  rw [cutoff_function_mul hNM,boundedIntegral_indicator hP measurableSet_Icc] at hi
  exact (congrArg (fun T : H →L[ℂ] H => T ψ) hi).symm

lemma cutoff_action (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {A : H →ₗ.[ℂ] H} (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x => (x : ℂ)) A)
    (N : ℕ) (ψ : H) :
    A (cutoffDomainMap hP hAP N ψ) =
      TeschlQM.Shared.boundedSpectralIntegral P (cutoffFunction N) ψ := by
  apply tendsto_nhds_unique (pvm_cutoff_tendsto hP (A (cutoffDomainMap hP hAP N ψ)))
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with M hM
  exact (cutoff_cross_compression hP hAP hM ψ).symm

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE SpectralCutoffAction

-- BEGIN COMPLETE MODULE BoundedIntegralCommute
section

open MeasureTheory

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma boundedIntegral_commute (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖g x‖ ≤ D) :
    TeschlQM.Shared.boundedSpectralIntegral P f * TeschlQM.Shared.boundedSpectralIntegral P g =
      TeschlQM.Shared.boundedSpectralIntegral P g * TeschlQM.Shared.boundedSpectralIntegral P f := by
  rw [← boundedIntegral_mul hP f g hf hg C D hC hD,
    ← boundedIntegral_mul hP g f hg hf D C hD hC]
  congr 1
  funext x
  exact mul_comm _ _

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE BoundedIntegralCommute

-- BEGIN COMPLETE MODULE ContinuousCalculus
section

open MeasureTheory

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma hc_boundedIntegral (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (ψ : H) (hψ : ψ ∈ TeschlQM.Dynamics.hc P) :
    TeschlQM.Shared.boundedSpectralIntegral P f ψ ∈ TeschlQM.Dynamics.hc P := by
  apply (hc_iff_atomless hP _).mpr
  intro a
  have hz := (spectralMeasure_zero_iff hP ψ (measurableSet_singleton a)).mp
    ((hc_iff_atomless hP ψ).mp hψ a)
  apply (spectralMeasure_zero_iff hP _ (measurableSet_singleton a)).mpr
  have he := congrArg (fun A : H →L[ℂ] H => A ψ)
    (boundedIntegral_commute_projection hP f hf C hC (measurableSet_singleton a))
  change TeschlQM.Shared.boundedSpectralIntegral P f (P {a} ψ) =
    P {a} (TeschlQM.Shared.boundedSpectralIntegral P f ψ) at he
  rw [← he,hz,map_zero]

lemma hc_projection (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {S : Set ℝ} (hS : MeasurableSet S) (ψ : H) (hψ : ψ ∈ TeschlQM.Dynamics.hc P) :
    P S ψ ∈ TeschlQM.Dynamics.hc P := by
  rw [← boundedIntegral_indicator hP hS]
  exact hc_boundedIntegral hP _ (indicator_one_measurable hS) 1 (indicator_one_bound S) ψ hψ

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE ContinuousCalculus

-- BEGIN COMPLETE MODULE ContinuousLinearSubspace
section

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma hc_smul (hP : TeschlQM.Shared.IsProjValuedMeasure P) (c : ℂ) (ψ : H)
    (hψ : ψ ∈ TeschlQM.Dynamics.hc P) : c • ψ ∈ TeschlQM.Dynamics.hc P := by
  apply (hc_iff_atomless hP _).mpr
  intro a
  have hz := (spectralMeasure_zero_iff hP ψ (measurableSet_singleton a)).mp
    ((hc_iff_atomless hP ψ).mp hψ a)
  apply (spectralMeasure_zero_iff hP _ (measurableSet_singleton a)).mpr
  simp [hz]

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE ContinuousLinearSubspace

-- BEGIN COMPLETE MODULE ResolventCutoffOrbit
section

open MeasureTheory

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

noncomputable def cutoffResolventVector (P : Set ℝ → (H →L[ℂ] H)) (N : ℕ) (z : ℂ) (ψ : H) : H :=
  TeschlQM.Shared.boundedSpectralIntegral P (cutoffFunction N) ψ - z • P (Set.Icc (-(N : ℝ)) N) ψ

lemma cutoffResolventVector_hc (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (N : ℕ) (z : ℂ) (ψ : H) (hψ : ψ ∈ TeschlQM.Dynamics.hc P) :
    cutoffResolventVector P N z ψ ∈ TeschlQM.Dynamics.hc P := by
  exact hc_sub hP
    (hc_boundedIntegral hP _ (cutoffFunction_measurable N) N (cutoffFunction_bound N) ψ hψ)
    (hc_smul hP z _ (hc_projection hP measurableSet_Icc ψ hψ))

lemma cutoff_resolvent_orbit (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {A : H →ₗ.[ℂ] H} (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x => (x : ℂ)) A)
    {z : ℂ} {R : H →L[ℂ] H} (hR : TeschlQM.Dynamics.IsResolventAt A z R)
    (N : ℕ) (ψ : H) (t : ℝ) :
    R (TeschlQM.Shared.timeEvolution P t (cutoffResolventVector P N z ψ)) =
      TeschlQM.Shared.timeEvolution P t (P (Set.Icc (-(N : ℝ)) N) ψ) := by
  have hcomm := congrArg (fun B : H →L[ℂ] H => B ψ)
    (boundedIntegral_commute hP (cutoffFunction N) (spectralPhase t)
      (cutoffFunction_measurable N) (spectralPhase_measurable t) N 1
      (cutoffFunction_bound N) (fun x => (spectralPhase_norm t x).le))
  change TeschlQM.Shared.boundedSpectralIntegral P (cutoffFunction N)
      (TeschlQM.Shared.timeEvolution P t ψ) =
    TeschlQM.Shared.timeEvolution P t (TeschlQM.Shared.boundedSpectralIntegral P (cutoffFunction N) ψ) at hcomm
  have hr := hR.1 (cutoffDomainMap hP hAP N (TeschlQM.Shared.timeEvolution P t ψ))
  rw [cutoff_action hP hAP N] at hr
  change R (TeschlQM.Shared.boundedSpectralIntegral P (cutoffFunction N)
    (TeschlQM.Shared.timeEvolution P t ψ) - z • P (Set.Icc (-(N : ℝ)) N)
    (TeschlQM.Shared.timeEvolution P t ψ)) = P (Set.Icc (-(N : ℝ)) N)
    (TeschlQM.Shared.timeEvolution P t ψ) at hr
  unfold cutoffResolventVector
  rw [map_sub,map_smul,← hcomm]
  rw [timeEvolution_commute_projection hP t measurableSet_Icc ψ]
  exact hr

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE ResolventCutoffOrbit

-- BEGIN COMPLETE MODULE FiniteRankDecay
section

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma finite_rank_sq_decay (u : ℝ → H) (hu : Continuous u)
    (hw : ∀ φ : H, Tendsto (timeMean (fun t => ‖⟪φ, u t⟫_ℂ‖^2)) atTop (𝓝 0))
    (K : H →L[ℂ] H) (hK : TeschlQM.Shared.IsFiniteRank K) :
    Tendsto (timeMean (fun t => ‖K (u t)‖^2)) atTop (𝓝 0) := by
  let V := LinearMap.range (K : H →ₗ[ℂ] H)
  let : FiniteDimensional ℂ V := hK
  let b := stdOrthonormalBasis ℂ V
  let w (i : Fin (Module.finrank ℂ V)) : H := K.adjoint (b i : H)
  have he : ∀ t : ℝ, ‖K (u t)‖^2 = ∑ i, ‖⟪w i, u t⟫_ℂ‖^2 := by
    intro t
    have h := b.sum_sq_norm_inner_right (⟨K (u t), ⟨u t, rfl⟩⟩ : V)
    change (∑ i, ‖⟪(b i : H), K (u t)⟫_ℂ‖^2) = ‖K (u t)‖^2 at h
    simpa only [w, ContinuousLinearMap.adjoint_inner_left] using h.symm
  have ha : ∀ T : ℝ, timeMean (fun t => ‖K (u t)‖^2) T =
      ∑ i, timeMean (fun t => ‖⟪w i, u t⟫_ℂ‖^2) T := by
    intro T
    simp_rw [he]
    unfold timeMean
    rw [intervalIntegral.integral_finsetSum]
    · exact Finset.mul_sum _ _ _
    · intro i _
      exact ((continuous_const.inner hu).norm.pow 2).intervalIntegrable _ _
  have hh := tendsto_finsetSum Finset.univ (fun i _ => hw (w i))
  simpa only [Finset.sum_const_zero, ← ha] using hh

lemma finite_rank_decay (u : ℝ → H) (hu : Continuous u)
    (hw : ∀ φ : H, Tendsto (timeMean (fun t => ‖⟪φ, u t⟫_ℂ‖^2)) atTop (𝓝 0))
    (K : H →L[ℂ] H) (hK : TeschlQM.Shared.IsFiniteRank K) :
    Tendsto (timeMean (fun t => ‖K (u t)‖)) atTop (𝓝 0) := by
  apply timeMean_tendsto_of_sq _ (K.continuous.comp hu).norm (fun _ => norm_nonneg _)
  exact finite_rank_sq_decay u hu hw K hK

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE FiniteRankDecay

-- BEGIN COMPLETE MODULE CompactDecay
section

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma mean_operator_comparison (u : ℝ → H) (hu : Continuous u) (B : ℝ)
    (hB : ∀ t, ‖u t‖ ≤ B) (K L : H →L[ℂ] H) {T : ℝ} (hT : 0 < T) :
    timeMean (fun t => ‖K (u t)‖) T ≤
      timeMean (fun t => ‖L (u t)‖) T + ‖K-L‖ * B := by
  apply timeMean_le_of_le_add (K.continuous.comp hu).norm (L.continuous.comp hu).norm _ hT
  intro t
  calc
    ‖K (u t)‖ ≤ ‖L (u t)‖ + ‖K (u t) - L (u t)‖ := norm_le_insert' _ _
    _ ≤ ‖L (u t)‖ + ‖K-L‖ * ‖u t‖ := by
      exact add_le_add le_rfl ((K-L).le_opNorm (u t))
    _ ≤ ‖L (u t)‖ + ‖K-L‖ * B := by gcongr; exact hB t

lemma compact_decay (u : ℝ → H) (hu : Continuous u) (B : ℝ)
    (hB : ∀ t, ‖u t‖ ≤ B)
    (hw : ∀ φ : H, Tendsto (timeMean (fun t => ‖⟪φ, u t⟫_ℂ‖^2)) atTop (𝓝 0))
    (K : H →L[ℂ] H) (hK : K ∈ TeschlQM.Shared.compactOperators H) :
    Tendsto (timeMean (fun t => ‖K (u t)‖)) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := (norm_nonneg (u 0)).trans (hB 0)
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact ha.trans_le (timeMean_nonneg (fun _ => norm_nonneg _) hT)
  · intro b hb
    obtain ⟨L, hL, hLK⟩ := Metric.mem_closure_iff.mp hK
      (b / (2 * (B+1))) (by positivity)
    have hLK' : ‖K-L‖ < b / (2*(B+1)) := by simpa [dist_eq_norm, norm_sub_rev] using hLK
    have hsmall : ‖K-L‖ * B < b/2 := by
      have hh := (lt_div_iff₀ (by positivity : 0 < 2*(B+1))).mp hLK'
      nlinarith [norm_nonneg (K-L)]
    have hlim := finite_rank_decay u hu hw L hL
    have he := hlim.eventually (gt_mem_nhds (by positivity : 0 < b/2))
    filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with T hT hT0
    have hc := mean_operator_comparison u hu B hB K L hT0
    linarith

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE CompactDecay

-- BEGIN COMPLETE MODULE NativeCompactDecay
section

open Filter Topology

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma native_compact_decay (hP : TeschlQM.Shared.IsProjValuedMeasure P) (ψ : H)
    (hψ : ψ ∈ TeschlQM.Dynamics.hc P)
    (hu : Continuous (fun t => TeschlQM.Shared.timeEvolution P t ψ))
    (K : H →L[ℂ] H) (hK : K ∈ TeschlQM.Shared.compactOperators H) :
    Tendsto (timeMean (fun t => ‖K (TeschlQM.Shared.timeEvolution P t ψ)‖)) atTop (𝓝 0) := by
  apply compact_decay _ hu ‖ψ‖ (fun t => (timeEvolution_norm hP t ψ).le) _ K hK
  intro φ
  exact native_wiener hP ψ φ ((hc_iff_atomless hP ψ).mp hψ)

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE NativeCompactDecay

-- BEGIN COMPLETE MODULE MeanApproximation
section

open Filter Topology

namespace TeschlQM.Dynamics.Proof

lemma timeMean_decay_of_approx (f : ℝ → ℝ) (hf : Continuous f) (hn : ∀ t, 0 ≤ f t)
    (ha : ∀ ε > 0, ∃ g : ℝ → ℝ, Continuous g ∧
      Tendsto (timeMean g) atTop (𝓝 0) ∧ ∀ t, f t ≤ g t + ε) :
    Tendsto (timeMean f) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact ha.trans_le (timeMean_nonneg hn hT)
  · intro b hb
    obtain ⟨g,hg,hlim,hfg⟩ := ha (b/2) (by positivity)
    filter_upwards [hlim.eventually (gt_mem_nhds (by positivity : 0 < b/2)),
      eventually_gt_atTop (0 : ℝ)] with T hT hT0
    have hh := timeMean_le_of_le_add hf hg hfg hT0
    linarith

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE MeanApproximation

-- BEGIN COMPLETE MODULE RelativeCompactDecay
section

open MeasureTheory Filter Topology

namespace TeschlQM.Dynamics.Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : Set ℝ → (H →L[ℂ] H)}

lemma relatively_compact_decay (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    {A : H →ₗ.[ℂ] H} (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x => (x : ℂ)) A)
    (K : H →L[ℂ] H)
    (hK : TeschlQM.Dynamics.IsRelativelyCompact ((K : H →ₗ[ℂ] H).toPMap ⊤) A)
    (ψ : H) (hψ : ψ ∈ TeschlQM.Dynamics.hc P) :
    Tendsto (timeMean (fun t => ‖K (TeschlQM.Shared.timeEvolution P t ψ)‖)) atTop (𝓝 0) := by
  obtain ⟨z,R,hR,C,hC,hKR⟩ := hK
  have hKR' : ∀ φ : H, K (R φ) = C φ := by
    intro φ
    obtain ⟨hφ,hh⟩ := hKR φ
    exact hh
  apply timeMean_decay_of_approx _ (K.continuous.comp (timeEvolution_continuous_apply hP ψ)).norm
    (fun _ => norm_nonneg _)
  intro ε hε
  have ht : Tendsto (fun N : ℕ => ‖ψ-P (Set.Icc (-(N : ℝ)) N) ψ‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ψ) atTop (𝓝 ψ)).sub
      (pvm_cutoff_tendsto hP ψ)).norm
  obtain ⟨N,hN⟩ := (ht.eventually (gt_mem_nhds (show 0 < ε/(‖K‖+1) by positivity))).exists
  let η := cutoffResolventVector P N z ψ
  have hη : η ∈ TeschlQM.Dynamics.hc P := cutoffResolventVector_hc hP N z ψ hψ
  have he : ∀ t : ℝ, K (TeschlQM.Shared.timeEvolution P t (P (Set.Icc (-(N : ℝ)) N) ψ)) =
      C (TeschlQM.Shared.timeEvolution P t η) := by
    intro t
    rw [← cutoff_resolvent_orbit hP hAP hR N ψ t]
    exact hKR' _
  refine ⟨fun t => ‖C (TeschlQM.Shared.timeEvolution P t η)‖,
    (C.continuous.comp (timeEvolution_continuous_apply hP η)).norm,
    native_compact_decay hP η hη (timeEvolution_continuous_apply hP η) C hC,?_⟩
  intro t
  have hb : ‖K‖ * ‖ψ-P (Set.Icc (-(N : ℝ)) N) ψ‖ < ε := by
    have hh := (lt_div_iff₀ (by positivity : 0 < ‖K‖+1)).mp hN
    nlinarith [norm_nonneg (ψ-P (Set.Icc (-(N : ℝ)) N) ψ)]
  have hn := K.le_opNorm (TeschlQM.Shared.timeEvolution P t (ψ-P (Set.Icc (-(N : ℝ)) N) ψ))
  rw [timeEvolution_norm hP] at hn
  simp only [map_sub] at hn
  have hh := norm_le_insert' (K (TeschlQM.Shared.timeEvolution P t ψ))
    (K (TeschlQM.Shared.timeEvolution P t (P (Set.Icc (-(N : ℝ)) N) ψ)))
  rw [he t] at hh
  rw [he t] at hn
  change ‖K (TeschlQM.Shared.timeEvolution P t ψ)‖ ≤
    ‖C (TeschlQM.Shared.timeEvolution P t η)‖ + ε
  linarith

end TeschlQM.Dynamics.Proof
end
-- END COMPLETE MODULE RelativeCompactDecay

-- BEGIN COMPLETE MODULE RAGERoot
section

open Filter Topology
open scoped ENNReal

namespace TeschlQM.Dynamics

/-- Teschl, Theorem 5.7 (RAGE), p. 129, (5.14): let `A = ∫ λ dP(λ)` be self-adjoint and let
`K_n ∈ 𝔏(ℌ)` be relatively compact operators converging strongly to `𝕀`. Then
`ℌ_c = {ψ | lim_{n→∞} lim_{T→∞} (1/T) ∫₀ᵀ ‖K_n e^{−itA} ψ‖ dt = 0}` (for each `n` the inner limit
exists, and these limits tend to `0`) and
`ℌ_pp = {ψ | lim_{n→∞} sup_{t≥0} ‖(𝕀 − K_n) e^{−itA} ψ‖ = 0}` (the supremum taken in `[0, ∞]`).
`ℌ_c = ℌ_ac ⊕ ℌ_sc` and `ℌ_pp` are defined from the spectral measures `μ_ψ` (3.83). -/
theorem rage {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (_hA : IsSelfAdjoint A)
    (P : Set ℝ → (H →L[ℂ] H)) (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x : ℝ => (x : ℂ)) A)
    (K : ℕ → H →L[ℂ] H) (hK : ∀ n, IsRelativelyCompact ((K n : H →ₗ[ℂ] H).toPMap ⊤) A)
    (hKI : ∀ ψ : H, Tendsto (fun n => K n ψ) atTop (𝓝 ψ)) :
    hc P = {ψ : H | ∃ L : ℕ → ℝ,
      (∀ n, Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, ‖K n (TeschlQM.Shared.timeEvolution P t ψ)‖)
        atTop (𝓝 (L n))) ∧ Tendsto L atTop (𝓝 0)} ∧
    hpp P = {ψ : H | Tendsto (fun n : ℕ => ⨆ t : Set.Ici (0 : ℝ),
      ‖TeschlQM.Shared.timeEvolution P t ψ - K n (TeschlQM.Shared.timeEvolution P t ψ)‖ₑ) atTop (𝓝 0)} := by
  have hdecay := Proof.rage_of_continuous_decay hP K hKI
    (fun ψ hψ n => Proof.relatively_compact_decay hP hAP (K n) (hK n) ψ hψ)
  unfold Proof.timeMean at hdecay
  simpa only [one_div] using hdecay

end TeschlQM.Dynamics

open TeschlQM.Dynamics

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (P : Set ℝ → (H →L[ℂ] H)) (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x : ℝ => (x : ℂ)) A)
    (K : ℕ → H →L[ℂ] H) (hK : ∀ n, IsRelativelyCompact ((K n : H →ₗ[ℂ] H).toPMap ⊤) A)
    (hKI : ∀ ψ : H, Tendsto (fun n => K n ψ) atTop (𝓝 ψ)) :
    hc P = {ψ : H | ∃ L : ℕ → ℝ,
      (∀ n, Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, ‖K n (TeschlQM.Shared.timeEvolution P t ψ)‖)
        atTop (𝓝 (L n))) ∧ Tendsto L atTop (𝓝 0)} ∧
    hpp P = {ψ : H | Tendsto (fun n : ℕ => ⨆ t : Set.Ici (0 : ℝ),
      ‖TeschlQM.Shared.timeEvolution P t ψ - K n (TeschlQM.Shared.timeEvolution P t ψ)‖ₑ) atTop (𝓝 0)} := TeschlQM.Dynamics.rage A hA P hP hAP K hK hKI
end
-- END COMPLETE MODULE RAGERoot
