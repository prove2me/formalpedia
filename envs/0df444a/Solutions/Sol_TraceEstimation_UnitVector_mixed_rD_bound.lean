-- Prove2me | solution 1 for TraceEstimation.UnitVector.mixed_rD_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:52:29.483194+00:00
-- url     : https://prove2.me/submissions/58d9b7c5-cf37-4cc8-86f4-d22d245cdc90

import Definitions.Def_TraceEstimation_UnitVector_unitVectorEstimator
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_TraceEstimation_UnitVector_mixingMatrix
import Definitions.Def_TraceEstimation_UnitVector_rD
import Definitions.Def_TraceEstimation_Shared_IsApproximator
import Mathlib.Analysis.Matrix.PosDef

section

open MeasureTheory ProbabilityTheory Matrix Finset
namespace CTrace
open TraceEstimation.UnitVector

instance uniform_prob {n : ℕ} [NeZero n] : IsProbabilityMeasure (uniformIndex n) := by
  unfold uniformIndex
  infer_instance

instance sample_prob {n M : ℕ} [NeZero n] : IsProbabilityMeasure (indexSampleMeasure n M) := by
  unfold indexSampleMeasure
  infer_instance

theorem integral_uniform {n : ℕ} [NeZero n] (f : Fin n → ℝ) :
    (∫ i,f i ∂uniformIndex n)=(n : ℝ)⁻¹ * ∑ i,f i := by
  rw [integral_fintype ((MemLp.of_discrete (p:=1)).integrable le_rfl)]
  simp only [Measure.real,uniformIndex,uniformOn_univ,Measure.count_singleton,Fintype.card_fin,
    ENNReal.toReal_inv,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_natCast,one_div,smul_eq_mul,←Finset.mul_sum]

theorem integral_eval {n M : ℕ} [NeZero n] (f : Fin n → ℝ) (i : Fin M) :
    (∫ k,f (k i) ∂indexSampleMeasure n M)=(n : ℝ)⁻¹ * ∑ j,f j := by
  rw [←integral_uniform f]
  have hp:=measurePreserving_eval (fun _ : Fin M=>uniformIndex n) i
  rw [←hp.map_eq]
  exact (integral_map hp.measurable.aemeasurable (by fun_prop)).symm

theorem estimator_diag {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin M → Fin n) :
    unitVectorEstimator A M k=(n : ℝ)/(M : ℝ)*∑ i,A (k i) (k i) := by
  simp [unitVectorEstimator,Matrix.mulVec_single,single_dotProduct]

theorem unit_mean {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    (∫ k,unitVectorEstimator A 1 k ∂indexSampleMeasure n 1)=A.trace := by
  simp only [estimator_diag,Nat.cast_one,div_one,Fin.sum_univ_one]
  rw [integral_const_mul]
  rw [integral_eval (fun i=>A i i) (0 : Fin 1)]
  have hn : (n : ℝ)≠0:=by exact_mod_cast NeZero.ne n
  rw [←mul_assoc,mul_inv_cancel₀ hn,one_mul]
  rfl

theorem unit_variance {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    variance (unitVectorEstimator A 1) (indexSampleMeasure n 1)=
      (n : ℝ)*∑ i,A i i^2-A.trace^2 := by
  rw [variance_eq_sub (MemLp.of_discrete),unit_mean]
  congr 1
  change (∫ k,(unitVectorEstimator A 1 k)^2 ∂indexSampleMeasure n 1) = _
  simp only [estimator_diag,Nat.cast_one,div_one,Fin.sum_univ_one,mul_pow]
  rw [integral_const_mul]
  rw [integral_eval (fun i=>A i i^2) (0 : Fin 1)]
  have hn : (n : ℝ)≠0:=by exact_mod_cast NeZero.ne n
  field_simp

end CTrace
end

section

open MeasureTheory ProbabilityTheory Matrix Finset
open scoped NNReal
namespace CTrace
open TraceEstimation.UnitVector

theorem abs_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (c : ℝ≥0) (hX : HasSubgaussianMGF X c P) (t : ℝ) (ht : 0 ≤ t) :
    P.real {ω | t ≤ |X ω|} ≤ 2*Real.exp (-t^2/(2*c)) := by
  have he : {ω | t ≤ |X ω|}={ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
    ext ω
    simp only [Set.mem_setOf_eq,Set.mem_union,le_abs]
  rw [he]
  have h1:=hX.measure_ge_le ht
  have h2:=hX.neg.measure_ge_le ht
  have h3:=measureReal_union_le (μ:=P) {ω | t ≤ X ω} {ω | t ≤ -X ω}
  dsimp only [Pi.neg_apply] at h2
  linarith

theorem bounded_average_tail {n M : ℕ} [NeZero n] (hM : 0 < M) (f : Fin n → ℝ)
    (D : ℝ) (hD : 0 < D) (hf : ∀ i,f i∈Set.Icc 0 D) (t : ℝ) (ht : 0 ≤ t) :
    (indexSampleMeasure n M).real {k | t ≤ |(M : ℝ)⁻¹*∑ i,f (k i)-(n : ℝ)⁻¹*∑ j,f j|} ≤
      2*Real.exp (-2*(M : ℝ)*t^2/D^2) := by
  let m : ℝ:=(n : ℝ)⁻¹*∑ j,f j
  let Y : Fin M → (Fin M → Fin n) → ℝ:=fun i k=>f (k i)-m
  let c : ℝ≥0:=(‖D‖₊/2)^2
  have hsub : ∀ i,HasSubgaussianMGF (Y i) c (indexSampleMeasure n M) := by
    intro i
    have hh:=hasSubgaussianMGF_of_mem_Icc (μ:=indexSampleMeasure n M)
      (X:=fun k=>f (k i)) (Measurable.of_discrete.aemeasurable) (ae_of_all _ fun k=>hf (k i))
    rw [integral_eval] at hh
    simpa only [sub_zero] using hh
  have hind : iIndepFun Y (indexSampleMeasure n M) := by
    exact iIndepFun_pi (fun i=>(show Measurable (fun j=>f j-m) from by fun_prop).aemeasurable)
  have hs:=HasSubgaussianMGF.sum_of_iIndepFun (c:=fun _=>c) (s:=Finset.univ) hind (fun i _=>hsub i)
  have htail:=abs_tail (indexSampleMeasure n M) (fun k=>∑ i,Y i k) (∑ _ : Fin M,c)
    (by simpa using hs) ((M : ℝ)*t) (mul_nonneg (Nat.cast_nonneg _) ht)
  have hM0 : (M : ℝ)≠0:=by exact_mod_cast hM.ne'
  have he : {k : Fin M → Fin n | (M : ℝ)*t ≤ |∑ i,Y i k|}=
      {k | t ≤ |(M : ℝ)⁻¹*∑ i,f (k i)-m|} := by
    ext k
    have hx : (∑ i,Y i k)=(M : ℝ)*((M : ℝ)⁻¹*∑ i,f (k i)-m) := by
      simp [Y,Finset.sum_sub_distrib]
      field_simp
    rw [Set.mem_setOf_eq,Set.mem_setOf_eq,hx,abs_mul,abs_of_pos (by exact_mod_cast hM)]
    exact mul_le_mul_iff_right₀ (by exact_mod_cast hM)
  rw [he] at htail
  have hc : ((∑ _ : Fin M,c) : ℝ≥0)=(M : ℝ≥0)*c := by simp
  have hcval : (c : ℝ)=(D/2)^2 := by simp [c,Real.norm_eq_abs,abs_of_pos hD]
  convert htail using 1
  congr 2
  simp only [hc,NNReal.coe_mul,NNReal.coe_natCast,hcval]
  field_simp

end CTrace
end

section

open MeasureTheory ProbabilityTheory Matrix Finset
open scoped NNReal
namespace CTrace
open TraceEstimation.UnitVector

instance sign_prob (n : ℕ) : IsProbabilityMeasure (signMeasure n) := by
  unfold signMeasure
  infer_instance

theorem rademacher_Icc : ∀ᵐ x ∂rademacher,x∈Set.Icc (-1 : ℝ) 1 := by
  simp [rademacher,Measure.ae_ennreal_smul_measure_iff,ae_add_measure_iff]

theorem rademacher_mean : (∫ x,x ∂rademacher)=0 := by
  rw [rademacher,integral_smul_measure,integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp))]
  simp

theorem rademacher_subG : HasSubgaussianMGF id 1 rademacher := by
  have h:=hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (X:=id) (μ:=rademacher)
    (by fun_prop) rademacher_Icc rademacher_mean
  norm_num at h
  exact h

theorem subG_mono {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (c d : ℝ≥0) (hc : c ≤ d) (h : HasSubgaussianMGF X c P) : HasSubgaussianMGF X d P where
  integrable_exp_mul:=h.integrable_exp_mul
  mgf_le t := by
    apply (h.mgf_le t).trans
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right (show (c : ℝ) ≤ d from hc) (sq_nonneg t)

theorem sign_linear_subG {n : ℕ} (w : Fin n → ℝ) :
    HasSubgaussianMGF (fun d=>∑ i,w i*d i) (∑ i : Fin n,(⟨w i^2,sq_nonneg _⟩ : ℝ≥0)) (signMeasure n) := by
  have hsub : ∀ i : Fin n,HasSubgaussianMGF (fun d : Fin n → ℝ=>w i*d i)
      (⟨w i^2,sq_nonneg _⟩ : ℝ≥0) (signMeasure n) := by
    intro i
    have hp:=measurePreserving_eval (fun _ : Fin n=>rademacher) i
    have hg:=rademacher_subG
    rw [←hp.map_eq] at hg
    have hh:=HasSubgaussianMGF.of_map hp.measurable.aemeasurable hg
    have hconst:=hh.const_mul (w i)
    have hcg : (⟨w i^2,sq_nonneg _⟩ : ℝ≥0)*1=⟨w i^2,sq_nonneg _⟩ := by
      apply Subtype.ext
      change (w i)^2*(1 : ℝ)=(w i)^2
      ring
    erw [hcg] at hconst
    exact hconst
  have hi : iIndepFun (fun i (d : Fin n → ℝ)=>w i*d i) (signMeasure n):=
    iIndepFun_pi (fun i=>(by fun_prop : Measurable (fun x : ℝ=>w i*x)).aemeasurable)
  simpa using HasSubgaussianMGF.sum_of_iIndepFun (s:=Finset.univ) hi (fun i _=>hsub i)

theorem sign_linear_tail {n : ℕ} (w : Fin n → ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hw : ∑ i,w i^2 ≤ v) (t : ℝ) (ht : 0 ≤ t) :
    (signMeasure n).real {d | t ≤ |∑ i,w i*d i|} ≤ 2*Real.exp (-t^2/(2*v)) := by
  apply abs_tail (signMeasure n) _ ⟨v,hv⟩ _ t ht
  apply subG_mono (signMeasure n) _ _ ⟨v,hv⟩ _ (sign_linear_subG w)
  apply NNReal.coe_le_coe.mp
  change (↑(∑ i : Fin n,(⟨w i^2,sq_nonneg _⟩ : ℝ≥0)) : ℝ) ≤ v
  exact (NNReal.coe_sum Finset.univ (fun i : Fin n=>(⟨w i^2,sq_nonneg _⟩ : ℝ≥0))).trans_le hw

end CTrace

end

section

open MeasureTheory ProbabilityTheory Matrix Finset
namespace CTrace
open TraceEstimation.UnitVector

theorem approximator_of_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hm : Measurable X) (a t δ : ℝ)
    (h : P.real {ω | t ≤ |X ω-a|} ≤ δ) : 1-δ ≤ P.real {ω | |X ω-a| ≤ t} := by
  have hb : P.real ({ω | |X ω-a| ≤ t}ᶜ) ≤ δ :=
    (measureReal_mono (by intro ω hω; simp only [Set.mem_compl_iff,Set.mem_setOf_eq,not_le] at hω ⊢; exact hω.le)).trans h
  have he:=measureReal_add_measureReal_compl (μ:=P) (s:={ω | |X ω-a| ≤ t}) (measurableSet_le (hm.sub_const a).abs measurable_const)
  rw [probReal_univ] at he
  linarith

theorem diag_max {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : A i i ≤ maxDiag A := by
  unfold maxDiag
  rw [dif_pos Finset.univ_nonempty]
  exact Finset.le_sup' (fun j=>A j j) (Finset.mem_univ i)

theorem diag_zero_of_trace_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hz : A.trace=0) : ∀ i,A i i=0 := by
  intro i
  have hh : A i i ≤ A.trace:=Finset.single_le_sum (f:=fun j=>A j j) (fun j _=>hA.diag_nonneg) (Finset.mem_univ i)
  exact le_antisymm (by simpa [hz] using hh) hA.diag_nonneg

theorem unit_approximator {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (_hδ1 : δ < 1) (M : ℕ) (hM : 0 < M)
    (hMbound : (1/2 : ℝ)*ε⁻¹^2*Real.log (2/δ)*rD A^2 ≤ (M : ℝ)) :
    TraceEstimation.Shared.IsApproximator (indexSampleMeasure n M) (unitVectorEstimator A M) A ε δ := by
  haveI : NeZero n:=⟨hn.ne'⟩
  by_cases hz : A.trace=0
  · have hd:=diag_zero_of_trace_zero A hA hz
    have he : unitVectorEstimator A M=0 := by
      funext k
      simp [estimator_diag,hd]
    simp [TraceEstimation.Shared.IsApproximator,he,hz,probReal_univ,hδ.le]
  have htr : 0 < A.trace:=lt_of_le_of_ne hA.trace_nonneg (Ne.symm hz)
  let D : ℝ:=(n : ℝ)*maxDiag A
  have hD : 0 < D := by
    have hh : A.trace ≤ D := by
      exact (Finset.sum_le_sum fun i _=>diag_max A i).trans_eq (by simp [D,Matrix.trace,Matrix.diag])
    exact htr.trans_le hh
  let f : Fin n → ℝ:=fun i=>(n : ℝ)*A i i
  have hf : ∀ i,f i∈Set.Icc 0 D := fun i=>⟨mul_nonneg (Nat.cast_nonneg _) hA.diag_nonneg,
    mul_le_mul_of_nonneg_left (diag_max A i) (Nat.cast_nonneg _)⟩
  have htail:=bounded_average_tail hM f D hD hf (ε*A.trace) (mul_pos hε htr).le
  have hn0 : (n : ℝ)≠0:=by exact_mod_cast hn.ne'
  have hmean : (n : ℝ)⁻¹*∑ i,f i=A.trace := by
    dsimp [f]
    rw [←Finset.mul_sum,←mul_assoc,inv_mul_cancel₀ hn0,one_mul]
    rfl
  have hest : ∀ k : Fin M → Fin n,(M : ℝ)⁻¹*∑ i,f (k i)=unitVectorEstimator A M k := by
    intro k
    rw [estimator_diag]
    simp only [f,←Finset.mul_sum,div_eq_mul_inv]
    ring
  simp only [hest,hmean] at htail
  have hlog : Real.log (2/δ) ≤ 2*(M : ℝ)*(ε*A.trace)^2/D^2 := by
    have hh:=mul_le_mul_of_nonneg_right hMbound (show 0 ≤ 2*(ε*A.trace)^2/D^2 by positivity)
    have he : ((1/2 : ℝ)*ε⁻¹^2*Real.log (2/δ)*rD A^2)*(2*(ε*A.trace)^2/D^2)=Real.log (2/δ) := by
      unfold rD
      dsimp [D]
      have hd0 : maxDiag A≠0 := by intro hh; simp [D,hh] at hD
      field_simp
      <;> ring
    rw [he] at hh
    calc
      _ ≤ (M : ℝ)*(2*(ε*A.trace)^2/D^2) := hh
      _ = _ := by ring
  have hexp : 2*Real.exp (-2*(M : ℝ)*(ε*A.trace)^2/D^2) ≤ δ := by
    calc
    _ ≤ 2*Real.exp (-Real.log (2/δ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      calc
        _ = -(2*(M : ℝ)*(ε*A.trace)^2/D^2) := by ring
        _ ≤ _ := neg_le_neg hlog
    _ = δ := by
      rw [Real.exp_neg,Real.exp_log (div_pos (by norm_num) hδ)]
      field_simp
  exact approximator_of_tail (indexSampleMeasure n M) (unitVectorEstimator A M)
    Measurable.of_discrete A.trace (ε*A.trace) δ (htail.trans hexp)

end CTrace
end

section

open MeasureTheory ProbabilityTheory Matrix Finset
set_option maxHeartbeats 500000
namespace CTrace
open TraceEstimation.UnitVector

theorem eta_entry {n : ℕ} [NeZero n] (F : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (F i j)^2 ≤ eta F := by
  unfold eta
  rw [dif_pos Finset.univ_nonempty]
  convert! Finset.le_sup' (fun p : Fin n×Fin n=>|F p.1 p.2|^2) (Finset.mem_univ (i,j)) using 1 <;> simp only [sq_abs]

theorem mixing_entry_eq {n m : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin n) (Fin m) ℝ)
    (d : Fin n → ℝ) (i : Fin n) (j : Fin m) :
    (mixingMatrix F d*U) i j=∑ l,(F i l*U l j)*d l := by
  simp only [mixingMatrix,Matrix.mul_diagonal,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro l hl
  simp [Matrix.diagonal]
  <;> ring

theorem mixing_weights {n m : ℕ} [NeZero n] (F : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin m) ℝ) (hU : Uᵀ*U=1) (i : Fin n) (j : Fin m) :
    ∑ l,(F i l*U l j)^2 ≤ eta F := by
  have hu : ∑ l,U l j^2=1 := by
    have h:=congrArg (fun N : Matrix (Fin m) (Fin m) ℝ=>N j j) hU
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq,pow_two] using h
  calc
    _ = ∑ l,(F i l)^2*(U l j)^2 := by simp [mul_pow]
    _ ≤ ∑ l,eta F*(U l j)^2 := Finset.sum_le_sum (fun l _=>mul_le_mul_of_nonneg_right (eta_entry F i l) (sq_nonneg _))
    _ = eta F := by rw [←Finset.mul_sum,hu,mul_one]

theorem mixing_good {n m : ℕ} (hn : 0 < n) (F : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin m) ℝ) (hU : Uᵀ*U=1) (δ : ℝ) (hδ : 0 < δ) :
    1-δ ≤ (signMeasure n).real {d | ∀ i j,|(mixingMatrix F d*U) i j| ≤
      Real.sqrt (2*eta F*Real.log (2*(m : ℝ)*(n : ℝ)/δ))} := by
  haveI : NeZero n:=⟨hn.ne'⟩
  by_cases hm : m=0
  · subst m
    simp only [Fin.forall_fin_zero,implies_true,Set.setOf_true,probReal_univ]
    linarith
  have hmpos : 0 < m:=Nat.pos_of_ne_zero hm
  have hnR : 0 < (n : ℝ):=by exact_mod_cast hn
  have hmR : 0 < (m : ℝ):=by exact_mod_cast hmpos
  have heta : 0 ≤ eta F := (sq_nonneg (F 0 0)).trans (eta_entry F 0 0)
  by_cases he0 : eta F=0
  · have hF0 : F=0 := by
      ext i j
      have h:=eta_entry F i j
      rw [he0] at h
      simpa using (sq_eq_zero_iff.mp (le_antisymm h (sq_nonneg _)))
    subst F
    simp only [mixingMatrix,Matrix.zero_mul,Matrix.zero_apply,abs_zero]
    have he : {d : Fin n → ℝ | ∀ i : Fin n,∀ j : Fin m,0 ≤ Real.sqrt (2*eta (0 : Matrix (Fin n) (Fin n) ℝ)*Real.log (2*(m : ℝ)*(n : ℝ)/δ))}=Set.univ := by
      ext d; simp [Real.sqrt_nonneg]
    rw [he,probReal_univ]
    linarith
  have hetaP : 0 < eta F:=lt_of_le_of_ne heta (Ne.symm he0)
  by_cases hd1 : 1 ≤ δ
  · exact (sub_nonpos.mpr hd1).trans measureReal_nonneg
  have hδ1 : δ < 1:=lt_of_not_ge hd1
  let R : ℝ:=Real.sqrt (2*eta F*Real.log (2*(m : ℝ)*(n : ℝ)/δ))
  have hratio : 1 < 2*(m : ℝ)*(n : ℝ)/δ := by
    have hmn : (1 : ℝ) ≤ m:=by exact_mod_cast hmpos
    have hnn : (1 : ℝ) ≤ n:=by exact_mod_cast hn
    apply (lt_div_iff₀ hδ).mpr
    nlinarith [mul_le_mul hmn hnn (by norm_num) hmR.le]
  have hr : R^2=2*eta F*Real.log (2*(m : ℝ)*(n : ℝ)/δ):=
    Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) heta) (Real.log_nonneg hratio.le))
  have hentry : ∀ p : Fin n×Fin m,(signMeasure n).real {d | R < |(mixingMatrix F d*U) p.1 p.2|} ≤ δ/((m : ℝ)*(n : ℝ)) := by
    intro p
    have ht:=sign_linear_tail (fun l=>F p.1 l*U l p.2) (eta F) heta (mixing_weights F U hU p.1 p.2) R (Real.sqrt_nonneg _)
    have hh : (signMeasure n).real {d | R < |(mixingMatrix F d*U) p.1 p.2|} ≤
        2*Real.exp (-R^2/(2*eta F)) := by
      apply le_trans (measureReal_mono _) ht
      intro d hd
      simpa only [Set.mem_setOf_eq,←mixing_entry_eq] using hd.le
    apply hh.trans_eq
    rw [hr]
    have he : -(2*eta F*Real.log (2*(m : ℝ)*(n : ℝ)/δ))/(2*eta F) =
        -Real.log (2*(m : ℝ)*(n : ℝ)/δ) := by field_simp
    rw [he,Real.exp_neg,Real.exp_log (lt_trans zero_lt_one hratio)]
    field_simp
    <;> ring
  let Bad : Set (Fin n → ℝ):=⋃ p : Fin n×Fin m,{d | R < |(mixingMatrix F d*U) p.1 p.2|}
  have hbad : (signMeasure n).real Bad ≤ δ := by
    apply (measureReal_iUnion_fintype_le _).trans
    apply (Finset.sum_le_sum fun p _=>hentry p).trans_eq
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]
    field_simp
    <;> ring
  have hgood : {d : Fin n → ℝ | ∀ i j,|(mixingMatrix F d*U) i j| ≤ R}=Badᶜ := by
    ext d
    simp [Bad,not_lt]
  change 1-δ ≤ (signMeasure n).real {d | ∀ i j,|(mixingMatrix F d*U) i j| ≤ R}
  rw [hgood,measureReal_compl (by
    apply MeasurableSet.iUnion
    intro p
    apply measurableSet_lt measurable_const
    simp only [mixing_entry_eq]
    fun_prop),probReal_univ]
  linarith

end CTrace
end

section

open MeasureTheory ProbabilityTheory Matrix Finset
namespace CTrace
open TraceEstimation.UnitVector

theorem sign_square (n : ℕ) : ∀ᵐ d ∂signMeasure n,∀ i,d i^2=1 := by
  rw [ae_all_iff]
  intro i
  exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin n=>rademacher) i).ae
    (show ∀ᵐ x ∂rademacher,x^2=1 by simp [rademacher,ae_add_measure_iff])

theorem mixing_orthogonal {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : Fᵀ*F=1)
    (d : Fin n → ℝ) (hd : ∀ i,d i^2=1) : (mixingMatrix F d)ᵀ*mixingMatrix F d=1 := by
  simp only [mixingMatrix,Matrix.transpose_mul,Matrix.diagonal_transpose]
  rw [Matrix.mul_assoc,←Matrix.mul_assoc Fᵀ F,hF,Matrix.one_mul,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simpa only [pow_two] using hd i

theorem trace_conjugate {n : ℕ} (A M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ*M=1) :
    (M*A*Mᵀ).trace=A.trace := by
  rw [Matrix.trace_mul_cycle,hM,Matrix.one_mul]

theorem psd_conjugate {n : ℕ} (A M : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) :
    (M*A*Mᵀ).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.mul_mul_conjTranspose_same M

theorem eigen_orthogonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ*hA.eigenvectorUnitary=1 := by
  simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial]
    using Unitary.coe_star_mul_self hA.eigenvectorUnitary

theorem diagonal_spectral {n : ℕ} (A M : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (j : Fin n) : (M*A*Mᵀ) j j=∑ k,hA.eigenvalues k*((M*hA.eigenvectorUnitary) j k)^2 := by
  have hs : A=(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)*Matrix.diagonal hA.eigenvalues*
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
    simpa only [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial,Function.comp_def,RCLike.ofReal_real_eq_id,id_eq] using hA.spectral_theorem
  let U : Matrix (Fin n) (Fin n) ℝ:=hA.eigenvectorUnitary
  have he : M*A*Mᵀ=(M*U)*Matrix.diagonal hA.eigenvalues*(M*U)ᵀ := by
    conv_lhs => rw [hs]
    simp only [U,Matrix.transpose_mul,Matrix.mul_assoc]
  rw [he,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Matrix.mul_diagonal,Matrix.transpose_apply]
  ring

theorem diagonal_bound {n : ℕ} (A M : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (R : ℝ) (hR : 0 ≤ R) (hb : ∀ i j,|(M*hA.isHermitian.eigenvectorUnitary) i j| ≤ R) :
    ∀ j,0 ≤ (M*A*Mᵀ) j j ∧ (M*A*Mᵀ) j j ≤ R^2*A.trace := by
  intro j
  refine ⟨(psd_conjugate A M hA).diag_nonneg,?_⟩
  rw [diagonal_spectral A M hA.isHermitian j,hA.isHermitian.trace_eq_sum_eigenvalues,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hsq : ((M*hA.isHermitian.eigenvectorUnitary) j k)^2 ≤ R^2 := by
    have h:=hb j k
    have hh:=pow_le_pow_left₀ (abs_nonneg ((M*hA.isHermitian.eigenvectorUnitary) j k)) h 2
    simpa only [sq_abs] using hh
  convert! mul_le_mul_of_nonneg_left hsq (hA.eigenvalues_nonneg k) using 1 <;> simp [RCLike.ofReal_real_eq_id,id_eq,mul_comm]

theorem ratio_of_diag {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (β : ℝ) (hβ : 0 ≤ β) (hb : ∀ i,A i i ≤ β*A.trace) : rD A ≤ (n : ℝ)*β := by
  unfold rD
  have hd : maxDiag A ≤ β*A.trace := by
    unfold maxDiag
    rw [dif_pos Finset.univ_nonempty]
    exact Finset.sup'_le _ _ (fun i _=>hb i)
  by_cases hz : A.trace=0
  · simp only [hz,div_zero]
    positivity
  · apply (div_le_iff₀ (lt_of_le_of_ne hA.trace_nonneg (Ne.symm hz))).mpr
    calc
      _ ≤ (n : ℝ)*(β*A.trace) := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)
      _ = _ := by ring

end CTrace

end

section

open MeasureTheory ProbabilityTheory Matrix Finset
namespace CTrace
open TraceEstimation.UnitVector

theorem mixed_diagonal {n : ℕ} (hn : 0 < n) (F : Matrix (Fin n) (Fin n) ℝ) (hF : Fᵀ*F=1)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1-δ/2 ≤ (signMeasure n).real
      {d | (∀ j,0 ≤ (mixingMatrix F d*A*(mixingMatrix F d)ᵀ) j j ∧
        (mixingMatrix F d*A*(mixingMatrix F d)ᵀ) j j ≤ 2*eta F*Real.log (4*(n : ℝ)^2/δ)*A.trace) ∧
        rD (mixingMatrix F d*A*(mixingMatrix F d)ᵀ) ≤ 2*(n : ℝ)*eta F*Real.log (4*(n : ℝ)^2/δ)} := by
  haveI : NeZero n:=⟨hn.ne'⟩
  have hnR : 0 < (n : ℝ):=by exact_mod_cast hn
  have hnn : (1 : ℝ) ≤ n:=by exact_mod_cast hn
  have heta : 0 ≤ eta F:=(sq_nonneg (F 0 0)).trans (eta_entry F 0 0)
  have hlog : 0 ≤ Real.log (4*(n : ℝ)^2/δ) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  let β : ℝ:=2*eta F*Real.log (4*(n : ℝ)^2/δ)
  have hβ : 0 ≤ β:=mul_nonneg (mul_nonneg (by norm_num) heta) hlog
  have hg:=mixing_good hn F (hA.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    (eigen_orthogonal A hA.isHermitian) (δ/2) (half_pos hδ)
  have harg : 2*(n : ℝ)*(n : ℝ)/(δ/2)=4*(n : ℝ)^2/δ := by ring
  rw [harg] at hg
  apply hg.trans
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [sign_square n] with d hd
  intro hgood
  have hdiag:=diagonal_bound A (mixingMatrix F d) hA (Real.sqrt β) (Real.sqrt_nonneg _) hgood
  rw [Real.sq_sqrt hβ] at hdiag
  have htrace:=trace_conjugate A (mixingMatrix F d) (mixing_orthogonal F hF d hd)
  refine ⟨hdiag,?_⟩
  have hratio:=ratio_of_diag (mixingMatrix F d*A*(mixingMatrix F d)ᵀ)
    (psd_conjugate A (mixingMatrix F d) hA) β hβ (by simpa only [htrace] using fun j=>(hdiag j).2)
  simpa only [β,mul_assoc,mul_left_comm,mul_comm] using hratio

end CTrace
end

section
open MeasureTheory ProbabilityTheory Matrix TraceEstimation TraceEstimation.UnitVector
theorem solution {n : ℕ} (hn : 0 < n)
    (F : Matrix (Fin n) (Fin n) ℝ) (hF : Fᵀ * F = 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ / 2 ≤ (signMeasure n).real
      {d | (∀ j, 0 ≤ (mixingMatrix F d * A * (mixingMatrix F d)ᵀ) j j ∧
              (mixingMatrix F d * A * (mixingMatrix F d)ᵀ) j j ≤
                2 * eta F * Real.log (4 * (n : ℝ) ^ 2 / δ) * A.trace) ∧
        rD (mixingMatrix F d * A * (mixingMatrix F d)ᵀ) ≤
          2 * (n : ℝ) * eta F * Real.log (4 * (n : ℝ) ^ 2 / δ)} := by
  exact CTrace.mixed_diagonal hn F hF A hA δ hδ hδ1

end
