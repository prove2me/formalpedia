-- Prove2me | solution 1 for TraceEstimation.Rayleigh.rayleigh_estimator_approximator
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:10:52.200315+00:00
-- url     : https://prove2.me/submissions/075345eb-2740-47ee-9b01-cfbdb9da2971

import Definitions.Def_TraceEstimation_UnitVector_unitVectorEstimator
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_TraceEstimation_UnitVector_mixingMatrix
import Definitions.Def_TraceEstimation_UnitVector_rD
import Definitions.Def_TraceEstimation_Shared_IsApproximator
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_TraceEstimation_Rayleigh_kappaF
import Definitions.Def_TraceEstimation_Rayleigh_rayleighEstimator

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
open TraceEstimation.Rayleigh

theorem kappa_eigen_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (hA0 : A≠0) :
    0 < A.rank ∧ 0 < kappaF hA.isHermitian ∧
      ∀ i,hA.isHermitian.eigenvalues i ≤ A.trace*kappaF hA.isHermitian/(A.rank : ℝ) := by
  classical
  let lam : Fin n → ℝ:=hA.isHermitian.eigenvalues
  let E:=nonzeroEigenvalues hA.isHermitian
  have heig : ∃ i,lam i≠0 := by
    by_contra h
    apply hA0
    apply hA.isHermitian.eigenvalues_eq_zero_iff.mp
    funext i
    simpa [lam] using not_exists.mp h i
  obtain ⟨j,hj⟩:=heig
  have hemem : ∀ x,x∈E ↔ ∃ i,lam i≠0 ∧ lam i=x := by
    intro x
    simp [E,nonzeroEigenvalues,lam]
  have hE : E.Nonempty:=⟨lam j,(hemem _).mpr ⟨j,hj,rfl⟩⟩
  let lo:=E.min' hE
  let hi:=E.max' hE
  have hlo : 0 < lo := by
    obtain ⟨i,hi,he⟩:=(hemem _).mp (Finset.min'_mem E hE)
    change 0 < E.min' hE
    rw [←he]
    exact lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm hi)
  have hhi : 0 < hi := hlo.trans_le (Finset.min'_le E hi (Finset.max'_mem E hE))
  have hc : (Finset.univ.filter (fun i=>lam i≠0)).card=A.rank := by
    rw [hA.isHermitian.rank_eq_card_non_zero_eigs]
    exact (Fintype.card_subtype (fun i=>lam i≠0)).symm
  have hr : 0 < A.rank := by
    rw [←hc,Finset.card_pos]
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  have htr : (A.rank : ℝ)*lo ≤ A.trace := by
    have hh : (∑ i∈Finset.univ.filter (fun i=>lam i≠0),lo) ≤ ∑ i∈Finset.univ.filter (fun i=>lam i≠0),lam i := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.min'_le E (lam i) ((hemem _).mpr ⟨i,(Finset.mem_filter.mp hi).2,rfl⟩)
    have hsum : (∑ i∈Finset.univ.filter (fun i=>lam i≠0),lam i)=A.trace := by
      rw [hA.isHermitian.trace_eq_sum_eigenvalues]
      simp only [RCLike.ofReal_real_eq_id,id_eq]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs with hz
      · rfl
      · simp only [not_not] at hz
        exact hz.symm
    simpa only [Finset.sum_const,hc,nsmul_eq_mul,hsum] using hh
  have hk : kappaF hA.isHermitian=hi/lo := by
    unfold kappaF
    rw [dif_pos hE]
  have hkpos : 0 < kappaF hA.isHermitian:=by rw [hk];exact div_pos hhi hlo
  refine ⟨hr,hkpos,?_⟩
  intro i
  have hlamhi : lam i ≤ hi := by
    by_cases hz : lam i=0
    · simpa [hz] using hhi.le
    · exact Finset.le_max' E (lam i) ((hemem _).mpr ⟨i,hz,rfl⟩)
  apply hlamhi.trans
  rw [hk]
  apply (le_div_iff₀ (by exact_mod_cast hr : 0 < (A.rank : ℝ))).mpr
  calc
    hi*(A.rank : ℝ) = ((A.rank : ℝ)*lo)*(hi/lo) := by field_simp
    _ ≤ A.trace*(hi/lo) := mul_le_mul_of_nonneg_right htr (div_nonneg hhi.le hlo.le)

theorem quadratic_upper {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (b : ℝ) (hb : ∀ i,hA.eigenvalues i ≤ b) (z : Fin n → ℝ) :
    z⬝ᵥ(A*ᵥz) ≤ b*(z⬝ᵥz) := by
  let M : Matrix (Fin n) (Fin n) ℝ:=fun _ k=>z k
  let U : Matrix (Fin n) (Fin n) ℝ:=hA.eigenvectorUnitary
  have hu : U*Uᵀ=1 := by
    simpa only [U,Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hn : (∑ k,(M*U) 0 k^2)=z⬝ᵥz := by
    have he : (M*U)*(M*U)ᵀ=M*Mᵀ := by
      rw [Matrix.transpose_mul,Matrix.mul_assoc,←Matrix.mul_assoc U Uᵀ,hu,Matrix.one_mul]
    have hh:=congrArg (fun N : Matrix (Fin n) (Fin n) ℝ=>N 0 0) he
    change (∑ k,(M*U) 0 k*(M*U) 0 k)=∑ k,z k*z k at hh
    simpa only [pow_two,dotProduct] using hh
  have he : (M*A*Mᵀ) 0 0=z⬝ᵥ(A*ᵥz) := by
    rw [Matrix.mul_assoc]
    rfl
  rw [←he,diagonal_spectral A M hA 0]
  calc
    _ ≤ ∑ k,b*(M*U) 0 k^2 := Finset.sum_le_sum (fun k _=>mul_le_mul_of_nonneg_right (hb k) (sq_nonneg _))
    _ = b*(z⬝ᵥz) := by rw [←Finset.mul_sum,hn]

end CTrace
end

section

open MeasureTheory ProbabilityTheory Matrix Finset
open scoped NNReal
namespace CTrace

theorem indep_average_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {M : ℕ} (hM : 0 < M) (X : Fin M → Ω → ℝ) (hX : ∀ i,Measurable (X i))
    (hind : iIndepFun X P) (μ D : ℝ) (hD : 0 < D)
    (hb : ∀ i,∀ᵐ ω ∂P,X i ω∈Set.Icc 0 D) (hm : ∀ i,(∫ ω,X i ω ∂P)=μ)
    (t : ℝ) (ht : 0 ≤ t) :
    P.real {ω | t ≤ |(M : ℝ)⁻¹*∑ i,X i ω-μ|} ≤ 2*Real.exp (-2*(M : ℝ)*t^2/D^2) := by
  let Y : Fin M → Ω → ℝ:=fun i ω=>X i ω-μ
  let c : ℝ≥0:=(‖D‖₊/2)^2
  have hsub : ∀ i,HasSubgaussianMGF (Y i) c P := by
    intro i
    have hh:=hasSubgaussianMGF_of_mem_Icc (hX i).aemeasurable (hb i)
    rw [hm i] at hh
    simpa only [sub_zero] using hh
  have hiy : iIndepFun Y P:=hind.comp (fun i (x : ℝ)=>x-μ) (fun i=>by fun_prop)
  have hs:=HasSubgaussianMGF.sum_of_iIndepFun (c:=fun _=>c) (s:=Finset.univ) hiy (fun i _=>hsub i)
  have htail:=abs_tail P (fun ω=>∑ i,Y i ω) (∑ _ : Fin M,c) (by simpa using hs)
    ((M : ℝ)*t) (mul_nonneg (Nat.cast_nonneg _) ht)
  have hM0 : (M : ℝ)≠0:=by exact_mod_cast hM.ne'
  have he : {ω | (M : ℝ)*t ≤ |∑ i,Y i ω|}={ω | t ≤ |(M : ℝ)⁻¹*∑ i,X i ω-μ|} := by
    ext ω
    have hx : (∑ i,Y i ω)=(M : ℝ)*((M : ℝ)⁻¹*∑ i,X i ω-μ) := by
      simp [Y,Finset.sum_sub_distrib]
      field_simp
    rw [Set.mem_setOf_eq,Set.mem_setOf_eq,hx,abs_mul,abs_of_pos (by exact_mod_cast hM)]
    exact mul_le_mul_iff_right₀ (by exact_mod_cast hM)
  rw [he] at htail
  have hc : ((∑ _ : Fin M,c) : ℝ≥0)=(M : ℝ≥0)*c:=by simp
  have hcval : (c : ℝ)=(D/2)^2:=by simp [c,Real.norm_eq_abs,abs_of_pos hD]
  convert htail using 1
  congr 2
  simp only [hc,NNReal.coe_mul,NNReal.coe_natCast,hcval]
  field_simp

end CTrace
end

section

open MeasureTheory ProbabilityTheory Matrix Finset
set_option maxHeartbeats 700000
namespace CTrace
open TraceEstimation.Rayleigh

theorem rayleigh_parameters {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (hA0 : A≠0) :
    0 < n ∧ 0 < A.trace ∧ 0 < A.rank ∧ 0 < kappaF hA.isHermitian := by
  have hn : 0 < n := by
    by_contra h
    have he : n=0:=by omega
    subst n
    exact hA0 (Subsingleton.elim _ _)
  have ht : 0 < A.trace:=lt_of_le_of_ne hA.trace_nonneg (Ne.symm fun h=>hA0 (hA.trace_eq_zero_iff.mp h))
  exact ⟨hn,ht,(kappa_eigen_bound A hA hA0).1,(kappa_eigen_bound A hA hA0).2.1⟩

theorem rayleigh_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (hA0 : A≠0) (hM : 0 < M)
    (z : Fin M → Ω → Fin n → ℝ) (hz : IsNormalizedRayleighSample P A z) (t : ℝ) (ht : 0 < t) :
    P.real {ω | t ≤ |rayleighEstimator A z ω-A.trace|} ≤
      2*Real.exp (-(2*(M : ℝ)*(A.rank : ℝ)^2*t^2)/((n : ℝ)^2*A.trace^2*kappaF hA.isHermitian^2)) := by
  obtain ⟨hn,htr,hr,hκ⟩:=rayleigh_parameters A hA hA0
  haveI : NeZero n:=⟨hn.ne'⟩
  let X : Fin M → Ω → ℝ:=fun i ω=>z i ω⬝ᵥ(A*ᵥz i ω)
  let D : ℝ:=(n : ℝ)*A.trace*kappaF hA.isHermitian/(A.rank : ℝ)
  have hD : 0 < D:=by dsimp [D];positivity
  have hX : ∀ i,Measurable (X i) := by
    intro i
    have h:=hz.measurable i
    dsimp [X]
    simp only [dotProduct,Matrix.mulVec]
    fun_prop
  have hind : iIndepFun X P := by
    exact hz.indep.comp (fun _ v=>v⬝ᵥ(A*ᵥv)) (fun i=>by simp only [dotProduct,Matrix.mulVec];fun_prop)
  have hb : ∀ i,∀ᵐ ω ∂P,X i ω∈Set.Icc 0 D := by
    intro i
    filter_upwards [hz.normalized i] with ω hω
    refine ⟨?_,?_⟩
    · simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg (z i ω)
    · have h:=quadratic_upper A hA.isHermitian (A.trace*kappaF hA.isHermitian/(A.rank : ℝ))
        (kappa_eigen_bound A hA hA0).2.2 (z i ω)
      rw [hω] at h
      change z i ω⬝ᵥ(A*ᵥz i ω) ≤ D
      calc
        _ ≤ (A.trace*kappaF hA.isHermitian/(A.rank : ℝ))*(n : ℝ) := h
        _ = D := by dsimp [D];ring
  have hm : ∀ i,(∫ ω,X i ω ∂P)=A.trace:=hz.unbiased
  have hh:=indep_average_tail P hM X hX hind A.trace D hD hb hm t ht.le
  have he : -2*(M : ℝ)*t^2/D^2 = -(2*(M : ℝ)*(A.rank : ℝ)^2*t^2)/
      ((n : ℝ)^2*A.trace^2*kappaF hA.isHermitian^2) := by dsimp [D];field_simp <;> ring
  rw [he] at hh
  exact hh

theorem rayleigh_hoeffding {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (hA0 : A≠0) (hM : 0 < M)
    (z : Fin M → Ω → Fin n → ℝ) (hz : IsNormalizedRayleighSample P A z) (t : ℝ) (ht : 0 < t) :
    P.real {ω | t ≤ |rayleighEstimator A z ω-A.trace|} ≤
      2*Real.exp (-(2*(M : ℝ)^2*(A.rank : ℝ)^2*t^2)/((M : ℝ)*(n : ℝ)^2*A.trace^2*kappaF hA.isHermitian^2)) := by
  have hM0 : (M : ℝ)≠0:=by exact_mod_cast hM.ne'
  convert rayleigh_tail P A hA hA0 hM z hz t ht using 1
  congr 2
  field_simp

theorem rayleigh_relative {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (hA0 : A≠0) (hM : 0 < M)
    (z : Fin M → Ω → Fin n → ℝ) (hz : IsNormalizedRayleighSample P A z) (ε : ℝ) (hε : 0 < ε) :
    P.real {ω | ε*A.trace ≤ |rayleighEstimator A z ω-A.trace|} ≤
      2*Real.exp (-(2*(M : ℝ)*(A.rank : ℝ)^2*ε^2)/((n : ℝ)^2*kappaF hA.isHermitian^2)) := by
  have ht:=(rayleigh_parameters A hA hA0).2.1
  convert rayleigh_tail P A hA hA0 hM z hz (ε*A.trace) (mul_pos hε ht) using 1
  congr 2
  field_simp

theorem rayleigh_approximator {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (hA0 : A≠0) (hM : 0 < M)
    (z : Fin M → Ω → Fin n → ℝ) (hz : IsNormalizedRayleighSample P A z)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (_hδ1 : δ < 1)
    (hMbound : Real.log (2/δ)*(n : ℝ)^2*kappaF hA.isHermitian^2/(2*(A.rank : ℝ)^2*ε^2) ≤ (M : ℝ)) :
    TraceEstimation.Shared.IsApproximator P (rayleighEstimator A z) A ε δ := by
  obtain ⟨hn,htr,hr,hκ⟩:=rayleigh_parameters A hA hA0
  have hcoef : 0 < 2*(A.rank : ℝ)^2*ε^2/((n : ℝ)^2*kappaF hA.isHermitian^2) := by positivity
  have hlog : Real.log (2/δ) ≤ (2*(M : ℝ)*(A.rank : ℝ)^2*ε^2)/((n : ℝ)^2*kappaF hA.isHermitian^2) := by
    have hh:=mul_le_mul_of_nonneg_right hMbound hcoef.le
    have he : (Real.log (2/δ)*(n : ℝ)^2*kappaF hA.isHermitian^2/(2*(A.rank : ℝ)^2*ε^2))*
        (2*(A.rank : ℝ)^2*ε^2/((n : ℝ)^2*kappaF hA.isHermitian^2))=Real.log (2/δ) := by field_simp
    rw [he] at hh
    calc
      _ ≤ (M : ℝ)*(2*(A.rank : ℝ)^2*ε^2/((n : ℝ)^2*kappaF hA.isHermitian^2)) := hh
      _ = _ := by ring
  have hb : 2*Real.exp (-(2*(M : ℝ)*(A.rank : ℝ)^2*ε^2)/((n : ℝ)^2*kappaF hA.isHermitian^2)) ≤ δ := by
    calc
      _ ≤ 2*Real.exp (-Real.log (2/δ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        simpa only [neg_div] using neg_le_neg hlog
      _ = δ := by rw [Real.exp_neg,Real.exp_log (div_pos (by norm_num) hδ)];field_simp
  apply approximator_of_tail P (rayleighEstimator A z) _ A.trace (ε*A.trace) δ ((rayleigh_relative P A hA hA0 hM z hz ε hε).trans hb)
  unfold rayleighEstimator
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i hi
  have hh:=hz.measurable i
  simp only [dotProduct,Matrix.mulVec]
  fun_prop

end CTrace
end

section
open MeasureTheory ProbabilityTheory Matrix TraceEstimation TraceEstimation.Rayleigh
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hA0 : A ≠ 0) (hM : 0 < M) (z : Fin M → Ω → Fin n → ℝ)
    (hz : IsNormalizedRayleighSample P A z) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hMbound : Real.log (2 / δ) * (n : ℝ) ^ 2 * kappaF hA.isHermitian ^ 2 /
        (2 * (A.rank : ℝ) ^ 2 * ε ^ 2) ≤ (M : ℝ)) :
    Shared.IsApproximator P (rayleighEstimator A z) A ε δ := by
  exact CTrace.rayleigh_approximator P A hA hA0 hM z hz ε δ hε hδ hδ1 hMbound

end
