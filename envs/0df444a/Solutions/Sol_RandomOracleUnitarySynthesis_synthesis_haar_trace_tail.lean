-- Prove2me | solution 1 for RandomOracleUnitarySynthesis.synthesis_haar_trace_tail
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T09:22:32.52993+00:00
-- url     : https://prove2.me/submissions/d3dc9973-4ba3-40ab-b073-ea7ff9254fca

import Mathlib
import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_circuit
import Definitions.Def_DirectFidelity_State_Setting
import Definitions.Def_SpaceReset_Hardness_Quantum
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Theorems.Thm_HaarPhaseInvariantUnitary_logMeanBound


/- Module RandomOracleInfluence -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.InfluenceProof
open Matrix Finset
open scoped ComplexConjugate

section Frobenius
variable {α β : Type} [Fintype α] [Fintype β]
open scoped Matrix.Norms.Frobenius in
lemma frob_sq_entries (A : Matrix α β ℂ) :
    QAlgorithms.frobNorm A^2=∑i,∑j,‖A i j‖^2 := by
  change ‖A‖^2=_
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (sum_nonneg (fun i _=>sum_nonneg (fun j _=>sq_nonneg _)))

lemma frob_sq_gram [DecidableEq β] (A : Matrix α β ℂ) :
    QAlgorithms.frobNorm A^2=(Aᴴ*A).trace.re := by
  rw [frob_sq_entries]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply,Complex.mul_re,Complex.star_def]

lemma frob_sq_leftGram [DecidableEq α] [DecidableEq β] (A : Matrix α β ℂ) :
    QAlgorithms.frobNorm A^2=(A*Aᴴ).trace.re := by rw [frob_sq_gram,Matrix.trace_mul_comm]
end Frobenius

variable {n m m₀ k : ℕ}

lemma prefix_join (h:n ≤ m) (x : synthesis_Bits n) (a : synthesis_Bits (m-n)) :
    synthesis_prefix h (synthesis_join h x a)=x := by
  funext i
  simp [synthesis_prefix,synthesis_join,i.isLt]

lemma join_left_injective (h:n ≤ m) (a : synthesis_Bits (m-n)) :
    Function.Injective (fun x=>synthesis_join h x a) := by
  intro x y hh
  have hpre:=congrArg (synthesis_prefix h) hh
  simpa only [prefix_join] using hpre

lemma J_isometry (C : synthesis_Circuit n m m₀ k) : (synthesis_J C)ᴴ*synthesis_J C=1 := by
  have hinj:=join_left_injective C.system_le (fun _=>0)
  ext x y
  simp [synthesis_J,Matrix.mul_apply,Matrix.conjTranspose_apply,ite_mul,mul_ite,hinj.eq_iff,eq_comm,Matrix.one_apply]

lemma gate_unitary (C : synthesis_Circuit n m m₀ k) (i : ℕ) :
    synthesis_gate C i∈Matrix.unitaryGroup (synthesis_Bits m) ℂ := by
  unfold synthesis_gate
  split_ifs with hi
  · exact (C.gates ⟨i,hi⟩).property
  · exact one_mem _

lemma oracle_unitary (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) :
    synthesis_oracle C f∈Matrix.unitaryGroup (synthesis_Bits m) ℂ := by
  apply Unitary.mem_iff.mpr
  constructor <;> ext x y <;> by_cases h:x=y
  all_goals simp [synthesis_oracle,Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal,Matrix.one_apply,Matrix.diagonal_apply,h]
  all_goals split_ifs <;> norm_num

lemma segment_unitary (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (a b : ℕ) :
    synthesis_segment C f a b∈Matrix.unitaryGroup (synthesis_Bits m) ℂ := by
  have hfold:∀(L:List ℕ) (W:synthesis_Mat m),W∈Matrix.unitaryGroup (synthesis_Bits m) ℂ→
      L.foldl (fun W t=>synthesis_gate C (a+t+1)*synthesis_oracle C f*W) W∈
        Matrix.unitaryGroup (synthesis_Bits m) ℂ := by
    intro L
    induction L with
    | nil => intro W hW;exact hW
    | cons t L ih =>
      intro W hW
      exact ih _ (mul_mem (mul_mem (gate_unitary C _) (oracle_unitary C f)) hW)
  exact hfold _ _ (gate_unitary C a)

lemma projector_columns (C : synthesis_Circuit n m m₀ k) (x : synthesis_Bits m₀)
    {α : Type} [Fintype α] (A : Matrix α (synthesis_Bits m) ℂ) (i : α) (j : synthesis_Bits m) :
    (A*synthesis_projector C x) i j=if synthesis_prefix C.oracle_le j=x then A i j else 0 := by
  simp [Matrix.mul_apply,synthesis_projector,ite_and,mul_ite]

lemma projector_rows (C : synthesis_Circuit n m m₀ k) (x : synthesis_Bits m₀)
    {α : Type} [Fintype α] (A : Matrix (synthesis_Bits m) α ℂ) (i : synthesis_Bits m) (j : α) :
    (synthesis_projector C x*A) i j=if synthesis_prefix C.oracle_le i=x then A i j else 0 := by
  simp [Matrix.mul_apply,synthesis_projector,ite_and,ite_mul]

lemma sum_projector_right_frob (C : synthesis_Circuit n m m₀ k)
    {α : Type} [Fintype α] (A : Matrix α (synthesis_Bits m) ℂ) :
    (∑x,QAlgorithms.frobNorm (A*synthesis_projector C x)^2)=QAlgorithms.frobNorm A^2 := by
  simp only [frob_sq_entries,projector_columns]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [Finset.sum_eq_single (synthesis_prefix C.oracle_le j)]
  · simp
  · intro x hx hne
    simp [Ne.symm hne]
  · simp

lemma sum_projector_left_frob (C : synthesis_Circuit n m m₀ k)
    {α : Type} [Fintype α] (A : Matrix (synthesis_Bits m) α ℂ) :
    (∑x,QAlgorithms.frobNorm (synthesis_projector C x*A)^2)=QAlgorithms.frobNorm A^2 := by
  simp only [frob_sq_entries,projector_rows]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [Finset.sum_eq_single (synthesis_prefix C.oracle_le i)]
  · simp
  · intro x hx hne
    simp [Ne.symm hne]
  · simp

lemma left_gram (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (j : Fin k) :
    synthesis_left C f j*(synthesis_left C f j)ᴴ=1 := by
  have hU:=segment_unitary C f (j.val+1) k
  have hh:(synthesis_segment C f (j.val+1) k)*(synthesis_segment C f (j.val+1) k)ᴴ=1 :=
    (Unitary.mem_iff.mp hU).2
  simp only [synthesis_left,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ _ (synthesis_J C),hh,Matrix.one_mul,J_isometry]

lemma right_gram (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (j : Fin k) :
    (synthesis_right C f j)ᴴ*synthesis_right C f j=1 := by
  have hU:=segment_unitary C f 0 j.val
  have hh:(synthesis_segment C f 0 j.val)ᴴ*(synthesis_segment C f 0 j.val)=1 :=
    (Unitary.mem_iff.mp hU).1
  simp only [synthesis_right,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ _ (synthesis_J C),hh,Matrix.one_mul,J_isometry]

lemma trace_one_bits (n : ℕ) : ((1:synthesis_Mat n).trace).re=(2:ℝ)^n := by
  rw [Matrix.trace_one]
  simp only [Complex.natCast_re,Fintype.card_fun,Fintype.card_fin]
  norm_cast

/-- Exact public Lemma4.7, retaining the full computational basis and the
published circuit fold products and ancilla embedding. -/
theorem synthesis_total_influence (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) :
    (∑x,synthesis_influence C f x)=2*(k:ℝ)*(2:ℝ)^n := by
  unfold synthesis_influence
  rw [sum_comm]
  simp only [sum_add_distrib,sum_projector_right_frob,sum_projector_left_frob]
  have he:∀j:Fin k,QAlgorithms.frobNorm (synthesis_left C f j)^2+
      QAlgorithms.frobNorm (synthesis_right C f j)^2=2*(2:ℝ)^n := by
    intro j
    rw [frob_sq_leftGram,frob_sq_gram,left_gram,right_gram,trace_one_bits]
    ring
  rw [← sum_add_distrib]
  simp only [he,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end RandomOracleUnitarySynthesis.InfluenceProof

/- Module RandomOracleSegments -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace RandomOracleUnitarySynthesis.InfluenceProof
open Matrix Finset
open scoped ComplexConjugate
variable {n m m₀ k : ℕ}

lemma segment_self (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (a : ℕ) :
    synthesis_segment C f a a=synthesis_gate C a := by simp [synthesis_segment]

lemma segment_succ (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (a b : ℕ)
    (hab:a ≤ b) : synthesis_segment C f a (b+1)=
      synthesis_gate C (b+1)*synthesis_oracle C f*synthesis_segment C f a b := by
  unfold synthesis_segment
  have hd:b+1-a=(b-a)+1 := by omega
  rw [hd,List.range_succ,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil]
  have hi:a+(b-a)+1=b+1 := by omega
  rw [hi]

/-- Literal circuit-fold product difference; each summand uses the left
segment from f and the right segment from g, with no unproved hybrid rule. -/
theorem segment_difference (C : synthesis_Circuit n m m₀ k) (f g : synthesis_Oracle m₀)
    (b : ℕ) :
    synthesis_segment C g 0 b-synthesis_segment C f 0 b=
      ∑j∈Finset.range b,synthesis_segment C f (j+1) b*
        (synthesis_oracle C g-synthesis_oracle C f)*synthesis_segment C g 0 j := by
  induction b with
  | zero => simp [synthesis_segment]
  | succ b ih =>
    rw [segment_succ C g 0 b (Nat.zero_le b),segment_succ C f 0 b (Nat.zero_le b),sum_range_succ]
    have he:synthesis_gate C (b+1)*synthesis_oracle C g*synthesis_segment C g 0 b-
        synthesis_gate C (b+1)*synthesis_oracle C f*synthesis_segment C f 0 b=
        synthesis_gate C (b+1)*synthesis_oracle C f*
          (synthesis_segment C g 0 b-synthesis_segment C f 0 b)+
        synthesis_gate C (b+1)*(synthesis_oracle C g-synthesis_oracle C f)*synthesis_segment C g 0 b := by
      noncomm_ring
    rw [he,ih,Matrix.mul_sum,segment_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [segment_succ C f (j+1) b (by have hh:=Finset.mem_range.mp hj;omega)]
    simp only [Matrix.mul_assoc]

theorem A_difference (C : synthesis_Circuit n m m₀ k) (f g : synthesis_Oracle m₀) :
    synthesis_A C g-synthesis_A C f=
      ∑j:Fin k,synthesis_left C f j*(synthesis_oracle C g-synthesis_oracle C f)*synthesis_right C g j := by
  unfold synthesis_A synthesis_W
  rw [← Matrix.sub_mul,← Matrix.mul_sub,segment_difference,Matrix.mul_sum,Matrix.sum_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [synthesis_left,synthesis_right,Matrix.mul_assoc]

lemma projector_idempotent (C : synthesis_Circuit n m m₀ k) (x : synthesis_Bits m₀) :
    synthesis_projector C x*synthesis_projector C x=synthesis_projector C x := by
  ext y z
  rw [projector_rows]
  by_cases h:synthesis_prefix C.oracle_le y=x <;> simp [synthesis_projector,h]

lemma oracle_flip_difference (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀)
    (x : synthesis_Bits m₀) :
    synthesis_oracle C (synthesis_flip f x)-synthesis_oracle C f=
      (if f x then (2:ℂ) else -2) • synthesis_projector C x := by
  ext y z
  by_cases hyz:y=z
  · subst z
    by_cases hx:synthesis_prefix C.oracle_le y=x
    · simp [synthesis_oracle,synthesis_flip,synthesis_projector,hx]
      cases f x <;> norm_num
    · simp [synthesis_oracle,synthesis_flip,synthesis_projector,hx,Ne.symm hx]
  · simp [synthesis_oracle,synthesis_projector,Matrix.diagonal_apply,hyz]

theorem A_flip_difference (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀)
    (x : synthesis_Bits m₀) :
    synthesis_A C (synthesis_flip f x)-synthesis_A C f=
      (if f x then (2:ℂ) else -2) •
        ∑j:Fin k,(synthesis_left C f j*synthesis_projector C x)*
          (synthesis_projector C x*synthesis_right C (synthesis_flip f x) j) := by
  rw [A_difference,oracle_flip_difference,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.mul_smul,Matrix.smul_mul]
  congr 1
  simp only [Matrix.mul_assoc,← Matrix.mul_assoc (synthesis_projector C x) (synthesis_projector C x),
    projector_idempotent]

end RandomOracleUnitarySynthesis.InfluenceProof

/- Module RandomOraclePerturbation -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.InfluenceProof
open Matrix Finset
open scoped ComplexConjugate

section Frobenius
variable {ι α β γ : Type} [Fintype ι] [Fintype α] [Fintype β] [Fintype γ]
open scoped Matrix.Norms.Frobenius in
lemma frob_nonneg (A : Matrix α β ℂ) : 0 ≤ QAlgorithms.frobNorm A := norm_nonneg _

open scoped Matrix.Norms.Frobenius in
lemma frob_smul (c : ℂ) (A : Matrix α β ℂ) :
    QAlgorithms.frobNorm (c • A)=‖c‖*QAlgorithms.frobNorm A := norm_smul _ _

open scoped Matrix.Norms.Frobenius in
/-- Finite Schatten--Cauchy--Schwarz, equivalently the horizontal/vertical
block-factor argument in the original proof. There is no extra k factor. -/
theorem frob_sum_mul_sq_le (A : ι→Matrix α β ℂ) (B : ι→Matrix β γ ℂ) :
    QAlgorithms.frobNorm (∑j,A j*B j)^2  ≤ 
      (∑j,QAlgorithms.frobNorm (A j)^2)*(∑j,QAlgorithms.frobNorm (B j)^2) := by
  have htriangle:QAlgorithms.frobNorm (∑j,A j*B j)  ≤  ∑j,QAlgorithms.frobNorm (A j*B j) :=
    norm_sum_le _ _
  have hmul:∀j,QAlgorithms.frobNorm (A j*B j)  ≤  QAlgorithms.frobNorm (A j)*QAlgorithms.frobNorm (B j) :=
    fun j=>Matrix.frobenius_norm_mul _ _
  have hcs:=Real.sum_mul_le_sqrt_mul_sqrt (univ:Finset ι)
    (fun j=>QAlgorithms.frobNorm (A j)) (fun j=>QAlgorithms.frobNorm (B j))
  have hh:=htriangle.trans ((sum_le_sum (fun j _=>hmul j)).trans hcs)
  have hA:0 ≤ ∑j,QAlgorithms.frobNorm (A j)^2 := sum_nonneg (fun j _=>sq_nonneg _)
  have hB:0 ≤ ∑j,QAlgorithms.frobNorm (B j)^2 := sum_nonneg (fun j _=>sq_nonneg _)
  have hs:=pow_le_pow_left₀ (frob_nonneg _) hh 2
  rw [mul_pow,Real.sq_sqrt hA,Real.sq_sqrt hB] at hs
  exact hs
end Frobenius

variable {n m m₀ k : ℕ}

lemma influence_nonneg (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (x : synthesis_Bits m₀) :
    0 ≤ synthesis_influence C f x := by
  exact sum_nonneg (fun j _=>add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Exact public Lemma4.8 for the full oracle and the compressed block. -/
theorem synthesis_one_bit_perturbation (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀)
    (x : synthesis_Bits m₀) :
    QAlgorithms.frobNorm (synthesis_A C (synthesis_flip f x)-synthesis_A C f)^2  ≤ 
      4*synthesis_influence C f x*synthesis_influence C (synthesis_flip f x) x := by
  have hA:(∑j:Fin k,QAlgorithms.frobNorm (synthesis_left C f j*synthesis_projector C x)^2)  ≤ 
      synthesis_influence C f x := sum_le_sum (fun j _=>le_add_of_nonneg_right (sq_nonneg _))
  have hB:(∑j:Fin k,QAlgorithms.frobNorm (synthesis_projector C x*synthesis_right C (synthesis_flip f x) j)^2)  ≤ 
      synthesis_influence C (synthesis_flip f x) x := sum_le_sum (fun j _=>
        le_add_of_nonneg_left (sq_nonneg _))
  have hh:=frob_sum_mul_sq_le
    (fun j:Fin k=>synthesis_left C f j*synthesis_projector C x)
    (fun j:Fin k=>synthesis_projector C x*synthesis_right C (synthesis_flip f x) j)
  have hb0:0 ≤ ∑j:Fin k,QAlgorithms.frobNorm
      (synthesis_projector C x*synthesis_right C (synthesis_flip f x) j)^2 := sum_nonneg (fun j _=>sq_nonneg _)
  have hp:=mul_le_mul hA hB hb0 (influence_nonneg C f x)
  rw [A_flip_difference,frob_smul,mul_pow]
  have hc:‖(if f x then (2:ℂ) else -2)‖^2=4 := by cases f x <;> norm_num
  rw [hc]
  nlinarith [hh.trans hp]

end RandomOracleUnitarySynthesis.InfluenceProof

/- Module RandomOraclePauliCompleteness -/

namespace RandomOracleUnitarySynthesis.PauliProof
open DirectFidelity.State

theorem pauli_orth1 (a b c d : Fin 2) :
    ∑ j : Fin 4, pauli1 j a b * star (pauli1 j c d) = if a = c ∧ b = d then 2 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [pauli1, Fin.sum_univ_four] <;> norm_num

theorem pauli_orth {n : ℕ} (y x y' x' : Q n) :
    ∑ k : P n, W k y x * star (W k y' x') = if y = y' ∧ x = x' then (2 : ℂ) ^ n else 0 := by
  have e1 : ∀ k : P n, W k y x * star (W k y' x') =
      ∏ i, (pauli1 (k i) (y i) (x i) * star (pauli1 (k i) (y' i) (x' i))) := by
    intro k
    unfold W
    rw [star_prod, ← Finset.prod_mul_distrib]
  simp only [e1]
  rw [← Fintype.prod_sum (fun i j => pauli1 j (y i) (x i) * star (pauli1 j (y' i) (x' i)))]
  simp only [pauli_orth1]
  by_cases h : y = y' ∧ x = x'
  · rw [if_pos h]
    obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h]
    have : ∃ i, ¬ (y i = y' i ∧ x i = x' i) := by
      by_contra hc
      push_neg at hc
      exact h ⟨funext fun i => (hc i).1, funext fun i => (hc i).2⟩
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem trace_mul_W {n : ℕ} (σ : Matrix (Q n) (Q n) ℂ) (k : P n) :
    (σ * W k).trace = ∑ z : Q n × Q n, σ z.1 z.2 * W k z.2 z.1 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]

theorem polar {n : ℕ} (ρ σ : Matrix (Q n) (Q n) ℂ) :
    ∑ k : P n, (ρ * W k).trace * star ((σ * W k).trace) =
      (2 : ℂ) ^ n * ∑ z : Q n × Q n, ρ z.1 z.2 * star (σ z.1 z.2) := by
  simp only [trace_mul_W, star_sum, Finset.sum_mul_sum, star_mul']
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_comm]
  have : ∀ z' : Q n × Q n, ∑ k : P n, ρ z.1 z.2 * W k z.2 z.1 * (star (σ z'.1 z'.2) *
      star (W k z'.2 z'.1)) = ρ z.1 z.2 * star (σ z'.1 z'.2) *
      (if z.2 = z'.2 ∧ z.1 = z'.1 then (2 : ℂ) ^ n else 0) := by
    intro z'
    rw [← pauli_orth, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [this]
  rw [Finset.sum_eq_single z]
  · simp; ring
  · intro z' _ hz'
    have : ¬ (z.2 = z'.2 ∧ z.1 = z'.1) := by
      rintro ⟨h1, h2⟩; exact hz' (Prod.ext h2 h1).symm
    rw [if_neg this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ z) h

theorem pauli_herm1 (j : Fin 4) (a b : Fin 2) : star (pauli1 j a b) = pauli1 j b a := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;> simp [pauli1]

theorem W_herm {n : ℕ} (k : P n) : Matrix.conjTranspose (W k) = W k := by
  ext x y
  rw [Matrix.conjTranspose_apply]
  unfold W
  rw [star_prod]
  exact Finset.prod_congr rfl fun i _ => pauli_herm1 _ _ _

theorem trace_im {n : ℕ} (τ : Matrix (Q n) (Q n) ℂ) (hτ : τ.IsHermitian) (k : P n) :
    ((τ * W k).trace).im = 0 := by
  have h : star ((τ * W k).trace) = (τ * W k).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, W_herm, hτ.eq,
      Matrix.trace_mul_comm]
  rw [Complex.star_def] at h
  exact Complex.conj_eq_iff_im.mp h

theorem trace_mul_herm {n : ℕ} (ρ σ : Matrix (Q n) (Q n) ℂ) (hσ : σ.IsHermitian) :
    (ρ * σ).trace = ∑ z : Q n × Q n, ρ z.1 z.2 * star (σ z.1 z.2) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have := congrFun (congrFun hσ.eq y) x
  rw [Matrix.conjTranspose_apply] at this
  rw [← this]

theorem eq2 (n : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ((ρ * σ).trace).re = ∑ k : P n, chi ρ k * chi σ k := by
  have hd : (0 : ℝ) < dim n := by unfold dim; positivity
  have hpol := congrArg Complex.re (polar ρ σ)
  rw [← trace_mul_herm ρ σ hσ] at hpol
  rw [show (2 : ℂ) ^ n = ((2 ^ n : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
    Complex.re_sum] at hpol
  have hterm : ∀ k : P n, ((ρ * W k).trace * star ((σ * W k).trace)).re =
      ((ρ * W k).trace).re * ((σ * W k).trace).re := by
    intro k
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, trace_im σ hσ k]
    ring
  simp only [hterm] at hpol
  have hchi : ∀ k : P n, chi ρ k * chi σ k =
      ((ρ * W k).trace).re * ((σ * W k).trace).re / dim n := by
    intro k
    unfold chi
    rw [div_mul_div_comm, Real.mul_self_sqrt hd.le]
  simp only [hchi]
  rw [← Finset.sum_div, hpol]
  unfold dim
  field_simp

end RandomOracleUnitarySynthesis.PauliProof

namespace RandomOracleUnitarySynthesis.PauliProof
open DirectFidelity.State
lemma pauli_complete {n : ℕ} (a b c d : Q n) :
    (∑P:P n,W P a b*W P c d)=if a=d ∧ b=c then (2:ℂ)^n else 0 := by
  have he:∀P:P n,star (W P d c)=W P c d := by
    intro P
    exact congrFun (congrFun (W_herm P) c) d
  simpa only [he] using pauli_orth a b d c
end RandomOracleUnitarySynthesis.PauliProof

/- Module RandomOraclePauliTwirl -/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace RandomOracleUnitarySynthesis.PauliProof
open Matrix Finset Classical DirectFidelity.State
open scoped ComplexConjugate

lemma pauli_twirl {n : ℕ} (X : Matrix (Q n) (Q n) ℂ) :
    (∑P:P n,W P*X*W P)=((2:ℂ)^n*X.trace) • (1:Matrix (Q n) (Q n) ℂ) := by
  ext a d
  simp only [Matrix.sum_apply,Matrix.mul_apply,Finset.sum_mul]
  calc
    _ = ∑b:Q n,∑c:Q n,∑P:P n,W P a c*X c b*W P b d := by
      rw [sum_comm]
      apply sum_congr rfl
      intro b hb
      rw [sum_comm]
    _ = ∑b:Q n,∑c:Q n,X c b*(if a=d ∧ c=b then (2:ℂ)^n else 0) := by
      apply sum_congr rfl
      intro b hb
      apply sum_congr rfl
      intro c hc
      rw [←pauli_complete a c b d,Finset.mul_sum]
      apply sum_congr rfl
      intro P hP
      ring
    _ = _ := by
      by_cases had:a=d
      · subst d
        simp [Matrix.smul_apply,Matrix.one_apply,Matrix.trace,Matrix.diag,mul_comm]
        rw [←Finset.sum_mul]
        ring
      · simp [had,Matrix.smul_apply,Matrix.one_apply]

lemma pauli_trace_bilinear {n : ℕ} (A B : Matrix (Q n) (Q n) ℂ) :
    (∑P:P n,(A*W P*B*W P).trace)=(2:ℂ)^n*A.trace*B.trace := by
  rw [←Matrix.trace_sum]
  have he:(∑P:P n,A*W P*B*W P)=A*(∑P:P n,W P*B*W P) := by
    simp only [Matrix.mul_sum,Matrix.mul_assoc]
  rw [he,pauli_twirl,Matrix.mul_smul,Matrix.mul_one,Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

lemma pauli_kraus_overlap {n : ℕ} (M U : Matrix (Q n) (Q n) ℂ) :
    (∑P:P n,(Mᴴ*W P*M*Uᴴ*W P*U).trace)=
      (2:ℂ)^n*star ((M*Uᴴ).trace)*(M*Uᴴ).trace := by
  have he:∀P:P n,(Mᴴ*W P*M*Uᴴ*W P*U).trace=
      ((U*Mᴴ)*W P*(M*Uᴴ)*W P).trace := by
    intro P
    rw [Matrix.trace_mul_comm]
    congr 1
    simp only [Matrix.mul_assoc]
  simp only [he]
  rw [pauli_trace_bilinear]
  have ht:(U*Mᴴ).trace=star ((M*Uᴴ).trace) := by
    rw [←Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  rw [ht]

end RandomOracleUnitarySynthesis.PauliProof

/- Module RandomOraclePauliUnitary -/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace RandomOracleUnitarySynthesis.PauliProof
open Matrix Finset Classical DirectFidelity.State
open scoped ComplexConjugate

lemma pauli1_square (p : Fin 4) (a b : Fin 2) :
    (∑c:Fin 2,pauli1 p a c*pauli1 p c b)=if a=b then (1:ℂ) else 0 := by
  fin_cases p <;> fin_cases a <;> fin_cases b <;> norm_num [pauli1,Fin.sum_univ_two]

lemma pauli1_trace (p : Fin 4) :
    (∑a:Fin 2,pauli1 p a a)=if p=0 then (2:ℂ) else 0 := by
  fin_cases p <;> norm_num [pauli1,Fin.sum_univ_two]

lemma W_square {n : ℕ} (P : P n) : W P*W P=1 := by
  ext x y
  simp only [Matrix.mul_apply,W]
  simp_rw [←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun i a=>pauli1 (P i) (x i) a*pauli1 (P i) a (y i))]
  simp only [pauli1_square,Matrix.one_apply]
  by_cases h:x=y
  · subst y
    simp
  · rw [if_neg h]
    have he:∃i:Fin n,x i≠y i := by
      by_contra hh
      push_neg at hh
      exact h (funext hh)
    obtain ⟨i,hi⟩:=he
    exact prod_eq_zero (mem_univ i) (if_neg hi)

lemma W_unitary {n : ℕ} (P : P n) : W P∈Matrix.unitaryGroup (Q n) ℂ := by
  apply Unitary.mem_iff.mpr
  constructor
  · change (W P)ᴴ*W P=1
    rw [W_herm,W_square]
  · change W P*(W P)ᴴ=1
    rw [W_herm,W_square]

def pauliUnitary {n : ℕ} (P : P n) : Matrix.unitaryGroup (Q n) ℂ := ⟨W P,W_unitary P⟩

lemma trace_W {n : ℕ} (P : P n) :
    (W P).trace=if P=(fun _=>0) then (2:ℂ)^n else 0 := by
  simp only [Matrix.trace,Matrix.diag,W]
  rw [←Fintype.prod_sum (fun i a=>pauli1 (P i) a a)]
  simp only [pauli1_trace]
  by_cases h:P=(fun _=>0)
  · rw [if_pos h]
    subst P
    simp
  · rw [if_neg h]
    have he:∃i:Fin n,P i≠0 := by
      by_contra hh
      push_neg at hh
      exact h (funext hh)
    obtain ⟨i,hi⟩:=he
    exact prod_eq_zero (mem_univ i) (if_neg hi)

lemma W_zero (n : ℕ) : W (fun _:Fin n=>0)=1 := by
  have h0:∀a b:Fin 2,pauli1 0 a b=if a=b then (1:ℂ) else 0 := by
    intro a b
    fin_cases a <;> fin_cases b <;> norm_num [pauli1]
  ext x y
  simp only [W,h0,Matrix.one_apply]
  by_cases h:x=y
  · subst y
    simp
  · rw [if_neg h]
    have he:∃i:Fin n,x i≠y i := by
      by_contra hh
      push_neg at hh
      exact h (funext hh)
    obtain ⟨i,hi⟩:=he
    exact prod_eq_zero (mem_univ i) (if_neg hi)

end RandomOracleUnitarySynthesis.PauliProof

/- Module RandomOracleContraction -/

set_option autoImplicit false
noncomputable section
namespace RandomOracleUnitarySynthesis.NetProof
open Matrix Finset Classical
open scoped Matrix.Norms.L2Operator ComplexConjugate
variable {n m m₀ k : ℕ}

lemma J_specNorm (C : synthesis_Circuit n m m₀ k) : QAlgorithms.specNorm (synthesis_J C)=1 := by
  change ‖synthesis_J C‖=1
  have he:=Matrix.l2_opNorm_conjTranspose_mul_self (synthesis_J C)
  rw [InfluenceProof.J_isometry C,norm_one] at he
  nlinarith [norm_nonneg (synthesis_J C)]

/-- Every original center is a contraction; no clean-ancilla assumption is used. -/
theorem A_contraction (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) :
    synthesis_IsContraction (synthesis_A C f) := by
  have hJ:‖synthesis_J C‖=1 := J_specNorm C
  have hW:‖synthesis_W C f‖=1 :=
    CStarRing.norm_of_mem_unitary (InfluenceProof.segment_unitary C f 0 k)
  change ‖(synthesis_J C)ᴴ*synthesis_W C f*synthesis_J C‖ ≤ 1
  calc
    _ ≤ ‖(synthesis_J C)ᴴ*synthesis_W C f‖*‖synthesis_J C‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(synthesis_J C)ᴴ‖*‖synthesis_W C f‖)*‖synthesis_J C‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = 1 := by rw [Matrix.l2_opNorm_conjTranspose,hJ,hW]; norm_num

end RandomOracleUnitarySynthesis.NetProof

/- Module SpaceResetFidelityCore -/

/-! Finite matrix foundations, extracted from the accepted Prove2Me proof
of Uhlmann (submission e7f79aee-b42a-40df-9b8b-becca22296a9,
theorem c84df38e-32fb-41ea-8ea7-c4b571ce7f65, Apache-2.0).
Only the Mathlib-only matrix proofs are retained; the unrelated relative
entropy sections and paper-specific definition imports are omitted. -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate

namespace CFCBasics
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma psd_re {X : Matrix I I ℂ} (h : X.PosSemidef) : 0 ≤ X.trace.re :=
  (Complex.nonneg_iff.mp h.trace_nonneg).1

lemma fin (X : Matrix I I ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma cs (X Y : Matrix I I ℂ) :
    (Xᴴ * Y).trace.re + (Yᴴ * X).trace.re ≤ (Xᴴ * X).trace.re + (Yᴴ * Y).trace.re := by
  have h0 := psd_re (Matrix.posSemidef_conjTranspose_mul_self (X - Y))
  simp only [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
    Complex.sub_re] at h0
  linarith

/-- `Re Tr Z ≤ Tr √(Z Z†)` -/
theorem re_tr_le (Z : Matrix I I ℂ) : Z.trace.re ≤ (cfc Real.sqrt (Z * Zᴴ)).trace.re := by
  set M := Z * Zᴴ
  have hM : M.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose Z
  have hMs : IsSelfAdjoint M := hM.1.isSelfAdjoint
  have hspec : ∀ x ∈ spectrum ℝ M, 0 ≤ x := fun x hx => spectrum_nonneg_of_nonneg hM.nonneg hx
  have key : ∀ ε : ℝ, 0 < ε → Z.trace.re ≤ (cfc Real.sqrt M).trace.re + ε * Fintype.card I / 2 := by
    intro ε hε
    set L := cfc (fun x => Real.sqrt (Real.sqrt x + ε)) M
    set K := cfc (fun x => (Real.sqrt (Real.sqrt x + ε))⁻¹) M
    have hpos : ∀ x : ℝ, 0 < Real.sqrt (Real.sqrt x + ε) :=
      fun x => Real.sqrt_pos.2 (by positivity)
    have hLK : L * K = 1 := by
      rw [← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_const_one ℝ M]
      exact cfc_congr fun x _ => mul_inv_cancel₀ (hpos x).ne'
    have hKL : K * L = 1 := by
      rw [← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_const_one ℝ M]
      exact cfc_congr fun x _ => inv_mul_cancel₀ (hpos x).ne'
    have hLh : Lᴴ = L := (cfc_predicate _ M : IsSelfAdjoint L)
    have hKh : Kᴴ = K := (cfc_predicate _ M : IsSelfAdjoint K)
    have h := cs L (K * Z)
    have e1 : Lᴴ * (K * Z) = Z := by rw [hLh, ← Matrix.mul_assoc, hLK, Matrix.one_mul]
    have e2 : (K * Z)ᴴ * L = Zᴴ := by
      rw [conjTranspose_mul, hKh, Matrix.mul_assoc, hKL, Matrix.mul_one]
    have e3 : (Lᴴ * L).trace.re = (cfc Real.sqrt M).trace.re + ε * Fintype.card I := by
      have : Lᴴ * L = cfc Real.sqrt M + (ε : ℂ) • 1 := by
        rw [hLh, ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
        rw [show (ε : ℂ) • (1 : Matrix I I ℂ) = cfc (fun _ : ℝ => ε) M by
          rw [cfc_const ε M hMs]; simp [Algebra.algebraMap_eq_smul_one]]
        rw [← cfc_add _ _ _ (fin _ _) (fin _ _)]
        refine cfc_congr fun x hx => ?_
        exact Real.mul_self_sqrt (by have := Real.sqrt_nonneg x; linarith)
      rw [this, Matrix.trace_add, Complex.add_re, Matrix.trace_smul, Matrix.trace_one]
      simp
    have e4 : ((K * Z)ᴴ * (K * Z)).trace.re ≤ (cfc Real.sqrt M).trace.re := by
      have t1 : ((K * Z)ᴴ * (K * Z)).trace = (K * K * M).trace := by
        rw [conjTranspose_mul, hKh]
        rw [show Zᴴ * K * (K * Z) = Zᴴ * (K * K * Z) by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm]
        simp only [M, Matrix.mul_assoc]
      have t2 : K * K * M = cfc (fun x => x / (Real.sqrt x + ε)) M := by
        rw [show K * K * M = K * K * cfc (fun x : ℝ => x) M by rw [cfc_id' ℝ M hMs],
          ← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
        refine cfc_congr fun x hx => ?_
        have h0 := hspec x hx
        have h1 : 0 < Real.sqrt x + ε := by positivity
        rw [← mul_inv, Real.mul_self_sqrt h1.le, div_eq_inv_mul]
      have t3 : (cfc Real.sqrt M - K * K * M).PosSemidef := by
        rw [t2, ← cfc_sub _ _ _ (fin _ _) (fin _ _)]
        refine (cfc_nonneg (fun x hx => ?_) :
          0 ≤ cfc (fun x => Real.sqrt x - x / (Real.sqrt x + ε)) M).posSemidef
        have h0 := hspec x hx
        have h1 : 0 < Real.sqrt x + ε := by positivity
        rw [sub_nonneg, div_le_iff₀ h1]
        have := Real.mul_self_sqrt h0
        nlinarith [Real.sqrt_nonneg x]
      have := psd_re t3
      rw [Matrix.trace_sub, Complex.sub_re] at this
      rw [t1]; linarith
    rw [e1, e2, e3, Matrix.trace_conjTranspose] at h
    simp only [RCLike.star_def, Complex.conj_re] at h
    linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hc : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have := key (2 * δ / (Fintype.card I + 1)) (by positivity)
  refine this.trans ?_
  have : 2 * δ / (Fintype.card I + 1) * Fintype.card I / 2 ≤ δ := by
    rw [div_mul_eq_mul_div, div_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

lemma sqrt_herm (X : Matrix I I ℂ) : (cfc Real.sqrt X)ᴴ = cfc Real.sqrt X :=
  (cfc_predicate Real.sqrt X : IsSelfAdjoint _)

lemma sqrt_sq {X : Matrix I I ℂ} (hX : X.PosSemidef) : cfc Real.sqrt X * cfc Real.sqrt X = X := by
  have hs : IsSelfAdjoint X := hX.1.isSelfAdjoint
  rw [← cfc_mul _ _ _ (fin _ _) (fin _ _)]
  conv_rhs => rw [← cfc_id' ℝ X hs]
  refine cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hX.nonneg hx)

end CFCBasics
namespace Nuclear
open Polynomial
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
lemma tr_pow_swap (X : Matrix m n ℂ) (k : ℕ) :
    ((Xᴴ * X) ^ (k + 1)).trace = ((X * Xᴴ) ^ (k + 1)).trace := by
  have h : ∀ k : ℕ, (Xᴴ * X) ^ (k + 1) = Xᴴ * (X * Xᴴ) ^ k * X := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← pow_succ']

lemma tr_aeval_swap (X : Matrix m n ℂ) (p : ℝ[X]) (hp : p.coeff 0 = 0) :
    (aeval (Xᴴ * X) p).trace = (aeval (X * Xᴴ) p).trace := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [hp]
  · rw [tr_pow_swap]

theorem tr_cfc_swap (X : Matrix m n ℂ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f (Xᴴ * X)).trace = (cfc f (X * Xᴴ)).trace := by
  set A := Xᴴ * X
  set B := X * Xᴴ
  have hA : IsSelfAdjoint A := (Matrix.posSemidef_conjTranspose_mul_self X).1.isSelfAdjoint
  have hB : IsSelfAdjoint B := (Matrix.posSemidef_self_mul_conjTranspose X).1.isSelfAdjoint
  have fA : (spectrum ℝ A).Finite := A.finite_real_spectrum
  have fB : (spectrum ℝ B).Finite := B.finite_real_spectrum
  set s : Finset ℝ := {0} ∪ fA.toFinset ∪ fB.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have h1 : cfc f A = cfc (fun x => p.eval x) A :=
    cfc_congr fun x hx => (hp x (by simp [s, fA.mem_toFinset.2 hx])).symm
  have h2 : cfc f B = cfc (fun x => p.eval x) B :=
    cfc_congr fun x hx => (hp x (by simp [s, fB.mem_toFinset.2 hx])).symm
  rw [h1, h2, cfc_polynomial p A hA, cfc_polynomial p B hB]
  refine tr_aeval_swap X p ?_
  rw [Polynomial.coeff_zero_eq_eval_zero, hp 0 (by simp [s]), hf]

section Polar
variable {R : Type*} [Fintype R] [DecidableEq R]
lemma dot_self (Y : Matrix R R ℂ) (v : R → ℂ) :
    star (Y *ᵥ v) ⬝ᵥ (Y *ᵥ v) = star v ⬝ᵥ ((Yᴴ * Y) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

lemma norm_sq_eq (x : EuclideanSpace ℂ R) : ((‖x‖ ^ 2 : ℝ) : ℂ) = star (x.ofLp) ⬝ᵥ x.ofLp := by
  rw [Complex.ofReal_pow, show ((‖x‖ : ℂ)) ^ 2 = inner ℂ x x from
    (inner_self_eq_norm_sq_to_K x).symm, PiLp.inner_apply]
  simp [dotProduct, mul_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl

/-- Polar decomposition: `Y = W |Y|` with `W` unitary. -/
theorem polar (Y : Matrix R R ℂ) :
    ∃ W : Matrix.unitaryGroup R ℂ, (W : Matrix R R ℂ) * cfc Real.sqrt (Yᴴ * Y) = Y := by
  set G := Yᴴ * Y
  have hG : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Y
  set A := cfc Real.sqrt G
  set Ap := cfc (fun x => (Real.sqrt x)⁻¹) G
  set P := cfc (fun x => Real.sqrt x * (Real.sqrt x)⁻¹) G
  have hAh : Aᴴ = A := CFCBasics.sqrt_herm G
  have hAA : A * A = G := CFCBasics.sqrt_sq hG
  have hApA : Ap * A = P := by
    rw [← cfc_mul _ _ _ (CFCBasics.fin _ _) (CFCBasics.fin _ _)]
    exact cfc_congr fun x _ => mul_comm _ _
  have hA1P : A * (1 - P) = 0 := by
    rw [← cfc_one ℝ G, ← cfc_sub _ _ _ (CFCBasics.fin _ _) (CFCBasics.fin _ _),
      ← cfc_mul _ _ _ (CFCBasics.fin _ _) (CFCBasics.fin _ _)]
    rw [show (0 : Matrix R R ℂ) = cfc (fun _ : ℝ => (0 : ℝ)) G by simp]
    refine cfc_congr fun x _ => ?_
    by_cases h : Real.sqrt x = 0
    · simp [h]
    · simp [mul_inv_cancel₀ h]
  have hY1P : Y * (1 - P) = 0 := by
    have : (Y * (1 - P))ᴴ * (Y * (1 - P)) = 0 := by
      have e : (Y * (1 - P))ᴴ * (Y * (1 - P)) = (A * (1 - P))ᴴ * (A * (1 - P)) := by
        simp only [conjTranspose_mul, hAh]
        rw [show (1 - P)ᴴ * Yᴴ * (Y * (1 - P)) = (1 - P)ᴴ * G * (1 - P) by
            simp only [G, Matrix.mul_assoc],
          ← hAA]
        simp only [Matrix.mul_assoc]
      rw [e, hA1P, Matrix.mul_zero]
    exact Matrix.conjTranspose_mul_self_eq_zero.mp this
  set M := Y * Ap
  have hMA : M * A = Y := by
    rw [Matrix.mul_assoc, hApA]
    have := hY1P
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  -- isometry on the range of A
  have hnorm : ∀ v : R → ℂ, ‖(WithLp.toLp 2 (Y *ᵥ v) : EuclideanSpace ℂ R)‖ =
      ‖(WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R)‖ := by
    intro v
    have h1 := norm_sq_eq (WithLp.toLp 2 (Y *ᵥ v) : EuclideanSpace ℂ R)
    have h2 := norm_sq_eq (WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R)
    simp only [WithLp.ofLp_toLp] at h1 h2
    rw [dot_self] at h1
    rw [dot_self, hAh, hAA] at h2
    rw [← h2] at h1
    have := Complex.ofReal_injective h1
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  set TA := Matrix.toEuclideanLin A
  set S := LinearMap.range TA
  let L : S →ₗᵢ[ℂ] EuclideanSpace ℂ R :=
    { toLinearMap := (Matrix.toEuclideanLin M).domRestrict S
      norm_map' := by
        rintro ⟨s, v, rfl⟩
        simp only [LinearMap.domRestrict_apply, TA, Matrix.toEuclideanLin_apply,
          WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hMA, Submodule.coe_norm]
        exact hnorm _ }
  set W := L.extend
  set Wm := Matrix.toEuclideanLin.symm W.toLinearMap
  have hW : ∀ x, Matrix.toEuclideanLin Wm x = W x := by
    intro x; simp [Wm]
  have hWv : ∀ u : R → ℂ, Wm *ᵥ u = (W (WithLp.toLp 2 u)).ofLp := by
    intro u; rw [← hW]; simp
  have hWA : Wm * A = Y := by
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    rw [← Matrix.mulVec_mulVec, hWv]
    have hx : (WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R) ∈ S := ⟨WithLp.toLp 2 v, by simp [TA]⟩
    have := L.extend_apply ⟨_, hx⟩
    simp only at this
    rw [this]
    simp [L, Matrix.mulVec_mulVec, hMA]
  have hU : Wm ∈ Matrix.unitaryGroup R ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    have := W.inner_map_map (EuclideanSpace.single i (1 : ℂ)) (EuclideanSpace.single j 1)
    have hc : ∀ j : R, (W (EuclideanSpace.single j (1 : ℂ))).ofLp = Wm.col j := by
      intro j; rw [← Matrix.mulVec_single_one, hWv]; rfl
    rw [EuclideanSpace.inner_single_left, PiLp.inner_apply] at this
    simp only [hc] at this
    simp only [star_eq_conjTranspose, Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply]
    convert this using 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.col_apply, RCLike.inner_apply]
      exact mul_comm _ _
    · simp [EuclideanSpace.single_apply, eq_comm]
  exact ⟨⟨Wm, hU⟩, hWA⟩
lemma psd_tr {X : Matrix R R ℂ} (h : X.PosSemidef) : X.trace = ((X.trace.re : ℝ) : ℂ) := by
  have := h.trace_nonneg
  rw [Complex.nonneg_iff] at this
  exact Complex.ext (by simp) (by simp [← this.2])

/-- `|Tr (Z V)| ≤ Tr √(Z Z†)` for unitary `V`. -/
lemma abs_tr_le (Z V : Matrix R R ℂ) (hV : V * Vᴴ = 1) :
    ‖(Z * V).trace‖ ≤ (cfc Real.sqrt (Z * Zᴴ)).trace.re := by
  set t := (Z * V).trace
  by_cases ht : t = 0
  · rw [ht, norm_zero]
    exact CFCBasics.psd_re (cfc_nonneg (fun x _ => Real.sqrt_nonneg x) :
      0 ≤ cfc Real.sqrt (Z * Zᴴ)).posSemidef
  set c : ℂ := star t / (‖t‖ : ℂ)
  have hn : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ht
  have hc : c * star c = 1 := by
    simp only [c, star_div₀, star_star, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    rw [div_mul_div_comm, Complex.conj_mul', ← pow_two]
    exact div_self (pow_ne_zero 2 hn)
  have h := CFCBasics.re_tr_le (c • (Z * V))
  have e1 : (c • (Z * V)) * (c • (Z * V))ᴴ = Z * Zᴴ := by
    rw [conjTranspose_smul, smul_mul_smul_comm, hc, one_smul, conjTranspose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc V, hV, Matrix.one_mul]
  have e2 : (c • (Z * V)).trace.re = ‖t‖ := by
    rw [Matrix.trace_smul, smul_eq_mul]
    simp only [c, Complex.star_def]
    rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rw [pow_two, mul_div_assoc, div_self hn, mul_one]
    simp only [Complex.ofReal_re]; rfl
  rw [e1, e2] at h
  exact h

lemma tr_attain (Z : Matrix R R ℂ) :
    ∃ V : Matrix.unitaryGroup R ℂ, ‖(Z * (V : Matrix R R ℂ)).trace‖ =
      (cfc Real.sqrt (Z * Zᴴ)).trace.re := by
  obtain ⟨W, hW⟩ := polar Zᴴ
  rw [conjTranspose_conjTranspose] at hW
  have hZ : Z = cfc Real.sqrt (Z * Zᴴ) * (W : Matrix R R ℂ)ᴴ := by
    have := congrArg conjTranspose hW
    rw [conjTranspose_conjTranspose, conjTranspose_mul, CFCBasics.sqrt_herm] at this
    exact this.symm
  refine ⟨W, ?_⟩
  have hWW : (W : Matrix R R ℂ)ᴴ * W = 1 := by
    have := W.2; rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
  nth_rewrite 1 [hZ]
  rw [Matrix.mul_assoc, hWW, Matrix.mul_one]
  have hp : (cfc Real.sqrt (Z * Zᴴ)).PosSemidef :=
    (cfc_nonneg (fun x _ => Real.sqrt_nonneg x) : 0 ≤ cfc Real.sqrt (Z * Zᴴ)).posSemidef
  rw [psd_tr hp, Complex.norm_real, Real.norm_of_nonneg (CFCBasics.psd_re hp), Complex.ofReal_re]

end Polar
end Nuclear
end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetNuclearNorm -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma sqrt_eq_cfc (A : Matrix α α ℂ) (hA:A.PosSemidef) :
    CFC.sqrt A=cfc Real.sqrt A := by
  rw [CFC.sqrt_eq_real_sqrt A hA.nonneg,cfcₙ_eq_cfc]

/-- The public trace norm agrees with either rectangular Gram expression. -/
lemma traceNorm_eq_left (A : Matrix α β ℂ) :
    WildeQIT.traceNorm A=(cfc Real.sqrt (A*Aᴴ)).trace.re := by
  rw [WildeQIT.traceNorm,sqrt_eq_cfc _ (Matrix.posSemidef_conjTranspose_mul_self A),
    Nuclear.tr_cfc_swap A _ Real.sqrt_zero]

lemma traceNorm_nonneg (A : Matrix α β ℂ) : 0 ≤ WildeQIT.traceNorm A := by
  rw [traceNorm_eq_left]
  exact CFCBasics.psd_re (cfc_nonneg (fun _ _=>Real.sqrt_nonneg _) :
    0 ≤ cfc Real.sqrt (A*Aᴴ)).posSemidef

lemma traceNorm_zero : WildeQIT.traceNorm (0:Matrix α β ℂ)=0 := by
  simp [WildeQIT.traceNorm]

lemma traceNorm_dual (A : Matrix α α ℂ) (U : Matrix.unitaryGroup α ℂ) :
    ‖(A*(U:Matrix α α ℂ)).trace‖ ≤ WildeQIT.traceNorm A := by
  rw [traceNorm_eq_left]
  exact Nuclear.abs_tr_le A U (by exact Unitary.coe_mul_star_self U)

lemma traceNorm_attain (A : Matrix α α ℂ) :
    ∃ U : Matrix.unitaryGroup α ℂ,‖(A*(U:Matrix α α ℂ)).trace‖=WildeQIT.traceNorm A := by
  rw [traceNorm_eq_left]
  exact Nuclear.tr_attain A

lemma traceNorm_add_le_square (A B : Matrix α α ℂ) :
    WildeQIT.traceNorm (A+B) ≤ WildeQIT.traceNorm A+WildeQIT.traceNorm B := by
  obtain ⟨U,hU⟩:=traceNorm_attain (A+B)
  rw [← hU,add_mul,Matrix.trace_add]
  exact (norm_add_le _ _).trans (add_le_add (traceNorm_dual A U) (traceNorm_dual B U))

lemma traceNorm_smul_square (c : ℂ) (A : Matrix α α ℂ) :
    WildeQIT.traceNorm (c • A)=‖c‖*WildeQIT.traceNorm A := by
  apply le_antisymm
  · obtain ⟨U,hU⟩:=traceNorm_attain (c • A)
    rw [← hU,Matrix.smul_mul,Matrix.trace_smul,norm_smul]
    exact mul_le_mul_of_nonneg_left (traceNorm_dual A U) (norm_nonneg _)
  · obtain ⟨U,hU⟩:=traceNorm_attain A
    have hh:=traceNorm_dual (c • A) U
    rwa [Matrix.smul_mul,Matrix.trace_smul,norm_smul,hU] at hh

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetHilbertSchmidt -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

def entryVector (A : Matrix α β ℂ) : EuclideanSpace ℂ (α×β) :=
  WithLp.toLp 2 (fun p=>A p.1 p.2)

def hsNorm (A : Matrix α β ℂ) : ℝ := Real.sqrt (Aᴴ*A).trace.re

lemma trace_gram_eq_inner (A B : Matrix α β ℂ) :
    (Aᴴ*B).trace=inner ℂ (entryVector A) (entryVector B) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
    entryVector,PiLp.inner_apply,WithLp.ofLp_toLp,RCLike.inner_apply,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact mul_comm _ _

lemma hsNorm_eq_norm (A : Matrix α β ℂ) : hsNorm A=‖entryVector A‖ := by
  rw [hsNorm,trace_gram_eq_inner,inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_pow,Complex.ofReal_re]
  exact Real.sqrt_sq (norm_nonneg _)

lemma hsNorm_nonneg (A : Matrix α β ℂ) : 0 ≤ hsNorm A := Real.sqrt_nonneg _

lemma hs_trace_cauchy (A B : Matrix α β ℂ) :
    ‖(Aᴴ*B).trace‖ ≤ hsNorm A*hsNorm B := by
  rw [trace_gram_eq_inner,hsNorm_eq_norm,hsNorm_eq_norm]
  exact norm_inner_le_norm _ _

lemma hsNorm_conjTranspose (A : Matrix α β ℂ) : hsNorm Aᴴ=hsNorm A := by
  rw [hsNorm,hsNorm,Matrix.conjTranspose_conjTranspose,Matrix.trace_mul_comm]

lemma hsNorm_mul_unitary (A : Matrix α β ℂ) (U : Matrix.unitaryGroup β ℂ) :
    hsNorm (A*(U:Matrix β β ℂ))=hsNorm A := by
  unfold hsNorm
  congr 1
  have he:((A*(U:Matrix β β ℂ))ᴴ*(A*(U:Matrix β β ℂ))).trace=(Aᴴ*A).trace := by
    rw [Matrix.conjTranspose_mul]
    rw [show (U:Matrix β β ℂ)ᴴ*Aᴴ*(A*(U:Matrix β β ℂ))=
      (U:Matrix β β ℂ)ᴴ*(Aᴴ*A)*(U:Matrix β β ℂ) by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_cycle]
    have hu:(U:Matrix β β ℂ)*(U:Matrix β β ℂ)ᴴ=1 := Unitary.coe_mul_star_self U
    rw [hu,Matrix.one_mul]
  rw [he]

lemma traceNorm_mul_le_hs_square (A B : Matrix α α ℂ) :
    WildeQIT.traceNorm (A*B) ≤ hsNorm A*hsNorm B := by
  obtain ⟨U,hU⟩:=traceNorm_attain (A*B)
  have hh:=hs_trace_cauchy Aᴴ (B*(U:Matrix α α ℂ))
  rw [Matrix.conjTranspose_conjTranspose,← Matrix.mul_assoc,hU,
    hsNorm_conjTranspose,hsNorm_mul_unitary] at hh
  exact hh

/-- Schatten 2–2→1 Hölder, with arbitrary finite rectangular dimensions. -/
theorem traceNorm_mul_le_hs (A : Matrix α β ℂ) (B : Matrix β γ ℂ) :
    WildeQIT.traceNorm (A*B) ≤ hsNorm A*hsNorm B := by
  let S : Matrix β β ℂ := CFC.sqrt (Aᴴ*A)
  let T : Matrix β β ℂ := CFC.sqrt (B*Bᴴ)
  have hS:Sᴴ=S := (CFC.sqrt_nonneg (Aᴴ*A)).isSelfAdjoint.star_eq
  have hT:Tᴴ=T := (CFC.sqrt_nonneg (B*Bᴴ)).isSelfAdjoint.star_eq
  have hSS:S*S=Aᴴ*A := CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  have hTT:T*T=B*Bᴴ := CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_self_mul_conjTranspose B).nonneg
  have he1:WildeQIT.traceNorm (A*B)=WildeQIT.traceNorm (S*B) := by
    have hg:(A*B)ᴴ*(A*B)=(S*B)ᴴ*(S*B) := by
      simp only [Matrix.conjTranspose_mul,hS]
      simp only [Matrix.mul_assoc,← Matrix.mul_assoc S S,hSS]
    simp only [WildeQIT.traceNorm,hg]
  have he2:WildeQIT.traceNorm (S*B)=WildeQIT.traceNorm (S*T) := by
    have hg:(S*B)*(S*B)ᴴ=(S*T)*(S*T)ᴴ := by
      simp only [Matrix.conjTranspose_mul,hS,hT]
      simp only [Matrix.mul_assoc,← Matrix.mul_assoc T T,hTT]
    rw [traceNorm_eq_left,traceNorm_eq_left,hg]
  have hnS:hsNorm S=hsNorm A := by rw [hsNorm,hS,hSS];rfl
  have hnT:hsNorm T=hsNorm B := by
    rw [hsNorm,hT,hTT,Matrix.trace_mul_comm]
    rfl
  rw [he1,he2]
  exact (traceNorm_mul_le_hs_square S T).trans_eq (by rw [hnS,hnT])

end SpaceReset.Hardness.FidelityProof

/- Module RandomOracleCorrelationGeometry -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.GeometryProof
open Matrix Finset Classical
open SpaceReset.Hardness.FidelityProof
open scoped ComplexConjugate Matrix.Norms.L2Operator
variable {α : Type} [Fintype α] [DecidableEq α]

lemma hsNorm_eq_frob (A : Matrix α α ℂ) : hsNorm A=QAlgorithms.frobNorm A := by
  unfold hsNorm
  rw [←InfluenceProof.frob_sq_gram]
  exact Real.sqrt_sq (InfluenceProof.frob_nonneg _)

lemma norm_trace_mul_le_frob (A B : Matrix α α ℂ) :
    ‖(A*B).trace‖ ≤ QAlgorithms.frobNorm A*QAlgorithms.frobNorm B := by
  have hh:=hs_trace_cauchy Aᴴ B
  rw [Matrix.conjTranspose_conjTranspose,hsNorm_conjTranspose,hsNorm_eq_frob,hsNorm_eq_frob] at hh
  exact hh

lemma frob_conjTranspose (A : Matrix α α ℂ) : QAlgorithms.frobNorm Aᴴ=QAlgorithms.frobNorm A := by
  rw [←hsNorm_eq_frob,hsNorm_conjTranspose,hsNorm_eq_frob]

lemma frob_mul_unitary (A : Matrix α α ℂ) (U : Matrix.unitaryGroup α ℂ) :
    QAlgorithms.frobNorm (A*(U:Matrix α α ℂ))=QAlgorithms.frobNorm A := by
  rw [←hsNorm_eq_frob,hsNorm_mul_unitary,hsNorm_eq_frob]

lemma frob_unitary_mul (U : Matrix.unitaryGroup α ℂ) (A : Matrix α α ℂ) :
    QAlgorithms.frobNorm ((U:Matrix α α ℂ)*A)=QAlgorithms.frobNorm A := by
  rw [←frob_conjTranspose,Matrix.conjTranspose_mul]
  have hh:=frob_mul_unitary Aᴴ (star U)
  simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose,frob_conjTranspose] using hh

lemma unitary_frob [Nonempty α] (U : Matrix.unitaryGroup α ℂ) :
    QAlgorithms.frobNorm (U:Matrix α α ℂ)=Real.sqrt (Fintype.card α:ℝ) := by
  have hs:=InfluenceProof.frob_sq_gram (U:Matrix α α ℂ)
  rw [show (U:Matrix α α ℂ)ᴴ*(U:Matrix α α ℂ)=1 from Unitary.star_mul_self_of_mem U.property,
    Matrix.trace_one] at hs
  have he:(Fintype.card α:ℂ).re=(Fintype.card α:ℝ) := by simp
  rw [he] at hs
  calc
    _ = Real.sqrt (QAlgorithms.frobNorm (U:Matrix α α ℂ)^2) :=
      (Real.sqrt_sq (InfluenceProof.frob_nonneg _)).symm
    _ = _ := congrArg Real.sqrt hs

lemma column_norm_le_specNorm (A : Matrix α α ℂ) (j : α) :
    ‖(WithLp.toLp 2 (A.col j):EuclideanSpace ℂ α)‖ ≤ QAlgorithms.specNorm A := by
  have hh:=Matrix.l2_opNorm_mulVec A (PiLp.single 2 j (1:ℂ))
  change ‖(WithLp.toLp 2 (A*ᵥPi.single j (1:ℂ)):EuclideanSpace ℂ α)‖ ≤
    QAlgorithms.specNorm A*‖(PiLp.single 2 j (1:ℂ):EuclideanSpace ℂ α)‖ at hh
  rwa [Matrix.mulVec_single_one,PiLp.norm_single,norm_one,mul_one] at hh

lemma contraction_frob_le (A : Matrix α α ℂ) (hA:QAlgorithms.specNorm A ≤ 1) :
    QAlgorithms.frobNorm A ≤ Real.sqrt (Fintype.card α:ℝ) := by
  have hc:∀j:α,(∑i:α,‖A i j‖^2) ≤ 1 := by
    intro j
    have hh:‖(WithLp.toLp 2 (A.col j):EuclideanSpace ℂ α)‖ ≤ 1 :=
      (column_norm_le_specNorm A j).trans hA
    have hs:‖(WithLp.toLp 2 (A.col j):EuclideanSpace ℂ α)‖^2 ≤ 1 := by
      nlinarith [norm_nonneg (WithLp.toLp 2 (A.col j):EuclideanSpace ℂ α)]
    simpa only [EuclideanSpace.norm_sq_eq,WithLp.ofLp_toLp,Matrix.col_apply] using hs
  have hs:=sum_le_sum (fun j (_:j∈(univ:Finset α))=>hc j)
  rw [sum_comm,←InfluenceProof.frob_sq_entries] at hs
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one] at hs
  exact (sq_le_sq₀ (InfluenceProof.frob_nonneg _) (Real.sqrt_nonneg _)).mp
    (by rwa [Real.sq_sqrt (Nat.cast_nonneg _)])

lemma frob_eq_sqrt_entries (A : Matrix α α ℂ) :
    QAlgorithms.frobNorm A=Real.sqrt (∑i:α,∑j:α,‖A i j‖^2) := by
  rw [←InfluenceProof.frob_sq_entries,Real.sqrt_sq (InfluenceProof.frob_nonneg _)]

end RandomOracleUnitarySynthesis.GeometryProof

/- Module RandomOracleMatrixCorrelation -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.GeometryProof
open Matrix Finset Classical
open scoped ComplexConjugate Matrix.Norms.L2Operator
variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

def matrixCorrelation (A : Matrix α α ℂ) (Q U : Matrix.unitaryGroup α ℂ) : ℝ :=
  (A*(↑(star U*Q*U):Matrix α α ℂ)).trace.re/(Fintype.card α:ℝ)

lemma matrixCorrelation_continuous (A : Matrix α α ℂ) (Q : Matrix.unitaryGroup α ℂ) :
    Continuous (matrixCorrelation A Q) := by
  unfold matrixCorrelation
  fun_prop

lemma matrixCorrelation_bound (A : Matrix α α ℂ) (hA:QAlgorithms.specNorm A ≤ 1)
    (Q U : Matrix.unitaryGroup α ℂ) : |matrixCorrelation A Q U| ≤ 1 := by
  have hN:0<(Fintype.card α:ℝ) := by exact_mod_cast Fintype.card_pos
  have hh:|(A*(↑(star U*Q*U):Matrix α α ℂ)).trace.re| ≤ (Fintype.card α:ℝ) := by
    calc
      _ ≤ ‖(A*(↑(star U*Q*U):Matrix α α ℂ)).trace‖ := Complex.abs_re_le_norm _
      _ ≤ QAlgorithms.frobNorm A*QAlgorithms.frobNorm (↑(star U*Q*U):Matrix α α ℂ) := norm_trace_mul_le_frob _ _
      _ ≤ Real.sqrt (Fintype.card α:ℝ)*Real.sqrt (Fintype.card α:ℝ) := by
        rw [unitary_frob]
        exact mul_le_mul_of_nonneg_right (contraction_frob_le A hA) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt hN.le
  unfold matrixCorrelation
  rw [abs_div,abs_of_pos hN]
  exact (div_le_one hN).mpr hh

lemma matrixCorrelation_change (A B : Matrix α α ℂ) (Q U : Matrix.unitaryGroup α ℂ) :
    |matrixCorrelation A Q U-matrixCorrelation B Q U| ≤
      QAlgorithms.frobNorm (A-B)/Real.sqrt (Fintype.card α:ℝ) := by
  have hN:0<(Fintype.card α:ℝ) := by exact_mod_cast Fintype.card_pos
  have hs:0<Real.sqrt (Fintype.card α:ℝ) := Real.sqrt_pos.mpr hN
  have ht:(A*(↑(star U*Q*U):Matrix α α ℂ)).trace.re-
      (B*(↑(star U*Q*U):Matrix α α ℂ)).trace.re=
      ((A-B)*(↑(star U*Q*U):Matrix α α ℂ)).trace.re := by
    rw [sub_mul,Matrix.trace_sub,Complex.sub_re]
  have hh:|((A-B)*(↑(star U*Q*U):Matrix α α ℂ)).trace.re| ≤
      QAlgorithms.frobNorm (A-B)*Real.sqrt (Fintype.card α:ℝ) := by
    calc
      _ ≤ ‖((A-B)*(↑(star U*Q*U):Matrix α α ℂ)).trace‖ := Complex.abs_re_le_norm _
      _ ≤ QAlgorithms.frobNorm (A-B)*QAlgorithms.frobNorm (↑(star U*Q*U):Matrix α α ℂ) := norm_trace_mul_le_frob _ _
      _ = _ := by rw [unitary_frob]
  unfold matrixCorrelation
  rw [←sub_div,ht,abs_div,abs_of_pos hN]
  have hd:=div_le_div_of_nonneg_right hh hN.le
  have he:QAlgorithms.frobNorm (A-B)*Real.sqrt (Fintype.card α:ℝ)/(Fintype.card α:ℝ)=
      QAlgorithms.frobNorm (A-B)/Real.sqrt (Fintype.card α:ℝ) := by
    field_simp [hN.ne',hs.ne']
    nlinarith [congrArg (fun z:ℝ=>QAlgorithms.frobNorm (A-B)*z) (Real.sq_sqrt hN.le)]
  exact hd.trans_eq he

lemma matrixCorrelation_lipschitz (A : Matrix α α ℂ) (hA:QAlgorithms.specNorm A ≤ 1)
    (Q U V : Matrix.unitaryGroup α ℂ) :
    |matrixCorrelation A Q U-matrixCorrelation A Q V| ≤
      (2/Real.sqrt (Fintype.card α:ℝ))*QAlgorithms.frobNorm ((U:Matrix α α ℂ)-(V:Matrix α α ℂ)) := by
  let u:Matrix α α ℂ:=U
  let v:Matrix α α ℂ:=V
  let q:Matrix α α ℂ:=Q
  have hT:(A*(uᴴ*q*u)).trace-(A*(vᴴ*q*v)).trace=
      ((u-v)*(A*uᴴ*q)).trace+((uᴴ-vᴴ)*(q*v*A)).trace := by
    have hr:∀z:Matrix α α ℂ,(A*(zᴴ*q*z)).trace=(z*A*zᴴ*q).trace := by
      intro z
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (A*zᴴ*q) z
    rw [hr,hr,←Matrix.trace_sub]
    have he:u*A*uᴴ*q-v*A*vᴴ*q=(u-v)*(A*uᴴ*q)+v*A*(uᴴ-vᴴ)*q := by noncomm_ring
    rw [he,Matrix.trace_add]
    congr 1
    rw [Matrix.trace_mul_cycle,Matrix.trace_mul_comm]
    congr 1
    simp only [Matrix.mul_assoc]
  have h1:QAlgorithms.frobNorm (A*uᴴ*q)=QAlgorithms.frobNorm A := by
    simpa only [u,q,Submonoid.coe_mul,Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.mul_assoc] using
      frob_mul_unitary A (star U*Q)
  have h2:QAlgorithms.frobNorm (q*v*A)=QAlgorithms.frobNorm A := by
    simpa only [q,v,Submonoid.coe_mul] using frob_unitary_mul (Q*V) A
  have h3:QAlgorithms.frobNorm (uᴴ-vᴴ)=QAlgorithms.frobNorm (u-v) := by
    rw [←Matrix.conjTranspose_sub,frob_conjTranspose]
  have hn:‖(A*(uᴴ*q*u)).trace-(A*(vᴴ*q*v)).trace‖ ≤
      2*QAlgorithms.frobNorm (u-v)*Real.sqrt (Fintype.card α:ℝ) := by
    rw [hT]
    calc
      _ ≤ ‖((u-v)*(A*uᴴ*q)).trace‖+‖((uᴴ-vᴴ)*(q*v*A)).trace‖ := norm_add_le _ _
      _ ≤ QAlgorithms.frobNorm (u-v)*QAlgorithms.frobNorm (A*uᴴ*q)+
          QAlgorithms.frobNorm (uᴴ-vᴴ)*QAlgorithms.frobNorm (q*v*A) :=
        add_le_add (norm_trace_mul_le_frob _ _) (norm_trace_mul_le_frob _ _)
      _ ≤ _ := by
        rw [h1,h2,h3]
        have hh:=mul_le_mul_of_nonneg_left (contraction_frob_le A hA) (InfluenceProof.frob_nonneg (u-v))
        nlinarith
  have hN:0<(Fintype.card α:ℝ) := by exact_mod_cast Fintype.card_pos
  have hs:0<Real.sqrt (Fintype.card α:ℝ) := Real.sqrt_pos.mpr hN
  have hreal:=Complex.abs_re_le_norm ((A*(uᴴ*q*u)).trace-(A*(vᴴ*q*v)).trace)
  have ha:=hreal.trans hn
  simp only [Complex.sub_re] at ha
  change |(A*(uᴴ*q*u)).trace.re/(Fintype.card α:ℝ)-
      (A*(vᴴ*q*v)).trace.re/(Fintype.card α:ℝ)| ≤ _
  rw [←sub_div,abs_div,abs_of_pos hN]
  have hd:=div_le_div_of_nonneg_right ha hN.le
  have he:2*QAlgorithms.frobNorm (u-v)*Real.sqrt (Fintype.card α:ℝ)/(Fintype.card α:ℝ)=
      (2/Real.sqrt (Fintype.card α:ℝ))*QAlgorithms.frobNorm (u-v) := by
    field_simp [hN.ne',hs.ne']
    nlinarith [congrArg (fun z:ℝ=>2*QAlgorithms.frobNorm (u-v)*z) (Real.sq_sqrt hN.le)]
  exact hd.trans_eq he

lemma matrixCorrelation_phase (A : Matrix α α ℂ) (Q U V : Matrix.unitaryGroup α ℂ)
    (z : Circle) (hUV:(U:Matrix α α ℂ)=(z:ℂ) • (V:Matrix α α ℂ)) :
    matrixCorrelation A Q U=matrixCorrelation A Q V := by
  have hz:(z:ℂ)*star (z:ℂ)=1 := by
    rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,Circle.norm_coe]
    norm_num
  have hz':star (z:ℂ)*(z:ℂ)=1 := by rw [mul_comm,hz]
  change (A*((U:Matrix α α ℂ)ᴴ*(Q:Matrix α α ℂ)*(U:Matrix α α ℂ))).trace.re/(Fintype.card α:ℝ)=
    (A*((V:Matrix α α ℂ)ᴴ*(Q:Matrix α α ℂ)*(V:Matrix α α ℂ))).trace.re/(Fintype.card α:ℝ)
  rw [hUV,Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,hz,hz',one_smul]

end RandomOracleUnitarySynthesis.GeometryProof

/- Module RandomOraclePublicUnitaryReindex -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.PublicHaarProof
open Matrix Finset Classical MeasureTheory
open GeometryProof
open scoped ComplexConjugate
instance public_unitaryHaar_isHaar (d:ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsHaarMeasure := by
  unfold QAlgorithms.Schur.unitaryHaar
  infer_instance

instance public_unitaryHaar_probability (d:ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def reindexUnitary (e : β≃α) (U : Matrix.unitaryGroup α ℂ) : Matrix.unitaryGroup β ℂ := by
  refine ⟨(U:Matrix α α ℂ).submatrix e e,?_⟩
  apply Unitary.mem_iff.mpr
  constructor
  · change ((U:Matrix α α ℂ).submatrix e e)ᴴ*((U:Matrix α α ℂ).submatrix e e)=1
    rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,
      show (U:Matrix α α ℂ)ᴴ*(U:Matrix α α ℂ)=1 from Unitary.star_mul_self_of_mem U.property,
      Matrix.submatrix_one_equiv]
  · change ((U:Matrix α α ℂ).submatrix e e)*((U:Matrix α α ℂ).submatrix e e)ᴴ=1
    rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,
      show (U:Matrix α α ℂ)*(U:Matrix α α ℂ)ᴴ=1 from Unitary.mul_star_self_of_mem U.property,
      Matrix.submatrix_one_equiv]

@[simp] lemma reindexUnitary_val (e : β≃α) (U : Matrix.unitaryGroup α ℂ) :
    (reindexUnitary e U:Matrix β β ℂ)=(U:Matrix α α ℂ).submatrix e e := rfl

def unitaryReindexEquiv (e : β≃α) : Matrix.unitaryGroup α ℂ≃*Matrix.unitaryGroup β ℂ where
  toFun:=reindexUnitary e
  invFun:=reindexUnitary e.symm
  left_inv U:=by apply Subtype.ext;ext x y;simp [Matrix.submatrix_apply]
  right_inv U:=by apply Subtype.ext;ext x y;simp [Matrix.submatrix_apply]
  map_mul' U V:=by
    apply Subtype.ext
    change ((U:Matrix α α ℂ)*(V:Matrix α α ℂ)).submatrix e e=
      (U:Matrix α α ℂ).submatrix e e*(V:Matrix α α ℂ).submatrix e e
    exact (Matrix.submatrix_mul_equiv _ _ e e e).symm

lemma continuous_unitaryReindexEquiv (e : β≃α) : Continuous (unitaryReindexEquiv e) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i=>continuous_pi (fun j=>
    (continuous_apply (e j)).comp ((continuous_apply (e i)).comp continuous_subtype_val)))

lemma frob_reindex (e : β≃α) (A : Matrix α α ℂ) :
    QAlgorithms.frobNorm (A.submatrix e e)=QAlgorithms.frobNorm A := by
  rw [frob_eq_sqrt_entries,frob_eq_sqrt_entries]
  congr 1
  have hi:∀i:α,(∑j:β,‖A i (e j)‖^2)=∑j:α,‖A i j‖^2 :=
    fun i=>e.sum_comp (fun j:α=>‖A i j‖^2)
  simp only [Matrix.submatrix_apply,hi]
  exact e.sum_comp (fun i:α=>∑j:α,‖A i j‖^2)

/-- Change only the finite basis labels; the full normalized Haar law is
transported by a continuous group isomorphism. -/
theorem qubit_unitary_reindex_measurePreserving (n : ℕ) :
    MeasurePreserving (unitaryReindexEquiv (Fintype.equivFin (synthesis_Bits n)).symm)
      (synthesis_haar n) (QAlgorithms.Schur.unitaryHaar (Fintype.card (synthesis_Bits n))) := by
  letI : Measure.IsHaarMeasure (synthesis_haar n) := by
    unfold synthesis_haar
    infer_instance
  exact MonoidHom.measurePreserving
    (f:=(unitaryReindexEquiv (Fintype.equivFin (synthesis_Bits n)).symm).toMonoidHom)
    (continuous_unitaryReindexEquiv (Fintype.equivFin (synthesis_Bits n)).symm)
    (unitaryReindexEquiv (Fintype.equivFin (synthesis_Bits n)).symm).surjective (by simp)

end RandomOracleUnitarySynthesis.PublicHaarProof

/- Module RandomOraclePublicHaarSubgaussian -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.PublicHaarProof
open MeasureTheory ProbabilityTheory Finset Classical

/-- Centered sub-Gaussian MGF for the actual full Haar measure, using the
proved SU kernel and genuine phase invariance. -/
theorem phase_invariant_subgaussian (d : ℕ) (hd:1 ≤ d)
    (F : Matrix.unitaryGroup (Fin d) ℂ→ℝ) (hF:Continuous F) (L : ℝ) (hL:0 ≤ L)
    (hLip:∀U V:Matrix.unitaryGroup (Fin d) ℂ,|F U-F V| ≤ L*Real.sqrt
      (∑x:Fin d,∑y:Fin d,‖(U:Matrix (Fin d) (Fin d) ℂ) x y-(V:Matrix (Fin d) (Fin d) ℂ) x y‖^2))
    (hphase:∀z:Circle,∀U V:Matrix.unitaryGroup (Fin d) ℂ,
      (U:Matrix (Fin d) (Fin d) ℂ)=(z:ℂ) • (V:Matrix (Fin d) (Fin d) ℂ)→F U=F V) :
    HasSubgaussianMGF (fun U=>F U-∫V,F V ∂QAlgorithms.Schur.unitaryHaar d)
      ⟨2*L^2/d,by positivity⟩ (QAlgorithms.Schur.unitaryHaar d) := by
  let μ:=QAlgorithms.Schur.unitaryHaar d
  let m:=∫U,F U ∂μ
  have hFi:Integrable F μ := hF.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset isClosed_closure (by simp))
  have hc:∀t:ℝ,Continuous (fun U=>t*(F U-m)) := fun t=>(hF.sub continuous_const).const_mul t
  have he:∀t:ℝ,Integrable (fun U=>Real.exp (t*(F U-m))) μ :=
    fun t=>(hc t).rexp.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset isClosed_closure (by simp))
  refine ⟨he,?_⟩
  intro t
  have hh:=HaarPhaseInvariantUnitary.logMeanBound d hd (fun U=>t*(F U-m)) (hc t) (|t| *L)
    (mul_nonneg (abs_nonneg t) hL) (by
      intro U V
      rw [←mul_sub,sub_sub_sub_cancel_right,abs_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hLip U V) (abs_nonneg t))
    (by intro z U V he;rw [hphase z U V he])
  have hi:(∫U,t*(F U-m) ∂μ)=0 := by
    rw [integral_const_mul,integral_sub hFi (integrable_const m)]
    simp [m]
  change Real.log (∫U,Real.exp (t*(F U-m)) ∂μ) ≤ (∫U,t*(F U-m) ∂μ)+(|t| *L)^2/d at hh
  rw [hi,zero_add] at hh
  have hcoef:(|t| *L)^2/d=(2*L^2/d)*t^2/2 := by rw [mul_pow,sq_abs];ring
  rw [hcoef] at hh
  exact (Real.log_le_iff_le_exp (integral_exp_pos (he t))).mp hh

end RandomOracleUnitarySynthesis.PublicHaarProof

/- Module RandomOraclePublicQubitSubgaussian -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.PublicHaarProof
open Matrix Finset Classical MeasureTheory ProbabilityTheory
open GeometryProof
open scoped ComplexConjugate

/-- The proved phase-invariant concentration uses only finite basis labels;
transporting back to the public binary register preserves its Haar law. -/
theorem qubit_phase_subgaussian (n : ℕ) (F : synthesis_Unitary n→ℝ) (hF:Continuous F)
    (L : ℝ) (hL:0 ≤ L)
    (hLip:∀U V:synthesis_Unitary n,|F U-F V| ≤ L*QAlgorithms.frobNorm
      ((U:synthesis_Mat n)-(V:synthesis_Mat n)))
    (hphase:∀z:Circle,∀U V:synthesis_Unitary n,
      (U:synthesis_Mat n)=(z:ℂ) • (V:synthesis_Mat n)→F U=F V) :
    HasSubgaussianMGF (fun U=>F U-∫V,F V ∂synthesis_haar n)
      ⟨2*L^2/(Fintype.card (synthesis_Bits n):ℝ),by positivity⟩ (synthesis_haar n) := by
  let d:=Fintype.card (synthesis_Bits n)
  let e:Fin d≃synthesis_Bits n:=(Fintype.equivFin (synthesis_Bits n)).symm
  let E:=unitaryReindexEquiv e
  let G:Matrix.unitaryGroup (Fin d) ℂ→ℝ:=fun V=>F (E.symm V)
  have hd:1 ≤ d := Fintype.card_pos
  have hEi:Continuous (fun V:Matrix.unitaryGroup (Fin d) ℂ=>E.symm V) :=
    continuous_unitaryReindexEquiv e.symm
  have hG:Continuous G := hF.comp hEi
  have hmetric:∀U V:Matrix.unitaryGroup (Fin d) ℂ,
      QAlgorithms.frobNorm ((E.symm U:synthesis_Mat n)-(E.symm V:synthesis_Mat n))=
        Real.sqrt (∑x:Fin d,∑y:Fin d,‖(U:Matrix (Fin d) (Fin d) ℂ) x y-
          (V:Matrix (Fin d) (Fin d) ℂ) x y‖^2) := by
    intro U V
    have he:((E.symm U:synthesis_Mat n)-(E.symm V:synthesis_Mat n))=
        ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ)).submatrix e.symm e.symm := rfl
    rw [he,frob_reindex,frob_eq_sqrt_entries]
    simp only [Matrix.sub_apply]
  have hsg:=phase_invariant_subgaussian d hd G hG L hL (by
    intro U V
    have hh:=hLip (E.symm U) (E.symm V)
    rwa [hmetric] at hh) (by
      intro z U V he
      apply hphase z
      ext x y
      exact congrFun (congrFun he (e.symm x)) (e.symm y))
  have hMP:=qubit_unitary_reindex_measurePreserving n
  have hI:(∫V,G V ∂QAlgorithms.Schur.unitaryHaar d)=∫U,F U ∂synthesis_haar n := by
    rw [←hMP.map_eq,integral_map hMP.measurable.aemeasurable hG.aestronglyMeasurable]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun U=>by dsimp only [G];rw [E.symm_apply_apply])
  have hsg':HasSubgaussianMGF (fun V:Matrix.unitaryGroup (Fin d) ℂ=>G V-∫W,G W ∂QAlgorithms.Schur.unitaryHaar d)
      ⟨2*L^2/d,by positivity⟩ ((synthesis_haar n).map E) := by
    rw [hMP.map_eq]
    exact hsg
  have hh:=HasSubgaussianMGF.of_map hMP.measurable.aemeasurable hsg'
  have hEE:∀U:synthesis_Unitary n,
      E.symm ((unitaryReindexEquiv (Fintype.equivFin (synthesis_Bits n)).symm) U)=U :=
    fun U=>E.symm_apply_apply U
  simpa only [Function.comp_def,G,hEE,hI] using hh

end RandomOracleUnitarySynthesis.PublicHaarProof

/- Module RandomOraclePauliHaarMean -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.HaarProof
open Matrix Finset Classical MeasureTheory
open GeometryProof PauliProof DirectFidelity.State
open scoped ComplexConjugate

@[simp] lemma pauliUnitary_val {n : ℕ} (P : synthesis_Pauli n) :
    (pauliUnitary P:synthesis_Mat n)=W P := rfl

lemma pauli_conjugate_correlation_sum {n : ℕ} (A : synthesis_Mat n)
    (Q : synthesis_Pauli n) (hQ:Q≠(fun _=>0)) (U : synthesis_Unitary n) :
    (∑P:synthesis_Pauli n,matrixCorrelation A (pauliUnitary Q) (pauliUnitary P*U))=0 := by
  have he:∀P:synthesis_Pauli n,matrixCorrelation A (pauliUnitary Q) (pauliUnitary P*U)=
      (A*(U:synthesis_Mat n)ᴴ*(W P*W Q*W P)*(U:synthesis_Mat n)).trace.re/
        (Fintype.card (synthesis_Bits n):ℝ) := by
    intro P
    unfold matrixCorrelation
    simp only [Submonoid.coe_mul,Unitary.coe_star,Matrix.star_eq_conjTranspose,
      pauliUnitary_val,Matrix.conjTranspose_mul,W_herm]
    congr 2
    simp only [Matrix.mul_assoc]
  have hM:(∑P:synthesis_Pauli n,A*(U:synthesis_Mat n)ᴴ*(W P*W Q*W P)*(U:synthesis_Mat n))=0 := by
    have hh:(∑P:synthesis_Pauli n,A*(U:synthesis_Mat n)ᴴ*(W P*W Q*W P)*(U:synthesis_Mat n))=
        (A*(U:synthesis_Mat n)ᴴ)*(∑P:synthesis_Pauli n,W P*W Q*W P)*(U:synthesis_Mat n) := by
      simp only [Matrix.mul_sum,Matrix.sum_mul]
    rw [hh,pauli_twirl,trace_W,if_neg hQ,mul_zero,zero_smul,Matrix.mul_zero,Matrix.zero_mul]
  calc
    _ = ((∑P:synthesis_Pauli n,A*(U:synthesis_Mat n)ᴴ*(W P*W Q*W P)*(U:synthesis_Mat n)).trace).re/
        (Fintype.card (synthesis_Bits n):ℝ) := by
      simp only [he,Matrix.trace_sum,Complex.re_sum,sum_div]
    _ = 0 := by rw [hM];simp

/-- Mean zero is proved from the actual Haar left invariance and finite Pauli
twirl, using no assumed centeredness of the correlation observable. -/
theorem pauli_haar_mean_zero {n : ℕ} (A : synthesis_Mat n)
    (Q : synthesis_Pauli n) (hQ:Q≠(fun _=>0)) :
    (∫U,matrixCorrelation A (pauliUnitary Q) U ∂synthesis_haar n)=0 := by
  letI : Measure.IsHaarMeasure (synthesis_haar n) := by unfold synthesis_haar;infer_instance
  let F:synthesis_Unitary n→ℝ:=matrixCorrelation A (pauliUnitary Q)
  have hc:Continuous F := matrixCorrelation_continuous A (pauliUnitary Q)
  have hi:∀P:synthesis_Pauli n,Integrable (fun U:synthesis_Unitary n=>F (pauliUnitary P*U)) (synthesis_haar n) := by
    intro P
    exact (hc.comp (continuous_const.mul continuous_id)).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (by simp))
  have hz:(fun U:synthesis_Unitary n=>∑P:synthesis_Pauli n,F (pauliUnitary P*U))=(fun _=>0) :=
    funext (fun U=>pauli_conjugate_correlation_sum A Q hQ U)
  have hh:=congrArg (fun g:synthesis_Unitary n→ℝ=>∫U,g U ∂synthesis_haar n) hz
  rw [integral_finset_sum _ (fun P _=>hi P)] at hh
  simp only [integral_zero,integral_mul_left_eq_self,sum_const,card_univ,nsmul_eq_mul] at hh
  have hcard:(Fintype.card (synthesis_Pauli n):ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  exact (mul_eq_zero.mp hh).resolve_left hcard

end RandomOracleUnitarySynthesis.HaarProof

/- Module RandomOracleHaarTailPublic -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis
open Matrix Finset Classical MeasureTheory ProbabilityTheory
open GeometryProof HaarProof PublicHaarProof PauliProof
open scoped ComplexConjugate ENNReal

/-- Exact public Lemma4.13. The proof derives the stronger exponent 1/16
from the actual phase-invariant SU log-Sobolev kernel and then relaxes to 1/48. -/
theorem synthesis_haar_trace_tail (n : ℕ) (A : synthesis_Mat n)
    (hA : A.IsHermitian) (hcontract : synthesis_IsContraction A)
    (Q : synthesis_Pauli n) (hQ : Q ≠ (fun _ => 0)) (t : ℝ) (ht : 0 ≤ t) :
    (synthesis_haar n) {U | t ≤ synthesis_correlation A Q U} ≤
      ENNReal.ofReal (Real.exp (-((2 : ℝ)^n)^2 * t^2 / 48)) := by
  let F:synthesis_Unitary n→ℝ:=matrixCorrelation A (pauliUnitary Q)
  have hcard:(Fintype.card (synthesis_Bits n):ℝ)=(2:ℝ)^n := by
    simp [synthesis_Bits,DirectFidelity.State.Q]
  have hN:0<(2:ℝ)^n := pow_pos (by norm_num) _
  have hs:0<Real.sqrt ((2:ℝ)^n) := Real.sqrt_pos.mpr hN
  have hF:∀U:synthesis_Unitary n,F U=synthesis_correlation A Q U := by
    intro U
    change (A*((U:synthesis_Mat n)ᴴ*DirectFidelity.State.W Q*(U:synthesis_Mat n))).trace.re/
        (Fintype.card (synthesis_Bits n):ℝ)=_
    rw [hcard]
    rfl
  have hL:0 ≤ 2/Real.sqrt (Fintype.card (synthesis_Bits n):ℝ) := by positivity
  have hsg:=qubit_phase_subgaussian n F (matrixCorrelation_continuous A (pauliUnitary Q))
    (2/Real.sqrt (Fintype.card (synthesis_Bits n):ℝ)) hL
    (fun U V=>matrixCorrelation_lipschitz A hcontract (pauliUnitary Q) U V)
    (fun z U V he=>matrixCorrelation_phase A (pauliUnitary Q) U V z he)
  have hmean:(∫U,F U ∂synthesis_haar n)=0 := pauli_haar_mean_zero A Q hQ
  rw [hmean] at hsg
  simp only [sub_zero] at hsg
  have hh:=hsg.measure_ge_le ht
  change (synthesis_haar n).real {U|t ≤ F U} ≤
    Real.exp (-t^2/(2*(2*(2/Real.sqrt (Fintype.card (synthesis_Bits n):ℝ))^2/
      (Fintype.card (synthesis_Bits n):ℝ)))) at hh
  rw [hcard] at hh
  have hc:2*(2/Real.sqrt ((2:ℝ)^n))^2/((2:ℝ)^n)=8/((2:ℝ)^n)^2 := by
    rw [div_pow,Real.sq_sqrt hN.le]
    field_simp
    <;> ring
  rw [hc] at hh
  have he:-t^2/(2*(8/((2:ℝ)^n)^2))=-((2:ℝ)^n)^2*t^2/16 := by
    field_simp
    <;> ring
  rw [he] at hh
  have hweak:Real.exp (-((2:ℝ)^n)^2*t^2/16) ≤ Real.exp (-((2:ℝ)^n)^2*t^2/48) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sq_nonneg ((2:ℝ)^n)) (sq_nonneg t)]
  have hset:{U:synthesis_Unitary n|t ≤ F U}={U|t ≤ synthesis_correlation A Q U} := by
    ext U
    change t ≤ F U ↔ t ≤ synthesis_correlation A Q U
    rw [hF]
  rw [←hset]
  calc
    _ = ENNReal.ofReal ((synthesis_haar n).real {U|t ≤ F U}) :=
      (ENNReal.ofReal_toReal (measure_ne_top (synthesis_haar n) _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hh.trans hweak)

end RandomOracleUnitarySynthesis

open RandomOracleUnitarySynthesis

theorem solution (n : ℕ) (A : synthesis_Mat n)
    (hA : A.IsHermitian) (hcontract : synthesis_IsContraction A)
    (Q : synthesis_Pauli n) (hQ : Q ≠ (fun _ => 0)) (t : ℝ) (ht : 0 ≤ t) :
    (synthesis_haar n) {U | t ≤ synthesis_correlation A Q U} ≤
      ENNReal.ofReal (Real.exp (-((2 : ℝ)^n)^2 * t^2 / 48)) :=
  RandomOracleUnitarySynthesis.synthesis_haar_trace_tail n A hA hcontract Q hQ t ht
