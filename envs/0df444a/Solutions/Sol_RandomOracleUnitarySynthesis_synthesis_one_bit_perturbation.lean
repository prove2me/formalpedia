-- Prove2me | solution 1 for RandomOracleUnitarySynthesis.synthesis_one_bit_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T18:19:15.057728+00:00
-- url     : https://prove2.me/submissions/e32ad347-4292-466f-a8c2-94c5d45581d5

import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_circuit


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

open RandomOracleUnitarySynthesis

theorem solution {n m m₀ k : ℕ}
    (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (x : synthesis_Bits m₀) :
    QAlgorithms.frobNorm (synthesis_A C (synthesis_flip f x) - synthesis_A C f)^2 ≤
      4 * synthesis_influence C f x * synthesis_influence C (synthesis_flip f x) x :=
  InfluenceProof.synthesis_one_bit_perturbation C f x
