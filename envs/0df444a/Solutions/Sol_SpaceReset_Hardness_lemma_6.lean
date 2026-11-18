-- Prove2me | solution 1 for SpaceReset.Hardness.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T16:32:24.408884+00:00
-- url     : https://prove2.me/submissions/900aa5dc-0da5-4145-888e-3cb9eab8a684

import Mathlib
import Definitions.Def_SpaceReset_Hardness_DiscardDevice


/- Module SpaceResetCodeState -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped ComplexOrder

variable {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ}

lemma independent_of_fullRowRank (G : Matrix κ (Fin n) F2) (hG:FullRowRank G) :
    LinearIndependent F2 G.row := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change Fintype.card κ=Module.finrank F2 (Submodule.span F2 (Set.range G.row))
  rw [← Matrix.rank_eq_finrank_span_row G]
  exact hG.symm

lemma f2_decide_one_injective : Function.Injective (fun z : F2=>decide (z=1)) := by decide

/-- Full row rank makes the exact public Bool-valued code map injective. -/
theorem codeword_injective (G : Matrix κ (Fin n) F2) (hG:FullRowRank G) :
    Function.Injective (codeword G) := by
  intro x y hxy
  apply (Matrix.vecMul_injective_iff.mpr (independent_of_fullRowRank G hG))
  funext j
  apply f2_decide_one_injective
  have hh:=congrFun hxy j
  simpa [codeword,parityBit,Matrix.vecMul,dotProduct,mul_comm] using hh

lemma ketbra_diagonal {α : Type} [DecidableEq α] (x : α) :
    ketbra x=Matrix.diagonal (fun y=>if y=x then (1:ℂ) else 0) := by
  ext y z
  by_cases hy:y=x <;> by_cases hz:z=x <;> by_cases hyz:y=z <;>
    simp_all [ketbra,Matrix.diagonal_apply]

def codeProjector (G : Matrix κ (Fin n) F2) : Matrix (Fin n→Bool) (Fin n→Bool) ℂ :=
  Matrix.diagonal (fun y=>if y∈Set.range (codeword G) then (1:ℂ) else 0)

/-- The target is exactly a scalar multiple of the diagonal projector onto the
literal codeword image, rather than a coherent code superposition. -/
theorem codeState_flat (G : Matrix κ (Fin n) F2) (hG:FullRowRank G) :
    codeState G=((1:ℂ)/(2:ℂ)^Fintype.card κ) • codeProjector G := by
  rw [codeState,← Finset.smul_sum]
  congr 1
  ext a b
  simp only [Matrix.sum_apply]
  by_cases hab:a=b
  · subst b
    simp only [ketbra,codeProjector,Matrix.diagonal_apply_eq]
    by_cases hmem:a∈Set.range (codeword G)
    · obtain ⟨x,hx⟩ := hmem
      rw [if_pos ⟨x,hx⟩]
      rw [Finset.sum_eq_single x]
      · simp [hx]
      · intro y hy hne
        have hn:a ≠ codeword G y := by
          intro hh
          exact hne ((codeword_injective G hG) (hh.symm.trans hx.symm))
        simp [hn]
      · simp
    · rw [if_neg hmem]
      apply Finset.sum_eq_zero
      intro x hx
      have hn:a ≠ codeword G x := fun hh=>hmem ⟨x,hh.symm⟩
      simp [hn]
  · have hba:b ≠ a := Ne.symm hab
    simp only [codeProjector,Matrix.diagonal_apply_ne _ hab]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases ha:a=codeword G x
    · have hb:b ≠ codeword G x := fun hh=>hba (hh.trans ha.symm)
      simp [ketbra,hb]
    · simp [ketbra,ha]

theorem codeProjector_idempotent (G : Matrix κ (Fin n) F2) :
    codeProjector G*codeProjector G=codeProjector G := by
  rw [codeProjector,Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  split_ifs <;> simp

theorem codeProjector_posSemidef (G : Matrix κ (Fin n) F2) :
    (codeProjector G).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro x
  split_ifs <;> norm_num

theorem codeProjector_rank (G : Matrix κ (Fin n) F2) (hG:FullRowRank G) :
    (codeProjector G).rank=2^Fintype.card κ := by
  rw [codeProjector,Matrix.rank_diagonal]
  have he : {i : Fin n→Bool // (if i∈Set.range (codeword G) then (1:ℂ) else 0) ≠ 0}
      ≃ Set.range (codeword G) := Equiv.subtypeEquivRight (fun i=>by simp)
  rw [Fintype.card_congr he,← Fintype.card_congr (Equiv.ofInjective (codeword G) (codeword_injective G hG))]
  simp [F2]

theorem codeProjector_trace (G : Matrix κ (Fin n) F2) (hG:FullRowRank G) :
    (codeProjector G).trace=(2:ℂ)^Fintype.card κ := by
  have htrace:(codeProjector G).trace=((codeProjector G).rank:ℂ) := by
    rw [codeProjector,Matrix.trace_diagonal,Matrix.rank_diagonal]
    simp [Finset.sum_boole,Fintype.card_subtype]
  rw [htrace,codeProjector_rank G hG,Nat.cast_pow,Nat.cast_ofNat]

theorem codeState_rank (G : Matrix κ (Fin n) F2) (hG:FullRowRank G) :
    (codeState G).rank=2^Fintype.card κ := by
  rw [codeState_flat G hG,Matrix.rank_smul_of_mem_nonZeroDivisors,
    codeProjector_rank G hG]
  apply mem_nonZeroDivisors_of_ne_zero
  exact one_div_ne_zero (pow_ne_zero _ (by norm_num))

theorem codeState_density (G : Matrix κ (Fin n) F2) (hG:FullRowRank G) :
    IsDensity (codeState G) := by
  rw [codeState_flat G hG]
  constructor
  · exact (codeProjector_posSemidef G).smul (by positivity : 0 ≤ (1:ℂ)/(2:ℂ)^Fintype.card κ)
  · rw [Matrix.trace_smul,codeProjector_trace G hG,smul_eq_mul]
    exact one_div_mul_cancel (pow_ne_zero _ (by norm_num))

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetTraceDistance -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped MatrixOrder ComplexOrder
variable {α : Type} [Fintype α] [DecidableEq α]

lemma trace_mul_posSemidef_nonneg (A B : Matrix α α ℂ) (ha:A.PosSemidef) (hb:B.PosSemidef) :
    0 ≤ (A*B).trace.re := by
  let S := CFC.sqrt A
  have hs:Sᴴ=S := (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq
  have ht:=hb.mul_mul_conjTranspose_same S
  have htr:0 ≤ (S*B*Sᴴ).trace.re := (Complex.nonneg_iff.mp ht.trace_nonneg).1
  rw [hs,Matrix.trace_mul_cycle] at htr
  change 0 ≤ ((CFC.sqrt A*CFC.sqrt A)*B).trace.re at htr
  rw [CFC.sqrt_mul_sqrt_self A ha.nonneg] at htr
  exact htr

lemma trace_mul_effect_le (P A : Matrix α α ℂ) (ha:A.PosSemidef)
    (hp:(1-P).PosSemidef) : (P*A).trace.re ≤ A.trace.re := by
  have ht:=trace_mul_posSemidef_nonneg (1-P) A hp ha
  simp only [sub_mul,Matrix.one_mul,Matrix.trace_sub,Complex.sub_re] at ht
  linarith

/-- The sharp half-trace-norm variational bound for a traceless Hermitian
matrix, with an arbitrary matrix effect. -/
theorem trace_effect_le_half_traceNorm (H P : Matrix α α ℂ)
    (hH:H.IsHermitian) (htr:H.trace=0) (hp:P.PosSemidef) (hpc:(1-P).PosSemidef) :
    (P*H).trace.re ≤ WildeQIT.traceNorm H/2 := by
  have hpos:(H⁺).PosSemidef := (CFC.posPart_nonneg H).posSemidef
  have hneg:(H⁻).PosSemidef := (CFC.negPart_nonneg H).posSemidef
  have habs:CFC.abs H=H⁺+H⁻ := (CFC.posPart_add_negPart H hH.isSelfAdjoint).symm
  have hsplit:H=H⁺-H⁻ := (CFC.posPart_sub_negPart H hH.isSelfAdjoint).symm
  have heq:(H⁺).trace.re=(H⁻).trace.re := by
    have hh:=congrArg (fun M : Matrix α α ℂ=>M.trace.re) hsplit
    rw [htr,Matrix.trace_sub] at hh
    simp only [Complex.zero_re,Complex.sub_re] at hh
    linarith
  have hnorm:WildeQIT.traceNorm H=(H⁺).trace.re+(H⁻).trace.re := by
    change (CFC.abs H).trace.re= _
    rw [habs,Matrix.trace_add,Complex.add_re]
  have h1:=trace_mul_effect_le P H⁺ hpos hpc
  have h2:=trace_mul_posSemidef_nonneg P H⁻ hp hneg
  have h3:(P*H).trace.re=(P*H⁺).trace.re-(P*H⁻).trace.re := by
    conv_lhs => rw [hsplit]
    rw [mul_sub,Matrix.trace_sub,Complex.sub_re]
  linarith

/-- Outcome probabilities of an arbitrary effect differ by at most the
public trace distance of two equal-trace Hermitian matrices. -/
theorem trace_effect_sub_le_tdist (A B P : Matrix α α ℂ)
    (ha:A.IsHermitian) (hb:B.IsHermitian) (ht:A.trace=B.trace)
    (hp:P.PosSemidef) (hpc:(1-P).PosSemidef) :
    (P*(A-B)).trace.re ≤ tdist A B := by
  exact trace_effect_le_half_traceNorm (A-B) P (ha.sub hb) (by simp [ht]) hp hpc

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetSupportProjection -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped MatrixOrder ComplexOrder
variable {α : Type} [Fintype α] [DecidableEq α]

lemma unitary_left_cancel (U : Matrix.unitaryGroup α ℂ) (B : Matrix α α ℂ) :
    star (U:Matrix α α ℂ)*((U:Matrix α α ℂ)*B)=B := by
  rw [← Matrix.mul_assoc,Unitary.coe_star_mul_self,Matrix.one_mul]

lemma spectral_formula (A : Matrix α α ℂ) (hA:A.IsHermitian) :
    A=(hA.eigenvectorUnitary:Matrix α α ℂ)*
      Matrix.diagonal (fun i=>(hA.eigenvalues i:ℂ))*star (hA.eigenvectorUnitary:Matrix α α ℂ) := by
  simpa [Unitary.conjStarAlgAut_apply,Function.comp_def] using hA.spectral_theorem

def supportProjection (A : Matrix α α ℂ) (hA:A.IsHermitian) : Matrix α α ℂ :=
  (hA.eigenvectorUnitary:Matrix α α ℂ)*
    Matrix.diagonal (fun i=>if hA.eigenvalues i=0 then (0:ℂ) else 1)*
      star (hA.eigenvectorUnitary:Matrix α α ℂ)

lemma supportProjection_posSemidef (A : Matrix α α ℂ) (hA:A.IsHermitian) :
    (supportProjection A hA).PosSemidef := by
  have hd:(Matrix.diagonal (fun i=>if hA.eigenvalues i=0 then (0:ℂ) else 1)).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    split_ifs <;> norm_num
  exact hd.mul_mul_conjTranspose_same _

lemma supportProjection_compl_posSemidef (A : Matrix α α ℂ) (hA:A.IsHermitian) :
    (1-supportProjection A hA).PosSemidef := by
  have hd:(Matrix.diagonal (fun i=>if hA.eigenvalues i=0 then (1:ℂ) else 0)).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    split_ifs <;> norm_num
  have hh:=hd.mul_mul_conjTranspose_same (hA.eigenvectorUnitary:Matrix α α ℂ)
  have he:Matrix.diagonal (fun i=>if hA.eigenvalues i=0 then (1:ℂ) else 0)=
      1-Matrix.diagonal (fun i=>if hA.eigenvalues i=0 then (0:ℂ) else 1) := by
    ext i j
    by_cases hij:i=j <;> by_cases hi:hA.eigenvalues i=0 <;> simp_all
  rw [he,mul_sub,sub_mul] at hh
  simpa only [supportProjection,← Matrix.star_eq_conjTranspose,← Unitary.coe_star,
    Matrix.mul_one,Unitary.coe_mul_star_self] using hh

lemma supportProjection_mul (A : Matrix α α ℂ) (hA:A.IsHermitian) :
    supportProjection A hA*A=A := by
  have he:Matrix.diagonal (fun i=>if hA.eigenvalues i=0 then (0:ℂ) else 1)*
      Matrix.diagonal (fun i=>(hA.eigenvalues i:ℂ))=
      Matrix.diagonal (fun i=>(hA.eigenvalues i:ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs with hi <;> simp [hi]
  calc
    supportProjection A hA*A =
      ((hA.eigenvectorUnitary:Matrix α α ℂ)*
        Matrix.diagonal (fun i=>if hA.eigenvalues i=0 then (0:ℂ) else 1)*
          star (hA.eigenvectorUnitary:Matrix α α ℂ))*
        ((hA.eigenvectorUnitary:Matrix α α ℂ)*Matrix.diagonal (fun i=>(hA.eigenvalues i:ℂ))*
          star (hA.eigenvectorUnitary:Matrix α α ℂ)) :=
      congrArg (fun B=>supportProjection A hA*B) (spectral_formula A hA)
    _ = (hA.eigenvectorUnitary:Matrix α α ℂ)*
        (Matrix.diagonal (fun i=>if hA.eigenvalues i=0 then (0:ℂ) else 1)*
          Matrix.diagonal (fun i=>(hA.eigenvalues i:ℂ)))*star (hA.eigenvectorUnitary:Matrix α α ℂ) := by
      simp only [Matrix.mul_assoc,unitary_left_cancel]
    _ = A := by rw [he];exact (spectral_formula A hA).symm

lemma supportProjection_trace (A : Matrix α α ℂ) (hA:A.IsHermitian) :
    (supportProjection A hA).trace=(A.rank:ℂ) := by
  rw [supportProjection,Matrix.trace_mul_cycle]
  simp only [Unitary.coe_star_mul_self,Matrix.one_mul,
    Matrix.trace_diagonal,hA.rank_eq_card_non_zero_eigs,Fintype.card_subtype]
  simpa only [ite_not] using (Finset.sum_boole (R:=ℂ) (fun i=>hA.eigenvalues i ≠ 0) Finset.univ)

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetFlatRank -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped MatrixOrder ComplexOrder
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The measurement outside an actual state's support gives the sharp rank
lower bound against a flat (or spectrally flatter) target. -/
theorem rank_ge_one_sub_distance_mul (ρ τ : Matrix α α ℂ)
    (hρ:IsDensity ρ) (hτ:IsDensity τ) (d : ℕ)
    (hflat:(1-(d:ℂ) • τ).PosSemidef) :
    (1-tdist ρ τ)*(d:ℝ) ≤ (ρ.rank:ℝ) := by
  let Q := supportProjection ρ hρ.1.isHermitian
  have hQ:Q.PosSemidef := supportProjection_posSemidef ρ hρ.1.isHermitian
  have hQc:(1-Q).PosSemidef := supportProjection_compl_posSemidef ρ hρ.1.isHermitian
  have hQρ:Q*ρ=ρ := supportProjection_mul ρ hρ.1.isHermitian
  have hQt:Q.trace.re=(ρ.rank:ℝ) := by
    change (supportProjection ρ hρ.1.isHermitian).trace.re= _
    rw [supportProjection_trace]
    simp
  have htest:=trace_effect_sub_le_tdist ρ τ Q hρ.1.isHermitian hτ.1.isHermitian
    (hρ.2.trans hτ.2.symm) hQ hQc
  rw [mul_sub,hQρ,Matrix.trace_sub,hρ.2,Complex.sub_re,Complex.one_re] at htest
  have hbound:=trace_mul_posSemidef_nonneg Q (1-(d:ℂ) • τ) hQ hflat
  simp only [mul_sub,Matrix.mul_one,Matrix.mul_smul,Matrix.trace_sub,
    Matrix.trace_smul,smul_eq_mul,Complex.sub_re,Complex.mul_re,Complex.natCast_re,
    Complex.natCast_im,zero_mul,sub_zero,hQt] at hbound
  have hd:0 ≤ (d:ℝ) := Nat.cast_nonneg d
  nlinarith

lemma codeProjector_compl_posSemidef {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ}
    (G : Matrix κ (Fin n) F2) : (1-codeProjector G).PosSemidef := by
  have hh:(1-codeProjector G)=Matrix.diagonal
      (fun x=>if x∈Set.range (codeword G) then (0:ℂ) else 1) := by
    ext i j
    by_cases hij:i=j <;> by_cases hi:i∈Set.range (codeword G) <;> simp_all [codeProjector]
  rw [hh]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro x
  split_ifs <;> norm_num

/-- The exact quantitative code-state rank benchmark, before substituting a
circuit's output-rank bound. -/
theorem codeState_rank_benchmark {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ}
    (G : Matrix κ (Fin n) F2) (hG:FullRowRank G) (ρ : Matrix (Fin n→Bool) (Fin n→Bool) ℂ)
    (hρ:IsDensity ρ) (ε : ℝ) (he:tdist ρ (codeState G) ≤ ε) :
    (1-ε)*(2:ℝ)^Fintype.card κ ≤ (ρ.rank:ℝ) := by
  have hf:(1-((2^Fintype.card κ:ℕ):ℂ) • codeState G).PosSemidef := by
    rw [codeState_flat G hG,smul_smul]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    rw [mul_one_div_cancel (pow_ne_zero _ (by norm_num)),one_smul]
    exact codeProjector_compl_posSemidef G
  have hh:=rank_ge_one_sub_distance_mul ρ (codeState G) hρ (codeState_density G hG)
    (2^Fintype.card κ) hf
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hh
  have hd:0 ≤ (2:ℝ)^Fintype.card κ := by positivity
  nlinarith

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetQuantumRankBasics -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped ComplexOrder MatrixOrder

variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

lemma matrix_rank_add_le (A B : Matrix α β ℂ) : (A+B).rank ≤ A.rank+B.rank := by
  rw [Matrix.rank,Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma matrix_rank_sum_le {ι : Type} (S : Finset ι) (A : ι→Matrix α β ℂ) :
    (∑ i∈S,A i).rank ≤ ∑ i∈S,(A i).rank := by
  induction S using Finset.cons_induction with
  | empty => simp
  | @cons i S hi ih =>
    rw [Finset.sum_cons hi,Finset.sum_cons hi]
    exact (matrix_rank_add_le _ _).trans (Nat.add_le_add_left ih _)

lemma ptraceRight_eq_sum (ρ : Matrix (α×β) (α×β) ℂ) :
    ptraceRight ρ=∑ b:β,ρ.submatrix (fun a=>(a,b)) (fun a=>(a,b)) := by
  ext a a'
  simp [ptraceRight,Matrix.sum_apply]

lemma ptraceLeft_eq_sum (ρ : Matrix (α×β) (α×β) ℂ) :
    ptraceLeft ρ=∑ a:α,ρ.submatrix (fun b=>(a,b)) (fun b=>(a,b)) := by
  ext b b'
  simp [ptraceLeft,Matrix.sum_apply]

/-- Tracing out a d-dimensional factor multiplies rank by at most d. -/
theorem rank_ptraceRight_le (ρ : Matrix (α×β) (α×β) ℂ) :
    (ptraceRight ρ).rank ≤ Fintype.card β*ρ.rank := by
  rw [ptraceRight_eq_sum]
  exact (matrix_rank_sum_le _ _).trans ((Finset.sum_le_sum (fun b hb=>Matrix.rank_submatrix_le _ _ _)).trans_eq
    (by simp [Nat.mul_comm]))

theorem rank_ptraceLeft_le (ρ : Matrix (α×β) (α×β) ℂ) :
    (ptraceLeft ρ).rank ≤ Fintype.card α*ρ.rank := by
  rw [ptraceLeft_eq_sum]
  exact (matrix_rank_sum_le _ _).trans ((Finset.sum_le_sum (fun b hb=>Matrix.rank_submatrix_le _ _ _)).trans_eq
    (by simp [Nat.mul_comm]))

lemma ptraceRight_posSemidef (ρ : Matrix (α×β) (α×β) ℂ) (hρ:ρ.PosSemidef) :
    (ptraceRight ρ).PosSemidef := by
  rw [ptraceRight_eq_sum]
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg (fun b hb=>(hρ.submatrix _).nonneg)

lemma ptraceLeft_posSemidef (ρ : Matrix (α×β) (α×β) ℂ) (hρ:ρ.PosSemidef) :
    (ptraceLeft ρ).PosSemidef := by
  rw [ptraceLeft_eq_sum]
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg (fun a ha=>(hρ.submatrix _).nonneg)

lemma trace_ptraceRight (ρ : Matrix (α×β) (α×β) ℂ) : (ptraceRight ρ).trace=ρ.trace := by
  change (∑ a,∑ b,ρ (a,b) (a,b))=(∑ x:α×β,ρ x x)
  rw [Fintype.sum_prod_type]

lemma trace_ptraceLeft (ρ : Matrix (α×β) (α×β) ℂ) : (ptraceLeft ρ).trace=ρ.trace := by
  change (∑ b,∑ a,ρ (a,b) (a,b))=(∑ x:α×β,ρ x x)
  rw [Fintype.sum_prod_type,Finset.sum_comm]

lemma rank_kraus_le {ι : Type} [Fintype ι] (K : ι→Matrix β α ℂ) (ρ : Matrix α α ℂ) :
    (∑ i,K i*ρ*(K i)ᴴ).rank ≤ Fintype.card ι*ρ.rank := by
  exact (matrix_rank_sum_le _ _).trans ((Finset.sum_le_sum (fun i hi=>
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _))).trans_eq (by simp [Nat.mul_comm]))

lemma DiscardDevice_slot_rank {n q g : ℕ} (D : DiscardDevice n q g) (j : Fin n)
    (ρ : Matrix (Bool×D.M) (Bool×D.M) ℂ) :
    (D.slot j ρ).rank ≤ Fintype.card (D.E j)*ρ.rank := by
  exact (rank_ptraceRight_le _).trans (Nat.mul_le_mul_left _
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)))

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetReferenceKraus -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped ComplexOrder MatrixOrder
variable {α β R : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype R] [DecidableEq R]

def referenceLift (K : Matrix β α ℂ) : Matrix (β×R) (α×R) ℂ :=
  fun x y=>if x.2=y.2 then K x.1 y.1 else 0

def referenceSlice (ρ : Matrix (α×R) (α×R) ℂ) (r s : R) : Matrix α α ℂ :=
  fun a a'=>ρ (a,r) (a',s)

lemma referenceLift_conjugation (K : Matrix β α ℂ) (ρ : Matrix (α×R) (α×R) ℂ) :
    referenceLift (R:=R) K*ρ*(referenceLift (R:=R) K)ᴴ=
      (fun x x'=>(K*referenceSlice ρ x.2 x'.2*Kᴴ) x.1 x'.1 : Matrix (β×R) (β×R) ℂ) := by
  ext x x'
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,referenceLift,Fintype.sum_prod_type,
    Finset.sum_mul,Finset.mul_sum,ite_mul,mul_ite,apply_ite,referenceSlice]

def slotKraus {n q g : ℕ} (D : DiscardDevice n q g) (j : Fin n) (e : D.E j) :
    Matrix (Bool×D.M) (Bool×D.M) ℂ :=
  (D.V j).submatrix (fun a=>(a,e)) id

lemma slot_eq_kraus {n q g : ℕ} (D : DiscardDevice n q g) (j : Fin n)
    (ρ : Matrix (Bool×D.M) (Bool×D.M) ℂ) :
    D.slot j ρ=∑e: D.E j,slotKraus D j e*ρ*(slotKraus D j e)ᴴ := by
  rw [DiscardDevice.slot,ptraceRight_eq_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    Matrix.submatrix_mul _ _ _ id _ Function.bijective_id]
  simp [slotKraus,Matrix.conjTranspose_submatrix]

def amplify (Φ : Matrix α α ℂ→Matrix β β ℂ) (ρ : Matrix (α×R) (α×R) ℂ) :
    Matrix (β×R) (β×R) ℂ :=
  fun x x'=>Φ (fun a a'=>ρ (a,x.2) (a',x'.2)) x.1 x'.1

lemma amplify_kraus {ι : Type} [Fintype ι] (Φ : Matrix α α ℂ→Matrix β β ℂ)
    (K : ι→Matrix β α ℂ) (hΦ:∀ρ,Φ ρ=∑i,K i*ρ*(K i)ᴴ)
    (ρ : Matrix (α×R) (α×R) ℂ) :
    amplify Φ ρ=∑i,referenceLift (R:=R) (K i)*ρ*(referenceLift (R:=R) (K i))ᴴ := by
  simp_rw [referenceLift_conjugation]
  ext x x'
  simp only [amplify,hΦ,Matrix.sum_apply]
  rfl

lemma rank_amplify_kraus {ι : Type} [Fintype ι] (Φ : Matrix α α ℂ→Matrix β β ℂ)
    (K : ι→Matrix β α ℂ) (hΦ:∀ρ,Φ ρ=∑i,K i*ρ*(K i)ᴴ)
    (ρ : Matrix (α×R) (α×R) ℂ) :
    (amplify Φ ρ).rank ≤ Fintype.card ι*ρ.rank := by
  rw [amplify_kraus Φ K hΦ ρ]
  exact rank_kraus_le _ _

lemma rank_amplify_conjugation (K : Matrix β α ℂ) (ρ : Matrix (α×R) (α×R) ℂ) :
    (amplify (fun A=>K*A*Kᴴ) ρ).rank ≤ ρ.rank := by
  have he:amplify (fun A=>K*A*Kᴴ) ρ=referenceLift (R:=R) K*ρ*(referenceLift (R:=R) K)ᴴ :=
    (referenceLift_conjugation K ρ).symm
  rw [he]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetDeviceRank -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped ComplexOrder MatrixOrder

variable {M R : Type} [Fintype M] [DecidableEq M] [Fintype R] [DecidableEq R]

def deviceReferenceEquiv (M R : Type) : (Bool×M×R) ≃ ((Bool×M)×R) :=
  (Equiv.prodAssoc Bool M R).symm

def testerReferenceEquiv (M R : Type) : (Bool×M×R) ≃ ((Bool×R)×M) where
  toFun x:=((x.1,x.2.2),x.2.1)
  invFun x:=(x.1.1,x.2,x.1.2)
  left_inv _:=rfl
  right_inv _:=rfl

lemma applyDevice_eq_amplify
    (Φ : Matrix (Bool×M) (Bool×M) ℂ→Matrix (Bool×M) (Bool×M) ℂ)
    (ρ : Matrix (Bool×M×R) (Bool×M×R) ℂ) :
    applyDevice Φ ρ=(amplify Φ (ρ.reindex (deviceReferenceEquiv M R) (deviceReferenceEquiv M R))).reindex
      (deviceReferenceEquiv M R).symm (deviceReferenceEquiv M R).symm := by
  rfl

lemma applyTester_eq_amplify
    (Φ : Matrix (Bool×R) (Bool×R) ℂ→Matrix (Bool×R) (Bool×R) ℂ)
    (ρ : Matrix (Bool×M×R) (Bool×M×R) ℂ) :
    applyTester Φ ρ=(amplify Φ (ρ.reindex (testerReferenceEquiv M R) (testerReferenceEquiv M R))).reindex
      (testerReferenceEquiv M R).symm (testerReferenceEquiv M R).symm := by
  rfl

lemma rank_applyDevice_slot {n q g : ℕ} (D : DiscardDevice n q g) (j : Fin n)
    {R : Type} [Fintype R] [DecidableEq R]
    (ρ : Matrix (Bool×D.M×R) (Bool×D.M×R) ℂ) :
    (applyDevice (D.slot j) ρ).rank ≤ Fintype.card (D.E j)*ρ.rank := by
  rw [applyDevice_eq_amplify,Matrix.rank_reindex]
  have hh:=rank_amplify_kraus (D.slot j) (slotKraus D j) (slot_eq_kraus D j)
    (ρ.reindex (deviceReferenceEquiv D.M R) (deviceReferenceEquiv D.M R))
  simpa only [Matrix.rank_reindex] using hh

lemma rank_applyTester_conjugation (K : Matrix (Bool×R) (Bool×R) ℂ)
    (ρ : Matrix (Bool×M×R) (Bool×M×R) ℂ) :
    (applyTester (fun A=>K*A*Kᴴ) ρ).rank ≤ ρ.rank := by
  rw [applyTester_eq_amplify,Matrix.rank_reindex]
  have hh:=rank_amplify_conjugation K
    (ρ.reindex (testerReferenceEquiv M R) (testerReferenceEquiv M R))
  simpa only [Matrix.rank_reindex] using hh

lemma rank_applyBlankTester {n : ℕ} (j : Fin n)
    (ρ : Matrix (Bool×M×(Fin n→Bool)) (Bool×M×(Fin n→Bool)) ℂ) :
    (applyTester ((blankTester n).T j) ρ).rank ≤ ρ.rank :=
  rank_applyTester_conjugation (swapIn j) ρ

def blankInitEmbed (n : ℕ) (M : Type) : Matrix (Bool×M×(Fin n→Bool)) M ℂ :=
  fun x m=>if x.1=false ∧ x.2.2=(fun _=>false) then (if x.2.1=m then 1 else 0) else 0

lemma jointState_blank_zero_factor {n : ℕ} (D : Process n) :
    jointState D (blankTester n) 0=blankInitEmbed n D.M*D.σ*(blankInitEmbed n D.M)ᴴ := by
  ext x x'
  by_cases h1:x.1=false <;> by_cases h2:x.2.2=(fun _=>false) <;>
    by_cases h3:x'.1=false <;> by_cases h4:x'.2.2=(fun _=>false)
  all_goals
    simp [jointState,blankTester,ketbra,blankInitEmbed,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Finset.sum_mul,Finset.mul_sum,ite_mul,mul_ite,apply_ite,h1,h2,h3,h4]
  all_goals split_ifs <;> simp_all

lemma jointState_blank_zero_rank {n : ℕ} (D : Process n) :
    (jointState D (blankTester n) 0).rank ≤ D.σ.rank := by
  rw [jointState_blank_zero_factor]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

def environmentPrefix {n q g : ℕ} (D : DiscardDevice n q g) (j : ℕ) : ℕ :=
  ∏ t∈Finset.univ.filter (fun t:Fin n=>t.val<j),Fintype.card (D.E t)

lemma environmentPrefix_zero {n q g : ℕ} (D : DiscardDevice n q g) : environmentPrefix D 0=1 := by
  simp [environmentPrefix]

lemma environmentPrefix_succ {n q g : ℕ} (D : DiscardDevice n q g) (j : ℕ) (hj:j<n) :
    environmentPrefix D (j+1)=Fintype.card (D.E ⟨j,hj⟩)*environmentPrefix D j := by
  have hs:Finset.univ.filter (fun t:Fin n=>t.val<j+1)=
      insert ⟨j,hj⟩ (Finset.univ.filter (fun t:Fin n=>t.val<j)) := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Fin.ext_iff]
    omega
  rw [environmentPrefix,hs,Finset.prod_insert]
  · rfl
  · simp

/-- Rank growth in the actual public blank-input interaction: each discarded
slot environment contributes only its own dimension. -/
theorem jointState_blank_rank {n q g : ℕ} (D : DiscardDevice n q g) (j : ℕ) (hj:j ≤ n) :
    (jointState D.toProcess (blankTester n) j).rank ≤ environmentPrefix D j*D.σ.rank := by
  induction j with
  | zero =>
    rw [environmentPrefix_zero,one_mul]
    convert jointState_blank_zero_rank D.toProcess using 1
    rfl
  | succ j ih =>
    have hjn:j<n := by omega
    rw [jointState,dif_pos hjn]
    change (applyTester ((blankTester n).T ⟨j,hjn⟩)
      (applyDevice (D.slot ⟨j,hjn⟩) (jointState D.toProcess (blankTester n) j))).rank ≤ _
    have hh:=rank_applyBlankTester ⟨j,hjn⟩
      (applyDevice (D.slot ⟨j,hjn⟩) (jointState D.toProcess (blankTester n) j))
    have hd:=rank_applyDevice_slot D ⟨j,hjn⟩ (jointState D.toProcess (blankTester n) j)
    have hi:=ih (by omega)
    rw [environmentPrefix_succ D j hjn]
    calc
      _ ≤ (applyDevice (D.slot ⟨j,hjn⟩) (jointState D.toProcess (blankTester n) j)).rank := hh
      _ ≤ Fintype.card (D.E ⟨j,hjn⟩)*(jointState D.toProcess (blankTester n) j).rank := hd
      _ ≤ Fintype.card (D.E ⟨j,hjn⟩)*(environmentPrefix D j*D.σ.rank) :=
        Nat.mul_le_mul_left _ hi
      _ = (Fintype.card (D.E ⟨j,hjn⟩)*environmentPrefix D j)*D.σ.rank :=
        (Nat.mul_assoc _ _ _).symm

lemma environmentPrefix_final {n q g : ℕ} (D : DiscardDevice n q g) :
    environmentPrefix D n=∏ t:Fin n,Fintype.card (D.E t) := by
  simp [environmentPrefix]

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetBlankSwap -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped ComplexOrder MatrixOrder

def swapBasis {n : ℕ} (j : Fin n) (x : Bool×(Fin n→Bool)) : Bool×(Fin n→Bool) :=
  (x.2 j,Function.update x.2 j x.1)

lemma swapBasis_involutive {n : ℕ} (j : Fin n) : Function.Involutive (swapBasis j) := by
  intro x
  apply Prod.ext
  · simp [swapBasis]
  · funext k
    by_cases hk:k=j <;> simp [swapBasis,hk]

def swapPerm {n : ℕ} (j : Fin n) : Equiv.Perm (Bool×(Fin n→Bool)) :=
  Function.Involutive.toPerm (swapBasis j) (swapBasis_involutive j)

lemma swapPerm_symm {n : ℕ} (j : Fin n) : (swapPerm j).symm=swapPerm j := by
  apply Equiv.ext
  intro x
  rfl

lemma swapIn_eq {n : ℕ} (j : Fin n) :
    swapIn j=(1:Matrix (Bool×(Fin n→Bool)) (Bool×(Fin n→Bool)) ℂ).submatrix id (swapPerm j) := by
  ext y x
  simp [swapIn,Matrix.one_apply,swapPerm,swapBasis,Function.Involutive.toPerm]

lemma swapIn_conjugation {n : ℕ} (j : Fin n)
    (ρ : Matrix (Bool×(Fin n→Bool)) (Bool×(Fin n→Bool)) ℂ) :
    swapIn j*ρ*(swapIn j)ᴴ=ρ.submatrix (swapPerm j) (swapPerm j) := by
  rw [swapIn_eq,Matrix.conjTranspose_submatrix,Matrix.conjTranspose_one,
    Matrix.one_submatrix_mul id (swapPerm j),Matrix.mul_submatrix_one (swapPerm j) id]
  simp only [swapPerm_symm,Matrix.submatrix_submatrix,Function.comp_id,Function.id_comp]

lemma applyBlankTester_apply {n : ℕ} {M : Type} [Fintype M] [DecidableEq M] (j : Fin n)
    (ρ : Matrix (Bool×M×(Fin n→Bool)) (Bool×M×(Fin n→Bool)) ℂ)
    (x x' : Bool×M×(Fin n→Bool)) :
    applyTester ((blankTester n).T j) ρ x x'=
      ρ (x.2.2 j,x.2.1,Function.update x.2.2 j x.1)
        (x'.2.2 j,x'.2.1,Function.update x'.2.2 j x'.1) := by
  let σ : Matrix (Bool×(Fin n→Bool)) (Bool×(Fin n→Bool)) ℂ :=
    fun a a'=>ρ (a.1,x.2.1,a.2) (a'.1,x'.2.1,a'.2)
  change (swapIn j*σ*
    (swapIn j)ᴴ) (x.1,x.2.2) (x'.1,x'.2.2)= _
  rw [swapIn_conjugation]
  rfl

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetBlankSupport -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped ComplexOrder MatrixOrder

lemma slot_zero {n q g : ℕ} (D : DiscardDevice n q g) (j : Fin n) : D.slot j 0=0 := by
  ext a b
  simp [DiscardDevice.slot,ptraceRight]

lemma applyDevice_zero_reference_row {M R : Type} [Fintype M] [DecidableEq M]
    [Fintype R] [DecidableEq R]
    (Φ : Matrix (Bool×M) (Bool×M) ℂ→Matrix (Bool×M) (Bool×M) ℂ)
    (hΦ:Φ 0=0) (ρ : Matrix (Bool×M×R) (Bool×M×R) ℂ) (r : R)
    (hr:∀ b m x',ρ (b,m,r) x'=0) (b : Bool) (m : M) (x' : Bool×M×R) :
    applyDevice Φ ρ (b,m,r) x'=0 := by
  have hs:(fun a a'=>ρ (a.1,a.2,r) (a'.1,a'.2,x'.2.2) : Matrix (Bool×M) (Bool×M) ℂ)=0 := by
    ext a a'
    exact hr a.1 a.2 _
  change Φ _ _ _=0
  rw [hs]
  exact congrFun (congrFun hΦ (b,m)) (x'.1,x'.2.1)

/-- The exact public blank tester returns its carrier to false, and leaves
all not-yet-used reference bits false. This prevents an extra carrier factor
in the final partial-trace rank bound. -/
theorem jointState_blank_fresh {n q g : ℕ} (D : DiscardDevice n q g) (t : ℕ) (ht:t ≤ n)
    (x x' : Bool×D.M×(Fin n→Bool))
    (hbad:x.1 ≠ false ∨ ∃ k : Fin n,t ≤ k.val ∧ x.2.2 k ≠ false) :
    jointState D.toProcess (blankTester n) t x x'=0 := by
  induction t generalizing x x' with
  | zero =>
    change (if (x.1,x.2.2)=(false,fun _=>false) ∧
      (x'.1,x'.2.2)=(false,fun _=>false) then (1:ℂ) else 0)*D.σ x.2.1 x'.2.1=0
    split_ifs with h
    · exfalso
      have hx:=Prod.mk.inj h.1
      rcases hbad with hc|⟨k,hk,hc⟩
      · exact hc hx.1
      · exact hc (congrFun hx.2 k)
    · simp
  | succ t ih =>
    have htn:t<n := by omega
    rw [jointState,dif_pos htn]
    change applyTester ((blankTester n).T ⟨t,htn⟩)
      (applyDevice (D.slot ⟨t,htn⟩) (jointState D.toProcess (blankTester n) t)) x x'=0
    rw [applyBlankTester_apply]
    apply applyDevice_zero_reference_row (D.slot ⟨t,htn⟩) (slot_zero D ⟨t,htn⟩)
    intro b m y'
    apply ih (by omega) (b,m,Function.update x.2.2 ⟨t,htn⟩ x.1) y'
    right
    rcases hbad with hc|⟨k,hk,hc⟩
    · exact ⟨⟨t,htn⟩,le_rfl,by simpa using hc⟩
    · have hne:k ≠ ⟨t,htn⟩ := fun he=>by have hh:k.val=t:=congrArg Fin.val he;omega
      exact ⟨k,by omega,by simpa [hne] using hc⟩

lemma emittedState_eq_sum {n q g : ℕ} (D : DiscardDevice n q g) :
    emittedState D.toProcess=∑m:D.M,
      (jointState D.toProcess (blankTester n) n).submatrix (fun a=>(false,m,a)) (fun a=>(false,m,a)) := by
  ext a a'
  have hz (m : D.M) : jointState D.toProcess (blankTester n) n (true,m,a) (true,m,a')=0 :=
    jointState_blank_fresh D n le_rfl _ _ (Or.inl (by simp))
  change (∑ b:Bool,∑m:D.M,jointState D.toProcess (blankTester n) n (b,m,a) (b,m,a'))= _
  simp [Matrix.sum_apply,hz]

/-- Actual output-rank upper bound for the public Definition-4 device and its
blank-input experiment, with the exact q+g exponent. -/
theorem emittedState_rank_upper {n q g : ℕ} (D : DiscardDevice n q g) :
    (emittedState D.toProcess).rank ≤ 2^(q+g)*D.σ.rank := by
  rw [emittedState_eq_sum]
  have h1:((∑m:D.M,(jointState D.toProcess (blankTester n) n).submatrix
      (fun a=>(false,m,a)) (fun a=>(false,m,a)))).rank ≤
        Fintype.card D.M*(jointState D.toProcess (blankTester n) n).rank :=
    (matrix_rank_sum_le _ _).trans ((Finset.sum_le_sum (fun m hm=>Matrix.rank_submatrix_le _ _ _)).trans_eq (by simp))
  have hj:=jointState_blank_rank D n le_rfl
  rw [environmentPrefix_final] at hj
  have h3:=Nat.mul_le_mul D.card_le D.discard_le
  have h4:=Nat.mul_le_mul_right D.σ.rank h3
  rw [← Nat.pow_add] at h4
  calc
    _ ≤ Fintype.card D.M*(jointState D.toProcess (blankTester n) n).rank := h1
    _ ≤ Fintype.card D.M*((∏t:Fin n,Fintype.card (D.E t))*D.σ.rank) :=
      Nat.mul_le_mul_left _ hj
    _ = (Fintype.card D.M*(∏t:Fin n,Fintype.card (D.E t)))*D.σ.rank :=
      (Nat.mul_assoc _ _ _).symm
    _ ≤ _ := h4

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetKrausDensity -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped ComplexOrder MatrixOrder
variable {α β γ R : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] [Fintype R] [DecidableEq R]

lemma referenceLift_one : referenceLift (R:=R) (1:Matrix α α ℂ)=1 := by
  ext x y
  by_cases h1:x.1=y.1 <;> by_cases h2:x.2=y.2 <;> simp [referenceLift,Matrix.one_apply,Prod.ext_iff,h1,h2]

lemma referenceLift_star (K : Matrix β α ℂ) :
    referenceLift (R:=R) Kᴴ=(referenceLift (R:=R) K)ᴴ := by
  ext x y
  by_cases h:x.2=y.2
  · simp [referenceLift,Matrix.conjTranspose_apply,h]
  · simp [referenceLift,Matrix.conjTranspose_apply,h,Ne.symm h]

lemma referenceLift_mul (A : Matrix γ β ℂ) (B : Matrix β α ℂ) :
    referenceLift (R:=R) (A*B)=referenceLift (R:=R) A*referenceLift (R:=R) B := by
  ext x y
  by_cases h:x.2=y.2
  · simp [referenceLift,Matrix.mul_apply,Fintype.sum_prod_type,ite_mul,mul_ite,h]
  · simp [referenceLift,Matrix.mul_apply,Fintype.sum_prod_type,ite_mul,mul_ite,h]

lemma referenceLift_sum {ι : Type} (S : Finset ι) (K : ι→Matrix β α ℂ) :
    referenceLift (R:=R) (∑i∈S,K i)=∑i∈S,referenceLift (R:=R) (K i) := by
  ext x y
  by_cases h:x.2=y.2 <;> simp [referenceLift,Matrix.sum_apply,h]

lemma referenceLift_complete {ι : Type} [Fintype ι] (K : ι→Matrix β α ℂ)
    (h:∑i,(K i)ᴴ*K i=1) :
    (∑i,(referenceLift (R:=R) (K i))ᴴ*referenceLift (R:=R) (K i))=1 := by
  simp_rw [← referenceLift_star,← referenceLift_mul]
  rw [← referenceLift_sum,h,referenceLift_one]

lemma kraus_density {ι : Type} [Fintype ι] (K : ι→Matrix β α ℂ)
    (hK:∑i,(K i)ᴴ*K i=1) (ρ : Matrix α α ℂ) (hρ:IsDensity ρ) :
    IsDensity (∑i,K i*ρ*(K i)ᴴ) := by
  constructor
  · apply Matrix.nonneg_iff_posSemidef.mp
    exact Finset.sum_nonneg (fun i hi=>(hρ.1.mul_mul_conjTranspose_same (K i)).nonneg)
  · calc
      _ = ∑i,((K i)ᴴ*K i*ρ).trace := by
        rw [Matrix.trace_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Matrix.trace_mul_cycle]
      _ = ((∑i,(K i)ᴴ*K i)*ρ).trace := by
        rw [Finset.sum_mul,Matrix.trace_sum]
      _ = 1 := by rw [hK,Matrix.one_mul,hρ.2]

lemma amplify_density {ι : Type} [Fintype ι] (Φ : Matrix α α ℂ→Matrix β β ℂ)
    (K : ι→Matrix β α ℂ) (hΦ:∀ρ,Φ ρ=∑i,K i*ρ*(K i)ᴴ) (hK:∑i,(K i)ᴴ*K i=1)
    (ρ : Matrix (α×R) (α×R) ℂ) (hρ:IsDensity ρ) : IsDensity (amplify Φ ρ) := by
  rw [amplify_kraus Φ K hΦ ρ]
  exact kraus_density _ (referenceLift_complete K hK) ρ hρ

lemma density_reindex (ρ : Matrix α α ℂ) (hρ:IsDensity ρ) (e : α≃β) :
    IsDensity (ρ.reindex e e) := by
  constructor
  · exact hρ.1.submatrix _
  · change (∑b,ρ (e.symm b) (e.symm b))=1
    calc
      _ = ∑a,ρ a a := Equiv.sum_comp e.symm (fun a=>ρ a a)
      _ = 1 := hρ.2

lemma slotKraus_complete {n q g : ℕ} (D : DiscardDevice n q g) (j : Fin n) :
    (∑ e : D.E j,(slotKraus D j e)ᴴ*slotKraus D j e)=1 := by
  rw [← D.isometry j]
  ext a b
  simp only [Matrix.sum_apply,Matrix.mul_apply,slotKraus,Matrix.conjTranspose_submatrix,
    Matrix.submatrix_apply,Matrix.conjTranspose_apply,id_eq]
  conv_rhs => rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetDeviceDensity -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped ComplexOrder MatrixOrder
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma conjugate_density (K : Matrix β α ℂ) (hK:Kᴴ*K=1)
    (ρ : Matrix α α ℂ) (hρ:IsDensity ρ) : IsDensity (K*ρ*Kᴴ) := by
  have hh:=kraus_density (fun _:Unit=>K) (by simpa using hK) ρ hρ
  simpa using hh

lemma ptraceRight_density (ρ : Matrix (α×β) (α×β) ℂ) (hρ:IsDensity ρ) :
    IsDensity (ptraceRight ρ) :=
  ⟨ptraceRight_posSemidef ρ hρ.1,(trace_ptraceRight ρ).trans hρ.2⟩

lemma ptraceLeft_density (ρ : Matrix (α×β) (α×β) ℂ) (hρ:IsDensity ρ) :
    IsDensity (ptraceLeft ρ) :=
  ⟨ptraceLeft_posSemidef ρ hρ.1,(trace_ptraceLeft ρ).trans hρ.2⟩

lemma applyDevice_slot_density {n q g : ℕ} (D : DiscardDevice n q g) (j : Fin n)
    {R : Type} [Fintype R] [DecidableEq R]
    (ρ : Matrix (Bool×D.M×R) (Bool×D.M×R) ℂ) (hρ:IsDensity ρ) :
    IsDensity (applyDevice (D.slot j) ρ) := by
  rw [applyDevice_eq_amplify]
  apply density_reindex
  apply amplify_density (D.slot j) (slotKraus D j) (slot_eq_kraus D j) (slotKraus_complete D j)
  exact density_reindex ρ hρ _

lemma amplify_conjugate_density {R : Type} [Fintype R] [DecidableEq R]
    (K : Matrix β α ℂ) (hK:Kᴴ*K=1)
    (ρ : Matrix (α×R) (α×R) ℂ) (hρ:IsDensity ρ) :
    IsDensity (amplify (fun A=>K*A*Kᴴ) ρ) := by
  apply amplify_density _ (fun _:Unit=>K)
  · intro A
    simp
  · simpa using hK
  · exact hρ

lemma applyTester_conjugate_density {M R : Type} [Fintype M] [DecidableEq M]
    [Fintype R] [DecidableEq R] (K : Matrix (Bool×R) (Bool×R) ℂ) (hK:Kᴴ*K=1)
    (ρ : Matrix (Bool×M×R) (Bool×M×R) ℂ) (hρ:IsDensity ρ) :
    IsDensity (applyTester (fun A=>K*A*Kᴴ) ρ) := by
  rw [applyTester_eq_amplify]
  apply density_reindex
  apply amplify_conjugate_density K hK
  exact density_reindex ρ hρ _

lemma swapIn_isometry {n : ℕ} (j : Fin n) : (swapIn j)ᴴ*swapIn j=1 := by
  rw [swapIn_eq,Matrix.conjTranspose_submatrix,Matrix.conjTranspose_one]
  calc
    (1:Matrix (Bool×(Fin n→Bool)) (Bool×(Fin n→Bool)) ℂ).submatrix (swapPerm j) id *
      (1:Matrix (Bool×(Fin n→Bool)) (Bool×(Fin n→Bool)) ℂ).submatrix id (swapPerm j) =
      ((1:Matrix (Bool×(Fin n→Bool)) (Bool×(Fin n→Bool)) ℂ)*1).submatrix
        (swapPerm j) (swapPerm j) := Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl _) _
    _ = 1 := by simp

lemma blankInitEmbed_complete (n : ℕ) (M : Type) [Fintype M] [DecidableEq M] :
    (blankInitEmbed n M)ᴴ*blankInitEmbed n M=1 := by
  ext m m'
  simp [blankInitEmbed,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
    ite_mul,mul_ite,apply_ite,Matrix.one_apply]
  all_goals split_ifs <;> aesop

lemma jointState_blank_zero_density {n q g : ℕ} (D : DiscardDevice n q g) :
    IsDensity (jointState D.toProcess (blankTester n) 0) := by
  rw [jointState_blank_zero_factor]
  exact conjugate_density _ (blankInitEmbed_complete n D.M) D.σ D.σ_density

theorem jointState_blank_density {n q g : ℕ} (D : DiscardDevice n q g) (t : ℕ) (ht:t ≤ n) :
    IsDensity (jointState D.toProcess (blankTester n) t) := by
  induction t with
  | zero => exact jointState_blank_zero_density D
  | succ t ih =>
    have htn:t<n := by omega
    rw [jointState,dif_pos htn]
    exact applyTester_conjugate_density (swapIn ⟨t,htn⟩) (swapIn_isometry _)
      (applyDevice (D.slot ⟨t,htn⟩) (jointState D.toProcess (blankTester n) t))
      (applyDevice_slot_density D ⟨t,htn⟩ _ (ih (by omega)))

lemma finalState_eq_ptraceRight {n : ℕ} (D : Process n) (T : Tester n) :
    finalState D T=ptraceRight ((jointState D T n).reindex
      (testerReferenceEquiv D.M T.R) (testerReferenceEquiv D.M T.R)) := by
  rfl

theorem emittedState_density {n q g : ℕ} (D : DiscardDevice n q g) :
    IsDensity (emittedState D.toProcess) := by
  apply ptraceLeft_density
  rw [finalState_eq_ptraceRight]
  apply ptraceRight_density
  exact density_reindex _ (jointState_blank_density D n le_rfl) _

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetRankRounding -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical

lemma power_two_rounding (a b : ℕ) (ε : ℝ) (hε:ε<1/2)
    (h:(1-ε)*(2:ℝ)^b ≤ (2:ℝ)^a) : b ≤ a := by
  by_contra hh
  have hab:a+1 ≤ b := by omega
  have hp:(2:ℝ)^(a+1) ≤ (2:ℝ)^b := pow_le_pow_right₀ (by norm_num) hab
  have hpos:0<(2:ℝ)^a := by positivity
  rw [pow_succ] at hp
  nlinarith

/-- The discrete consequences of the global rank inequality, with the
actual public device memory dimension and pure-initialization predicate. -/
theorem rank_benchmark_rounding {n q g : ℕ} (D : DiscardDevice n q g) (k : ℕ) (ε : ℝ)
    (hb:(1-ε)*(2:ℝ)^k ≤ (2:ℝ)^(q+g)*(D.σ.rank:ℝ)) :
    (ε<1/2 → k ≤ 2*q+g) ∧ (ε<1/2 → D.PureInit → k ≤ q+g) := by
  constructor
  · intro he
    apply power_two_rounding (2*q+g) k ε he
    have hr:D.σ.rank ≤ 2^q := (Matrix.rank_le_card_height D.σ).trans D.card_le
    have hrr:(D.σ.rank:ℝ) ≤ (2:ℝ)^q := by exact_mod_cast hr
    have hp:0 ≤ (2:ℝ)^(q+g) := by positivity
    have hh:=mul_le_mul_of_nonneg_left hrr hp
    have heq:(2:ℝ)^(q+g)*(2:ℝ)^q=(2:ℝ)^(2*q+g) := by
      rw [← pow_add]
      congr 1
      omega
    rw [heq] at hh
    exact hb.trans hh
  · intro he hPure
    change D.σ.rank=1 at hPure
    apply power_two_rounding (q+g) k ε he
    simpa [hPure] using hb

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetCodeContractRank -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical

/-- Lemma 6 in full for the code-state output contract; the phase-process
contract requires a separate pure-input tester and is not assumed here. -/
theorem lemma_6_codeState {k n : ℕ} (G : Matrix (Fin k) (Fin n) F2) (hG:FullRowRank G)
    (q g : ℕ) (D : DiscardDevice n q g) (ε : ℝ)
    (hD:ErrorLE G .codeState D.toProcess ε) :
    (2:ℝ)^(q+g)*(D.σ.rank:ℝ) ≥ (1-ε)*(2:ℝ)^k ∧
    (ε<1/2 → k ≤ 2*q+g) ∧ (ε<1/2 → D.PureInit → k ≤ q+g) := by
  have hl:=codeState_rank_benchmark G hG (emittedState D.toProcess) (emittedState_density D) ε hD
  simp only [Fintype.card_fin] at hl
  have hu:( (emittedState D.toProcess).rank:ℝ) ≤ (2:ℝ)^(q+g)*(D.σ.rank:ℝ) := by
    exact_mod_cast emittedState_rank_upper D
  have hb:=hl.trans hu
  exact ⟨hb,rank_benchmark_rounding D k ε hb⟩

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetConjugationTester -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped ComplexOrder MatrixOrder

abbrev TestBasis (n : ℕ) := Bool×(Fin n→Bool)

def blankInput (n : ℕ) : Matrix (TestBasis n) (TestBasis n) ℂ :=
  ketbra (false,fun _=>false)

def conjugationTester {n : ℕ} (I : Matrix (TestBasis n) (TestBasis n) ℂ)
    (K : Fin n→Matrix (TestBasis n) (TestBasis n) ℂ) : Tester n where
  R := Fin n→Bool
  τ := I*blankInput n*Iᴴ
  T := fun j A=>K j*A*(K j)ᴴ

lemma conjugationTester_zero {n : ℕ} (D : Process n)
    (I : Matrix (TestBasis n) (TestBasis n) ℂ)
    (K : Fin n→Matrix (TestBasis n) (TestBasis n) ℂ) :
    jointState D (conjugationTester I K) 0=
      applyTester (fun A : Matrix (TestBasis n) (TestBasis n) ℂ=>I*A*Iᴴ) (jointState D (blankTester n) 0) := by
  ext x x'
  let S : Matrix (TestBasis n) (TestBasis n) ℂ := fun a a'=>jointState D (blankTester n) 0
      (a.1,x.2.1,a.2) (a'.1,x'.2.1,a'.2)
  have hs:S=
      (D.σ x.2.1 x'.2.1) • blankInput n := by
    ext a a'
    simp [S,jointState,blankTester,blankInput,mul_comm]
  change (I*blankInput n*Iᴴ) (x.1,x.2.2) (x'.1,x'.2.2)*D.σ x.2.1 x'.2.1=
    (I*S*Iᴴ) (x.1,x.2.2) (x'.1,x'.2.2)
  rw [hs,Matrix.mul_smul,Matrix.smul_mul]
  simp [mul_comm]

lemma conjugationTester_zero_rank {n : ℕ} (D : Process n)
    (I : Matrix (TestBasis n) (TestBasis n) ℂ)
    (K : Fin n→Matrix (TestBasis n) (TestBasis n) ℂ) :
    (jointState D (conjugationTester I K) 0).rank ≤ D.σ.rank := by
  rw [conjugationTester_zero]
  exact (rank_applyTester_conjugation I _).trans (jointState_blank_zero_rank D)

lemma conjugationTester_zero_density {n q g : ℕ} (D : DiscardDevice n q g)
    (I : Matrix (TestBasis n) (TestBasis n) ℂ) (hI:Iᴴ*I=1)
    (K : Fin n→Matrix (TestBasis n) (TestBasis n) ℂ) :
    IsDensity (jointState D.toProcess (conjugationTester I K) 0) := by
  rw [conjugationTester_zero]
  exact applyTester_conjugate_density I hI _ (jointState_blank_zero_density D)

theorem jointState_conjugation_rank {n q g : ℕ} (D : DiscardDevice n q g)
    (I : Matrix (TestBasis n) (TestBasis n) ℂ)
    (K : Fin n→Matrix (TestBasis n) (TestBasis n) ℂ) (t : ℕ) (ht:t ≤ n) :
    (jointState D.toProcess (conjugationTester I K) t).rank ≤ environmentPrefix D t*D.σ.rank := by
  induction t with
  | zero =>
    rw [environmentPrefix_zero,one_mul]
    convert conjugationTester_zero_rank D.toProcess I K using 1
    rfl
  | succ t ih =>
    have htn:t<n := by omega
    rw [jointState,dif_pos htn,environmentPrefix_succ D t htn]
    have hi:=ih (by omega)
    calc
      _ ≤ (applyDevice (D.slot ⟨t,htn⟩) (jointState D.toProcess (conjugationTester I K) t)).rank :=
        rank_applyTester_conjugation (K ⟨t,htn⟩) _
      _ ≤ Fintype.card (D.E ⟨t,htn⟩)*(jointState D.toProcess (conjugationTester I K) t).rank :=
        rank_applyDevice_slot D ⟨t,htn⟩ _
      _ ≤ Fintype.card (D.E ⟨t,htn⟩)*(environmentPrefix D t*D.σ.rank) := Nat.mul_le_mul_left _ hi
      _ = _ := (Nat.mul_assoc _ _ _).symm

theorem jointState_conjugation_density {n q g : ℕ} (D : DiscardDevice n q g)
    (I : Matrix (TestBasis n) (TestBasis n) ℂ) (hI:Iᴴ*I=1)
    (K : Fin n→Matrix (TestBasis n) (TestBasis n) ℂ) (hK:∀j,(K j)ᴴ*K j=1)
    (t : ℕ) (ht:t ≤ n) : IsDensity (jointState D.toProcess (conjugationTester I K) t) := by
  induction t with
  | zero => exact conjugationTester_zero_density D I hI K
  | succ t ih =>
    have htn:t<n := by omega
    rw [jointState,dif_pos htn]
    exact applyTester_conjugate_density (K ⟨t,htn⟩) (hK ⟨t,htn⟩) _
      (applyDevice_slot_density D ⟨t,htn⟩ _ (ih (by omega)))

theorem finalState_conjugation_rank {n q g : ℕ} (D : DiscardDevice n q g)
    (I : Matrix (TestBasis n) (TestBasis n) ℂ)
    (K : Fin n→Matrix (TestBasis n) (TestBasis n) ℂ) :
    (finalState D.toProcess (conjugationTester I K)).rank ≤ 2^(q+g)*D.σ.rank := by
  rw [finalState_eq_ptraceRight]
  have hp:=rank_ptraceRight_le ((jointState D.toProcess (conjugationTester I K) n).reindex
    (testerReferenceEquiv D.M (Fin n→Bool)) (testerReferenceEquiv D.M (Fin n→Bool)))
  rw [Matrix.rank_reindex] at hp
  have hj:=jointState_conjugation_rank D I K n le_rfl
  rw [environmentPrefix_final] at hj
  have h3:=Nat.mul_le_mul_right D.σ.rank (Nat.mul_le_mul D.card_le D.discard_le)
  rw [← Nat.pow_add] at h3
  calc
    _ ≤ Fintype.card D.M*(jointState D.toProcess (conjugationTester I K) n).rank := hp
    _ ≤ Fintype.card D.M*((∏t:Fin n,Fintype.card (D.E t))*D.σ.rank) := Nat.mul_le_mul_left _ hj
    _ = (Fintype.card D.M*(∏t:Fin n,Fintype.card (D.E t)))*D.σ.rank := (Nat.mul_assoc _ _ _).symm
    _ ≤ _ := h3

theorem finalState_conjugation_density {n q g : ℕ} (D : DiscardDevice n q g)
    (I : Matrix (TestBasis n) (TestBasis n) ℂ) (hI:Iᴴ*I=1)
    (K : Fin n→Matrix (TestBasis n) (TestBasis n) ℂ) (hK:∀j,(K j)ᴴ*K j=1) :
    IsDensity (finalState D.toProcess (conjugationTester I K)) := by
  rw [finalState_eq_ptraceRight]
  apply ptraceRight_density
  exact density_reindex _ (jointState_conjugation_density D I hI K hK n le_rfl) _

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetPhaseTesterLocal -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped ComplexOrder MatrixOrder

/-- Gaussian-rational Hadamard, with harmless global phase exp(pi*i/4). -/
def phaseH : Matrix Bool Bool ℂ :=
  fun a b=>if a && b then -((1+Complex.I)/2) else (1+Complex.I)/2

lemma phaseH_isometry : phaseHᴴ*phaseH=1 := by
  ext a b
  cases a <;> cases b <;>
    norm_num [phaseH,Matrix.mul_apply,Fintype.sum_bool,Matrix.conjTranspose_apply,Matrix.one_apply,
      Complex.ext_iff,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]

lemma phaseH_coisometry : phaseH*phaseHᴴ=1 := by
  exact mul_eq_one_comm.mp phaseH_isometry

def phaseHRef (n : ℕ) : Matrix (TestBasis n) (TestBasis n) ℂ :=
  referenceLift (R:=Fin n→Bool) phaseH

lemma phaseHRef_isometry (n : ℕ) : (phaseHRef n)ᴴ*phaseHRef n=1 := by
  rw [phaseHRef,← referenceLift_star,← referenceLift_mul,phaseH_isometry,referenceLift_one]

lemma phaseHRef_coisometry (n : ℕ) : phaseHRef n*(phaseHRef n)ᴴ=1 :=
  mul_eq_one_comm.mp (phaseHRef_isometry n)

def phaseTesterGate {n : ℕ} (j : Fin n) : Matrix (TestBasis n) (TestBasis n) ℂ :=
  phaseHRef n*swapIn j*(phaseHRef n)ᴴ

lemma phaseTesterGate_isometry {n : ℕ} (j : Fin n) : (phaseTesterGate j)ᴴ*phaseTesterGate j=1 := by
  unfold phaseTesterGate
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((phaseHRef n)ᴴ) (phaseHRef n),phaseHRef_isometry]
  simp only [Matrix.one_mul]
  rw [← Matrix.mul_assoc (swapIn j)ᴴ (swapIn j),swapIn_isometry]
  simp [phaseHRef_coisometry]

def phaseCodeTester (n : ℕ) : Tester n := conjugationTester (phaseHRef n) phaseTesterGate

lemma phaseCodeTester_valid (n : ℕ) : (phaseCodeTester n).Valid := by
  change IsDensity (phaseHRef n*blankInput n*(phaseHRef n)ᴴ) ∧
    ∀ j : Fin n,IsChannel (fun A : Matrix (TestBasis n) (TestBasis n) ℂ=>phaseTesterGate j*A*(phaseTesterGate j)ᴴ)
  constructor
  · have hblank:IsDensity (blankInput n) := by
      have hp:(ketbra (false,fun _:Fin n=>false)).PosSemidef := by
        rw [ketbra_diagonal]
        exact Matrix.posSemidef_diagonal_iff.mpr (by intro x;split_ifs <;> norm_num)
      exact ⟨hp,by simp [blankInput,ketbra_diagonal,Matrix.trace_diagonal]⟩
    exact conjugate_density _ (phaseHRef_isometry n) _ hblank
  · intro j
    refine ⟨1,(fun _=>phaseTesterGate j),?_,?_⟩
    · simpa using phaseTesterGate_isometry j
    · intro A
      simp

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetPhaseBasis -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped ComplexOrder MatrixOrder

def phaseZ (b : Bool) : Matrix Bool Bool ℂ :=
  if b then Matrix.diagonal (fun a=>if a then -1 else 1) else 1

def phaseX (b : Bool) : Matrix Bool Bool ℂ :=
  fun a c=>if a=Bool.xor b c then 1 else 0

lemma phaseZ_hermitian (b : Bool) : (phaseZ b)ᴴ=phaseZ b := by
  ext a c
  cases b <;> cases a <;> cases c <;> norm_num [phaseZ,Matrix.conjTranspose_apply,Matrix.one_apply]

lemma phaseH_gauge (b : Bool) : phaseZ b*phaseH=phaseH*phaseX b := by
  ext a c
  cases b <;> cases a <;> cases c <;>
    norm_num [phaseZ,phaseX,phaseH,Matrix.mul_apply,Fintype.sum_bool,Matrix.one_apply]

def phaseZRef (n : ℕ) (b : Bool) : Matrix (TestBasis n) (TestBasis n) ℂ :=
  referenceLift (R:=Fin n→Bool) (phaseZ b)

def phaseXRef (n : ℕ) (b : Bool) : Matrix (TestBasis n) (TestBasis n) ℂ :=
  referenceLift (R:=Fin n→Bool) (phaseX b)

lemma phaseZRef_hermitian (n : ℕ) (b : Bool) : (phaseZRef n b)ᴴ=phaseZRef n b := by
  rw [phaseZRef,← referenceLift_star,phaseZ_hermitian]

lemma phaseHRef_gauge (n : ℕ) (b : Bool) : phaseZRef n b*phaseHRef n=phaseHRef n*phaseXRef n b := by
  simp only [phaseZRef,phaseHRef,phaseXRef,← referenceLift_mul,phaseH_gauge]

lemma phaseTesterGate_gauge {n : ℕ} (j : Fin n) (b : Bool) :
    phaseTesterGate j*phaseZRef n b*phaseHRef n=phaseHRef n*(swapIn j*phaseXRef n b) := by
  have hi:(phaseHRef n)ᴴ*(phaseZRef n b*phaseHRef n)=phaseXRef n b := by
    rw [phaseHRef_gauge,← Matrix.mul_assoc,phaseHRef_isometry,Matrix.one_mul]
  simp only [phaseTesterGate,Matrix.mul_assoc,hi]

lemma conjugate_ketbra_apply {α β : Type} [Fintype α] [DecidableEq α]
    (K : Matrix β α ℂ) (x : α) (a b : β) :
    (K*ketbra x*Kᴴ) a b=K a x*star (K b x) := by
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,ketbra,ite_mul,mul_ite,
    Finset.sum_mul,Finset.mul_sum,ite_and]

lemma conjugation_product {α β γ : Type} [Fintype α] [Fintype β]
    (A : Matrix γ β ℂ) (B : Matrix β α ℂ) (ρ : Matrix α α ℂ) :
    A*(B*ρ*Bᴴ)*Aᴴ=(A*B)*ρ*(A*B)ᴴ := by
  simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]

lemma phaseXRef_column (n : ℕ) (b : Bool) (x y : TestBasis n) :
    phaseXRef n b x y=if x=(Bool.xor b y.1,y.2) then 1 else 0 := by
  by_cases h1:x.1=Bool.xor b y.1 <;> by_cases h2:x.2=y.2 <;>
    simp [phaseXRef,referenceLift,phaseX,Prod.ext_iff,h1,h2]

lemma phaseXRef_ketbra (n : ℕ) (b : Bool) (x : TestBasis n) :
    phaseXRef n b*ketbra x*(phaseXRef n b)ᴴ=ketbra (Bool.xor b x.1,x.2) := by
  ext a c
  rw [conjugate_ketbra_apply,phaseXRef_column,phaseXRef_column]
  by_cases ha:a=(Bool.xor b x.1,x.2) <;> by_cases hc:c=(Bool.xor b x.1,x.2) <;>
    simp [ketbra,ha,hc,apply_ite]

lemma swapIn_ketbra {n : ℕ} (j : Fin n) (x : TestBasis n) :
    swapIn j*ketbra x*(swapIn j)ᴴ=ketbra (swapBasis j x) := by
  ext a c
  rw [conjugate_ketbra_apply]
  by_cases ha:a=(x.2 j,Function.update x.2 j x.1) <;>
    by_cases hc:c=(x.2 j,Function.update x.2 j x.1) <;>
    simp [swapIn,swapBasis,ketbra,ha,hc,apply_ite]

lemma basis_classical_step {n : ℕ} (j : Fin n) (b : Bool) (w : Fin n→Bool) (hw:w j=false) :
    (swapIn j*phaseXRef n b)*ketbra (false,w)*(swapIn j*phaseXRef n b)ᴴ=
      ketbra (false,Function.update w j b) := by
  rw [← conjugation_product,phaseXRef_ketbra,swapIn_ketbra]
  cases b <;> simp [swapBasis,hw]

lemma phase_basis_step {n : ℕ} (j : Fin n) (b : Bool) (w : Fin n→Bool) (hw:w j=false) :
    (phaseTesterGate j*phaseZRef n b)*(phaseHRef n*ketbra (false,w)*(phaseHRef n)ᴴ)*
      (phaseTesterGate j*phaseZRef n b)ᴴ=
    phaseHRef n*ketbra (false,Function.update w j b)*(phaseHRef n)ᴴ := by
  rw [conjugation_product,phaseTesterGate_gauge,← conjugation_product,basis_classical_step j b w hw]

def prefixWord {n : ℕ} (w : Fin n→Bool) (t : ℕ) : Fin n→Bool :=
  fun j=>if j.val<t then w j else false

lemma prefixWord_zero {n : ℕ} (w : Fin n→Bool) : prefixWord w 0=fun _=>false := by
  funext j
  simp [prefixWord]

lemma prefixWord_final {n : ℕ} (w : Fin n→Bool) : prefixWord w n=w := by
  funext j
  simp [prefixWord,j.isLt]

lemma prefixWord_current {n : ℕ} (w : Fin n→Bool) (t : ℕ) (ht:t<n) : prefixWord w t ⟨t,ht⟩=false := by
  simp [prefixWord]

lemma prefixWord_update {n : ℕ} (w : Fin n→Bool) (t : ℕ) (ht:t<n) :
    Function.update (prefixWord w t) ⟨t,ht⟩ (w ⟨t,ht⟩)=prefixWord w (t+1) := by
  funext j
  by_cases hj:j=⟨t,ht⟩
  · subst j
    simp [prefixWord]
  · have hjv:j.val ≠ t := fun h=>hj (Fin.ext h)
    simp only [Function.update_of_ne hj,prefixWord,Fin.val_mk]
    split_ifs <;> simp_all <;> omega

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetPhaseInteraction -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped ComplexOrder MatrixOrder

variable {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ}

lemma jointState_succ_eq {n : ℕ} (D : Process n) (T : Tester n) (t : ℕ) (ht:t<n) :
    jointState D T (t+1)=applyTester (T.T ⟨t,ht⟩) (applyDevice (D.Φ ⟨t,ht⟩) (jointState D T t)) := by
  rw [jointState,dif_pos ht]

def unitMemoryMatrix {R : Type} (ρ : Matrix (Bool×Unit×R) (Bool×Unit×R) ℂ) : Matrix (Bool×R) (Bool×R) ℂ :=
  fun x y=>ρ (x.1,(),x.2) (y.1,(),y.2)

lemma unitMemory_applyTester {R : Type} [Fintype R] [DecidableEq R]
    (Φ : Matrix (Bool×R) (Bool×R) ℂ→Matrix (Bool×R) (Bool×R) ℂ)
    (ρ : Matrix (Bool×Unit×R) (Bool×Unit×R) ℂ) :
    unitMemoryMatrix (applyTester Φ ρ)=Φ (unitMemoryMatrix ρ) := by rfl

lemma unitMemory_phase_slot (G : Matrix κ (Fin n) F2) (x : κ→F2) (j : Fin n)
    (ρ : Matrix (Bool×Unit×(Fin n→Bool)) (Bool×Unit×(Fin n→Bool)) ℂ) :
    unitMemoryMatrix (applyDevice ((phaseProcessAt G x).Φ j) ρ)=
      phaseZRef n (parityBit G x j)*unitMemoryMatrix ρ*(phaseZRef n (parityBit G x j))ᴴ := by
  cases h:parityBit G x j
  · simp only [phaseProcessAt,h,Bool.false_eq_true,if_false,phaseZRef,phaseZ,
      referenceLift_one,Matrix.one_mul,Matrix.conjTranspose_one,Matrix.mul_one]
    rfl
  · rw [phaseZRef,referenceLift_conjugation]
    ext a b
    rcases a with ⟨a,r⟩
    rcases b with ⟨b,s⟩
    cases a <;> cases b <;>
      simp [unitMemoryMatrix,applyDevice,phaseProcessAt,h,carrierZ,phaseZ,referenceSlice,
        Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,Matrix.diagonal_apply,Pi.star_apply]

def phaseJoint (G : Matrix κ (Fin n) F2) (x : κ→F2) (t : ℕ) : Matrix (TestBasis n) (TestBasis n) ℂ :=
  fun a b=>jointState (phaseProcessAt G x) (phaseCodeTester n) t (a.1,(),a.2) (b.1,(),b.2)

lemma phase_joint_zero (G : Matrix κ (Fin n) F2) (x : κ→F2) :
    phaseJoint G x 0=
      phaseHRef n*ketbra (false,fun _=>false)*(phaseHRef n)ᴴ := by
  ext a b
  simp [phaseJoint,unitMemoryMatrix,jointState,phaseProcessAt,phaseCodeTester,conjugationTester,blankInput]

lemma phase_joint_step (G : Matrix κ (Fin n) F2) (x : κ→F2) (t : ℕ) (ht:t<n) :
    phaseJoint G x (t+1)=
      (phaseTesterGate ⟨t,ht⟩*phaseZRef n (parityBit G x ⟨t,ht⟩))*
        phaseJoint G x t*
        (phaseTesterGate ⟨t,ht⟩*phaseZRef n (parityBit G x ⟨t,ht⟩))ᴴ := by
  let J : Matrix (Bool×Unit×(Fin n→Bool)) (Bool×Unit×(Fin n→Bool)) ℂ :=
    jointState (phaseProcessAt G x) (phaseCodeTester n) t
  let Φ : Matrix (Bool×Unit) (Bool×Unit) ℂ→Matrix (Bool×Unit) (Bool×Unit) ℂ :=
    (phaseProcessAt G x).Φ ⟨t,ht⟩
  let K : Matrix (TestBasis n) (TestBasis n) ℂ := phaseTesterGate ⟨t,ht⟩
  have hs:phaseJoint G x (t+1)=unitMemoryMatrix
      (applyTester (fun A : Matrix (TestBasis n) (TestBasis n) ℂ=>K*A*Kᴴ) (applyDevice Φ J)) := by
    ext a b
    change jointState (phaseProcessAt G x) (phaseCodeTester n) (t+1) (a.1,(),a.2) (b.1,(),b.2)= _
    rw [jointState_succ_eq _ _ t ht]
    rfl
  have hz:unitMemoryMatrix (applyDevice Φ J)=
      phaseZRef n (parityBit G x ⟨t,ht⟩)*unitMemoryMatrix J*(phaseZRef n (parityBit G x ⟨t,ht⟩))ᴴ :=
    unitMemory_phase_slot G x ⟨t,ht⟩ J
  have hJ:unitMemoryMatrix J=phaseJoint G x t := rfl
  rw [hs,unitMemory_applyTester,hz,hJ]
  exact conjugation_product _ _ _

/-- Exact evolution for each latent vector: the explicit valid tester stores
the decoded codeword, and resets the carrier to the same pure plus state. -/
theorem phase_joint_basis (G : Matrix κ (Fin n) F2) (x : κ→F2) (t : ℕ) (ht:t ≤ n) :
    phaseJoint G x t=
      phaseHRef n*ketbra (false,prefixWord (codeword G x) t)*(phaseHRef n)ᴴ := by
  induction t with
  | zero => rw [prefixWord_zero];exact phase_joint_zero G x
  | succ t ih =>
    have htn:t<n := by omega
    rw [phase_joint_step G x t htn,ih (by omega),
      phase_basis_step ⟨t,htn⟩ (parityBit G x ⟨t,htn⟩) _ (prefixWord_current _ t htn)]
    change phaseHRef n*ketbra (false,Function.update (prefixWord (codeword G x) t) ⟨t,htn⟩
      (codeword G x ⟨t,htn⟩))*(phaseHRef n)ᴴ= _
    rw [prefixWord_update]

lemma finalState_unitMemory {n : ℕ} (G : Matrix κ (Fin n) F2) (x : κ→F2) (T : Tester n) :
    finalState (phaseProcessAt G x) T=unitMemoryMatrix (jointState (phaseProcessAt G x) T n) := by
  ext a b
  simp [finalState,unitMemoryMatrix,phaseProcessAt]

theorem phase_final_basis (G : Matrix κ (Fin n) F2) (x : κ→F2) :
    finalState (phaseProcessAt G x) (phaseCodeTester n)=
      phaseHRef n*ketbra (false,codeword G x)*(phaseHRef n)ᴴ := by
  rw [finalState_unitMemory]
  change phaseJoint G x n= _
  rw [phase_joint_basis G x n le_rfl,prefixWord_final]

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetPhaseTarget -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped ComplexOrder MatrixOrder

variable {R : Type} [Fintype R] [DecidableEq R]

def pinCarrier (R : Type) : Matrix (Bool×R) R ℂ :=
  fun x y=>if x=(false,y) then 1 else 0

lemma pinCarrier_isometry : (pinCarrier R)ᴴ*pinCarrier R=1 := by
  ext r s
  by_cases h:r=s <;>
    simp [pinCarrier,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
      Prod.ext_iff,ite_mul,mul_ite,apply_ite,Matrix.one_apply,h]
  all_goals try split_ifs
  all_goals aesop

lemma pinCarrier_conjugation (ρ : Matrix R R ℂ) (x y : Bool×R) :
    (pinCarrier R*ρ*(pinCarrier R)ᴴ) x y=
      if x.1=false ∧ y.1=false then ρ x.2 y.2 else 0 := by
  rcases x with ⟨b,r⟩
  rcases y with ⟨c,s⟩
  cases b <;> cases c <;>
    simp [pinCarrier,Matrix.mul_apply,Matrix.conjTranspose_apply,Prod.ext_iff,
      ite_mul,mul_ite,apply_ite]

lemma pinCarrier_ketbra (x : R) :
    pinCarrier R*ketbra x*(pinCarrier R)ᴴ=ketbra (false,x) := by
  ext a b
  rw [pinCarrier_conjugation]
  by_cases h1:a.1=false <;> by_cases h2:b.1=false <;>
    simp [ketbra,Prod.ext_iff,h1,h2]

variable {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ}

def pinnedCodeProjector (G : Matrix κ (Fin n) F2) : Matrix (TestBasis n) (TestBasis n) ℂ :=
  pinCarrier (Fin n→Bool)*codeProjector G*(pinCarrier (Fin n→Bool))ᴴ

lemma pinnedCodeProjector_diagonal (G : Matrix κ (Fin n) F2) :
    pinnedCodeProjector G=Matrix.diagonal
      (fun x=>if x.1=false ∧ x.2∈Set.range (codeword G) then (1:ℂ) else 0) := by
  ext a b
  rw [pinnedCodeProjector,pinCarrier_conjugation]
  by_cases h1:a.1=false <;> by_cases h2:b.1=false <;> by_cases hr:a.2=b.2 <;>
    by_cases hm:a.2∈Set.range (codeword G) <;>
    simp_all [codeProjector,Matrix.diagonal_apply,Prod.ext_iff]

lemma pinnedCodeProjector_compl_posSemidef (G : Matrix κ (Fin n) F2) :
    (1-pinnedCodeProjector G).PosSemidef := by
  rw [pinnedCodeProjector_diagonal]
  have hd:(1:Matrix (TestBasis n) (TestBasis n) ℂ)-Matrix.diagonal
      (fun x=>if x.1=false ∧ x.2∈Set.range (codeword G) then (1:ℂ) else 0)=
      Matrix.diagonal (fun x=>if x.1=false ∧ x.2∈Set.range (codeword G) then (0:ℂ) else 1) := by
    ext a b
    by_cases hab:a=b <;> by_cases ha:a.1=false ∧ a.2∈Set.range (codeword G) <;> simp_all
    all_goals try split_ifs
    all_goals aesop
  rw [hd]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro x
  split_ifs <;> norm_num

def phaseCodeTarget (G : Matrix κ (Fin n) F2) : Matrix (TestBasis n) (TestBasis n) ℂ :=
  phaseHRef n*(pinCarrier (Fin n→Bool)*codeState G*(pinCarrier (Fin n→Bool))ᴴ)*(phaseHRef n)ᴴ

lemma phaseCodeTarget_density (G : Matrix κ (Fin n) F2) (hG:FullRowRank G) : IsDensity (phaseCodeTarget G) := by
  apply conjugate_density _ (phaseHRef_isometry n)
  exact conjugate_density _ pinCarrier_isometry _ (codeState_density G hG)

lemma phaseCodeTarget_flat (G : Matrix κ (Fin n) F2) (hG:FullRowRank G) :
    (1-((2^Fintype.card κ:ℕ):ℂ) • phaseCodeTarget G).PosSemidef := by
  have hs:((2^Fintype.card κ:ℕ):ℂ) • phaseCodeTarget G=
      phaseHRef n*pinnedCodeProjector G*(phaseHRef n)ᴴ := by
    rw [phaseCodeTarget,codeState_flat G hG]
    simp only [Matrix.mul_smul,Matrix.smul_mul,smul_smul,Nat.cast_pow,Nat.cast_ofNat]
    rw [mul_one_div_cancel (pow_ne_zero _ (by norm_num)),one_smul]
    rfl
  rw [hs]
  have hh:1-phaseHRef n*pinnedCodeProjector G*(phaseHRef n)ᴴ=
      phaseHRef n*(1-pinnedCodeProjector G)*(phaseHRef n)ᴴ := by
    rw [mul_sub,sub_mul,Matrix.mul_one,phaseHRef_coisometry]
  rw [hh]
  exact (pinnedCodeProjector_compl_posSemidef G).mul_mul_conjTranspose_same _

/-- The original public phase process, against the explicit valid tester,
has exactly the flat code-state target with a retained pure carrier. -/
theorem phaseFinal_eq_target (G : Matrix κ (Fin n) F2) :
    phaseFinal G (phaseCodeTester n)=phaseCodeTarget G := by
  unfold phaseFinal phaseCodeTarget codeState
  simp_rw [phase_final_basis,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,
    pinCarrier_ketbra]
  simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  rfl

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetGlobalRank -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical

lemma lemma_6_phaseProcess {k n : ℕ} (G : Matrix (Fin k) (Fin n) F2) (hG:FullRowRank G)
    (q g : ℕ) (D : DiscardDevice n q g) (ε : ℝ)
    (hD:ErrorLE G .phaseProcess D.toProcess ε) :
    (2:ℝ)^(q+g)*(D.σ.rank:ℝ) ≥ (1-ε)*(2:ℝ)^k ∧
    (ε<1/2 → k ≤ 2*q+g) ∧ (ε<1/2 → D.PureInit → k ≤ q+g) := by
  have he:=hD (phaseCodeTester n) (phaseCodeTester_valid n)
  rw [phaseFinal_eq_target] at he
  have hρ:IsDensity (finalState D.toProcess (phaseCodeTester n)) :=
    finalState_conjugation_density D (phaseHRef n) (phaseHRef_isometry n)
      phaseTesterGate phaseTesterGate_isometry
  have hl:=rank_ge_one_sub_distance_mul _ _ hρ (phaseCodeTarget_density G hG)
    (2^k) (by
      convert phaseCodeTarget_flat G hG using 1 <;> (try simp only [Fintype.card_fin]) <;> rfl)
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hl
  have hu:((finalState D.toProcess (phaseCodeTester n)).rank:ℝ) ≤
      (2:ℝ)^(q+g)*(D.σ.rank:ℝ) := by
    exact_mod_cast finalState_conjugation_rank D (phaseHRef n) phaseTesterGate
  have hb:(1-ε)*(2:ℝ)^k ≤ (2:ℝ)^(q+g)*(D.σ.rank:ℝ) := by
    have hp:0 ≤ (2:ℝ)^k := by positivity
    nlinarith
  exact ⟨hb,rank_benchmark_rounding D k ε hb⟩

/-- Exact public Lemma 6, covering both output contracts. -/
theorem lemma_6 {k n : ℕ} (G : Matrix (Fin k) (Fin n) F2) (hG : FullRowRank G)
    (q g : ℕ) (D : DiscardDevice n q g) (c : Contract) (ε : ℝ)
    (hD : ErrorLE G c D.toProcess ε) :
    (2 : ℝ) ^ (q + g) * (D.σ.rank : ℝ) ≥ (1 - ε) * (2 : ℝ) ^ k ∧
    (ε < 1 / 2 → k ≤ 2 * q + g) ∧
    (ε < 1 / 2 → D.PureInit → k ≤ q + g) := by
  cases c with
  | codeState => exact lemma_6_codeState G hG q g D ε hD
  | phaseProcess => exact lemma_6_phaseProcess G hG q g D ε hD

end SpaceReset.Hardness.QuantumRankProof

open SpaceReset.Hardness

theorem solution {k n : ℕ} (G : Matrix (Fin k) (Fin n) F2) (hG : FullRowRank G)
    (q g : ℕ) (D : DiscardDevice n q g) (c : Contract) (ε : ℝ)
    (hD : ErrorLE G c D.toProcess ε) :
    (2 : ℝ) ^ (q + g) * (D.σ.rank : ℝ) ≥ (1 - ε) * (2 : ℝ) ^ k ∧
    (ε < 1 / 2 → k ≤ 2 * q + g) ∧
    (ε < 1 / 2 → D.PureInit → k ≤ q + g) :=
  QuantumRankProof.lemma_6 G hG q g D c ε hD
