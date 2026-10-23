-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap50repair.P01.symplectic_polar_topology
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:19:56.444994+00:00
-- url     : https://prove2.me/submissions/ac12db06-5257-462f-a9a0-13268c9a0774

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Operator MatrixOrder

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

set_option backward.isDefEq.respectTransparency false

namespace X4T7

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

local notation "J" => canonicalJ n

lemma J_t : (canonicalJ n).transpose = -canonicalJ n := by
  unfold canonicalJ
  rw [Matrix.fromBlocks_transpose]
  simp [Matrix.fromBlocks_neg]

lemma J_sq : canonicalJ n * canonicalJ n = -1 := by
  unfold canonicalJ
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_neg, ← Matrix.fromBlocks_one]

lemma Jt_J : (canonicalJ n).transpose * canonicalJ n = 1 := by
  rw [J_t, Matrix.neg_mul, J_sq, neg_neg]

lemma J_Jt : canonicalJ n * (canonicalJ n).transpose = 1 := by
  rw [J_t, Matrix.mul_neg, J_sq, neg_neg]

lemma omega_eq : omegaMatrix n = -canonicalJ n := by
  unfold omegaMatrix canonicalJ
  simp [Matrix.fromBlocks_neg]

lemma inv_eq {A : GroupedRealMatrix n} (hA : IsSymplectic A) :
    -(canonicalJ n * A.transpose * canonicalJ n) * A = 1 := by
  unfold IsSymplectic at hA
  calc -(canonicalJ n * A.transpose * canonicalJ n) * A
      = -(canonicalJ n * (A.transpose * canonicalJ n * A)) := by simp only [Matrix.mul_assoc, Matrix.neg_mul]
    _ = 1 := by rw [hA, J_sq, neg_neg]

lemma symp_unit {A : GroupedRealMatrix n} (hA : IsSymplectic A) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse (inv_eq hA))

lemma symp_mul {A B : GroupedRealMatrix n} (hA : IsSymplectic A) (hB : IsSymplectic B) :
    IsSymplectic (A * B) := by
  unfold IsSymplectic at *
  rw [Matrix.transpose_mul]
  calc B.transpose * A.transpose * canonicalJ n * (A * B)
      = B.transpose * (A.transpose * canonicalJ n * A) * B := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hA, hB]

lemma symp_transpose {A : GroupedRealMatrix n} (hA : IsSymplectic A) :
    IsSymplectic A.transpose := by
  have h1 : A * -(canonicalJ n * A.transpose * canonicalJ n) = 1 :=
    mul_eq_one_comm.1 (inv_eq hA)
  unfold IsSymplectic
  rw [Matrix.transpose_transpose]
  have h2 : A * canonicalJ n * A.transpose * canonicalJ n = -1 := by
    rw [← neg_neg (A * canonicalJ n * A.transpose * canonicalJ n), ← h1]
    simp only [Matrix.mul_neg, Matrix.mul_assoc]
  calc A * canonicalJ n * A.transpose
      = A * canonicalJ n * A.transpose * canonicalJ n * (canonicalJ n).transpose := by
        rw [Matrix.mul_assoc (A * canonicalJ n * A.transpose), J_Jt, Matrix.mul_one]
    _ = canonicalJ n := by rw [h2, J_t]; simp

lemma symp_inv {A : GroupedRealMatrix n} (hA : IsSymplectic A) : IsSymplectic A⁻¹ := by
  have hu := symp_unit hA
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hu
  have ht := symp_transpose hA
  unfold IsSymplectic at *
  rw [Matrix.transpose_transpose] at ht
  calc A⁻¹.transpose * canonicalJ n * A⁻¹
      = A⁻¹.transpose * (A.transpose * canonicalJ n * A) * A⁻¹ := by rw [hA]
    _ = (A * A⁻¹).transpose * canonicalJ n * (A * A⁻¹) := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = canonicalJ n := by rw [Matrix.mul_nonsing_inv _ hd]; simp

lemma symp_one : IsSymplectic (1 : GroupedRealMatrix n) := by
  unfold IsSymplectic; simp

/-- conjugation by J -/
lemma exp_conjJ (T : GroupedRealMatrix n) :
    NormedSpace.exp ((canonicalJ n).transpose * T * canonicalJ n) =
      (canonicalJ n).transpose * NormedSpace.exp T * canonicalJ n := by
  have hu : IsUnit (canonicalJ n).transpose :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse J_Jt)
  have hi : ((canonicalJ n).transpose)⁻¹ = canonicalJ n := Matrix.inv_eq_right_inv Jt_J
  have := Matrix.exp_conj ((canonicalJ n).transpose) T hu
  rwa [hi] at this

lemma exp_mul_neg (T : GroupedRealMatrix n) :
    NormedSpace.exp (-T) * NormedSpace.exp T = 1 := by
  rw [← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl T)), neg_add_cancel,
    NormedSpace.exp_zero]

lemma exp_symm {T : GroupedRealMatrix n} (hT : T.transpose = T) :
    (NormedSpace.exp T).transpose = NormedSpace.exp T := by
  rw [← Matrix.exp_transpose, hT]

lemma exp_half (T : GroupedRealMatrix n) :
    NormedSpace.exp ((1/2 : ℝ) • T) * NormedSpace.exp ((1/2 : ℝ) • T) = NormedSpace.exp T := by
  rw [← NormedSpace.exp_add_of_commute (Commute.refl _), ← add_smul]
  norm_num

lemma exp_posDef {T : GroupedRealMatrix n} (hT : T.transpose = T) :
    (NormedSpace.exp T).PosDef := by
  have hsa : IsSelfAdjoint T := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, hT]
  have h0 : 0 ≤ NormedSpace.exp T := hsa.exp_nonneg
  exact (Matrix.LE.le.posSemidef h0).posDef_iff_isUnit.mpr (Matrix.isUnit_exp T)

lemma sa_of {T : GroupedRealMatrix n} (hT : T.transpose = T) : IsSelfAdjoint T := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, hT]

lemma exp_inj {S T : GroupedRealMatrix n} (hS : S.transpose = S) (hT : T.transpose = T)
    (h : NormedSpace.exp S = NormedSpace.exp T) : S = T := by
  rw [← CFC.log_exp S (sa_of hS), ← CFC.log_exp T (sa_of hT), h]

lemma lie_iff (S : GroupedRealMatrix n) :
    IsSymmetricLie S ↔ S.transpose = S ∧ S * canonicalJ n = -(canonicalJ n * S) := by
  unfold IsSymmetricLie
  rw [omega_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h1] at h2
    simp only [Matrix.mul_neg, Matrix.neg_mul] at h2
    rw [← sub_eq_zero, ← neg_eq_zero]
    rw [← h2]; abel
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    simp only [h1, Matrix.mul_neg, Matrix.neg_mul, h2]; abel

lemma conj_of_lie {S : GroupedRealMatrix n} (hS : S * canonicalJ n = -(canonicalJ n * S)) :
    (canonicalJ n).transpose * S * canonicalJ n = -S := by
  rw [Matrix.mul_assoc, hS, Matrix.mul_neg, ← Matrix.mul_assoc, Jt_J, Matrix.one_mul]

lemma exp_lie_symp {S : GroupedRealMatrix n} (hS : IsSymmetricLie S) :
    IsSymplectic (NormedSpace.exp S) := by
  rw [lie_iff] at hS
  obtain ⟨h1, h2⟩ := hS
  have hc := conj_of_lie h2
  have e := exp_conjJ S
  rw [hc] at e
  unfold IsSymplectic
  rw [exp_symm h1]
  calc NormedSpace.exp S * canonicalJ n * NormedSpace.exp S
      = canonicalJ n * ((canonicalJ n).transpose * NormedSpace.exp S * canonicalJ n) *
          NormedSpace.exp S := by
        simp only [← Matrix.mul_assoc, J_Jt, Matrix.one_mul]
    _ = canonicalJ n := by rw [← e, Matrix.mul_assoc, exp_mul_neg, Matrix.mul_one]

lemma lie_half {S : GroupedRealMatrix n} (hS : IsSymmetricLie S) : IsSymmetricLie ((1/2 : ℝ) • S) := by
  unfold IsSymmetricLie at *
  obtain ⟨h1, h2⟩ := hS
  refine ⟨by rw [Matrix.transpose_smul, h1], ?_⟩
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h2, smul_zero]

lemma lie_of_symp {S : GroupedRealMatrix n} (hS : S.transpose = S)
    (hM : IsSymplectic (NormedSpace.exp S)) : IsSymmetricLie S := by
  set M := NormedSpace.exp S with hMdef
  have hMt : M.transpose = M := exp_symm hS
  have hMJM : M * canonicalJ n * M = canonicalJ n := by
    have := hM; unfold IsSymplectic at this; rwa [hMt] at this
  have hinv : (canonicalJ n).transpose * M * canonicalJ n = NormedSpace.exp (-S) := by
    have h1 : (canonicalJ n).transpose * M * canonicalJ n * M = 1 := by
      calc (canonicalJ n).transpose * M * canonicalJ n * M
          = (canonicalJ n).transpose * (M * canonicalJ n * M) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hMJM, Jt_J]
    have h2 : NormedSpace.exp (-S) * M = 1 := exp_mul_neg S
    have hu : IsUnit M := Matrix.isUnit_exp S
    calc (canonicalJ n).transpose * M * canonicalJ n
        = (canonicalJ n).transpose * M * canonicalJ n * (M * M⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det M).mp hu), Matrix.mul_one]
      _ = M⁻¹ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
      _ = NormedSpace.exp (-S) * M * M⁻¹ := by rw [h2, Matrix.one_mul]
      _ = NormedSpace.exp (-S) := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det M).mp hu),
            Matrix.mul_one]
  rw [← exp_conjJ] at hinv
  have hsym : ((canonicalJ n).transpose * S * canonicalJ n).transpose =
      (canonicalJ n).transpose * S * canonicalJ n := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hS, Matrix.mul_assoc]
  have hnsym : (-S).transpose = -S := by rw [Matrix.transpose_neg, hS]
  have key := exp_inj hsym hnsym hinv
  rw [lie_iff]
  refine ⟨hS, ?_⟩
  calc S * canonicalJ n = canonicalJ n * ((canonicalJ n).transpose * S * canonicalJ n) := by
        simp only [← Matrix.mul_assoc, J_Jt, Matrix.one_mul]
    _ = -(canonicalJ n * S) := by rw [key, Matrix.mul_neg]

end X4T7

end

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Operator MatrixOrder

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

set_option backward.isDefEq.respectTransparency false

namespace X4T7

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

lemma ata_posDef {A : GroupedRealMatrix n} (hA : IsSymplectic A) : (A.transpose * A).PosDef := by
  have hinj : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr (symp_unit hA)
  have := Matrix.PosDef.conjTranspose_mul_self A hinj
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

lemma ata_symp {A : GroupedRealMatrix n} (hA : IsSymplectic A) : IsSymplectic (A.transpose * A) :=
  symp_mul (symp_transpose hA) hA

lemma sym_of_posDef {P : GroupedRealMatrix n} (hP : P.PosDef) : P.transpose = P := by
  have := hP.isHermitian
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- log of AᵀA -/
def logM (A : GroupedRealMatrix n) : GroupedRealMatrix n := CFC.log (A.transpose * A)

lemma exp_logM {A : GroupedRealMatrix n} (hA : IsSymplectic A) :
    NormedSpace.exp (logM A) = A.transpose * A :=
  CFC.exp_log _ (ata_posDef hA).isStrictlyPositive

lemma logM_symm (A : GroupedRealMatrix n) : (logM A).transpose = logM A := by
  have : IsSelfAdjoint (logM A) := IsSelfAdjoint.log
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact this

lemma logM_lie {A : GroupedRealMatrix n} (hA : IsSymplectic A) : IsSymmetricLie (logM A) := by
  apply lie_of_symp (logM_symm A)
  rw [exp_logM hA]; exact ata_symp hA

def P0 (A : GroupedRealMatrix n) : GroupedRealMatrix n := NormedSpace.exp ((1/2 : ℝ) • logM A)

lemma half_symm {S : GroupedRealMatrix n} (hS : S.transpose = S) :
    ((1/2 : ℝ) • S).transpose = (1/2 : ℝ) • S := by rw [Matrix.transpose_smul, hS]

lemma P0_props {A : GroupedRealMatrix n} (hA : IsSymplectic A) :
    (P0 A).transpose = P0 A ∧ (P0 A).PosDef ∧ IsSymplectic (P0 A) ∧
      P0 A * P0 A = A.transpose * A := by
  refine ⟨exp_symm (half_symm (logM_symm A)), exp_posDef (half_symm (logM_symm A)),
    exp_lie_symp (lie_half (logM_lie hA)), ?_⟩
  unfold P0; rw [exp_half, exp_logM hA]

lemma sqrt_uniq {A : GroupedRealMatrix n} (hA : IsSymplectic A) {P : GroupedRealMatrix n}
    (hP : P.PosDef) (hPP : P * P = A.transpose * A) : P = P0 A := by
  have h1 := (CFC.sqrt_eq_iff (A.transpose * A) P (ata_posDef hA).posSemidef.nonneg
    hP.posSemidef.nonneg).mpr hPP
  have h2 := (CFC.sqrt_eq_iff (A.transpose * A) (P0 A) (ata_posDef hA).posSemidef.nonneg
    (P0_props hA).2.1.posSemidef.nonneg).mpr (P0_props hA).2.2.2
  rw [← h1, h2]

def O0 (A : GroupedRealMatrix n) : GroupedRealMatrix n := A * (P0 A)⁻¹

lemma P0_unit (A : GroupedRealMatrix n) : IsUnit (P0 A).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)

lemma O0_props {A : GroupedRealMatrix n} (hA : IsSymplectic A) :
    A = O0 A * P0 A ∧ IsOrthogonal (O0 A) ∧ IsSymplectic (O0 A) := by
  obtain ⟨h1, h2, h3, h4⟩ := P0_props hA
  have hu := P0_unit A
  refine ⟨?_, ?_, symp_mul hA (symp_inv h3)⟩
  · unfold O0; rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  · unfold IsOrthogonal O0
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, h1]
    calc (P0 A)⁻¹ * A.transpose * (A * (P0 A)⁻¹) = (P0 A)⁻¹ * (A.transpose * A) * (P0 A)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [← h4, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
            Matrix.mul_nonsing_inv _ hu]

lemma polarP_eq {A : GroupedRealMatrix n} (hA : IsSymplectic A) : polarP A = P0 A := by
  obtain ⟨h1, h2, h3, h4⟩ := P0_props hA
  have hex : ∃ P : GroupedRealMatrix n, P.transpose = P ∧ P.PosDef ∧ P*P = A.transpose*A :=
    ⟨P0 A, h1, h2, h4⟩
  unfold polarP
  rw [dif_pos hex]
  obtain ⟨_, k2, k3⟩ := Classical.choose_spec hex
  exact sqrt_uniq hA k2 k3

theorem part12 (A : GroupedRealMatrix n) (hA : IsSymplectic A) :
    (∃! OP : GroupedRealMatrix n × GroupedRealMatrix n, A = OP.1*OP.2 ∧ IsOrthogonal OP.1 ∧
        IsSymplectic OP.1 ∧ OP.2.transpose = OP.2 ∧ OP.2.PosDef ∧ IsSymplectic OP.2 ∧
        OP.2*OP.2 = A.transpose*A) ∧
      (∃! S : GroupedRealMatrix n, IsSymmetricLie S ∧ NormedSpace.exp S = A.transpose*A ∧
        polarP A = NormedSpace.exp ((1/2 : ℝ) • S)) := by
  obtain ⟨h1, h2, h3, h4⟩ := P0_props hA
  obtain ⟨g1, g2, g3⟩ := O0_props hA
  constructor
  · refine ⟨(O0 A, P0 A), ⟨g1, g2, g3, h1, h2, h3, h4⟩, ?_⟩
    rintro ⟨O, P⟩ ⟨k1, -, -, -, k5, -, k7⟩
    have hP : P = P0 A := sqrt_uniq hA k5 k7
    subst hP
    have k1' : A = O * P0 A := k1
    have hO : O = O0 A := by
      unfold O0
      nth_rewrite 1 [k1']
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (P0_unit A), Matrix.mul_one]
    rw [hO]
  · refine ⟨logM A, ⟨logM_lie hA, exp_logM hA, polarP_eq hA⟩, ?_⟩
    rintro S ⟨k1, k2, -⟩
    exact exp_inj k1.1 (logM_symm A) (k2.trans (exp_logM hA).symm)

end X4T7

end

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Operator MatrixOrder

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

set_option backward.isDefEq.respectTransparency false

namespace X4T7

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

lemma sq_le_exp (x : ℝ) : x ^ 2 ≤ 2 * (Real.exp x + Real.exp (-x)) := by
  have h1 := Real.exp_pos x
  have h2 := Real.exp_pos (-x)
  rcases le_total 0 x with hx | hx
  · have := Real.quadratic_le_exp_of_nonneg hx
    nlinarith
  · have := Real.quadratic_le_exp_of_nonneg (neg_nonneg.mpr hx)
    nlinarith

lemma trace_conj (U X : GroupedRealMatrix n) (h : star U * U = 1) :
    (U * X * star U).trace = X.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul]

lemma trace_exp_diag (v : Coord n → ℝ) :
    (NormedSpace.exp (Matrix.diagonal v)).trace = ∑ i, Real.exp (v i) := by
  rw [Matrix.exp_diagonal, Matrix.trace_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.coe_exp, Real.exp_eq_exp_ℝ]

lemma spec_bound {S : GroupedRealMatrix n} (hS : S.transpose = S) (i j : Coord n) :
    S i j ^ 2 ≤ 2 * ((NormedSpace.exp S).trace + (NormedSpace.exp (-S)).trace) := by
  have hH : S.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hS]
  set U : GroupedRealMatrix n := (hH.eigenvectorUnitary : GroupedRealMatrix n) with hU
  set v := hH.eigenvalues with hv
  have e1 : S = U * Matrix.diagonal v * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa using this
  have h2 : star U * U = 1 := Unitary.coe_star_mul_self _
  have h3 : U * star U = 1 := Unitary.coe_mul_star_self _
  have hu : IsUnit U := (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse h2)
  have hinv : U⁻¹ = star U := Matrix.inv_eq_left_inv h2
  have eS : NormedSpace.exp S = U * NormedSpace.exp (Matrix.diagonal v) * star U := by
    rw [e1, ← hinv, Matrix.exp_conj U _ hu]
  have eN : NormedSpace.exp (-S) = U * NormedSpace.exp (Matrix.diagonal (-v)) * star U := by
    have : -S = U * Matrix.diagonal (-v) * star U := by
      have hd : Matrix.diagonal (-v) = -Matrix.diagonal v := by
        ext a b; simp [Matrix.diagonal_apply]; split_ifs <;> simp
      rw [e1, hd, Matrix.mul_neg, Matrix.neg_mul]
    rw [this, ← hinv, Matrix.exp_conj U _ hu]
  have tS : (NormedSpace.exp S).trace = ∑ k, Real.exp (v k) := by
    rw [eS, trace_conj _ _ h2, trace_exp_diag]
  have tN : (NormedSpace.exp (-S)).trace = ∑ k, Real.exp (-v k) := by
    rw [eN, trace_conj _ _ h2, trace_exp_diag]; rfl
  have tSS : (S * S).trace = ∑ k, v k ^ 2 := by
    have : S * S = U * (Matrix.diagonal v * Matrix.diagonal v) * star U := by
      rw [e1]
      calc U * Matrix.diagonal v * star U * (U * Matrix.diagonal v * star U)
          = U * Matrix.diagonal v * (star U * U) * Matrix.diagonal v * star U := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [this, trace_conj _ _ h2, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp [sq]
  have tSS' : (S * S).trace = ∑ k, ∑ l, S k l ^ 2 := by
    nth_rewrite 2 [← hS]
    simp [Matrix.trace, Matrix.mul_apply, sq]
  have b1 : S i j ^ 2 ≤ ∑ k, ∑ l, S k l ^ 2 := by
    calc S i j ^ 2 ≤ ∑ l, S i l ^ 2 :=
          Finset.single_le_sum (f := fun l => S i l ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ k, ∑ l, S k l ^ 2 :=
          Finset.single_le_sum (f := fun k => ∑ l, S k l ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  rw [tS, tN, ← tSS', tSS] at *
  calc S i j ^ 2 ≤ ∑ k, v k ^ 2 := by rw [← tSS', tSS] at b1; exact b1
    _ ≤ ∑ k, 2 * (Real.exp (v k) + Real.exp (-v k)) := Finset.sum_le_sum fun k _ => sq_le_exp _
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]

lemma trace_neg_lie {S : GroupedRealMatrix n} (hS : IsSymmetricLie S) :
    (NormedSpace.exp (-S)).trace = (NormedSpace.exp S).trace := by
  rw [lie_iff] at hS
  rw [← conj_of_lie hS.2, exp_conjJ, Matrix.trace_mul_comm, ← Matrix.mul_assoc, J_Jt, Matrix.one_mul]

lemma orth_entry {U : GroupedRealMatrix n} (hU : U.transpose * U = 1) (i j : Coord n) :
    |U i j| ≤ 1 := by
  have h1 : ∑ k, U k j * U k j = 1 := by
    have := congrFun (congrFun hU j) j
    simpa [Matrix.mul_apply] using this
  have : U i j * U i j ≤ 1 := by
    rw [← h1]
    exact Finset.single_le_sum (f := fun k => U k j * U k j) (fun _ _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  rw [abs_le]; constructor <;> nlinarith

lemma entry_bound {U S : GroupedRealMatrix n} (hU : U.transpose * U = 1) (hS : IsSymmetricLie S)
    (i j : Coord n) :
    |S i j| ≤ 4 * ((U * NormedSpace.exp ((1/2 : ℝ) • S)).transpose *
      (U * NormedSpace.exp ((1/2 : ℝ) • S))).trace + 1 := by
  have e : (U * NormedSpace.exp ((1/2 : ℝ) • S)).transpose * (U * NormedSpace.exp ((1/2 : ℝ) • S)) =
      NormedSpace.exp S := by
    rw [Matrix.transpose_mul, exp_symm (half_symm hS.1)]
    calc NormedSpace.exp ((1/2 : ℝ) • S) * U.transpose * (U * NormedSpace.exp ((1/2 : ℝ) • S))
        = NormedSpace.exp ((1/2 : ℝ) • S) * (U.transpose * U) * NormedSpace.exp ((1/2 : ℝ) • S) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one, exp_half]
  rw [e]
  have := spec_bound hS.1 i j
  rw [trace_neg_lie hS] at this
  have h0 : 0 ≤ S i j ^ 2 := sq_nonneg _
  rw [abs_le]; constructor <;> nlinarith [sq_abs (S i j), abs_nonneg (S i j)]

end X4T7

end

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

namespace X4CZB

lemma comm_iff {n : ℕ} (F B C D : Matrix (Fin n) (Fin n) ℝ) :
    CommutesWithComplexStructure (Matrix.fromBlocks F B C D) ↔ D = F ∧ C = -B := by
  unfold CommutesWithComplexStructure jMatrix omegaMatrix
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.zero_mul, Matrix.one_mul,
    Matrix.neg_mul, zero_add, add_zero]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h2.symm, by rw [← h1]⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨by simp, rfl, rfl, by simp⟩

lemma J_eq (n : ℕ) : canonicalJ n = jMatrix n := by
  unfold canonicalJ jMatrix omegaMatrix
  rw [Matrix.fromBlocks_neg]; simp

lemma orth_iff {n : ℕ} (F C : Matrix (Fin n) (Fin n) ℝ) :
    IsOrthogonal (Matrix.fromBlocks F (-C) C F) ↔ Fᵀ * F + Cᵀ * C = 1 ∧ Fᵀ * C = Cᵀ * F := by
  unfold IsOrthogonal
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one,
    Matrix.fromBlocks_inj]
  simp only [Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  constructor
  · rintro ⟨h1, h2, -, -⟩
    refine ⟨h1, ?_⟩
    have := h2; rw [add_comm, ← sub_eq_add_neg, sub_eq_zero] at this; exact this.symm
  · rintro ⟨h1, h2⟩
    refine ⟨h1, by rw [h2]; abel, by rw [h2]; abel, by rw [add_comm]; exact h1⟩

lemma cam_mul {n : ℕ} (F C : Matrix (Fin n) (Fin n) ℝ) :
    (complexActionMatrix (Matrix.fromBlocks F (-C) C F))ᴴ *
        complexActionMatrix (Matrix.fromBlocks F (-C) C F) =
      (Fᵀ * F + Cᵀ * C).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • (Fᵀ * C - Cᵀ * F).map (fun x : ℝ => (x : ℂ)) := by
  ext i j
  apply Complex.ext <;>
  simp [complexActionMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_re,
    Complex.mul_im, Finset.sum_add_distrib, Finset.sum_sub_distrib] <;> ring

lemma unit_iff {n : ℕ} (F C : Matrix (Fin n) (Fin n) ℝ) :
    (complexActionMatrix (Matrix.fromBlocks F (-C) C F))ᴴ *
        complexActionMatrix (Matrix.fromBlocks F (-C) C F) = 1 ↔
      Fᵀ * F + Cᵀ * C = 1 ∧ Fᵀ * C = Cᵀ * F := by
  rw [cam_mul]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · ext i j
      have := congrArg Complex.re (congrFun₂ h i j)
      simpa [Matrix.one_apply, apply_ite Complex.re] using this
    · rw [← sub_eq_zero]; ext i j
      have := congrArg Complex.im (congrFun₂ h i j)
      simpa [Matrix.one_apply, apply_ite Complex.im] using this
  · rintro ⟨h1, h2⟩
    rw [h1, h2, sub_self]
    ext i j
    simp [Matrix.one_apply, apply_ite]

theorem main {n : ℕ} (A : GroupedRealMatrix n) :
    IsUnitaryReal A ↔ IsOrthogonal A ∧ IsSymplectic A := by
  obtain ⟨F, B, C, D, rfl⟩ : ∃ F B C D, A = Matrix.fromBlocks F B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks A).symm⟩
  have key : ∀ A : GroupedRealMatrix n, IsOrthogonal A → CommutesWithComplexStructure A →
      IsSymplectic A := by
    intro A ho hc
    unfold IsSymplectic
    rw [J_eq, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ho, Matrix.one_mul]
  constructor
  · rintro ⟨hc, hu⟩
    have hc' := hc
    rw [comm_iff] at hc'
    obtain ⟨rfl, hC⟩ := hc'
    obtain rfl : B = -C := by rw [hC, neg_neg]
    have ho := (orth_iff _ C).2 ((unit_iff _ C).1 hu)
    exact ⟨ho, key _ ho hc⟩
  · rintro ⟨ho, hs⟩
    have hc : CommutesWithComplexStructure (Matrix.fromBlocks F B C D) := by
      unfold IsSymplectic at hs
      unfold IsOrthogonal at ho
      rw [J_eq] at hs
      have ho' : Matrix.fromBlocks F B C D * (Matrix.fromBlocks F B C D)ᵀ = 1 :=
        mul_eq_one_comm.1 ho
      unfold CommutesWithComplexStructure
      calc Matrix.fromBlocks F B C D * jMatrix n
          = Matrix.fromBlocks F B C D * ((Matrix.fromBlocks F B C D)ᵀ * jMatrix n *
              Matrix.fromBlocks F B C D) := by rw [hs]
        _ = (Matrix.fromBlocks F B C D * (Matrix.fromBlocks F B C D)ᵀ) * jMatrix n *
              Matrix.fromBlocks F B C D := by simp only [Matrix.mul_assoc]
        _ = jMatrix n * Matrix.fromBlocks F B C D := by rw [ho', Matrix.one_mul]
    refine ⟨hc, ?_⟩
    have hc' := hc
    rw [comm_iff] at hc'
    obtain ⟨rfl, hC⟩ := hc'
    obtain rfl : B = -C := by rw [hC, neg_neg]
    exact (unit_iff _ C).2 ((orth_iff _ C).1 ho)

end X4CZB

end

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Operator MatrixOrder

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

set_option backward.isDefEq.respectTransparency false

namespace X4T7

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

lemma closed_unitary : IsClosed {A : GroupedRealMatrix n | IsUnitaryReal A} := by
  have : {A : GroupedRealMatrix n | IsUnitaryReal A} =
      {A | A.transpose * A = 1} ∩ {A | A.transpose * canonicalJ n * A = canonicalJ n} := by
    ext A; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, X4CZB.main A]; rfl
  rw [this]
  refine IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_eq ?_ continuous_const)
  · exact continuous_id.matrix_transpose.matrix_mul continuous_id
  · exact (continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id

lemma closed_lie : IsClosed {S : GroupedRealMatrix n | IsSymmetricLie S} := by
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_transpose continuous_id)
    (isClosed_eq ?_ continuous_const)
  exact (continuous_id.matrix_transpose.matrix_mul continuous_const).add
    (continuous_const.matrix_mul continuous_id)

lemma symp_of_pair (x : UnitarySpace n × SymmetricLieSpace n) :
    IsSymplectic (x.1.val * NormedSpace.exp ((1/2 : ℝ) • x.2.val)) :=
  symp_mul ((X4CZB.main _).1 x.1.prop).2 (exp_lie_symp (lie_half x.2.prop))

def phi (x : UnitarySpace n × SymmetricLieSpace n) : SymplecticSpace n :=
  ⟨x.1.val * NormedSpace.exp ((1/2 : ℝ) • x.2.val), symp_of_pair x⟩

lemma phi_cont : Continuous (phi (n := n)) := by
  refine Continuous.subtype_mk ?_ _
  have h2 : Continuous (fun x : UnitarySpace n × SymmetricLieSpace n => (1/2 : ℝ) • x.2.val) :=
    (continuous_const_smul (1/2 : ℝ)).comp (continuous_subtype_val.comp continuous_snd)
  exact (continuous_subtype_val.comp continuous_fst).mul (NormedSpace.exp_continuous.comp h2)

lemma ata_phi (x : UnitarySpace n × SymmetricLieSpace n) :
    (phi x).val.transpose * (phi x).val = NormedSpace.exp x.2.val := by
  have hU : x.1.val.transpose * x.1.val = 1 := ((X4CZB.main _).1 x.1.prop).1
  have hS := x.2.prop
  show (x.1.val * NormedSpace.exp ((1/2 : ℝ) • x.2.val)).transpose *
    (x.1.val * NormedSpace.exp ((1/2 : ℝ) • x.2.val)) = _
  rw [Matrix.transpose_mul, exp_symm (half_symm hS.1)]
  calc NormedSpace.exp ((1/2 : ℝ) • x.2.val) * x.1.val.transpose *
        (x.1.val * NormedSpace.exp ((1/2 : ℝ) • x.2.val))
      = NormedSpace.exp ((1/2 : ℝ) • x.2.val) * (x.1.val.transpose * x.1.val) *
          NormedSpace.exp ((1/2 : ℝ) • x.2.val) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one, exp_half]

lemma phi_inj : Function.Injective (phi (n := n)) := by
  intro x y h
  have hS : x.2.val = y.2.val := by
    apply exp_inj x.2.prop.1 y.2.prop.1
    rw [← ata_phi, ← ata_phi, h]
  have hv : x.1.val * NormedSpace.exp ((1/2 : ℝ) • x.2.val) =
      y.1.val * NormedSpace.exp ((1/2 : ℝ) • y.2.val) := congrArg Subtype.val h
  rw [hS] at hv
  have hu : IsUnit (NormedSpace.exp ((1/2 : ℝ) • y.2.val)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)
  have hU : x.1.val = y.1.val := by
    have := congrArg (· * (NormedSpace.exp ((1/2 : ℝ) • y.2.val))⁻¹) hv
    simp only [Matrix.mul_assoc] at this
    rwa [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.mul_one] at this
  exact Prod.ext (Subtype.ext hU) (Subtype.ext hS)

lemma phi_surj : Function.Surjective (phi (n := n)) := by
  rintro ⟨A, hA⟩
  obtain ⟨g1, g2, g3⟩ := O0_props hA
  refine ⟨(⟨O0 A, (X4CZB.main _).2 ⟨g2, g3⟩⟩, ⟨logM A, logM_lie hA⟩), ?_⟩
  apply Subtype.ext
  show O0 A * P0 A = A
  exact g1.symm

lemma tr_cont : Continuous (fun A : GroupedRealMatrix n => (A.transpose * A).trace) :=
  (continuous_id.matrix_transpose.matrix_mul continuous_id).matrix_trace

lemma phi_proper : IsProperMap (phi (n := n)) := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨phi_cont, fun K hK => ?_⟩
  have hι : Topology.IsClosedEmbedding
      (Prod.map (Subtype.val : UnitarySpace n → GroupedRealMatrix n)
        (Subtype.val : SymmetricLieSpace n → GroupedRealMatrix n)) :=
    closed_unitary.isClosedEmbedding_subtypeVal.prodMap closed_lie.isClosedEmbedding_subtypeVal
  rw [hι.isInducing.isCompact_iff]
  have hcl : IsClosed (Prod.map (Subtype.val : UnitarySpace n → GroupedRealMatrix n)
        (Subtype.val : SymmetricLieSpace n → GroupedRealMatrix n) '' (phi ⁻¹' K)) :=
    hι.isClosedMap _ (hK.isClosed.preimage phi_cont)
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn
    (tr_cont.comp continuous_subtype_val).continuousOn
  set R' := 4 * R + 1
  have hbox : IsCompact ((Set.univ.pi fun _ : Coord n => Set.univ.pi fun _ : Coord n =>
      Set.Icc (-1 : ℝ) 1) ×ˢ (Set.univ.pi fun _ : Coord n => Set.univ.pi fun _ : Coord n =>
      Set.Icc (-R') R')) :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).prod
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc)
  have hc : Continuous (Prod.map (Matrix.of : (Coord n → Coord n → ℝ) → GroupedRealMatrix n)
      (Matrix.of : (Coord n → Coord n → ℝ) → GroupedRealMatrix n)) := continuous_id
  refine IsCompact.of_isClosed_subset (hbox.image hc) hcl ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨(Matrix.of.symm x.1.val, Matrix.of.symm x.2.val), ?_, rfl⟩
  have hU : x.1.val.transpose * x.1.val = 1 := ((X4CZB.main _).1 x.1.prop).1
  have hb := hR _ hx
  rw [Real.norm_eq_abs] at hb
  have hb' := (le_abs_self _).trans hb
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  refine ⟨fun i j => abs_le.mp (orth_entry hU i j), fun i j => abs_le.mp ?_⟩
  have := entry_bound hU x.2.prop i j
  have e : (phi x).val = x.1.val * NormedSpace.exp ((1/2 : ℝ) • x.2.val) := rfl
  simp only [Function.comp, e] at hb'
  show |x.2.val i j| ≤ R'
  linarith

theorem part3 :
    ∃ h : SymplecticSpace n ≃ₜ (UnitarySpace n × SymmetricLieSpace n),
      ∀ A, A.val = (h A).1.val*NormedSpace.exp ((1/2 : ℝ) • (h A).2.val) := by
  let e : UnitarySpace n × SymmetricLieSpace n ≃ SymplecticSpace n :=
    Equiv.ofBijective phi ⟨phi_inj, phi_surj⟩
  let H := e.toHomeomorphOfContinuousClosed phi_cont phi_proper.isClosedMap
  refine ⟨H.symm, fun A => ?_⟩
  have : phi (H.symm A) = A := H.apply_symm_apply A
  exact (congrArg Subtype.val this).symm

end X4T7

end

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

theorem solution {n : ℕ} (hn : 1 ≤ n) :
    (∀ A : GroupedRealMatrix n, IsSymplectic A →
      (∃! OP : GroupedRealMatrix n × GroupedRealMatrix n, A = OP.1*OP.2 ∧ IsOrthogonal OP.1 ∧ IsSymplectic OP.1 ∧
        OP.2.transpose = OP.2 ∧ OP.2.PosDef ∧ IsSymplectic OP.2 ∧ OP.2*OP.2 = A.transpose*A) ∧
      (∃! S : GroupedRealMatrix n, IsSymmetricLie S ∧ NormedSpace.exp S = A.transpose*A ∧
        polarP A = NormedSpace.exp ((1/2 : ℝ) • S))) ∧
    (∃ h : SymplecticSpace n ≃ₜ (UnitarySpace n × SymmetricLieSpace n),
      ∀ A, A.val = (h A).1.val*NormedSpace.exp ((1/2 : ℝ) • (h A).2.val)) :=
  ⟨fun A hA => X4T7.part12 A hA, X4T7.part3⟩

end
