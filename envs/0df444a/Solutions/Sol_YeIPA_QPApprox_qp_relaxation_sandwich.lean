-- Prove2me | solution 1 for YeIPA.QPApprox.qp_relaxation_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T22:33:16.921512+00:00
-- url     : https://prove2.me/submissions/c6e91e36-0f55-415d-8307-74a4accc4327

import Mathlib
import Definitions.Def_YeIPA_QPApprox_Relaxation
import Theorems.Thm_VBSDP_Duality_theorem_3_1

open Matrix

namespace QS98
open YeIPA.QPApprox

/-- block diagonal matrix -/
def bd {n : ℕ} (M W : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (n+n)) (Fin (n+n)) ℝ :=
  fun a b => Fin.addCases (fun i => Fin.addCases (fun j => M i j) (fun _ => (0:ℝ)) b)
    (fun i => Fin.addCases (fun _ => (0:ℝ)) (fun j => W i j) b) a

section
variable {n : ℕ} (M W : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
@[simp] lemma bd_ll : bd M W (Fin.castAdd n i) (Fin.castAdd n j) = M i j := by simp [bd]
lemma bd_lr : bd M W (Fin.castAdd n i) (Fin.natAdd n j) = 0 := by
  simp [bd, -Fin.natAdd_eq_addNat]
lemma bd_rl : bd M W (Fin.natAdd n i) (Fin.castAdd n j) = 0 := by
  simp [bd, -Fin.natAdd_eq_addNat]
lemma bd_rr : bd M W (Fin.natAdd n i) (Fin.natAdd n j) = W i j := by
  simp [bd, -Fin.natAdd_eq_addNat]
@[simp] lemma bd_lr' : bd M W (Fin.castAdd n i) (j.addNat n) = 0 := by
  rw [← Fin.natAdd_eq_addNat]; exact bd_lr M W i j
@[simp] lemma bd_rl' : bd M W (i.addNat n) (Fin.castAdd n j) = 0 := by
  rw [← Fin.natAdd_eq_addNat]; exact bd_rl M W i j
@[simp] lemma bd_rr' : bd M W (i.addNat n) (j.addNat n) = W i j := by
  rw [← Fin.natAdd_eq_addNat, ← Fin.natAdd_eq_addNat]; exact bd_rr M W i j
end

lemma bd_quad {n : ℕ} (M W : Matrix (Fin n) (Fin n) ℝ) (x : Fin (n+n) → ℝ) :
    x ⬝ᵥ (bd M W *ᵥ x) = (fun i => x (Fin.castAdd n i)) ⬝ᵥ (M *ᵥ fun i => x (Fin.castAdd n i))
      + (fun i => x (Fin.natAdd n i)) ⬝ᵥ (W *ᵥ fun i => x (Fin.natAdd n i)) := by
  simp [dotProduct, mulVec, Fin.sum_univ_add]

lemma bd_herm {n : ℕ} {M W : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (hW : W.IsHermitian) : (bd M W).IsHermitian := by
  have hM' : ∀ a b, M a b = M b a := fun a b => by simpa using (hM.apply b a)
  have hW' : ∀ a b, W a b = W b a := fun a b => by simpa using (hW.apply b a)
  ext a b
  induction a using Fin.addCases <;> induction b using Fin.addCases <;>
    simp [hM', hW', -Fin.natAdd_eq_addNat, bd_lr, bd_rl, bd_rr]

lemma bd_psd {n : ℕ} {M W : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef)
    (hW : W.PosSemidef) : (bd M W).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨bd_herm hM.isHermitian hW.isHermitian, fun x => ?_⟩
  simp only [star_trivial, bd_quad]
  have h1 := hM.dotProduct_mulVec_nonneg (fun i => x (Fin.castAdd n i))
  have h2 := hW.dotProduct_mulVec_nonneg (fun i => x (Fin.natAdd n i))
  simp only [star_trivial] at h1 h2
  linarith

lemma bd_posDef {n : ℕ} {M W : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (hW : W.PosDef) : (bd M W).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨bd_herm hM.isHermitian hW.isHermitian, fun x hx => ?_⟩
  simp only [star_trivial, bd_quad]
  have h1 := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => x (Fin.castAdd n i))
  have h2 := hW.posSemidef.dotProduct_mulVec_nonneg (fun i => x (Fin.natAdd n i))
  simp only [star_trivial] at h1 h2
  by_cases hu : (fun i => x (Fin.castAdd n i)) = 0
  · have hv : (fun i => x (Fin.natAdd n i)) ≠ 0 := by
      intro hv
      apply hx
      ext a
      induction a using Fin.addCases with
      | left i => exact congrFun hu i
      | right i => exact congrFun hv i
    have := hW.dotProduct_mulVec_pos hv
    simp only [star_trivial] at this
    linarith
  · have := hM.dotProduct_mulVec_pos hu
    simp only [star_trivial] at this
    linarith

lemma bd_psd_left {n : ℕ} {M W : Matrix (Fin n) (Fin n) ℝ} (h : (bd M W).PosSemidef) :
    M.PosSemidef := by
  have := h.submatrix (Fin.castAdd n)
  convert this using 1
  ext i j; simp

lemma bd_psd_right {n : ℕ} {M W : Matrix (Fin n) (Fin n) ℝ} (h : (bd M W).PosSemidef) :
    W.PosSemidef := by
  have := h.submatrix (Fin.natAdd n)
  convert this using 1
  ext i j; simp

lemma bd_trace {n : ℕ} (M W : Matrix (Fin n) (Fin n) ℝ) (Z : Matrix (Fin (n+n)) (Fin (n+n)) ℝ)
    (hZ : Z.IsHermitian) :
    (bd M W * Z).trace = frob M (Z.submatrix (Fin.castAdd n) (Fin.castAdd n))
      + frob W (Z.submatrix (Fin.natAdd n) (Fin.natAdd n)) := by
  have hs : ∀ a b, Z b a = Z a b := fun a b => by simpa using hZ.apply a b
  simp only [trace, diag, mul_apply, Fin.sum_univ_add, frob, Fin.natAdd_eq_addNat, bd_ll, bd_lr',
    bd_rl', bd_rr', zero_mul, Finset.sum_const_zero, add_zero, zero_add, submatrix_apply]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hs]

/-- the constraint matrices -/
noncomputable def Fs {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Fin (m+n) → Matrix (Fin (n+n)) (Fin (n+n)) ℝ :=
  Fin.append (fun i => bd (-constrMat A i) 0)
    (fun j => bd (-Matrix.diagonal (Pi.single j 1)) (-Matrix.diagonal (Pi.single j 1)))

/-- cost vector -/
def cv {m n : ℕ} (b : Fin m → ℝ) : Fin (m+n) → ℝ := Fin.append (-b) (fun _ => -1)

lemma lmi_eq {m n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin (m+n) → ℝ) :
    VBSDP.Duality.lmi (bd P 0) (Fs A) x =
      bd (P - (diagMat (fun j => x (Fin.natAdd m j)) +
        ∑ i, x (Fin.castAdd n i) • constrMat A i)) (-diagMat (fun j => x (Fin.natAdd m j))) := by
  ext a c
  induction a using Fin.addCases <;> induction c using Fin.addCases <;>
    simp [VBSDP.Duality.lmi, Fs, Fin.sum_univ_add, Matrix.sum_apply, diagMat, constrMat,
      diagonal_apply, Pi.single_apply, -Fin.natAdd_eq_addNat, bd_lr, bd_rl, bd_rr]
  split_ifs <;> ring

lemma cv_dot {m n : ℕ} (b : Fin m → ℝ) (x : Fin (m+n) → ℝ) :
    cv b ⬝ᵥ x = -dualObj b (fun i => x (Fin.castAdd n i)) (fun j => x (Fin.natAdd m j)) := by
  simp [cv, dualObj, dotProduct, Fin.sum_univ_add, -Fin.natAdd_eq_addNat]

lemma shift_posDef {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsHermitian) :
    (P - diagMat (fun _ => -(1 + ∑ i, ∑ j, |P i j|))).PosDef := by
  set S := ∑ i, ∑ j, |P i j| with hS
  have hmat : P - diagMat (fun _ => -(1 + S)) = P + (1 + S) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j; simp [diagMat, diagonal_apply, one_apply]; split_ifs <;> ring
  rw [hmat, posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun u hu => ?_⟩
  · rw [IsHermitian, conjTranspose_add, conjTranspose_smul, conjTranspose_one, hP.eq, star_trivial]
  simp only [star_trivial, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  have hsq : ∀ i, u i ^ 2 ≤ u ⬝ᵥ u := fun i => by
    simpa [dotProduct, sq] using Finset.single_le_sum (f := fun k => u k * u k)
      (fun k _ => mul_self_nonneg (u k)) (Finset.mem_univ i)
  have hterm : ∀ i j, -(|P i j| * (u ⬝ᵥ u)) ≤ u i * (P i j * u j) := by
    intro i j
    have h1 : |u i * u j| ≤ u ⬝ᵥ u := by
      rw [abs_mul]
      nlinarith [abs_nonneg (u i), abs_nonneg (u j), sq_abs (u i), sq_abs (u j), hsq i, hsq j,
        sq_nonneg (|u i| - |u j|)]
    have h2 : |u i * (P i j * u j)| = |P i j| * |u i * u j| := by
      simp only [abs_mul]; ring
    have h3 := neg_abs_le (u i * (P i j * u j))
    nlinarith [abs_nonneg (P i j)]
  have hq : -(S * (u ⬝ᵥ u)) ≤ u ⬝ᵥ (P *ᵥ u) := by
    have : u ⬝ᵥ (P *ᵥ u) = ∑ i, ∑ j, u i * (P i j * u j) := by
      simp [dotProduct, mulVec, Finset.mul_sum]
    rw [this, hS, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun j _ => hterm i j
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h; exact hu (funext fun k => by_contra fun hk => h ⟨k, hk⟩)
  have hpos : 0 < u ⬝ᵥ u := lt_of_lt_of_le (by positivity) (hsq i)
  nlinarith

lemma Fs_herm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : Fin (m+n)) : (Fs A k).IsHermitian := by
  induction k using Fin.addCases with
  | left i =>
    simp only [Fs, Fin.append_left]
    exact bd_herm (isHermitian_diagonal _).neg isHermitian_zero
  | right j =>
    simp only [Fs, Fin.append_right]
    exact bd_herm (isHermitian_diagonal _).neg (isHermitian_diagonal _).neg

lemma frob_neg {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℝ) : frob (-M) X = -frob M X := by
  simp [frob]

lemma frob_zero {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : frob 0 X = 0 := by
  simp [frob]

lemma frob_single {n : ℕ} (j : Fin n) (X : Matrix (Fin n) (Fin n) ℝ) :
    frob (diagonal (Pi.single j 1)) X = X j j := by
  simp [frob, diagonal_apply, Pi.single_apply]

lemma Fs_trace_l {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (Z : Matrix (Fin (n+n)) (Fin (n+n)) ℝ)
    (hZ : Z.IsHermitian) (i : Fin m) :
    (Fs A (Fin.castAdd n i) * Z).trace =
      -frob (constrMat A i) (Z.submatrix (Fin.castAdd n) (Fin.castAdd n)) := by
  simp only [Fs, Fin.append_left]
  rw [bd_trace _ _ _ hZ, frob_neg, frob_zero, add_zero]

lemma Fs_trace_r {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (Z : Matrix (Fin (n+n)) (Fin (n+n)) ℝ)
    (hZ : Z.IsHermitian) (j : Fin n) :
    (Fs A (Fin.natAdd m j) * Z).trace =
      -(Z (Fin.castAdd n j) (Fin.castAdd n j) + Z (Fin.natAdd n j) (Fin.natAdd n j)) := by
  simp only [Fs, Fin.append_right]
  rw [bd_trace _ _ _ hZ, frob_neg, frob_neg, frob_single, frob_single]
  simp only [submatrix_apply]
  ring

lemma bd_sub_l {n : ℕ} (M W : Matrix (Fin n) (Fin n) ℝ) :
    (bd M W).submatrix (Fin.castAdd n) (Fin.castAdd n) = M := by
  ext i j; simp

lemma bd_sub_r {n : ℕ} (M W : Matrix (Fin n) (Fin n) ℝ) :
    (bd M W).submatrix (Fin.natAdd n) (Fin.natAdd n) = W := by
  ext i j; simp

lemma neg_diagMat {n : ℕ} (d : Fin n → ℝ) : -diagMat d = diagonal (fun j => -d j) := by
  ext i j; by_cases h : i = j <;> simp [diagMat, h]

/-- Strong duality for the relaxation (9.48)/(9.49): the optimal value of any dual optimal pair
equals the primal minimum. -/
theorem dual_value {m n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hne : ∃ X, IsRelaxFeasible A b X)
    (hbdd : BddBelow (frob P '' {X | IsRelaxFeasible A b X}))
    (y : Fin m → ℝ) (z : Fin n → ℝ) (hyz : IsDualOptimal P A b y z) :
    sdpMin P A b = dualObj b y z := by
  classical
  obtain ⟨hfeas, hopt⟩ := hyz
  have hPh : P.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hP
  have hF0 : (bd P 0).IsHermitian := bd_herm hPh isHermitian_zero
  have key := (VBSDP.Duality.theorem_3_1 (cv (n := n) b) (bd P 0) (Fs A) hF0 (Fs_herm A)).1
    (Or.inl ⟨Fin.append 0 (fun _ => -(1 + ∑ i, ∑ j, |P i j|)), by
      rw [lmi_eq]
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, zero_smul,
        Finset.sum_const_zero, add_zero]
      refine bd_posDef (shift_posDef P hPh) ?_
      rw [neg_diagMat, posDef_diagonal_iff]
      intro i
      simp only [neg_neg]
      positivity⟩)
  have h1 : VBSDP.Duality.pStar (cv (n := n) b) (bd P 0) (Fs A) ≤ ((-dualObj b y z : ℝ) : EReal) := by
    apply sInf_le
    refine ⟨Fin.append y z, ?_, ?_⟩
    · show (VBSDP.Duality.lmi _ _ _).PosSemidef
      rw [lmi_eq]
      simp only [Fin.append_left, Fin.append_right]
      refine bd_psd hfeas.1 ?_
      rw [neg_diagMat, posSemidef_diagonal_iff]
      intro j
      simpa using hfeas.2 j
    · simp only [cv_dot, Fin.append_left, Fin.append_right]
  have h2 : ((-dualObj b y z : ℝ) : EReal) ≤ VBSDP.Duality.pStar (cv (n := n) b) (bd P 0) (Fs A) := by
    apply le_sInf
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (VBSDP.Duality.lmi (bd P 0) (Fs A) x).PosSemidef := hx
    rw [lmi_eq] at hx'
    rw [EReal.coe_le_coe_iff, cv_dot, neg_le_neg_iff]
    refine hopt _ _ ⟨bd_psd_left hx', fun j => ?_⟩
    have := (bd_psd_right hx').diag_nonneg (i := j)
    simpa [diagMat] using this
  have h3 : VBSDP.Duality.dStar (cv (n := n) b) (bd P 0) (Fs A) ≤ ((-sdpMin P A b : ℝ) : EReal) := by
    apply sSup_le
    rintro _ ⟨Z, hZ, rfl⟩
    obtain ⟨hZp, hZc⟩ := hZ
    have hZh := hZp.isHermitian
    have hX : IsRelaxFeasible A b (Z.submatrix (Fin.castAdd n) (Fin.castAdd n)) := by
      refine ⟨fun i => ?_, fun j => ?_, hZp.submatrix _⟩
      · have := hZc (Fin.castAdd n i)
        rw [Fs_trace_l A Z hZh] at this
        simpa [cv] using this
      · have := hZc (Fin.natAdd m j)
        rw [Fs_trace_r A Z hZh] at this
        have hw := (hZp.submatrix (Fin.natAdd n)).diag_nonneg (i := j)
        simp only [cv, Fin.append_right] at this
        simp only [diagVec, submatrix_apply] at hw ⊢
        linarith
    rw [EReal.coe_le_coe_iff, bd_trace _ _ _ hZh, frob_zero, add_zero, neg_le_neg_iff]
    exact csInf_le hbdd ⟨_, hX, rfl⟩
  have h4 : ∀ X, IsRelaxFeasible A b X →
      ((-frob P X : ℝ) : EReal) ≤ VBSDP.Duality.dStar (cv (n := n) b) (bd P 0) (Fs A) := by
    intro X hX
    obtain ⟨hXc, hXd, hXp⟩ := hX
    have hZp : (bd X (diagonal fun j => 1 - X j j)).PosSemidef := by
      refine bd_psd hXp ?_
      rw [posSemidef_diagonal_iff]
      intro j
      simpa [diagVec] using hXd j
    apply le_sSup
    refine ⟨bd X (diagonal fun j => 1 - X j j), ⟨hZp, fun k => ?_⟩, ?_⟩
    · induction k using Fin.addCases with
      | left i =>
        rw [Fs_trace_l A _ hZp.isHermitian, bd_sub_l, hXc]
        simp [cv]
      | right j =>
        rw [Fs_trace_r A _ hZp.isHermitian]
        simp [cv, -Fin.natAdd_eq_addNat, bd_rr]
    · simp only
      rw [bd_trace _ _ _ hZp.isHermitian, bd_sub_l, frob_zero, add_zero]
  apply le_antisymm
  · have h := h2.trans (key.trans_le h3)
    rw [EReal.coe_le_coe_iff] at h
    linarith
  · obtain ⟨X0, hX0⟩ := hne
    refine le_csInf ⟨frob P X0, X0, hX0, rfl⟩ ?_
    rintro _ ⟨X, hX, rfl⟩
    have h := (h4 X hX).trans (key.symm.trans_le h1)
    rw [EReal.coe_le_coe_iff] at h
    linarith

lemma attain {α : Type*} [TopologicalSpace α] {S : Set α} (hS : IsCompact S) (hne : S.Nonempty)
    {f : α → ℝ} (hf : Continuous f) :
    (∀ x ∈ S, sInf (f '' S) ≤ f x) ∧ ∃ x ∈ S, f x = sInf (f '' S) := by
  obtain ⟨x0, hx0, hmin⟩ := hS.exists_isMinOn hne hf.continuousOn
  have hl : IsLeast (f '' S) (f x0) :=
    ⟨⟨x0, hx0, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact hmin hx⟩
  rw [hl.csInf_eq]
  exact ⟨fun x hx => hmin hx, x0, hx0, rfl⟩

lemma quadForm_neg {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadForm (-Q) x = -quadForm Q x := by
  simp [quadForm, neg_mulVec]


lemma frob_vecMulVec {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    frob Q (vecMulVec x x) = quadForm Q x := by
  simp only [frob, quadForm, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma relax_of_qp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (hx : IsQPFeasible A b x) : IsRelaxFeasible A b (vecMulVec x x) := by
  refine ⟨fun i => ?_, fun j => ?_, ?_⟩
  · rw [← hx.1 i]
    simp only [frob, constrMat, diagonal_apply, vecMulVec_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun j _ => by ring
  · simp only [diagVec, vecMulVec_apply]
    have := hx.2 j; nlinarith
  · refine Matrix.posSemidef_iff_eq_sum_vecMulVec.2 ⟨1, fun _ => x, ?_⟩
    simp

lemma qp_compact {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    IsCompact {x | IsQPFeasible A b x} := by
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc (a := (-1 : ℝ)) (b := 1)))
    ?_ ?_
  · simp only [IsQPFeasible, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_eq (by fun_prop) (by fun_prop))
      (isClosed_iInter fun j => IsClosed.inter (isClosed_le (by fun_prop) (by fun_prop))
        (isClosed_le (by fun_prop) (by fun_prop)))
  · intro x hx
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_true_left]
    exact fun j => hx.2 j

lemma relax_abs_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : IsRelaxFeasible A b X) (i j : Fin n) :
    -1 ≤ X i j ∧ X i j ≤ 1 := by
  have hs : X j i = X i j := by simpa using hX.2.2.1.apply i j
  have key : ∀ s : ℝ, 0 ≤ X i i + s * X i j + s * X j i + s ^ 2 * X j j := by
    intro s
    have h := hX.2.2.dotProduct_mulVec_nonneg (Pi.single i 1 + s • Pi.single j 1)
    simp only [star_trivial, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
      smul_dotProduct, dotProduct_smul, mulVec_single_one, single_dotProduct,
      smul_eq_mul, one_mul] at h
    simp only [col_apply] at h
    nlinarith
  rw [hs] at key
  have k1 := key 1; have k2 := key (-1)
  have hi : X i i ≤ 1 := hX.2.1 i
  have hj : X j j ≤ 1 := hX.2.1 j
  constructor <;> nlinarith

lemma frob_cont {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Continuous (frob M) := by
  unfold frob; fun_prop

lemma diag_cont {n : ℕ} (j : Fin n) : Continuous fun X : Matrix (Fin n) (Fin n) ℝ => diagVec X j := by
  unfold diagVec; fun_prop

lemma relax_compact {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    IsCompact {X | IsRelaxFeasible A b X} := by
  have hK : IsCompact {X : Matrix (Fin n) (Fin n) ℝ | ∀ i j, X i j ∈ Set.Icc (-1 : ℝ) 1} := by
    have := isCompact_univ_pi (fun _ : Fin n =>
      isCompact_univ_pi (fun _ : Fin n => isCompact_Icc (a := (-1 : ℝ)) (b := 1)))
    have e : (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Set.Icc (-1 : ℝ) 1) =
        {X : Fin n → Fin n → ℝ | ∀ i j, X i j ∈ Set.Icc (-1 : ℝ) 1} := by
      ext X; simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
    rw [e] at this
    exact this
  refine IsCompact.of_isClosed_subset hK ?_ ?_
  · have hpsd : IsClosed {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} := by
      have : {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} =
          {X | Xᴴ = X} ∩ ⋂ v : Fin n → ℝ, {X | 0 ≤ star v ⬝ᵥ (X *ᵥ v)} := by
        ext X
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
        rw [posSemidef_iff_dotProduct_mulVec]; rfl
      rw [this]
      refine IsClosed.inter (isClosed_eq ?_ continuous_id) (isClosed_iInter fun v => ?_)
      · exact continuous_id.matrix_conjTranspose
      · refine isClosed_le continuous_const ?_
        simp only [dotProduct, mulVec]
        fun_prop
    simp only [IsRelaxFeasible, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_eq ?_ continuous_const)
      (IsClosed.inter (isClosed_iInter fun j => isClosed_le ?_ continuous_const) hpsd)
    · exact frob_cont _
    · exact diag_cont j
  · intro X hX i j
    exact relax_abs_le A b X hX i j

end QS98

open YeIPA.QPApprox in
theorem solution {m n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (hfeas : ∃ x, IsQPFeasible A b x) :
    -- (i)
    ((∀ x, IsQPFeasible A b x → quadForm Q x ≤ qpMax Q A b) ∧
      ∃ x, IsQPFeasible A b x ∧ quadForm Q x = qpMax Q A b) ∧
    -- (ii)
    ((∀ X, IsRelaxFeasible A b X → frob Q X ≤ sdpMax Q A b) ∧
      (∃ X, IsRelaxFeasible A b X ∧ frob Q X = sdpMax Q A b) ∧
      ∀ (y : Fin m → ℝ) (z : Fin n → ℝ), IsDualOptimal (-Q) A b y z →
        sdpMax Q A b = dualObj b (-y) (-z) ∧
        (diagMat (-z) + ∑ i, (-y) i • constrMat A i - Q).PosSemidef) ∧
    -- (iii)
    (sdpMin Q A b ≤ qpMin Q A b ∧ qpMin Q A b ≤ qpMax Q A b ∧ qpMax Q A b ≤ sdpMax Q A b) := by
  obtain ⟨x0, hx0⟩ := hfeas
  have hFc := QS98.qp_compact A b
  have hGc := QS98.relax_compact A b
  have hFne : Set.Nonempty {x | IsQPFeasible A b x} := ⟨x0, hx0⟩
  have hGne : Set.Nonempty {X | IsRelaxFeasible A b X} := ⟨_, QS98.relax_of_qp A b x0 hx0⟩
  have hqc : ∀ Q' : Matrix (Fin n) (Fin n) ℝ, Continuous (quadForm Q') := by
    intro Q'; unfold quadForm; simp only [dotProduct, mulVec]; fun_prop
  have hfc : ∀ Q' : Matrix (Fin n) (Fin n) ℝ, Continuous (frob Q') := by
    intro Q'; unfold frob; fun_prop
  obtain ⟨hFn1, xm, hxm, hxmv⟩ := QS98.attain hFc hFne (hqc (-Q))
  obtain ⟨hFp1, xp, hxp, hxpv⟩ := QS98.attain hFc hFne (hqc Q)
  obtain ⟨hGn1, Xm, hXm, hXmv⟩ := QS98.attain hGc hGne (hfc (-Q))
  obtain ⟨hGp1, Xp, hXp, hXpv⟩ := QS98.attain hGc hGne (hfc Q)
  -- unfold the definitions of the four values
  have eqMax : qpMax Q A b = -sInf (quadForm (-Q) '' {x | IsQPFeasible A b x}) := rfl
  have eqMin : qpMin Q A b = sInf (quadForm Q '' {x | IsQPFeasible A b x}) := rfl
  have esMax : sdpMax Q A b = -sInf (frob (-Q) '' {X | IsRelaxFeasible A b X}) := rfl
  have esMin : sdpMin Q A b = sInf (frob Q '' {X | IsRelaxFeasible A b X}) := rfl
  have i1 : ∀ x, IsQPFeasible A b x → quadForm Q x ≤ qpMax Q A b := by
    intro x hx; have := hFn1 x hx; rw [QS98.quadForm_neg] at this; rw [eqMax]; linarith
  have i2 : quadForm Q xm = qpMax Q A b := by
    rw [QS98.quadForm_neg] at hxmv; rw [eqMax]; linarith
  have ii1 : ∀ X, IsRelaxFeasible A b X → frob Q X ≤ sdpMax Q A b := by
    intro X hX; have := hGn1 X hX; rw [QS98.frob_neg] at this; rw [esMax]; linarith
  have ii2 : frob Q Xm = sdpMax Q A b := by
    rw [QS98.frob_neg] at hXmv; rw [esMax]; linarith
  refine ⟨⟨i1, xm, hxm, i2⟩, ⟨ii1, ⟨Xm, hXm, ii2⟩, fun y z hyz => ?_⟩, ?_, ?_, ?_⟩
  · have hsymm : (-Q).IsSymm := by
      unfold Matrix.IsSymm at hQ ⊢; rw [transpose_neg, hQ]
    have hbdd : BddBelow (frob (-Q) '' {X | IsRelaxFeasible A b X}) :=
      ⟨_, by rintro _ ⟨X, hX, rfl⟩; exact hGn1 X hX⟩
    have hd := QS98.dual_value (-Q) hsymm A b ⟨_, hXm⟩ hbdd y z hyz
    constructor
    · show -sdpMin (-Q) A b = _
      rw [hd]; simp only [dualObj, dotProduct_neg, Finset.sum_neg_distrib, Pi.neg_apply]
      ring
    · have h := hyz.1.1
      convert h using 1
      simp only [diagMat, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
      rw [show diagonal (-z) = -diagonal z from (diagonal_neg z).symm]
      abel
  · rw [eqMin, ← hxpv, ← QS98.frob_vecMulVec, esMin]
    exact hGp1 _ (QS98.relax_of_qp A b xp hxp)
  · rw [eqMin]; exact (hFp1 xm hxm).trans (i1 xm hxm)
  · rw [← i2, ← QS98.frob_vecMulVec]; exact ii1 _ (QS98.relax_of_qp A b xm hxm)
