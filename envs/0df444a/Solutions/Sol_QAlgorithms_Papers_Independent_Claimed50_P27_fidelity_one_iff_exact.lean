-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P27.fidelity_one_iff_exact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:37:06.477316+00:00
-- url     : https://prove2.me/submissions/f7e360a0-9a9e-475d-a4f5-8bafc3db4b3e

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P27

-- part Core

open scoped Matrix ComplexConjugate ComplexOrder

namespace X7P27Q

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped MatrixOrder in
lemma fac {A : Matrix n n ℂ} (hA : A.PosSemidef) : ∃ B : Matrix n n ℂ, A = Bᴴ * B := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨B, rfl⟩

lemma psd_trace_mul {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∃ X : Matrix n n ℂ, (A * B).trace = (Xᴴ * X).trace ∧ (X = 0 → A * B = 0) := by
  obtain ⟨C, rfl⟩ := fac hA
  obtain ⟨D, rfl⟩ := fac hB
  refine ⟨C * Dᴴ, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [show Cᴴ * C * (Dᴴ * D) = (Cᴴ * C * Dᴴ) * D by simp [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  · intro h
    rw [show Cᴴ * C * (Dᴴ * D) = Cᴴ * (C * Dᴴ) * D by simp [Matrix.mul_assoc], h]
    simp

/-- the squared norm as a real number -/
def ns (w : n → ℂ) : ℝ := ∑ x, Complex.normSq (w x)

lemma ns_nonneg (w : n → ℂ) : 0 ≤ ns w := Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _

lemma cs (w x : n → ℂ) : Complex.normSq (∑ i, star (w i) * x i) ≤ ns w * ns x := by
  let W : EuclideanSpace ℂ n := WithLp.toLp 2 w
  let X : EuclideanSpace ℂ n := WithLp.toLp 2 x
  have h := norm_inner_le_norm (𝕜 := ℂ) W X
  have hin : (inner ℂ W X : ℂ) = ∑ i, star (w i) * x i := by
    simp [W, X, PiLp.inner_apply, mul_comm]
  have hW : ‖W‖ ^ 2 = ns w := by
    rw [EuclideanSpace.norm_sq_eq]; simp [W, ns, Complex.sq_norm]
  have hX : ‖X‖ ^ 2 = ns x := by
    rw [EuclideanSpace.norm_sq_eq]; simp [X, ns, Complex.sq_norm]
  rw [hin] at h
  rw [← Complex.sq_norm, ← hW, ← hX, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

def Q (w : n → ℂ) : Matrix n n ℂ := ((ns w : ℝ) : ℂ) • (1 : Matrix n n ℂ) - Matrix.vecMulVec w (star w)

lemma Q_psd (w : n → ℂ) : (Q w).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · unfold Q
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    congr 1
    · simp
    · ext i j; simp [Matrix.vecMulVec_apply, mul_comm]
  · have hq : star x ⬝ᵥ (Q w *ᵥ x) = ((ns w * ns x : ℝ) : ℂ) -
        ((Complex.normSq (∑ i, star (w i) * x i) : ℝ) : ℂ) := by
      unfold Q ns
      have e1 : ∀ z : ℂ, ((Complex.normSq z : ℝ) : ℂ) = z * star z := fun z => by
        rw [RCLike.star_def, Complex.mul_conj]
      push_cast
      simp only [e1, star_sum, star_mul', star_star]
      simp only [dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib, mul_sub,
        Finset.mul_sum, Finset.sum_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    rw [hq]
    have := cs w x
    rw [sub_nonneg]
    exact_mod_cast this

def qf (C : Matrix n n ℂ) (w : n → ℂ) : ℂ := ∑ x, ∑ y, star (w x) * C x y * w y

lemma trCQ (C : Matrix n n ℂ) (w : n → ℂ) :
    (C * Q w).trace = ((ns w : ℝ) : ℂ) * C.trace - qf C w := by
  unfold Q qf
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma trCQ_nonneg {C : Matrix n n ℂ} (hC : C.PosSemidef) (w : n → ℂ) : 0 ≤ (C * Q w).trace := by
  obtain ⟨X, hX, -⟩ := psd_trace_mul hC (Q_psd w)
  rw [hX]
  exact (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg

lemma bound {C : Matrix n n ℂ} (hC : C.PosSemidef) (w : n → ℂ) :
    (qf C w).re ≤ ns w * C.trace.re := by
  have h := (Complex.nonneg_iff.mp (trCQ_nonneg hC w)).1
  rw [trCQ] at h
  simp at h
  linarith

lemma qf_nonneg {C : Matrix n n ℂ} (hC : C.PosSemidef) (w : n → ℂ) : 0 ≤ (qf C w).re := by
  have := hC.dotProduct_mulVec_nonneg w
  have e : star w ⬝ᵥ (C *ᵥ w) = qf C w := by
    simp only [qf, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e] at this
  exact (Complex.nonneg_iff.mp this).1

lemma eq_case {C : Matrix n n ℂ} (hC : C.PosSemidef) (w : n → ℂ) (hs : 0 < ns w)
    (htr : C.trace = ns w) (hq : qf C w = ((ns w : ℝ) : ℂ) ^ 2) : C = Matrix.vecMulVec w (star w) := by
  have h0 : (C * Q w).trace = 0 := by rw [trCQ, htr, hq]; ring
  obtain ⟨X, hX, hX0⟩ := psd_trace_mul hC (Q_psd w)
  have hCQ : C * Q w = 0 := by
    apply hX0
    rw [← Matrix.trace_conjTranspose_mul_self_eq_zero_iff, ← hX, h0]
  set s : ℂ := ((ns w : ℝ) : ℂ)
  have hs0 : s ≠ 0 := by simp [s]; exact hs.ne'
  set u : n → ℂ := fun x => ∑ y, C x y * w y
  -- s C x z = u x * star (w z)
  have h1 : ∀ x z, s * C x z = u x * star (w z) := by
    intro x z
    have := congrFun (congrFun hCQ x) z
    simp only [Q, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.zero_apply] at this
    simp only [u, Finset.sum_mul]
    rw [sub_eq_zero] at this
    rw [mul_comm, this]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have hH : ∀ x z, C x z = star (C z x) := by
    intro x z
    have := congrFun (congrFun hC.1 x) z
    rw [Matrix.conjTranspose_apply] at this
    exact this.symm
  have hsr : star s = s := by simp [s]
  have h2 : ∀ x z, u x * star (w z) = w x * star (u z) := by
    intro x z
    rw [← h1 x z, hH x z, ← hsr, ← star_mul', h1 z x, star_mul', star_star, mul_comm]
  have hqu : ∑ z, star (u z) * w z = s ^ 2 := by
    have : star (qf C w) = ∑ z, star (u z) * w z := by
      simp only [qf, u, star_sum, star_mul', star_star, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [← this, hq, star_pow, hsr]
  have h3 : ∀ x, u x = s * w x := by
    intro x
    have : ∑ z, u x * star (w z) * w z = ∑ z, w x * star (u z) * w z :=
      Finset.sum_congr rfl fun z _ => by rw [h2]
    simp only [mul_assoc, ← Finset.mul_sum, hqu] at this
    have hn : ∑ z, star (w z) * w z = s := by
      simp only [s, ns]; push_cast
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [RCLike.star_def, mul_comm, Complex.mul_conj]
    rw [hn] at this
    apply mul_left_cancel₀ hs0
    rw [mul_comm s (u x), this]; ring
  ext x z
  rw [Matrix.vecMulVec_apply]
  apply mul_left_cancel₀ hs0
  rw [h1, h3]; simp; ring

end X7P27Q

-- part S

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

def X7Q_w {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) : PairReg d × PairReg d → ℂ :=
  fun x => Matrix.kronecker U.val U.val x.2 x.1

lemma X7Q_single_entry {m n p q : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix p q ℂ) (a : n) (b : p) (k : m) (l : q) :
    (A * Matrix.single a b (1:ℂ) * B) k l = A k a * B b l := by
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_mul]
  simp [ite_and]

lemma X7Q_J {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    channelChoi (targetChannel U) = Matrix.vecMulVec (X7Q_w U) (star (X7Q_w U)) := by
  ext x y
  simp only [channelChoi, targetChannel, conjSuperop, X7Q_single_entry, Matrix.vecMulVec_apply, X7Q_w,
    Pi.star_apply, Matrix.conjTranspose_apply]

lemma X7Q_trace_CJ {d : ℕ} (C : Matrix (PairReg d × PairReg d) (PairReg d × PairReg d) ℂ)
    (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    (C * channelChoi (targetChannel U)).trace = X7P27Q.qf C (X7Q_w U) := by
  rw [X7Q_J]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, X7P27Q.qf, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma X7Q_ns {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) : X7P27Q.ns (X7Q_w U) = (d : ℝ) ^ 2 := by
  have hk : ∀ A B C D : Matrix (Fin d) (Fin d) ℂ,
      Matrix.kronecker A B * Matrix.kronecker C D = Matrix.kronecker (A * C) (B * D) :=
    fun A B C D => (Matrix.mul_kronecker_mul A C B D).symm
  have hW : (Matrix.kronecker U.val U.val)ᴴ * Matrix.kronecker U.val U.val = 1 := by
    rw [show (Matrix.kronecker U.val U.val)ᴴ = Matrix.kronecker U.valᴴ U.valᴴ from
      Matrix.conjTranspose_kronecker _ _, hk]
    have := U.2; rw [Matrix.mem_unitaryGroup_iff'] at this
    rw [show U.valᴴ * U.val = 1 from this]
    exact Matrix.one_kronecker_one
  have ht := congrArg Matrix.trace hW
  rw [Matrix.trace_one, Fintype.card_prod, Fintype.card_fin] at ht
  have : ((X7P27Q.ns (X7Q_w U) : ℝ) : ℂ) = ((d : ℝ) ^ 2 : ℝ) := by
    have e1 : ∀ z : ℂ, ((Complex.normSq z : ℝ) : ℂ) = star z * z := fun z => by
      rw [RCLike.star_def, mul_comm, Complex.mul_conj]
    simp only [X7P27Q.ns, X7Q_w]
    push_cast
    simp only [e1]
    rw [show ((d:ℂ))^2 = ((d * d : ℕ) : ℂ) by push_cast; ring, ← ht]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  exact_mod_cast this

lemma X7Q_front3 {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (g : α → β → γ → M) : ∑ a, ∑ b, ∑ c, g a b c = ∑ c, ∑ a, ∑ b, g a b c := by
  calc ∑ a, ∑ b, ∑ c, g a b c = ∑ a, ∑ c, ∑ b, g a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

def X7Q_V {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) : Matrix (CombReg d) (PairReg d × PairReg d) ℂ :=
  fun x a => if x.1 = a.1 ∧ x.2.2.2 = a.2 then conj (U.val x.2.2.1 x.2.1) else 0

lemma X7Q_sumV {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) (g : CombReg d → ℂ) (b : PairReg d × PairReg d) :
    ∑ x, g x * X7Q_V U x b = ∑ j, ∑ l, g (b.1, (j, (l, b.2))) * conj (U.val l j) := by
  rw [Fintype.sum_prod_type (fun x : CombReg d => g x * X7Q_V U x b)]
  rw [Finset.sum_eq_single b.1]
  · rw [Fintype.sum_prod_type (fun x : Fin d × (Fin d × PairReg d) => g (b.1, x) * X7Q_V U (b.1, x) b)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_prod_type (fun x : Fin d × PairReg d => g (b.1, (j, x)) * X7Q_V U (b.1, (j, x)) b)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_eq_single b.2]
    · simp [X7Q_V]
    · intro c _ hc; simp [X7Q_V, hc]
    · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [X7Q_V, hc]
  · simp

lemma X7Q_sumV' {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) (g : CombReg d → ℂ) (a : PairReg d × PairReg d) :
    ∑ x, star (X7Q_V U x a) * g x = ∑ i, ∑ k, U.val k i * g (a.1, (i, (k, a.2))) := by
  rw [Fintype.sum_prod_type (fun x : CombReg d => star (X7Q_V U x a) * g x)]
  rw [Finset.sum_eq_single a.1]
  · rw [Fintype.sum_prod_type (fun x : Fin d × (Fin d × PairReg d) => star (X7Q_V U (a.1, x) a) * g (a.1, x))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_prod_type (fun x : Fin d × PairReg d => star (X7Q_V U (a.1, (j, x)) a) * g (a.1, (j, x)))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_eq_single a.2]
    · simp [X7Q_V]
    · intro c _ hc; simp [X7Q_V, hc]
    · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [X7Q_V, hc]
  · simp

lemma X7Q_VRV {d : ℕ} (R : Matrix (CombReg d) (CombReg d) ℂ) (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    insertedChoi R U = (X7Q_V U)ᴴ * R * X7Q_V U := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [X7Q_sumV]
  simp only [X7Q_sumV', insertedChoi, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, X7Q_front3]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [X7Q_front3]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma X7Q_psd {d : ℕ} {R : Matrix (CombReg d) (CombReg d) ℂ} (hR : CloningAdmissible R)
    (U : (Matrix.unitaryGroup (Fin d) ℂ)) : (insertedChoi R U).PosSemidef := by
  rw [X7Q_VRV]; exact hR.1.conjTranspose_mul_mul_same _

lemma X7Q_trace {d : ℕ} {R : Matrix (CombReg d) (CombReg d) ℂ} (hR : CloningAdmissible R)
    (U : (Matrix.unitaryGroup (Fin d) ℂ)) : (insertedChoi R U).trace = ((d : ℝ) ^ 2 : ℝ) := by
  obtain ⟨-, R0, -, h1, h2⟩ := hR
  have hU : ∀ i j : Fin d, ∑ k, U.val k i * conj (U.val k j) = if i = j then 1 else 0 := by
    intro i j
    have := U.2; rw [Matrix.mem_unitaryGroup_iff'] at this
    have h := congrFun (congrFun this j) i
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] at h
    rw [show (if i = j then (1:ℂ) else 0) = if j = i then 1 else 0 by
      by_cases hij : i = j <;> simp [hij, eq_comm]]
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RCLike.star_def]; ring
  unfold Matrix.trace
  rw [Fintype.sum_prod_type (fun x : PairReg d × PairReg d => (insertedChoi R U).diag x)]
  simp only [Matrix.diag, insertedChoi]
  have step : ∀ a1 : PairReg d, (∑ a2 : PairReg d, ∑ i, ∑ j, ∑ k, ∑ l,
      U.val k i * conj (U.val l j) * R (a1, (i, (k, a2))) (a1, (j, (l, a2)))) = 1 := by
    intro a1
    rw [Finset.sum_comm]
    have e : ∀ i : Fin d, (∑ a2 : PairReg d, ∑ j, ∑ k, ∑ l,
        U.val k i * conj (U.val l j) * R (a1, (i, (k, a2))) (a1, (j, (l, a2)))) =
        ∑ j, ∑ k, U.val k i * conj (U.val k j) * R0 (a1, i) (a1, j) := by
      intro i
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, h1]
      simp [mul_ite, Finset.sum_ite_eq]
    simp only [e, ← Finset.sum_mul, hU, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have := h2 a1 a1
    simpa using this
  simp only [step, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast; ring

end QAlgorithms.Papers.Independent.Claimed50.P27

-- part T

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

instance X7Q_haar (d : ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsHaarMeasure := by
  unfold QAlgorithms.Schur.unitaryHaar; infer_instance

instance X7Q_prob (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

lemma X7Q_point {d : ℕ} (R : Matrix (CombReg d) (CombReg d) ℂ) (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    pointScore (insertedChoi R U) U = (X7P27Q.qf (insertedChoi R U) (X7Q_w U)).re / (d : ℝ) ^ 4 := by
  unfold pointScore; rw [X7Q_trace_CJ]

lemma X7Q_point_bounds {d : ℕ} (hd : 2 ≤ d) {R : Matrix (CombReg d) (CombReg d) ℂ} (hR : CloningAdmissible R)
    (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    0 ≤ pointScore (insertedChoi R U) U ∧ pointScore (insertedChoi R U) U ≤ 1 := by
  rw [X7Q_point]
  have hd4 : (0:ℝ) < (d:ℝ) ^ 4 := by
    have : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  have h0 := X7P27Q.qf_nonneg (X7Q_psd hR U) (X7Q_w U)
  have h1 := X7P27Q.bound (X7Q_psd hR U) (X7Q_w U)
  rw [X7Q_ns, X7Q_trace hR, Complex.ofReal_re] at h1
  refine ⟨div_nonneg h0 hd4.le, ?_⟩
  rw [div_le_one hd4]
  nlinarith

lemma X7Q_cont {d : ℕ} (R : Matrix (CombReg d) (CombReg d) ℂ) :
    Continuous fun U : (Matrix.unitaryGroup (Fin d) ℂ) => pointScore (insertedChoi R U) U := by
  have hU : Continuous (fun U : (Matrix.unitaryGroup (Fin d) ℂ) => (U : Matrix (Fin d) (Fin d) ℂ)) :=
    continuous_subtype_val
  have hC : Continuous fun U : (Matrix.unitaryGroup (Fin d) ℂ) => insertedChoi R U := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    unfold insertedChoi
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
    exact ((hU.matrix_elem k i).mul (Complex.continuous_conj.comp (hU.matrix_elem l j))).mul continuous_const
  have hw : Continuous fun U : (Matrix.unitaryGroup (Fin d) ℂ) => X7Q_w U := by
    refine continuous_pi fun x => ?_
    unfold X7Q_w
    exact (hU.matrix_elem x.2.1 x.1.1).mul (hU.matrix_elem x.2.2 x.1.2)
  have hJ : Continuous fun U : (Matrix.unitaryGroup (Fin d) ℂ) => channelChoi (targetChannel U) := by
    simp only [X7Q_J]
    refine continuous_pi fun x => continuous_pi fun y => ?_
    simp only [Matrix.vecMulVec_apply, Pi.star_apply]
    exact (continuous_apply x |>.comp hw).mul ((continuous_apply y |>.comp hw).star)
  unfold pointScore
  exact (Complex.continuous_re.comp (hC.matrix_mul hJ).matrix_trace).div_const _

lemma X7Q_qf_real {d : ℕ} {R : Matrix (CombReg d) (CombReg d) ℂ} (hR : CloningAdmissible R)
    (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    X7P27Q.qf (insertedChoi R U) (X7Q_w U) = ((X7P27Q.qf (insertedChoi R U) (X7Q_w U)).re : ℂ) := by
  have := (X7Q_psd hR U).dotProduct_mulVec_nonneg (X7Q_w U)
  have e : star (X7Q_w U) ⬝ᵥ (insertedChoi R U *ᵥ X7Q_w U) = X7P27Q.qf (insertedChoi R U) (X7Q_w U) := by
    simp only [X7P27Q.qf, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e] at this
  apply Complex.ext
  · simp
  · simp [(Complex.nonneg_iff.mp this).2.symm]

lemma X7Q_qf_J {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    X7P27Q.qf (channelChoi (targetChannel U)) (X7Q_w U) = (((d : ℝ) ^ 2 : ℝ) : ℂ) ^ 2 := by
  rw [X7Q_J, ← X7Q_ns]
  have e1 : ∀ z : ℂ, ((Complex.normSq z : ℝ) : ℂ) = star z * z := fun z => by
    rw [RCLike.star_def, mul_comm, Complex.mul_conj]
  simp only [X7P27Q.qf, X7P27Q.ns, Matrix.vecMulVec_apply, Pi.star_apply]
  push_cast
  simp only [e1, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end QAlgorithms.Papers.Independent.Claimed50.P27

open QAlgorithms.Papers.Independent.Claimed50.P27 in
theorem solution (d : ℕ) (hd : 2 ≤ d)
    (R : Matrix (CombReg d) (CombReg d) ℂ) (hR : CloningAdmissible R) :
    (0 ≤ combScore R ∧ combScore R ≤ 1) ∧
    (combScore R = 1 ↔ ∀ U : (Matrix.unitaryGroup (Fin d) ℂ),
      insertedChoi R U = channelChoi (targetChannel U)) := by
  have hint : Integrable (fun U : (Matrix.unitaryGroup (Fin d) ℂ) => pointScore (insertedChoi R U) U)
      (QAlgorithms.Schur.unitaryHaar d) :=
    (X7Q_cont R).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hd4 : (0:ℝ) < (d:ℝ) ^ 4 := by
    have : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  refine ⟨⟨?_, ?_⟩, ⟨fun h1 U => ?_, fun h => ?_⟩⟩
  · exact integral_nonneg fun U => (X7Q_point_bounds hd hR U).1
  · unfold combScore
    calc _ ≤ ∫ _U : (Matrix.unitaryGroup (Fin d) ℂ), (1:ℝ) ∂(QAlgorithms.Schur.unitaryHaar d) :=
          integral_mono hint (integrable_const _) fun U => (X7Q_point_bounds hd hR U).2
      _ = 1 := by simp
  · -- the defect 1 - score is continuous, nonnegative, with zero integral
    set f := fun U : (Matrix.unitaryGroup (Fin d) ℂ) => 1 - pointScore (insertedChoi R U) U
    have hf0 : 0 ≤ f := fun U => by
      show (0:ℝ) ≤ 1 - pointScore (insertedChoi R U) U
      linarith [(X7Q_point_bounds hd hR U).2]
    have hfi : Integrable f (QAlgorithms.Schur.unitaryHaar d) := (integrable_const _).sub hint
    have hfint : ∫ U, f U ∂(QAlgorithms.Schur.unitaryHaar d) = 0 := by
      simp only [f]
      rw [integral_sub (integrable_const _) hint]
      unfold combScore at h1
      rw [h1]; simp
    have hae := (integral_eq_zero_iff_of_nonneg hf0 hfi).mp hfint
    have hfc : Continuous f := continuous_const.sub (X7Q_cont R)
    have hall : f = 0 := (hfc.ae_eq_iff_eq (QAlgorithms.Schur.unitaryHaar d) continuous_const).mp hae
    have hU := congrFun hall U
    simp only [f, Pi.zero_apply, sub_eq_zero] at hU
    rw [X7Q_point, eq_comm, div_eq_one_iff_eq hd4.ne'] at hU
    rw [X7Q_J]
    refine X7P27Q.eq_case (X7Q_psd hR U) (X7Q_w U) ?_ ?_ ?_
    · rw [X7Q_ns]; positivity
    · rw [X7Q_trace hR, X7Q_ns]
    · rw [X7Q_qf_real hR, hU, X7Q_ns]; push_cast; ring
  · unfold combScore
    have : ∀ U : (Matrix.unitaryGroup (Fin d) ℂ), pointScore (insertedChoi R U) U = 1 := by
      intro U
      rw [X7Q_point, h U, X7Q_qf_J]
      have : ((((d:ℝ) ^ 2 : ℝ) : ℂ) ^ 2).re = (d:ℝ) ^ 4 := by
        rw [← Complex.ofReal_pow, Complex.ofReal_re]; ring
      rw [this, div_self hd4.ne']
    simp [this]
