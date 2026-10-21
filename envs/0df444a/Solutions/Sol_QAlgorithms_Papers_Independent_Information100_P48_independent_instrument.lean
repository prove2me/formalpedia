-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P48.independent_instrument
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T09:12:37.309473+00:00
-- url     : https://prove2.me/submissions/92eb0d19-ee28-40d5-ad34-64e9a7c8b655

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P48

namespace G56I

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Kraus operator of the column `e` of `A` at environment output `f`. -/
def KR (A : Matrix (Bool × E) (Bool × E) ℂ) (e f : E) : QOp := fun s s' => A (s, f) (s', e)

lemma cross_eq (A B : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (X : QOp) :
    cross A B e X = ∑ f, KR A e f * X * (KR B e f)ᴴ := by
  ext s t
  simp only [cross, traceEnv, cleanInput, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.single_apply, Fintype.sum_prod_type, Matrix.sum_apply, Matrix.conjTranspose_apply, KR]
  refine Finset.sum_congr rfl fun f _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [ite_and, mul_ite, Finset.sum_ite_eq, Finset.sum_mul, ite_mul]

lemma traceEnv_add (M N : Matrix (Bool × E) (Bool × E) ℂ) : traceEnv (M + N) = traceEnv M + traceEnv N := by
  ext s t; simp [traceEnv, Finset.sum_add_distrib]

lemma traceEnv_smul (c : ℂ) (M : Matrix (Bool × E) (Bool × E) ℂ) : traceEnv (c • M) = c • traceEnv M := by
  ext s t; simp [traceEnv, Finset.mul_sum]

lemma trace_traceEnv (M : Matrix (Bool × E) (Bool × E) ℂ) : (traceEnv M).trace = M.trace := by
  simp [Matrix.trace, traceEnv, Fintype.sum_prod_type]

lemma cross_add_left (A A' B : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (X : QOp) :
    cross (A + A') B e X = cross A B e X + cross A' B e X := by
  simp [cross, Matrix.add_mul, traceEnv_add]

lemma cross_add_right (A B B' : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (X : QOp) :
    cross A (B + B') e X = cross A B e X + cross A B' e X := by
  simp [cross, Matrix.conjTranspose_add, Matrix.mul_add, traceEnv_add]

lemma cross_smul_left (c : ℂ) (A B : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (X : QOp) :
    cross (c • A) B e X = c • cross A B e X := by
  simp [cross, Matrix.smul_mul, traceEnv_smul]

lemma cross_smul_right (c : ℂ) (A B : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (X : QOp) :
    cross A (c • B) e X = (starRingEnd ℂ c) • cross A B e X := by
  simp [cross, Matrix.conjTranspose_smul, Matrix.mul_smul, traceEnv_smul]

lemma cross_addX (A B : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (X Y : QOp) :
    cross A B e (X + Y) = cross A B e X + cross A B e Y := by
  simp [cross, cleanInput, Matrix.add_kronecker, Matrix.mul_add, Matrix.add_mul, traceEnv_add]

lemma cross_smulX (A B : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (c : ℂ) (X : QOp) :
    cross A B e (c • X) = c • cross A B e X := by
  simp [cross, cleanInput, Matrix.smul_kronecker, Matrix.mul_smul, Matrix.smul_mul, traceEnv_smul]

/-- branch as an explicit combination of cross maps. -/
lemma branch_eq (U V : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (m : Bool) (X : QOp) :
    branch U V e m X = (1 / 4 : ℂ) • (cross U U e X + cross V V e X) +
      ((outcomeSign m / 4 : ℝ) : ℂ) • (cross U V e X + cross V U e X) := by
  unfold branch selectedOperator
  simp only [cross_add_left, cross_add_right, cross_smul_left, cross_smul_right]
  cases m <;> simp [outcomeSign, map_ofNat] <;> module

lemma trace_cross_self (U : Matrix.unitaryGroup (Bool × E) ℂ) (e : E) (X : QOp) :
    (cross (U : Matrix (Bool × E) (Bool × E) ℂ) U e X).trace = X.trace := by
  unfold cross
  have hU := Matrix.mem_unitaryGroup_iff'.mp U.2
  rw [Matrix.star_eq_conjTranspose] at hU
  rw [trace_traceEnv, Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  simp [cleanInput, Matrix.trace_kronecker]

lemma psd_cross_self (U : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (X : QOp) (hX : X.PosSemidef) :
    (cross U U e X).PosSemidef := by
  rw [cross_eq]
  exact Matrix.posSemidef_sum _ fun f _ => hX.mul_mul_conjTranspose_same _

lemma isCP_cross_self (U : Matrix (Bool × E) (Bool × E) ℂ) (e : E) : IsCP (cross U U e) := by
  refine ⟨Fintype.card E, fun j => KR U e ((Fintype.equivFin E).symm j), fun X => ?_⟩
  rw [cross_eq]
  exact (Fintype.sum_equiv (Fintype.equivFin E).symm _ _ (fun _ => rfl)).symm

lemma cp_conj (U V : Matrix (Bool × E) (Bool × E) ℂ) (K : Matrix (Bool × (Bool × E)) (Bool × (Bool × E)) ℂ)
    (a b : Bool) (p q : Bool × E) :
    (controlledPair U V * K * (controlledPair U V)ᴴ) (a, p) (b, q) =
      ((if a then V else U) * (Matrix.of fun p q => K (a, p) (b, q)) * (if b then V else U)ᴴ) p q := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool, controlledPair,
    Matrix.conjTranspose_apply]
  cases a <;> cases b <;> simp

/-- `jointCS` block structure. -/
lemma jointCS_apply (tau : QOp) (U V : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (rho : QOp) (a x b y : Bool) :
    jointCS tau U V e rho (a, x) (b, y) =
      tau a b * cross (if a then V else U) (if b then V else U) e rho x y := by
  simp only [jointCS, cross, traceEnv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [cp_conj]
  have : (Matrix.of fun p q => (Matrix.kronecker tau (cleanInput e rho)) (a, p) (b, q)) =
      tau a b • cleanInput e rho := by
    ext p q; simp [Matrix.kronecker]
  rw [this, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

lemma selectControl_blocks (D0 D1 C01 C10 : QOp) (m : Bool) :
    selectControl (controlBlocks D0 D1 C01 C10) m =
      (1 / 4 : ℂ) • (D0 + D1) + ((outcomeSign m / 4 : ℝ) : ℂ) • (C01 + C10) := by
  ext s t
  cases m <;> cases t <;>
  simp [selectControl, traceLeft, controlBlocks, hadamardProjector, outcomeSign, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.conjTranspose_apply, map_ofNat] <;> ring

end G56I

namespace G56I

variable {E : Type*} [Fintype E] [DecidableEq E]

lemma dens_normalize (M : QOp) (hM : M.PosSemidef) (h : 0 < M.trace.re) : IsDensityMatrix (Papers.Independent.Information100.P48.normalize M) := by
  have h0 := hM.trace_nonneg
  have hre : M.trace = (M.trace.re : ℂ) := by
    rw [Complex.nonneg_iff] at h0
    apply Complex.ext <;> simp [h0.2.symm]
  refine ⟨?_, ?_⟩
  · unfold Papers.Independent.Information100.P48.normalize
    apply hM.smul
    have : (0 : ℝ) ≤ (M.trace.re)⁻¹ := inv_nonneg.mpr h.le
    exact_mod_cast this
  · unfold Papers.Independent.Information100.P48.normalize
    rw [Matrix.trace_smul, smul_eq_mul, hre]
    simp only [Complex.ofReal_re]
    have : (M.trace.re : ℂ) ≠ 0 := by exact_mod_cast h.ne'
    field_simp

lemma branch_psd (U V : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (m : Bool) (X : QOp) (hX : X.PosSemidef) :
    (branch U V e m X).PosSemidef := psd_cross_self _ e X hX

lemma branch_cp (U V : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (m : Bool) : IsCP (branch U V e m) :=
  isCP_cross_self _ e

lemma tr_re_nonneg (M : QOp) (hM : M.PosSemidef) : 0 ≤ M.trace.re := by
  have h0 := hM.trace_nonneg
  rw [Complex.nonneg_iff] at h0
  exact h0.1

lemma not_channel_neg : ¬ IsChannel (cross (1 : QQOp) (-1 : QQOp) false) := by
  rintro ⟨m, K, hK, hΦ⟩
  have h1 : cross (1 : QQOp) (-1 : QQOp) false 1 = -1 := by
    ext s t
    cases s <;> cases t <;>
      simp [cross, traceEnv, cleanInput, Matrix.mul_apply, Matrix.kronecker, Fintype.sum_prod_type,
        Matrix.one_apply, Matrix.single_apply]
  have h2 := congrArg Matrix.trace (h1.symm.trans (hΦ 1))
  unfold krausApply at h2
  rw [Matrix.trace_sum] at h2
  simp only [Matrix.mul_one] at h2
  have h3 : ∑ j, ((K j) * (K j)ᴴ).trace = ∑ j, ((K j)ᴴ * K j).trace :=
    Finset.sum_congr rfl fun j _ => Matrix.trace_mul_comm _ _
  rw [h3, ← Matrix.trace_sum, hK] at h2
  simp [Matrix.trace] at h2
  norm_num at h2

lemma traceEnv_conj (V : Matrix.unitaryGroup E ℂ) (M : Matrix (Bool × E) (Bool × E) ℂ) :
    traceEnv (Matrix.kronecker (1 : QOp) (V : Matrix E E ℂ) * M * (Matrix.kronecker (1 : QOp) (V : Matrix E E ℂ))ᴴ) =
      traceEnv M := by
  ext s t
  have hblk : ∀ f f', (Matrix.kronecker (1 : QOp) (V : Matrix E E ℂ) * M *
      (Matrix.kronecker (1 : QOp) (V : Matrix E E ℂ))ᴴ) (s, f) (t, f') =
      ((V : Matrix E E ℂ) * (Matrix.of fun f f' => M (s, f) (t, f')) * (V : Matrix E E ℂ)ᴴ) f f' := by
    intro f f'
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.of_apply]
    simp [Fintype.sum_bool, Finset.sum_add_distrib]
    cases s <;> cases t <;> simp
  have hU := Matrix.mem_unitaryGroup_iff'.mp V.2
  rw [Matrix.star_eq_conjTranspose] at hU
  calc traceEnv _ s t = ((V : Matrix E E ℂ) * (Matrix.of fun f f' => M (s, f) (t, f')) * (V : Matrix E E ℂ)ᴴ).trace := by
        simp only [traceEnv, hblk]; rfl
    _ = (Matrix.of fun f f' => M (s, f) (t, f')).trace := by
        rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
    _ = traceEnv M s t := rfl

lemma cross_conjV (V : Matrix.unitaryGroup E ℂ) (U : Matrix (Bool × E) (Bool × E) ℂ) (e : E) (X : QOp) :
    cross (Matrix.kronecker (1 : QOp) (V : Matrix E E ℂ) * U) (Matrix.kronecker (1 : QOp) (V : Matrix E E ℂ) * U) e X =
      cross U U e X := by
  unfold cross
  have : Matrix.kronecker (1 : QOp) (V : Matrix E E ℂ) * U * cleanInput e X *
      (Matrix.kronecker (1 : QOp) (V : Matrix E E ℂ) * U)ᴴ =
      Matrix.kronecker (1 : QOp) (V : Matrix E E ℂ) * (U * cleanInput e X * Uᴴ) *
        (Matrix.kronecker (1 : QOp) (V : Matrix E E ℂ))ᴴ := by
    rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [this]
  exact traceEnv_conj V _

end G56I

namespace G56I

variable {E0 E1 : Type*} [Fintype E0] [Fintype E1] [DecidableEq E0] [DecidableEq E1]

lemma KR_embed0 (U : Matrix (Bool × E0) (Bool × E0) ℂ) (e0 : E0) (e1 : E1) (f : E0 × E1) :
    KR (embed0 (E1 := E1) U) (e0, e1) f = if f.2 = e1 then KR U e0 f.1 else 0 := by
  ext s t; split_ifs with h <;> simp [KR, embed0, h]

lemma KR_embed1 (U : Matrix (Bool × E1) (Bool × E1) ℂ) (e0 : E0) (e1 : E1) (f : E0 × E1) :
    KR (embed1 (E0 := E0) U) (e0, e1) f = if f.1 = e0 then KR U e1 f.2 else 0 := by
  ext s t; split_ifs with h <;> simp [KR, embed1, h]

lemma KR_self (U : Matrix (Bool × E0) (Bool × E0) ℂ) (e0 : E0) : KR U e0 e0 = interference U e0 := rfl

lemma cross_e00 (U : Matrix (Bool × E0) (Bool × E0) ℂ) (e0 : E0) (e1 : E1) (X : QOp) :
    cross (embed0 (E1 := E1) U) (embed0 (E1 := E1) U) (e0, e1) X = cross U U e0 X := by
  rw [cross_eq, cross_eq, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_eq_single e1]
  · refine Finset.sum_congr rfl fun f _ => ?_
    simp [KR_embed0]
  · intro b _ hb; simp [KR_embed0, hb]
  · simp

lemma cross_e11 (U : Matrix (Bool × E1) (Bool × E1) ℂ) (e0 : E0) (e1 : E1) (X : QOp) :
    cross (embed1 (E0 := E0) U) (embed1 (E0 := E0) U) (e0, e1) X = cross U U e1 X := by
  rw [cross_eq, cross_eq, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single e0]
  · refine Finset.sum_congr rfl fun f _ => ?_
    simp [KR_embed1]
  · intro b _ hb; simp [KR_embed1, hb]
  · simp

lemma cross_e01 (U : Matrix (Bool × E0) (Bool × E0) ℂ) (V : Matrix (Bool × E1) (Bool × E1) ℂ)
    (e0 : E0) (e1 : E1) (X : QOp) :
    cross (embed0 (E1 := E1) U) (embed1 (E0 := E0) V) (e0, e1) X =
      interference U e0 * X * (interference V e1)ᴴ := by
  rw [cross_eq, Fintype.sum_prod_type, Finset.sum_eq_single e0]
  · rw [Finset.sum_eq_single e1]
    · rw [KR_embed0, KR_embed1]; simp only [if_true]; rfl
    · intro b _ hb; simp [KR_embed0, hb]
    · simp
  · intro b _ hb; simp [KR_embed1, hb]
  · simp

lemma cross_e10 (U : Matrix (Bool × E0) (Bool × E0) ℂ) (V : Matrix (Bool × E1) (Bool × E1) ℂ)
    (e0 : E0) (e1 : E1) (X : QOp) :
    cross (embed1 (E0 := E0) V) (embed0 (E1 := E1) U) (e0, e1) X =
      interference V e1 * X * (interference U e0)ᴴ := by
  rw [cross_eq, Fintype.sum_prod_type, Finset.sum_eq_single e0]
  · rw [Finset.sum_eq_single e1]
    · rw [KR_embed0, KR_embed1]; simp only [if_true]; rfl
    · intro b _ hb; simp [KR_embed0, hb]
    · simp
  · intro b _ hb; simp [KR_embed1, hb]
  · simp

end G56I

open G56I in
theorem solution
    {E0 E1 : Type*} [Fintype E0] [Fintype E1] [DecidableEq E0] [DecidableEq E1]
    (e0 : E0) (e1 : E1)
    (U0 : Matrix.unitaryGroup (Bool × E0) ℂ)
    (U1 : Matrix.unitaryGroup (Bool × E1) ℂ)
    (rho : QOp) (hrho : IsDensityMatrix rho) :
    let U := embed0 (E1 := E1) (U0 : Matrix (Bool × E0) (Bool × E0) ℂ)
    let V := embed1 (E0 := E0) (U1 : Matrix (Bool × E1) (Bool × E1) ℂ)
    let D0 := cross (U0 : Matrix (Bool × E0) (Bool × E0) ℂ) U0 e0 rho
    let D1 := cross (U1 : Matrix (Bool × E1) (Bool × E1) ℂ) U1 e1 rho
    let T0 := interference (U0 : Matrix (Bool × E0) (Bool × E0) ℂ) e0
    let T1 := interference (U1 : Matrix (Bool × E1) (Bool × E1) ℂ) e1
    jointCS (hadamardProjector false) U V (e0, e1) rho =
      controlBlocks D0 D1 (T0 * rho * T1ᴴ) (T1 * rho * T0ᴴ) ∧
    (∀ minus : Bool,
      selectControl (jointCS (hadamardProjector false) U V (e0, e1) rho) minus =
        branch U V (e0, e1) minus rho ∧
      branch U V (e0, e1) minus rho = (1 / 4 : ℂ) • (D0 + D1) +
        ((outcomeSign minus / 4 : ℝ) : ℂ) • (T0 * rho * T1ᴴ + T1 * rho * T0ᴴ) ∧
      IsCP (branch U V (e0, e1) minus) ∧
      0 ≤ (branch U V (e0, e1) minus rho).trace.re ∧
      (branch U V (e0, e1) minus rho).trace.re ≤ 1 ∧
      (0 < (branch U V (e0, e1) minus rho).trace.re →
        IsDensityMatrix (normalize (branch U V (e0, e1) minus rho)))) ∧
    (branch U V (e0, e1) false rho).trace.re +
      (branch U V (e0, e1) true rho).trace.re = 1 ∧
    (∀ minus : Bool, D0 = D1 → T0 = T1 →
      branch U V (e0, e1) minus rho = (1 / 2 : ℂ) • D0 +
        ((outcomeSign minus / 2 : ℝ) : ℂ) • (T0 * rho * T0ᴴ)) ∧
    (∀ minus : Bool,
      selectControl (jointCS (hadamardProjector true) U V (e0, e1) rho) minus =
        branch U V (e0, e1) (!minus) rho) := by
  intro U V D0 D1 T0 T1
  have hJ : ∀ m : Bool, jointCS (hadamardProjector m) U V (e0, e1) rho =
      controlBlocks D0 D1 (((outcomeSign m : ℝ) : ℂ) • (T0 * rho * T1ᴴ)) (((outcomeSign m : ℝ) : ℂ) • (T1 * rho * T0ᴴ)) := by
    intro m
    ext ⟨a, x⟩ ⟨b, y⟩
    rw [jointCS_apply]
    cases m <;> cases a <;> cases b <;>
      simp [controlBlocks, hadamardProjector, outcomeSign, D0, D1, T0, T1, U, V, cross_e00, cross_e11,
        cross_e01, cross_e10]
  have hB : ∀ m : Bool, branch U V (e0, e1) m rho = (1 / 4 : ℂ) • (D0 + D1) +
      ((outcomeSign m / 4 : ℝ) : ℂ) • (T0 * rho * T1ᴴ + T1 * rho * T0ᴴ) := by
    intro m
    rw [branch_eq]
    simp only [U, V, D0, D1, T0, T1, cross_e00, cross_e11, cross_e01, cross_e10]
  have hS : ∀ m : Bool, selectControl (jointCS (hadamardProjector false) U V (e0, e1) rho) m =
      branch U V (e0, e1) m rho := by
    intro m
    rw [hJ, selectControl_blocks, hB]
    simp [outcomeSign]
  have hpsd : ∀ m, (branch U V (e0, e1) m rho).PosSemidef := fun m => branch_psd _ _ _ m rho hrho.1
  have hsum : (branch U V (e0, e1) false rho).trace.re + (branch U V (e0, e1) true rho).trace.re = 1 := by
    rw [hB, hB, ← Complex.add_re, ← Matrix.trace_add]
    have : (1 / 4 : ℂ) • (D0 + D1) + ((outcomeSign false / 4 : ℝ) : ℂ) • (T0 * rho * T1ᴴ + T1 * rho * T0ᴴ) +
        ((1 / 4 : ℂ) • (D0 + D1) + ((outcomeSign true / 4 : ℝ) : ℂ) • (T0 * rho * T1ᴴ + T1 * rho * T0ᴴ)) =
          (1 / 2 : ℂ) • (D0 + D1) := by
      simp only [outcomeSign]; push_cast; module
    rw [this, Matrix.trace_smul, Matrix.trace_add]
    simp only [D0, D1]
    rw [trace_cross_self U0 e0 rho, trace_cross_self U1 e1 rho, hrho.2]
    norm_num
  refine ⟨?_, fun m => ?_, hsum, fun m h1 h2 => ?_, fun m => ?_⟩
  · simpa [outcomeSign] using hJ false
  · have h0 := tr_re_nonneg _ (hpsd m)
    refine ⟨hS m, hB m, branch_cp _ _ _ m, h0, ?_, fun hpos => dens_normalize _ (hpsd m) hpos⟩
    have h1 := tr_re_nonneg _ (hpsd (!m))
    cases m <;> simp at h1 <;> linarith
  · rw [hB, h1, h2]
    cases m <;> simp only [outcomeSign] <;> push_cast <;> module
  · rw [hJ, selectControl_blocks, hB]
    cases m <;> simp only [outcomeSign, Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true] <;>
      push_cast <;> module
