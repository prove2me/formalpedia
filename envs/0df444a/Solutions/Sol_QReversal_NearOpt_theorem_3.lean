-- Prove2me | solution 1 for QReversal.NearOpt.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T18:10:10.66815+00:00
-- url     : https://prove2.me/submissions/bfc981ab-c85c-4949-a9d9-e841cf14f08b

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_QReversal_NearOpt_Setting

/- Direct proof of the original commuting-ensemble near-optimal recovery theorem.
   NREC2: weighted rectangular Gram Cauchy--Schwarz.
   NREC3: support restriction and recovery factorization, singular input allowed.
   NREC4: density trace bound and trace-nonincreasing normalization.
   The Gram-amplitude assembly replaces the paper's Kraus SVD without changing
   the canonical statement. All helper proofs are included in this file. -/

noncomputable section

open Matrix
open scoped BigOperators

namespace QReversal.NearOpt.GramProof

noncomputable def frobSq {R C : Type*} [Fintype R] [Fintype C]
    (M : Matrix R C ℂ) : ℝ := ∑ r, ∑ c, Complex.normSq (M r c)

variable {R C : Type*} [Fintype R] [Fintype C]

/-- Direct trace expansion, from sometik179's accepted proof of
QReversal.PGMBound.theorem_5, submission090ebed5-52f3-4f18-8273-d47470c08eb3.
Only this elementary body is reused; no full-rank theorem is imported. -/
lemma frobSq_eq_trace (Y : Matrix R C ℂ) :
    frobSq Y = (Yᴴ * Y).trace.re := by
  simp only [frobSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := Y j i))

lemma frobSq_nonneg (Y : Matrix R C ℂ) : 0 ≤ frobSq Y := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma real_pair_sq_le (x y : ℂ) :
    (star x * y).re ^ 2 ≤ Complex.normSq x * Complex.normSq y := by
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  nlinarith [sq_nonneg (x.re * y.im - x.im * y.re)]

lemma sum_real_pair_sq_le {T : Type*} [Fintype T] (x y : T → ℂ) :
    (∑ t, (star (x t) * y t).re) ^ 2 ≤
      (∑ t, Complex.normSq (x t)) * ∑ t, Complex.normSq (y t) := by
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun t _ => Complex.normSq_nonneg (x t))
    (fun t _ => Complex.normSq_nonneg (y t))
    (fun t _ => real_pair_sq_le (x t) (y t))

lemma trace_pair (X Y : Matrix R C ℂ) :
    (Xᴴ * Y).trace.re = ∑ r, ∑ c, (star (X r c) * Y r c).re := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]

lemma trace_pair_sq_le (X Y : Matrix R C ℂ) :
    (Xᴴ * Y).trace.re ^ 2 ≤ frobSq X * frobSq Y := by
  rw [trace_pair]
  simpa only [Fintype.sum_prod_type, frobSq] using
    sum_real_pair_sq_le (fun rc : R × C => X rc.1 rc.2)
      (fun rc : R × C => Y rc.1 rc.2)

lemma frobSq_gram (Y : Matrix R C ℂ) :
    frobSq (Yᴴ * Y) = frobSq (Y * Yᴴ) := by
  simp only [frobSq_eq_trace, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  congr 1
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm Yᴴ (Y * Yᴴ * Y)

lemma mixed_gram_eq_trace {J : Type*} [Fintype J]
    (Y : Matrix R C ℂ) (Z : Matrix R J ℂ) :
    frobSq (Yᴴ * Z) = ((Y * Yᴴ)ᴴ * (Z * Zᴴ)).trace.re := by
  rw [frobSq_eq_trace]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  congr 1
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm Zᴴ (Y * Yᴴ * Z)

lemma gram_cauchy {J : Type*} [Fintype J]
    (Y : Matrix R C ℂ) (Z : Matrix R J ℂ) :
    frobSq (Yᴴ * Z) ^ 2 ≤ frobSq (Yᴴ * Y) * frobSq (Zᴴ * Z) := by
  rw [mixed_gram_eq_trace, frobSq_gram Y, frobSq_gram Z]
  exact trace_pair_sq_le (Y * Yᴴ) (Z * Zᴴ)

theorem weighted_gram_cauchy
    {L V I J : Type*} [Fintype L] [Fintype V] [Fintype I] [Fintype J]
    (p : L → ℝ) (hp : ∀ l, 0 ≤ p l)
    (Y : L → Matrix V I ℂ) (Z : L → Matrix V J ℂ) :
    (∑ l, p l * frobSq ((Y l)ᴴ * Z l)) ^ 2 ≤
      (∑ l, p l * frobSq ((Y l)ᴴ * Y l)) *
      (∑ l, p l * frobSq ((Z l)ᴴ * Z l)) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
  · intro l _
    exact mul_nonneg (hp l) (frobSq_nonneg _)
  · intro l _
    exact mul_nonneg (hp l) (frobSq_nonneg _)
  · intro l _
    have h := mul_le_mul_of_nonneg_left (gram_cauchy (Y l) (Z l)) (sq_nonneg (p l))
    nlinarith

end QReversal.NearOpt.GramProof

/-! Seven finite spectral CFC identities adapted from the actual accepted PGM
proof by sometik179, submission090ebed5-52f3-4f18-8273-d47470c08eb3.
Only namespace/type-variable scope changes; no imported implementation helpers. -/
open Matrix PeresTerno Unitary
open scoped MatrixOrder ComplexOrder BigOperators
noncomputable section
namespace QReversal.NearOpt.FactorizationProof
variable {C : Type*} [Fintype C] [DecidableEq C]

lemma functional_mul {M : Matrix C C ℂ} (h : M.IsHermitian) (f g : ℝ → ℝ) :
    h.cfc f * h.cfc g = h.cfc (fun t => f t * g t) := by
  unfold Matrix.IsHermitian.cfc
  rw [← map_mul, diagonal_mul_diagonal]
  congr 1
  funext i
  simp [Function.comp_def]

lemma functional_sub {M : Matrix C C ℂ} (h : M.IsHermitian) (f g : ℝ → ℝ) :
    h.cfc f - h.cfc g = h.cfc (fun t => f t - g t) := by
  unfold Matrix.IsHermitian.cfc
  rw [← map_sub, diagonal_sub]
  congr 1
  funext i
  simp [Function.comp_def]

lemma functional_id {M : Matrix C C ℂ} (h : M.IsHermitian) : h.cfc id = M := by
  exact h.spectral_theorem.symm

lemma functional_one {M : Matrix C C ℂ} (h : M.IsHermitian) : h.cfc (fun _ => 1) = 1 := by
  simp [Matrix.IsHermitian.cfc, Function.comp_def]

lemma functional_congr {M : Matrix C C ℂ} (h : M.IsHermitian) {f g : ℝ → ℝ}
    (heq : ∀ i, f (h.eigenvalues i) = g (h.eigenvalues i)) : h.cfc f = h.cfc g := by
  unfold Matrix.IsHermitian.cfc
  congr 1
  congr 1
  funext i
  simp only [Function.comp_apply, heq]

lemma functional_pos {M : Matrix C C ℂ} (h : M.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ i, 0 ≤ f (h.eigenvalues i)) : (h.cfc f).PosSemidef := by
  rw [Matrix.IsHermitian.cfc, conjStarAlgAut_apply]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply posSemidef_diagonal_iff.mpr
  intro i
  simpa [Function.comp_def] using (Complex.zero_le_real.mpr (hf i))

lemma functional_sqrt {M : Matrix C C ℂ} (h : M.PosSemidef) :
    h.isHermitian.cfc Real.sqrt = CFC.sqrt M := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ M, h.isHermitian.cfc_eq]
  congr 1
  funext x
  exact Real.sqrt.eq_def x


lemma invSqrt_posSemidef (M : Matrix C C ℂ) (hM : M.PosSemidef) :
    (invSqrt M).PosSemidef := by
  rw [invSqrt, hM.isHermitian.cfc_eq]
  exact functional_pos _ _ fun _ => inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma support_posSemidef (M : Matrix C C ℂ) (hM : M.PosSemidef) :
    (supportProj M).PosSemidef := by
  rw [supportProj, hM.isHermitian.cfc_eq]
  apply functional_pos
  intro i
  split_ifs <;> norm_num

lemma support_sq (M : Matrix C C ℂ) (hM : M.PosSemidef) :
    supportProj M * supportProj M = supportProj M := by
  rw [supportProj, hM.isHermitian.cfc_eq, functional_mul]
  apply functional_congr
  intro i
  split_ifs <;> norm_num

lemma support_le_one (M : Matrix C C ℂ) (hM : M.PosSemidef) :
    supportProj M ≤ 1 := by
  rw [Matrix.le_iff, supportProj, hM.isHermitian.cfc_eq,
    ← functional_one hM.isHermitian, functional_sub]
  apply functional_pos
  intro i
  split_ifs <;> norm_num

lemma mul_support (M : Matrix C C ℂ) (hM : M.PosSemidef) :
    M * supportProj M = M := by
  rw [supportProj, hM.isHermitian.cfc_eq]
  conv_lhs => lhs; rw [← functional_id hM.isHermitian]
  rw [functional_mul]
  conv_rhs => rw [← functional_id hM.isHermitian]
  apply functional_congr
  intro i
  split_ifs <;> simp_all

lemma sqrt_mul_invSqrt (M : Matrix C C ℂ) (hM : M.PosSemidef) :
    CFC.sqrt M * invSqrt M = supportProj M := by
  rw [← functional_sqrt hM, invSqrt, supportProj,
    hM.isHermitian.cfc_eq, hM.isHermitian.cfc_eq, functional_mul]
  apply functional_congr
  intro i
  by_cases hi : hM.isHermitian.eigenvalues i = 0
  · simp [hi]
  · have hp := lt_of_le_of_ne (hM.eigenvalues_nonneg i) (Ne.symm hi)
    simp [hi, ne_of_gt (Real.sqrt_pos.mpr hp)]

lemma invSqrt_mul_self_mul_invSqrt (M : Matrix C C ℂ) (hM : M.PosSemidef) :
    invSqrt M * M * invSqrt M = supportProj M := by
  rw [invSqrt, supportProj, hM.isHermitian.cfc_eq, hM.isHermitian.cfc_eq]
  conv_lhs => lhs; rhs; rw [← functional_id hM.isHermitian]
  rw [functional_mul, functional_mul]
  apply functional_congr
  intro i
  have ht := hM.eigenvalues_nonneg i
  by_cases hi : hM.isHermitian.eigenvalues i = 0
  · simp [hi]
  · have hn : Real.sqrt (hM.isHermitian.eigenvalues i) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne ht (Ne.symm hi)))
    simp only [hi, if_false, id_eq]
    field_simp
    nlinarith [Real.sq_sqrt ht]

lemma support_eq_one (M : Matrix C C ℂ) (hM : M.PosDef) : supportProj M = 1 := by
  rw [supportProj, hM.isHermitian.cfc_eq, ← functional_one hM.isHermitian]
  apply functional_congr
  intro i
  simp [ne_of_gt (hM.eigenvalues_pos i)]

lemma sqrt_mul_invSqrt_of_posDef (M : Matrix C C ℂ) (hM : M.PosDef) :
    CFC.sqrt M * invSqrt M = 1 := by
  rw [sqrt_mul_invSqrt M hM.posSemidef, support_eq_one M hM]

omit [Fintype C] [DecidableEq C] in
lemma avgState_posSemidef {L : Type*} [Fintype L]
    (p : L → ℝ) (ρs : L → Matrix C C ℂ)
    (hp : ∀ l, 0 ≤ p l) (hρ : ∀ l, (ρs l).PosSemidef) :
    (avgState p ρs).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg fun l _ =>
    ((hρ l).smul (Complex.zero_le_real.mpr (hp l))).nonneg

/-- A positive summand of a positive sum vanishes on the kernel of that sum. -/
lemma positive_summand_annihilates {L : Type*} [Fintype L]
    (M : L → Matrix C C ℂ) (hM : ∀ l, (M l).PosSemidef)
    (Q : Matrix C C ℂ) (hQ : (∑ l, M l) * Q = 0) (l : L) : M l * Q = 0 := by
  classical
  have hzero : ∑ j, Qᴴ * M j * Q = 0 := by
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.mul_assoc, hQ, Matrix.mul_zero]
  have hpos : ∀ j, 0 ≤ Qᴴ * M j * Q :=
    fun j => ((hM j).conjTranspose_mul_mul_same Q).nonneg
  have hle : Qᴴ * M l * Q ≤ ∑ j, Qᴴ * M j * Q :=
    Finset.single_le_sum (fun j _ => hpos j) (Finset.mem_univ l)
  rw [hzero] at hle
  have hz : Qᴴ * M l * Q = 0 := le_antisymm hle (hpos l)
  have hroot : CFC.sqrt (M l) * Q = 0 := by
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    have hh := (CFC.sqrt_nonneg (M l)).posSemidef.isHermitian.eq
    rw [Matrix.conjTranspose_mul, hh]
    calc
      (Qᴴ * CFC.sqrt (M l) * (CFC.sqrt (M l) * Q)).trace =
          (Qᴴ * (CFC.sqrt (M l) * CFC.sqrt (M l)) * Q).trace := by
            simp only [Matrix.mul_assoc]
      _ = 0 := by rw [CFC.sqrt_mul_sqrt_self _ (hM l).nonneg, hz, Matrix.trace_zero]
  rw [← CFC.sqrt_mul_sqrt_self (M l) (hM l).nonneg, Matrix.mul_assoc, hroot,
    Matrix.mul_zero]

lemma ensemble_mul_support {L : Type*} [Fintype L]
    (p : L → ℝ) (ρs : L → Matrix C C ℂ)
    (hp : ∀ l, 0 ≤ p l) (hρ : ∀ l, (ρs l).PosSemidef)
    (l : L) (hl : p l ≠ 0) : ρs l * supportProj (avgState p ρs) = ρs l := by
  let M : L → Matrix C C ℂ := fun j => (p j : ℂ) • ρs j
  have hM : ∀ j, (M j).PosSemidef := fun j =>
    (hρ j).smul (Complex.zero_le_real.mpr (hp j))
  have hQ : (∑ j, M j) * (1 - supportProj (avgState p ρs)) = 0 := by
    change avgState p ρs * (1 - supportProj (avgState p ρs)) = 0
    rw [Matrix.mul_sub, Matrix.mul_one, mul_support _ (avgState_posSemidef p ρs hp hρ), sub_self]
  have hz := positive_summand_annihilates M hM _ hQ l
  have hc : (p l : ℂ) ≠ 0 := by exact_mod_cast hl
  have hz' : ρs l * (1 - supportProj (avgState p ρs)) = 0 := by
    apply (smul_eq_zero.mp ?_).resolve_left hc
    simpa only [M, Matrix.smul_mul] using hz
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hz'
  exact hz'.symm

end QReversal.NearOpt.FactorizationProof


open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder BigOperators
noncomputable section
namespace QReversal.NearOpt.FactorizationProof

lemma fidelity_restrict_support {n L ι κ : Type*} [Fintype n] [DecidableEq n]
    [Fintype L] [Fintype ι] [Fintype κ]
    (A : ι → Matrix n n ℂ) (p : L → ℝ) (ρs : L → Matrix n n ℂ)
    (hp : ∀ l, 0 ≤ p l) (hρs : ∀ l, (ρs l).PosSemidef)
    (R : κ → Matrix n n ℂ) :
    Fbar p ρs (comp (fun k => supportProj (avgState p ρs) * R k) A) =
      Fbar p ρs (comp R A) := by
  classical
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : p l = 0
  · simp [hl]
  · apply congrArg (fun z : ℝ => p l * z)
    apply Finset.sum_congr rfl
    intro ki _
    apply congrArg Complex.normSq
    dsimp only [comp]
    have hs := ensemble_mul_support p ρs hp hρs l hl
    calc
      ((supportProj (avgState p ρs) * R ki.1 * A ki.2) * ρs l).trace =
          (supportProj (avgState p ρs) * (R ki.1 * A ki.2 * ρs l)).trace := by
            simp only [Matrix.mul_assoc]
      _ = ((R ki.1 * A ki.2 * ρs l) * supportProj (avgState p ρs)).trace :=
        Matrix.trace_mul_comm _ _
      _ = (R ki.1 * A ki.2 * ρs l).trace := by rw [Matrix.mul_assoc, hs]

lemma restricted_trace_nonincreasing {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]
    (ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef)
    (R : κ → Matrix n n ℂ) (hR : IsTracePreserving R) :
    IsTraceNonincreasing (fun k => supportProj ρ * R k) := by
  have hP := (support_posSemidef ρ hρ).isHermitian.eq
  change (∑ k, (supportProj ρ * R k)ᴴ * (supportProj ρ * R k)) ≤ 1
  calc
    _ = ∑ k, (R k)ᴴ * supportProj ρ * R k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.conjTranspose_mul, hP]
      calc
        (R k)ᴴ * supportProj ρ * (supportProj ρ * R k) =
            (R k)ᴴ * (supportProj ρ * supportProj ρ) * R k := by
              simp only [Matrix.mul_assoc]
        _ = _ := by rw [support_sq ρ hρ]
    _ ≤ ∑ k, (R k)ᴴ * R k := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [star_eq_conjTranspose, Matrix.mul_one] using
        star_left_conjugate_le_conjugate (support_le_one ρ hρ) (R k)
    _ = 1 := hR

lemma factorization_and_bound {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]
    (ρ S : Matrix n n ℂ) (hρ : ρ.PosSemidef) (hS : S.PosDef)
    (R : κ → Matrix n n ℂ) (hR : IsTraceNonincreasing R)
    (hsupport : ∀ k, supportProj ρ * R k = R k) :
    let B : κ → Matrix n n ℂ := fun k => CFC.sqrt S * (R k)ᴴ * invSqrt ρ
    (∀ k, R k = CFC.sqrt ρ * (B k)ᴴ * invSqrt S) ∧ krausUpdate B ρ ≤ S := by
  let B : κ → Matrix n n ℂ := fun k => CFC.sqrt S * (R k)ᴴ * invSqrt ρ
  have hD := (invSqrt_posSemidef ρ hρ).isHermitian.eq
  have hH := (CFC.sqrt_nonneg S).posSemidef.isHermitian.eq
  have hBadj : ∀ k, (B k)ᴴ = invSqrt ρ * R k * CFC.sqrt S := by
    intro k
    simp only [B, Matrix.conjTranspose_mul, hD, hH,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  change (∀ k, R k = CFC.sqrt ρ * (B k)ᴴ * invSqrt S) ∧ krausUpdate B ρ ≤ S
  constructor
  · intro k
    rw [hBadj]
    symm
    calc
      _ = (CFC.sqrt ρ * invSqrt ρ) * R k * (CFC.sqrt S * invSqrt S) := by
        simp only [Matrix.mul_assoc]
      _ = R k := by
        rw [sqrt_mul_invSqrt ρ hρ, sqrt_mul_invSqrt_of_posDef S hS,
          Matrix.mul_one, hsupport k]
  · have hb : krausUpdate B ρ = CFC.sqrt S * (∑ k, (R k)ᴴ * R k) * CFC.sqrt S := by
      rw [krausUpdate, Matrix.mul_sum, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [hBadj]
      change ((CFC.sqrt S * (R k)ᴴ * invSqrt ρ) * ρ) *
        (invSqrt ρ * R k * CFC.sqrt S) = _
      calc
        _ = CFC.sqrt S * (R k)ᴴ * (invSqrt ρ * ρ * invSqrt ρ) * R k *
            CFC.sqrt S := by simp only [Matrix.mul_assoc]
        _ = CFC.sqrt S * ((R k)ᴴ * R k) * CFC.sqrt S := by
          rw [invSqrt_mul_self_mul_invSqrt ρ hρ]
          simp only [Matrix.mul_assoc, hsupport k]
    rw [hb]
    calc
      _ ≤ CFC.sqrt S * 1 * CFC.sqrt S :=
        conjugate_le_conjugate_of_nonneg hR (CFC.sqrt_nonneg S)
      _ = S := by rw [Matrix.mul_one, CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg]

end QReversal.NearOpt.FactorizationProof

open QReversal.NearOpt

theorem native_factorization {n L ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype L] [Fintype ι]
    [Fintype κ]
    (A : ι → Matrix n n ℂ) (p : L → ℝ) (ρs : L → Matrix n n ℂ)
    (hE : IsCommutingEnsemble p ρs) (ρ : Matrix n n ℂ) (hρ : ρ = avgState p ρs)
    (hfull : (krausUpdate A ρ).PosDef)
    (R : κ → Matrix n n ℂ) (hR : IsTracePreserving R) :
    let R' : κ → Matrix n n ℂ := fun k => supportProj ρ * R k
    let B : κ → Matrix n n ℂ := fun k => CFC.sqrt (krausUpdate A ρ) * (R' k)ᴴ * invSqrt ρ
    Fbar p ρs (comp R' A) = Fbar p ρs (comp R A) ∧
    IsTraceNonincreasing R' ∧
    (∀ k, R' k = CFC.sqrt ρ * (B k)ᴴ * invSqrt (krausUpdate A ρ)) ∧
    krausUpdate B ρ ≤ krausUpdate A ρ := by
  have hρpos : ρ.PosSemidef := by
    rw [hρ]
    exact FactorizationProof.avgState_posSemidef p ρs hE.1 (fun l => (hE.2.2.1 l).1)
  let R' : κ → Matrix n n ℂ := fun k => supportProj ρ * R k
  have hR' := FactorizationProof.restricted_trace_nonincreasing ρ hρpos R hR
  refine ⟨?_, hR', ?_⟩
  · rw [hρ]
    exact FactorizationProof.fidelity_restrict_support A p ρs hE.1
      (fun l => (hE.2.2.1 l).1) R
  · apply FactorizationProof.factorization_and_bound ρ (krausUpdate A ρ) hρpos hfull R' hR'
    intro k
    dsimp [R']
    rw [← Matrix.mul_assoc, FactorizationProof.support_sq ρ hρpos]

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

noncomputable section
namespace QReversal.NearOpt.TraceBoundProof

lemma density_trace_bound {n : Type*} [Fintype n]
    (ρ T : Matrix n n ℂ) (hρ : IsDensityMatrix ρ) :
    Complex.normSq (T * ρ).trace ≤ (T * ρ * Tᴴ).trace.re := by
  classical
  let := Matrix.toMatrixSeminormedAddCommGroup ρ hρ.1
  let := Matrix.toMatrixInnerProductSpace ρ hρ.1
  have h := @inner_mul_inner_self_le ℂ (Matrix n n ℂ) _ _ _ (1 : Matrix n n ℂ) T
  change ‖(T * ρ * (1 : Matrix n n ℂ)ᴴ).trace‖ *
      ‖((1 : Matrix n n ℂ) * ρ * Tᴴ).trace‖ ≤
    ((1 : Matrix n n ℂ) * ρ * (1 : Matrix n n ℂ)ᴴ).trace.re *
      (T * ρ * Tᴴ).trace.re at h
  have heq : (ρ * Tᴴ).trace = star (T * ρ).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, hρ.1.isHermitian.eq]
  rw [Complex.normSq_eq_norm_sq, pow_two]
  simpa [heq, hρ.2] using h

lemma trace_sandwich_nonneg {n : Type*} [Fintype n]
    (ρ T : Matrix n n ℂ) (hρ : ρ.PosSemidef) : 0 ≤ (T * ρ * Tᴴ).trace.re :=
  (Complex.nonneg_iff.mp (hρ.mul_mul_conjTranspose_same T).trace_nonneg).1

lemma Fe_le_trace_update {n κ : Type*} [Fintype n] [Fintype κ]
    (ρ : Matrix n n ℂ) (hρ : IsDensityMatrix ρ) (K : κ → Matrix n n ℂ) :
    Fe ρ K ≤ (krausUpdate K ρ).trace.re := by
  simpa only [Fe, krausUpdate, Matrix.trace_sum, Complex.re_sum] using
    Finset.sum_le_sum (s := Finset.univ) (fun k _ => density_trace_bound ρ (K k) hρ)

lemma Fbar_le_weighted_trace {n κ L : Type*} [Fintype n] [Fintype κ] [Fintype L]
    (p : L → ℝ) (hp : ∀ l, 0 ≤ p l) (ρs : L → Matrix n n ℂ)
    (hρs : ∀ l, IsDensityMatrix (ρs l)) (K : κ → Matrix n n ℂ) :
    Fbar p ρs K ≤ ∑ l, p l * (krausUpdate K (ρs l)).trace.re := by
  exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left
    (Fe_le_trace_update (ρs l) (hρs l) K) (hp l)

end QReversal.NearOpt.TraceBoundProof

noncomputable section
open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

namespace QReversal.NearOpt.AmplitudeProof

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma sqrt_hermitian (M : Matrix n n ℂ) : (CFC.sqrt M).IsHermitian :=
  (CFC.sqrt_nonneg M).posSemidef.isHermitian

lemma commute_sqrt_left {M N : Matrix n n ℂ} (h : Commute M N) :
    Commute (CFC.sqrt M) N := by
  rw [CFC.sqrt_eq_cfc]
  exact h.cfc_nnreal NNReal.sqrt

omit [DecidableEq n] in
lemma avgState_commute {L : Type*} [Fintype L]
    (p : L → ℝ) (ρs : L → Matrix n n ℂ)
    (hc : ∀ l j, Commute (ρs l) (ρs j)) (j : L) :
    Commute (avgState p ρs) (ρs j) := by
  change avgState p ρs * ρs j = ρs j * avgState p ρs
  simp only [avgState, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul]
  apply Finset.sum_congr rfl
  intro l _
  rw [(hc l j).eq]

noncomputable def columns {ι : Type*} (X : ι → Matrix n n ℂ) :
    Matrix (n × n) ι ℂ := fun ab i => X i ab.1 ab.2

omit [DecidableEq n] in
lemma columns_gram {ι κ : Type*} (X : κ → Matrix n n ℂ)
    (Y : ι → Matrix n n ℂ) (k : κ) (i : ι) :
    ((columns X)ᴴ * columns Y) k i = ((X k)ᴴ * Y i).trace := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, columns,
    Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply]
  rw [Finset.sum_comm]

omit [DecidableEq n] in
lemma trace_quarter_product (K L T H D ρ A B : Matrix n n ℂ)
    (hK : K.IsHermitian) (hL : L.IsHermitian) (hT : T.IsHermitian)
    (hKK : K * K = H) (hLL : L * L = ρ) (hTT : T * T = D)
    (hcomm : Commute K ρ) :
    ((T * B * K * L)ᴴ * (T * A * K * L)).trace =
      (H * Bᴴ * D * A * ρ).trace := by
  have hfirst :
      (T * B * K * L)ᴴ * (T * A * K * L) =
        L * (K * Bᴴ * D * A * K) * L := by
    simp only [Matrix.conjTranspose_mul, hK.eq, hL.eq, hT.eq, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T T, hTT]
  rw [hfirst]
  calc
    (L * (K * Bᴴ * D * A * K) * L).trace =
        ((K * Bᴴ * D * A * K) * (L * L)).trace := by
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm L ((K * Bᴴ * D * A * K) * L)
    _ = (K * Bᴴ * D * A * (K * ρ)).trace := by rw [hLL]; simp only [Matrix.mul_assoc]
    _ = (K * Bᴴ * D * A * (ρ * K)).trace := by rw [hcomm.eq]
    _ = (K * (K * Bᴴ * D * A * ρ)).trace := by
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm (K * Bᴴ * D * A * ρ) K
    _ = (H * Bᴴ * D * A * ρ).trace := by
      simp only [← Matrix.mul_assoc, hKK]

noncomputable def twist {ι : Type*} (H D : Matrix n n ℂ)
    (X : ι → Matrix n n ℂ) : ι → Matrix n n ℂ :=
  fun i => H * (X i)ᴴ * D

lemma gram_fidelity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K T H D ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef)
    (hK : K.IsHermitian) (hT : T.IsHermitian)
    (hKK : K * K = H) (hTT : T * T = D) (hcomm : Commute K ρ)
    (X : κ → Matrix n n ℂ) (Y : ι → Matrix n n ℂ) :
    GramProof.frobSq
      ((columns (fun k => T * X k * K * CFC.sqrt ρ))ᴴ *
        columns (fun i => T * Y i * K * CFC.sqrt ρ)) =
      Fe ρ (comp (twist H D X) Y) := by
  simp only [GramProof.frobSq, Fe, Fintype.sum_prod_type, comp]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  rw [columns_gram]
  congr 1
  exact trace_quarter_product K (CFC.sqrt ρ) T H D ρ (Y i) (X k)
    hK (sqrt_hermitian ρ) hT hKK (CFC.sqrt_mul_sqrt_self ρ hρ.nonneg) hTT hcomm

lemma weighted_fidelity_cauchy {L ι κ : Type*}
    [Fintype L] [Fintype ι] [Fintype κ]
    (p : L → ℝ) (hp : ∀ l, 0 ≤ p l) (ρs : L → Matrix n n ℂ)
    (hρs : ∀ l, (ρs l).PosSemidef)
    (K T H D : Matrix n n ℂ) (hK : K.IsHermitian) (hT : T.IsHermitian)
    (hKK : K * K = H) (hTT : T * T = D)
    (hcomm : ∀ l, Commute K (ρs l))
    (X : κ → Matrix n n ℂ) (Y : ι → Matrix n n ℂ) :
    Fbar p ρs (comp (twist H D X) Y) ^ 2 ≤
      Fbar p ρs (comp (twist H D X) X) *
        Fbar p ρs (comp (twist H D Y) Y) := by
  have h := GramProof.weighted_gram_cauchy p hp
    (fun l => columns (fun k => T * X k * K * CFC.sqrt (ρs l)))
    (fun l => columns (fun i => T * Y i * K * CFC.sqrt (ρs l)))
  simpa only [gram_fidelity K T H D _ (hρs _) hK hT hKK hTT (hcomm _), Fbar] using h

lemma recovery_cauchy {L ι κ : Type*} [Fintype L] [Fintype ι] [Fintype κ]
    (p : L → ℝ) (hp : ∀ l, 0 ≤ p l) (ρs : L → Matrix n n ℂ)
    (hρs : ∀ l, (ρs l).PosSemidef) (ρ S : Matrix n n ℂ)
    (hcomm : ∀ l, Commute ρ (ρs l)) (hD : (invSqrt S).PosSemidef)
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ) :
    Fbar p ρs (comp (twist (CFC.sqrt ρ) (invSqrt S) B) A) ^ 2 ≤
      Fbar p ρs (comp (twist (CFC.sqrt ρ) (invSqrt S) B) B) *
        Fbar p ρs (comp (twist (CFC.sqrt ρ) (invSqrt S) A) A) := by
  apply weighted_fidelity_cauchy p hp ρs hρs
    (CFC.sqrt (CFC.sqrt ρ)) (CFC.sqrt (invSqrt S)) (CFC.sqrt ρ) (invSqrt S)
    (sqrt_hermitian _) (sqrt_hermitian _)
    (CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg ρ))
    (CFC.sqrt_mul_sqrt_self _ hD.nonneg)
    (fun l => commute_sqrt_left (commute_sqrt_left (hcomm l)))

end QReversal.NearOpt.AmplitudeProof

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

noncomputable section
namespace QReversal.NearOpt.NormalizationProof

variable {n ι κ L : Type*} [Fintype n] [Fintype ι] [Fintype κ]

lemma update_posSemidef (A : ι → Matrix n n ℂ) {X : Matrix n n ℂ}
    (hX : X.PosSemidef) : (krausUpdate A X).PosSemidef := by
  exact Matrix.posSemidef_sum _ fun i _ => hX.mul_mul_conjTranspose_same (A i)

lemma update_sub (A : ι → Matrix n n ℂ) (X Y : Matrix n n ℂ) :
    krausUpdate A (X-Y) = krausUpdate A X - krausUpdate A Y := by
  simp [krausUpdate, mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma update_mono (A : ι → Matrix n n ℂ) {X Y : Matrix n n ℂ} (h : X ≤ Y) :
    krausUpdate A X ≤ krausUpdate A Y := by
  rw [Matrix.le_iff] at h ⊢
  rw [← update_sub]
  exact update_posSemidef A h

lemma trace_re_mono {X Y : Matrix n n ℂ} (h : X ≤ Y) : X.trace.re ≤ Y.trace.re := by
  have hp := (Matrix.le_iff.mp h).trace_nonneg
  have hr := (Complex.nonneg_iff.mp hp).1
  simpa only [Matrix.trace_sub, Complex.sub_re, sub_nonneg] using hr

/- Reused from the inspected accepted proof 090ebed5-52f3-4f18-8273-d47470c08eb3
   (QReversal.PGMBound.theorem_5), also frozen in PGM2_Completion.lean.
   The proof applies without a positive-definiteness assumption. -/
lemma trace_psd_product_nonneg {X Z : Matrix n n ℂ}
    (hX : X.PosSemidef) (hZ : Z.PosSemidef) : 0 ≤ (X*Z).trace.re := by
  classical
  have hs : (CFC.sqrt X).PosSemidef := (CFC.sqrt_nonneg X).posSemidef
  have hp := hZ.mul_mul_conjTranspose_same (CFC.sqrt X)
  rw [hs.isHermitian.eq] at hp
  have ht := hp.trace_nonneg
  have heq : (CFC.sqrt X * Z * CFC.sqrt X).trace = (X*Z).trace := by
    rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self X hX.nonneg]
  rw [heq] at ht
  exact (Complex.nonneg_iff.mp ht).1

lemma trace_update (A : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    (krausUpdate A X).trace = ((∑ i, (A i)ᴴ * A i) * X).trace := by
  simp only [krausUpdate, Matrix.trace_sum, Finset.sum_mul]
  congr 1
  funext i
  rw [Matrix.trace_mul_cycle]

lemma trace_update_tp [DecidableEq n] (A : ι → Matrix n n ℂ) (hA : IsTracePreserving A)
    (X : Matrix n n ℂ) : (krausUpdate A X).trace = X.trace := by
  rw [trace_update, hA, one_mul]

lemma trace_update_tni [DecidableEq n] (A : ι → Matrix n n ℂ) (hA : IsTraceNonincreasing A)
    {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    (krausUpdate A X).trace.re ≤ X.trace.re := by
  have ht := trace_psd_product_nonneg (Matrix.le_iff.mp hA) hX
  rw [sub_mul, one_mul, Matrix.trace_sub, Complex.sub_re, ← trace_update] at ht
  linarith

lemma avg_density [Fintype L] (p : L → ℝ) (X : L → Matrix n n ℂ)
    (hp : ∀ l, 0 ≤ p l) (hp1 : ∑ l, p l = 1)
    (hX : ∀ l, IsDensityMatrix (X l)) : IsDensityMatrix (avgState p X) := by
  constructor
  · apply Matrix.posSemidef_sum
    intro l _
    exact (hX l).1.smul (by exact_mod_cast hp l)
  · simp only [avgState, Matrix.trace_sum, Matrix.trace_smul, (hX _).2, smul_eq_mul, mul_one]
    exact_mod_cast hp1

lemma update_sum [Fintype L] (A : ι → Matrix n n ℂ) (X : L → Matrix n n ℂ) :
    krausUpdate A (∑ l, X l) = ∑ l, krausUpdate A (X l) := by
  simp only [krausUpdate, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

lemma update_smul (A : ι → Matrix n n ℂ) (c : ℂ) (X : Matrix n n ℂ) :
    krausUpdate A (c • X) = c • krausUpdate A X := by
  simp [krausUpdate, Finset.smul_sum]

lemma trace_update_composite (R : κ → Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (X : Matrix n n ℂ) :
    (krausUpdate R (krausUpdate B X)).trace.re =
      ∑ i, ∑ j, (R i * B j * X * (B j)ᴴ * (R i)ᴴ).trace.re := by
  simp [krausUpdate, Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum, mul_assoc]

lemma trace_composite_avg [Fintype L] (R : κ → Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (p : L → ℝ) (X : L → Matrix n n ℂ) :
    (krausUpdate R (krausUpdate B (avgState p X))).trace.re =
      ∑ l, p l * (krausUpdate R (krausUpdate B (X l))).trace.re := by
  simp only [avgState, update_sum, update_smul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]

end QReversal.NearOpt.NormalizationProof

namespace QReversal.NearOpt.RootProof
open AmplitudeProof NormalizationProof TraceBoundProof

lemma update_comp {n ι κ : Type*} [Fintype n] [Fintype ι] [Fintype κ]
    (R : κ → Matrix n n ℂ) (A : ι → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    krausUpdate (comp R A) ρ = krausUpdate R (krausUpdate A ρ) := by
  simp only [krausUpdate, comp, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
    Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]

lemma Fbar_nonneg {n L κ : Type*} [Fintype n] [Fintype L] [Fintype κ]
    (p : L → ℝ) (hp : ∀ l, 0 ≤ p l) (ρs : L → Matrix n n ℂ)
    (R : κ → Matrix n n ℂ) : 0 ≤ Fbar p ρs R :=
  Finset.sum_nonneg fun l _ => mul_nonneg (hp l)
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

lemma bound_of_factor {n L ι κ : Type*} [Fintype n] [DecidableEq n]
    [Fintype L] [Fintype ι] [Fintype κ]
    (A : ι → Matrix n n ℂ) (hA : IsTracePreserving A)
    (p : L → ℝ) (ρs : L → Matrix n n ℂ) (hE : IsCommutingEnsemble p ρs)
    (ρ : Matrix n n ℂ) (hρ : ρ = avgState p ρs) (hfull : (krausUpdate A ρ).PosDef)
    (R' B : κ → Matrix n n ℂ) (hR' : IsTraceNonincreasing R')
    (hfactor : ∀ k, R' k = CFC.sqrt ρ * (B k)ᴴ * invSqrt (krausUpdate A ρ))
    (hBA : krausUpdate B ρ ≤ krausUpdate A ρ) :
    Fbar p ρs (comp R' A) ^ 2 ≤ Fbar p ρs (comp (reversal A ρ) A) := by
  have hden : IsDensityMatrix ρ := hρ ▸ avg_density p ρs hE.1 hE.2.1 hE.2.2.1
  have hcomm (l : L) : Commute ρ (ρs l) := by
    rw [hρ]
    exact avgState_commute p ρs hE.2.2.2 l
  have ht : twist (CFC.sqrt ρ) (invSqrt (krausUpdate A ρ)) B = R' :=
    funext fun k => (hfactor k).symm
  have hc := recovery_cauchy p hE.1 ρs (fun l => (hE.2.2.1 l).1)
    ρ (krausUpdate A ρ) hcomm
    (FactorizationProof.invSqrt_posSemidef _ hfull.posSemidef) A B
  rw [ht] at hc
  change Fbar p ρs (comp R' A) ^ 2 ≤
    Fbar p ρs (comp R' B) * Fbar p ρs (comp (reversal A ρ) A) at hc
  have hb : Fbar p ρs (comp R' B) ≤ 1 := by
    calc
      _ ≤ ∑ l, p l * (krausUpdate (comp R' B) (ρs l)).trace.re :=
        Fbar_le_weighted_trace p hE.1 ρs hE.2.2.1 (comp R' B)
      _ = (krausUpdate R' (krausUpdate B ρ)).trace.re := by
        simp only [update_comp]
        rw [hρ, trace_composite_avg]
      _ ≤ (krausUpdate R' (krausUpdate A ρ)).trace.re :=
        trace_re_mono (update_mono R' hBA)
      _ ≤ (krausUpdate A ρ).trace.re :=
        trace_update_tni R' hR' (update_posSemidef A hden.1)
      _ = 1 := by rw [trace_update_tp A hA, hden.2]; rfl
  exact hc.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hb (Fbar_nonneg p hE.1 ρs (comp (reversal A ρ) A)))

end QReversal.NearOpt.RootProof

open QReversal.NearOpt

/-- Original Theorem 3: the canonical reversal is near optimal for a commuting
ensemble, including zero weights and singular average input states. -/
theorem solution {n L ι : Type*} [Fintype n] [DecidableEq n] [Fintype L] [Fintype ι]
    (A : ι → Matrix n n ℂ) (hA : IsTracePreserving A)
    (p : L → ℝ) (ρs : L → Matrix n n ℂ) (hE : IsCommutingEnsemble p ρs)
    (ρ : Matrix n n ℂ) (hρ : ρ = avgState p ρs) (hfull : (krausUpdate A ρ).PosDef)
    {κ : Type*} [Fintype κ] (R : κ → Matrix n n ℂ) (hR : IsTracePreserving R) :
    Fbar p ρs (comp R A) ^ 2 ≤ Fbar p ρs (comp (reversal A ρ) A) := by
  obtain ⟨hfid, hR', hfactor, hBA⟩ := native_factorization A p ρs hE ρ hρ hfull R hR
  rw [← hfid]
  exact RootProof.bound_of_factor A hA p ρs hE ρ hρ hfull _ _ hR' hfactor hBA
