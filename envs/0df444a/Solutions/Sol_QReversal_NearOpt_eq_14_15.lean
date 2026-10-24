-- Prove2me | solution 1 for QReversal.NearOpt.eq_14_15
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T18:06:53.332983+00:00
-- url     : https://prove2.me/submissions/c527faf4-2768-45ff-b9b2-551a5ae42c75

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_QReversal_NearOpt_Setting

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

theorem solution {n L ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype L] [Fintype ι]
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
