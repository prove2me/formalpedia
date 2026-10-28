-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P67.actualMarginalStrongConverse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:08:33.194287+00:00
-- url     : https://prove2.me/submissions/3e5344c7-6ded-40b3-a81d-ae8395be7a34

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67

namespace S173A


section rf
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma sqrt_herm (X : Matrix I I ℂ) : (cfc Real.sqrt X).IsHermitian :=
  (cfc_predicate (R := ℝ) (p := IsSelfAdjoint) _ X)

lemma rf_nonneg (X Y : Matrix I I ℂ) : 0 ≤ rootFidelity X Y := by
  unfold rootFidelity
  have : (cfc Real.sqrt (cfc Real.sqrt X * Y * cfc Real.sqrt X)).PosSemidef := by
    open scoped MatrixOrder in
    rw [← Matrix.nonneg_iff_posSemidef]
    exact cfc_nonneg fun x _ => Real.sqrt_nonneg x
  exact (Complex.nonneg_iff.mp this.trace_nonneg).1

end rf

section bound
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma psd_le_norm (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    (((‖K‖ : ℝ) : ℂ) • (1 : Matrix I I ℂ) - K).PosSemidef := by
  have h := IsSelfAdjoint.le_algebraMap_norm_self (a := K) hK.1.isSelfAdjoint
  rw [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] at h
  simpa [Complex.coe_smul] using h

lemma spec_nonneg' {X : Matrix I I ℂ} (hX : X.PosSemidef) {x : ℝ} (hx : x ∈ spectrum ℝ X) : 0 ≤ x :=
  spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hX) hx

lemma sqrt_sq_psd (Y : Matrix I I ℂ) (hY : Y.PosSemidef) : cfc Real.sqrt Y * cfc Real.sqrt Y = Y := by
  rw [← cfc_mul _ _ Y (Matrix.finite_real_spectrum.continuousOn _) (Matrix.finite_real_spectrum.continuousOn _)]
  conv_rhs => rw [← cfc_id' ℝ Y]
  refine cfc_congr fun x hx => ?_
  exact Real.mul_self_sqrt (spec_nonneg' hY hx)

lemma rf_bound (X Y : Matrix I I ℂ) (hY : Y.PosSemidef) :
    rootFidelity X Y ≤ Fintype.card I + ‖cfc Real.sqrt X * cfc Real.sqrt X‖ * Y.trace.re := by
  set S := cfc Real.sqrt X with hS
  have hSh : S.IsHermitian := sqrt_herm X
  set Z := S * Y * S with hZ
  have hZp : Z.PosSemidef := by
    have := hY.conjTranspose_mul_mul_same S
    rwa [hSh.eq] at this
  -- step 1: tr √Z ≤ card + tr Z
  have h1 : rootFidelity X Y ≤ Fintype.card I + Z.trace.re := by
    unfold rootFidelity
    rw [← hS, ← hZ]
    have hle : cfc Real.sqrt Z ≤ cfc (fun x : ℝ => 1 + x) Z := by
      apply cfc_mono (fun x hx => ?_) (Matrix.finite_real_spectrum.continuousOn _)
        (Matrix.finite_real_spectrum.continuousOn _)
      have hx0 := spec_nonneg' hZp hx
      have hs := Real.sq_sqrt hx0
      have := Real.sqrt_nonneg x
      nlinarith
    rw [cfc_add Z (fun _ : ℝ => (1 : ℝ)) (fun x : ℝ => x) (Matrix.finite_real_spectrum.continuousOn _)
      (Matrix.finite_real_spectrum.continuousOn _), cfc_const (1 : ℝ) Z, map_one, cfc_id' ℝ Z] at hle
    have := (Matrix.le_iff.mp hle).trace_nonneg
    rw [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_one] at this
    have := (Complex.nonneg_iff.mp this).1
    simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re] at this
    linarith
  -- step 2: tr Z ≤ ‖S S‖ tr Y
  have h2 : Z.trace.re ≤ ‖S * S‖ * Y.trace.re := by
    have hW : (S * S).PosSemidef := by
      have := Matrix.posSemidef_conjTranspose_mul_self S
      rwa [hSh.eq] at this
    set R := cfc Real.sqrt Y
    have hRh : R.IsHermitian := sqrt_herm Y
    have hRR : R * R = Y := sqrt_sq_psd Y hY
    have hp := (psd_le_norm _ hW).conjTranspose_mul_mul_same R
    rw [hRh.eq] at hp
    have ht := (Complex.nonneg_iff.mp hp.trace_nonneg).1
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hRR,
      Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul] at ht
    have hZt : Z.trace = (R * (S * S) * R).trace := by
      rw [hZ, ← hRR, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    rw [hZt]; linarith
  have := Complex.nonneg_iff.mp hY.trace_nonneg
  linarith

end bound



section p67
variable {A B E : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

lemma tl_psd {α β : Type*} [Fintype α] [Fintype β] {M : Matrix (α × β) (α × β) ℂ}
    (hM : M.PosSemidef) : (traceLeft M).PosSemidef := by
  classical
  have : traceLeft M = ∑ a : α, M.submatrix (fun b => (a, b)) (fun b => (a, b)) := by
    ext b b'
    simp [traceLeft, Matrix.sum_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ (fun a _ => hM.submatrix _)

lemma tl_trace {α β : Type*} [Fintype α] [Fintype β] (M : Matrix (α × β) (α × β) ℂ) :
    (traceLeft M).trace = M.trace := by
  simp only [Matrix.trace, traceLeft, Matrix.diag, Matrix.of_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

lemma dil_iso (U : Matrix (B × E) A ℂ) (hU : IsIsometry U) (n : ℕ) :
    (dilationPower U n)ᴴ * dilationPower U n = 1 := by
  ext a a'
  have hU' : ∀ x y : A, ∑ z : B × E, star (U z x) * U z y = (1 : Matrix A A ℂ) x y := by
    intro x y
    rw [← hU]; simp [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dilationPower]
  have e1 : ∀ be : (Fin n → B) × (Fin n → E),
      star (∏ i, U (be.1 i, be.2 i) (a i)) * ∏ i, U (be.1 i, be.2 i) (a' i) =
      ∏ i, (star (U (be.1 i, be.2 i) (a i)) * U (be.1 i, be.2 i) (a' i)) := by
    intro be
    rw [star_prod, ← Finset.prod_mul_distrib]
  simp_rw [e1]
  rw [← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => B) (fun _ => E)).sum_comp]
  have := (Finset.prod_univ_sum (fun (_ : Fin n) => (Finset.univ : Finset (B × E)))
    (fun i z => star (U z (a i)) * U z (a' i))).symm
  rw [Fintype.piFinset_univ] at this
  refine Eq.trans ?_ (this.trans ?_)
  · rfl
  simp_rw [hU']
  by_cases h : a = a'
  · subst h; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Matrix.one_apply_ne hi])

lemma env_eq (U : Matrix (B × E) A ℂ) {n : ℕ} (code : PrivateCode A B n) (hc : code.Valid) :
    environmentMarginal U code = ((code.M : ℂ)⁻¹) • ∑ m : Fin code.M,
      traceLeft (dilationPower U n * code.messages m * (dilationPower U n)ᴴ) := by
  have hsum : ∀ c b, ∑ j, code.measurement j c b = (1 : Matrix (Fin n → B) (Fin n → B) ℂ) c b := by
    intro c b
    rw [← hc.2.2.2, Matrix.sum_apply]
  ext e f
  simp only [environmentMarginal, traceLeft, jointOutput, messageOutput, Matrix.of_apply, if_true,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  have h1 : ∀ c, ∑ j, code.measurement j c b *
      (dilationPower U n * code.messages m * (dilationPower U n)ᴴ) (b, e) (c, f) =
      (1 : Matrix (Fin n → B) (Fin n → B) ℂ) c b *
      (dilationPower U n * code.messages m * (dilationPower U n)ᴴ) (b, e) (c, f) := by
    intro c; rw [← Finset.sum_mul, hsum]
  rw [Finset.sum_congr rfl fun c _ => h1 c]
  simp [Matrix.one_apply]

lemma env_dens (U : Matrix (B × E) A ℂ) (hU : IsIsometry U) {n : ℕ} (code : PrivateCode A B n)
    (hc : code.Valid) : IsDensityMatrix (environmentMarginal U code) := by
  rw [env_eq U code hc]
  set W := dilationPower U n
  have hM : (0 : ℝ) < code.M := by exact_mod_cast hc.1
  refine ⟨?_, ?_⟩
  · have e : ((code.M : ℂ)⁻¹) = (((code.M : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [e]
    refine Matrix.PosSemidef.smul (Matrix.posSemidef_sum _ fun m _ => tl_psd ?_) (by positivity)
    exact (hc.2.1 m).1.mul_mul_conjTranspose_same W
  · rw [Matrix.trace_smul, Matrix.trace_sum]
    have : ∀ m, (traceLeft (W * code.messages m * Wᴴ)).trace = 1 := by
      intro m
      rw [tl_trace, Matrix.trace_mul_comm, ← Matrix.mul_assoc, dil_iso U hU n, Matrix.one_mul,
        (hc.2.1 m).2]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      smul_eq_mul]
    exact inv_mul_cancel₀ (by exact_mod_cast hc.1.ne')

lemma ij_psd {K : ℕ} (σ : Matrix E E ℂ) (hσ : IsDensityMatrix σ) :
    (idealJoint K σ).PosSemidef ∧ (idealJoint K σ).trace.re ≤ 1 := by
  set d : Fin K × Fin K → ℂ := fun p => if p.1 = p.2 then ((K : ℝ)⁻¹ : ℝ) else 0
  have hd : (Matrix.diagonal d).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro p
    simp only [d]
    split_ifs
    · exact_mod_cast (inv_nonneg.mpr (Nat.cast_nonneg K))
    · exact le_refl _
  have e : idealJoint K σ = (Matrix.kroneckerMap (· * ·) (Matrix.diagonal d) σ).submatrix
      (fun a : Fin K × (Fin K × E) => ((a.1, a.2.1), a.2.2))
      (fun a : Fin K × (Fin K × E) => ((a.1, a.2.1), a.2.2)) := by
    ext a b
    simp only [idealJoint, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.diagonal_apply, d,
      Prod.mk.injEq]
    by_cases h1 : a.1 = b.1 <;> by_cases h2 : a.2.1 = b.2.1 <;> by_cases h3 : a.1 = a.2.1 <;>
      by_cases h4 : b.1 = b.2.1 <;> simp_all <;> grind
  refine ⟨e ▸ (hd.kronecker hσ.1).submatrix _, ?_⟩
  have ht : (idealJoint K σ).trace = ∑ m : Fin K, ((K : ℂ)⁻¹ * σ.trace) := by
    simp only [Matrix.trace, Matrix.diag, idealJoint, Fintype.sum_prod_type, and_self]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_eq_single m]
    · simp [Finset.mul_sum]
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  rw [ht, hσ.2]
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos K with h | h
  · subst h; simp
  · have : (K : ℂ) * (K : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast h.ne')
    rw [this]; simp

end p67

end S173A

variable {A B E R S T X C Y G1 G2 : Type*}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]
variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]
variable [Fintype G2] [DecidableEq G2]

open S173A in
open scoped Matrix.Norms.L2Operator in
theorem solution [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsIsometry U)
    (q gap gamma : ℝ) (hgap : 0 < gap) (hgamma : 0 < gamma) (n0 : ℕ)
    (hdecay : OptimizedDecay U q gap gamma n0) :
    ∀ n ≥ n0, ∀ code : PrivateCode A B n, code.Valid →
      (n : ℝ) * (q + gap) ≤ Real.logb 2 code.M →
      marginalFidelity U code ≤ Real.rpow 2 (-gamma * n) ∧
      1 - Real.rpow 2 (-gamma * n) ≤ marginalError U code := by
  intro n hn code hc hrate
  have hopt := hdecay n hn code hc hrate
  set J := jointOutput U code
  set Cst : ℝ := Fintype.card (Fin code.M × (Fin code.M × (Fin n → E))) +
    ‖cfc Real.sqrt J * cfc Real.sqrt J‖ * 1
  have hbdd : BddAbove {r | ∃ sigma : Matrix (Fin n → E) (Fin n → E) ℂ,
      IsDensityMatrix sigma ∧ r = squaredFidelity J (idealJoint code.M sigma)} := by
    refine ⟨Cst ^ 2, ?_⟩
    rintro r ⟨σ, hσ, rfl⟩
    obtain ⟨hp, ht⟩ := ij_psd (K := code.M) σ hσ
    have h1 := rf_bound J (idealJoint code.M σ) hp
    have h0 := rf_nonneg J (idealJoint code.M σ)
    have hn : 0 ≤ ‖cfc Real.sqrt J * cfc Real.sqrt J‖ := norm_nonneg _
    have h2 : rootFidelity J (idealJoint code.M σ) ≤ Cst := by
      simp only [Cst]; nlinarith
    unfold squaredFidelity
    exact pow_le_pow_left₀ h0 h2 2
  have hle : marginalFidelity U code ≤ optimizedFidelity U code :=
    le_csSup hbdd ⟨environmentMarginal U code, env_dens U hU code hc, rfl⟩
  refine ⟨le_trans hle hopt, ?_⟩
  unfold marginalError
  linarith [le_trans hle hopt]
