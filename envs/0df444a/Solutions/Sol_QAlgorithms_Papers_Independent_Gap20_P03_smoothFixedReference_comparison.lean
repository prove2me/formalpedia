-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P03.smoothFixedReference_comparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:06:00.544182+00:00
-- url     : https://prove2.me/submissions/dc196089-2ddc-486e-8c57-5b1c595d8e62

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

open QAlgorithms
open scoped Matrix MatrixOrder

lemma g73a_sqrt_psd {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) :
    (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma g73a_sqrt_mul_sqrt {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ}
    (hQ : Q.PosSemidef) : cfc Real.sqrt Q * cfc Real.sqrt Q = Q := by
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [← cfc_mul Real.sqrt Real.sqrt Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma g73a_tr_psd_mul {n : Type*} [Fintype n] [DecidableEq n] {P Q : Matrix n n ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace.re := by
  have hR : (cfc Real.sqrt Q)ᴴ = cfc Real.sqrt Q := (g73a_sqrt_psd Q).1.eq
  have h := (hP.conjTranspose_mul_mul_same (cfc Real.sqrt Q)).trace_nonneg
  rw [hR, Matrix.trace_mul_comm, ← Matrix.mul_assoc, g73a_sqrt_mul_sqrt hQ,
    Matrix.trace_mul_comm] at h
  exact (Complex.nonneg_iff.mp h).1

lemma g73a_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) :
    QAlgorithms.traceNorm X =
      (cfc (fun t : ℝ => max t 0) X).trace.re + (cfc (fun t : ℝ => max (-t) 0) X).trace.re := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  unfold QAlgorithms.traceNorm
  rw [hX.eq]
  have h1 : X * X = cfc (fun t : ℝ => t * t) X := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) X, cfc_id' ℝ X]
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) X, ← Complex.add_re, ← Matrix.trace_add,
    ← cfc_add X (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
  congr 2
  apply cfc_congr
  intro t _
  simp only [Function.comp]
  rw [← sq, Real.sqrt_sq_eq_abs]
  rcases le_total t 0 with h | h
  · rw [abs_of_nonpos h]; simp [h]
  · rw [abs_of_nonneg h]; simp [h]

lemma g73a_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma g73a_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

/-- sign witness with both 1 - Z and 1 + Z positive -/
lemma g73a_sign {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∃ Z : Matrix n n ℂ, (1 - Z).PosSemidef ∧ (1 + Z).PosSemidef ∧
      (Z * H).trace.re = QAlgorithms.traceNorm H := by
  have hsa : IsSelfAdjoint H := hH.isSelfAdjoint
  have hfin := H.finite_real_spectrum
  set g : ℝ → ℝ := fun t => if 0 ≤ t then 1 else -1 with hg
  refine ⟨cfc g H, ?_, ?_, ?_⟩
  · have : 1 - cfc g H = cfc (fun t => 1 - g t) H := by
      rw [cfc_sub (fun _ => (1:ℝ)) g H (hfin.continuousOn _) (hfin.continuousOn _), cfc_const_one ℝ H]
    rw [this]; apply g73a_cfc_psd; intro t; simp only [hg]; split_ifs <;> norm_num
  · have : 1 + cfc g H = cfc (fun t => 1 + g t) H := by
      rw [cfc_add H (fun _ => (1:ℝ)) g (hfin.continuousOn _) (hfin.continuousOn _), cfc_const_one ℝ H]
    rw [this]; apply g73a_cfc_psd; intro t; simp only [hg]; split_ifs <;> norm_num
  · rw [g73a_traceNorm_herm hH, ← Complex.add_re, ← Matrix.trace_add,
      ← cfc_add H (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
    have : cfc g H * H = cfc (fun t => g t * t) H := by
      rw [cfc_mul g (fun t : ℝ => t) H (hfin.continuousOn _) (hfin.continuousOn _), cfc_id' ℝ H]
    rw [this]
    congr 3
    funext t
    simp only [hg]
    rcases le_total 0 t with h | h
    · simp [h]
    · rcases eq_or_lt_of_le h with h' | h'
      · simp [h']
      · simp [not_le.mpr h', h'.le]

/-- |Re tr(Z E)| ≤ Re tr E for a contraction Z and PSD E -/
lemma g73a_abs_tr_le {n : Type*} [Fintype n] [DecidableEq n] {Z E : Matrix n n ℂ}
    (h1 : (1 - Z).PosSemidef) (h2 : (1 + Z).PosSemidef) (hE : E.PosSemidef) :
    |(Z * E).trace.re| ≤ E.trace.re := by
  have a := g73a_tr_psd_mul h1 hE
  have b := g73a_tr_psd_mul h2 hE
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at a
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, Complex.add_re] at b
  rw [abs_le]; constructor <;> linarith

/-- diagonal entries are dominated by the trace norm -/
lemma g73a_diag_le {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : M.IsHermitian) : ∑ i, |(M i i).re| ≤ QAlgorithms.traceNorm M := by
  rw [g73a_traceNorm_herm hM]
  set P := cfc (fun t : ℝ => max t 0) M
  set N := cfc (fun t : ℝ => max (-t) 0) M
  have hP : P.PosSemidef := g73a_cfc_psd M _ (fun t => le_max_right _ _)
  have hN : N.PosSemidef := g73a_cfc_psd M _ (fun t => le_max_right _ _)
  have hPN : P - N = M := g73a_parts M hM
  rw [← hPN]
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have a : 0 ≤ (P i i).re := (Complex.nonneg_iff.mp hP.diag_nonneg).1
  have b : 0 ≤ (N i i).re := (Complex.nonneg_iff.mp hN.diag_nonneg).1
  rw [Matrix.sub_apply, Complex.sub_re, abs_le]; constructor <;> linarith

/-- a PSD matrix is dominated by its trace -/
lemma g73a_le_trace {n : Type*} [Fintype n] [DecidableEq n] {S : Matrix n n ℂ}
    (hS : S.PosSemidef) : (((S.trace.re : ℝ) : ℂ) • (1 : Matrix n n ℂ) - S).PosSemidef := by
  have hsa : IsSelfAdjoint S := hS.1.isSelfAdjoint
  have key : S ≤ algebraMap ℝ (Matrix n n ℂ) S.trace.re := by
    rw [le_algebraMap_iff_spectrum_le]
    intro x hx
    rw [hS.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [hS.1.trace_eq_sum_eigenvalues]
    simp only [Complex.re_sum]
    exact Finset.single_le_sum (fun j _ => hS.eigenvalues_nonneg j) (Finset.mem_univ i)
  rw [← sub_nonneg, Matrix.nonneg_iff_posSemidef, Algebra.algebraMap_eq_smul_one] at key
  rw [show ((S.trace.re:ℂ) • (1:Matrix n n ℂ)) = S.trace.re • (1 : Matrix n n ℂ) from by
    ext i j; simp [Complex.real_smul]]
  exact key

section g73aBlocks
variable {X U Q : Type*} [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype Q] [DecidableEq Q]

def g73a_blockDiag (B : X × U → Matrix Q Q ℂ) : Matrix ((X × Q) × U) ((X × Q) × U) ℂ :=
  fun a b => if a.1.1 = b.1.1 ∧ a.2 = b.2 then B (a.1.1, a.2) a.1.2 b.1.2 else 0

def g73a_emb (d : X × U) (S : Matrix Q Q ℂ) : Matrix ((X × Q) × U) ((X × Q) × U) ℂ :=
  fun a b => if (a.1.1, a.2) = d ∧ (b.1.1, b.2) = d then S a.1.2 b.1.2 else 0

def g73a_P (d : X × U) : Matrix Q ((X × Q) × U) ℂ :=
  fun q a => if (a.1.1, a.2) = d ∧ a.1.2 = q then 1 else 0

lemma g73a_emb_eq (d : X × U) (S : Matrix Q Q ℂ) :
    g73a_emb d S = ((g73a_P d : Matrix Q ((X × Q) × U) ℂ))ᴴ * S * (g73a_P d : Matrix Q ((X × Q) × U) ℂ) := by
  ext a b
  simp only [g73a_emb, g73a_P, Matrix.mul_apply, Matrix.conjTranspose_apply]
  by_cases ha : (a.1.1, a.2) = d <;> by_cases hb : (b.1.1, b.2) = d <;>
    simp [ha, hb, Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma g73a_emb_psd (d : X × U) {S : Matrix Q Q ℂ} (hS : S.PosSemidef) :
    (g73a_emb d S).PosSemidef := by
  rw [g73a_emb_eq]; exact hS.conjTranspose_mul_mul_same _

lemma g73a_blockDiag_eq_sum (B : X × U → Matrix Q Q ℂ) :
    g73a_blockDiag B = ∑ d, g73a_emb d (B d) := by
  ext a b
  rw [Matrix.sum_apply, Finset.sum_eq_single (a.1.1, a.2)]
  · unfold g73a_blockDiag g73a_emb
    by_cases h : a.1.1 = b.1.1 ∧ a.2 = b.2
    · rw [if_pos h, if_pos ⟨rfl, Prod.ext h.1.symm h.2.symm⟩]
    · rw [if_neg h, if_neg]; rintro ⟨-, h1⟩
      exact h ⟨(congrArg Prod.fst h1).symm, (congrArg Prod.snd h1).symm⟩
  · intro d _ hd; simp only [g73a_emb]; rw [if_neg]; rintro ⟨h, -⟩; exact hd h.symm
  · intro h; exact absurd (Finset.mem_univ _) h

lemma g73a_blockDiag_psd {B : X × U → Matrix Q Q ℂ} (hB : ∀ d, (B d).PosSemidef) :
    (g73a_blockDiag B).PosSemidef := by
  rw [g73a_blockDiag_eq_sum]
  have : ∀ s : Finset (X × U), (∑ d ∈ s, g73a_emb d (B d)).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using Matrix.PosSemidef.zero
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact (g73a_emb_psd a (hB a)).add ih
  exact this _

lemma g73a_emb_trace (d : X × U) (S : Matrix Q Q ℂ) : (g73a_emb d S).trace = S.trace := by
  simp only [Matrix.trace, Matrix.diag, g73a_emb, and_self]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single d.1]
  · rw [Finset.sum_comm, Finset.sum_eq_single d.2]
    · apply Finset.sum_congr rfl; intro q _; simp
    · intro u _ hu; apply Finset.sum_eq_zero; intro q _; rw [if_neg]; intro h; exact hu (congrArg Prod.snd h)
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro x _ hx; apply Finset.sum_eq_zero; intro q _; apply Finset.sum_eq_zero; intro u _
    rw [if_neg]; intro h; exact hx (congrArg Prod.fst h)
  · intro h; exact absurd (Finset.mem_univ _) h

lemma g73a_blockDiag_trace (B : X × U → Matrix Q Q ℂ) :
    (g73a_blockDiag B).trace = ∑ d, (B d).trace := by
  rw [g73a_blockDiag_eq_sum, Matrix.trace_sum]
  simp only [g73a_emb_trace]

lemma g73a_blockDiag_sub (B C : X × U → Matrix Q Q ℂ) :
    g73a_blockDiag B - g73a_blockDiag C = g73a_blockDiag (fun d => B d - C d) := by
  ext a b; simp only [g73a_blockDiag, Matrix.sub_apply]; split_ifs <;> simp

/-- trace-norm bound for real combinations of subnormalized PSD blocks -/
lemma g73a_blockDiag_traceNorm (c : X × U → ℝ) (S : X × U → Matrix Q Q ℂ)
    (hS : ∀ d, (S d).PosSemidef) (hS1 : ∀ d, (S d).trace.re ≤ 1)
    (hH : (g73a_blockDiag (fun d => (c d : ℂ) • S d)).IsHermitian) :
    QAlgorithms.traceNorm (g73a_blockDiag (fun d => (c d : ℂ) • S d)) ≤ ∑ d, |c d| := by
  obtain ⟨Z, h1, h2, hZ⟩ := g73a_sign hH
  rw [← hZ, g73a_blockDiag_eq_sum, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro d _
  have he : g73a_emb d ((c d : ℂ) • S d) = (c d : ℂ) • g73a_emb d (S d) := by
    ext a b; simp only [g73a_emb, Matrix.smul_apply]; split_ifs <;> simp
  rw [he, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hb := g73a_abs_tr_le h1 h2 (g73a_emb_psd d (hS d))
  rw [g73a_emb_trace] at hb
  calc c d * (Z * g73a_emb d (S d)).trace.re ≤ |c d| * |(Z * g73a_emb d (S d)).trace.re| := by
        rw [← abs_mul]; exact le_abs_self _
    _ ≤ |c d| * 1 := mul_le_mul_of_nonneg_left (hb.trans (hS1 d)) (abs_nonneg _)
    _ = |c d| := mul_one _

end g73aBlocks

/-- Lemma A.3, p.19: smoothed comparison with the ORIGINAL rho_U fixed on
both sides. The cited historical smoothing definition is verified in [28],
Definition 3.2.1; its reference operator is not replaced by the smoothed marginal.
The source proof's change to sigma_U is unnecessary for the stated inequality. -/
theorem solution {X U Q : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X] [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (blocks : (X × U) → Matrix Q Q ℂ) (hblocks : IsNormalizedCQBlocks blocks)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    smoothFixedMin (cqClassicalOperator blocks) (referenceMarginal blocks) epsilon ≤
      smoothFixedMin (reorderedCQ blocks) (referenceMarginal blocks) epsilon := by
  have eX : ‹DecidableEq X› = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  have eU : ‹DecidableEq U› = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  have eQ : ‹DecidableEq Q› = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  subst eX eU eQ
  obtain ⟨hpsd, htr1⟩ := hblocks
  set t : X × U → ℂ := fun d => (blocks d).trace with ht
  set shat : X × U → Matrix Q Q ℂ := fun d => (((t d).re⁻¹ : ℝ) : ℂ) • blocks d with hshat
  have ht_nonneg : ∀ d, 0 ≤ t d := fun d => (hpsd d).trace_nonneg
  have ht_re : ∀ d, 0 ≤ (t d).re := fun d => (Complex.nonneg_iff.mp (ht_nonneg d)).1
  have ht_real : ∀ d, t d = ((t d).re : ℂ) := fun d => by
    have := Complex.nonneg_iff.mp (ht_nonneg d)
    apply Complex.ext <;> simp [this.2.symm]
  have hshat_psd : ∀ d, (shat d).PosSemidef := fun d =>
    (hpsd d).smul (Complex.zero_le_real.mpr (inv_nonneg.mpr (ht_re d)))
  have hshat_tr : ∀ d, (shat d).trace.re ≤ 1 := by
    intro d
    simp only [hshat, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    change (t d).re⁻¹ * (t d).re ≤ 1
    by_cases h0 : (t d).re = 0
    · rw [h0]; simp
    · rw [inv_mul_cancel₀ h0]
  have hblocks_eq : ∀ d, blocks d = (((t d).re : ℝ) : ℂ) • shat d := by
    intro d
    by_cases h0 : (t d).re = 0
    · have : (blocks d).trace = 0 := by
        have := ht_real d; rw [h0] at this; simpa [ht] using this
      rw [(hpsd d).trace_eq_zero_iff.mp this, h0]; simp
    · simp only [hshat, smul_smul]
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ h0]; simp
  have hone_sub : ∀ d, (1 - shat d).PosSemidef := by
    intro d
    by_cases h0 : (t d).re = 0
    · have : shat d = 0 := by simp [hshat, h0]
      rw [this, sub_zero]; exact Matrix.PosSemidef.one
    · have h1 : (shat d).trace.re = 1 := by
        simp only [hshat, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
        change (t d).re⁻¹ * (t d).re = 1
        rw [inv_mul_cancel₀ h0]
      have := g73a_le_trace (hshat_psd d)
      rw [h1] at this; simpa using this
  have hreord : reorderedCQ blocks = g73a_blockDiag blocks := by
    ext a b; unfold reorderedCQ g73a_blockDiag; split_ifs <;> rfl
  have hrho_psd : (cqClassicalOperator blocks).PosSemidef := by
    unfold cqClassicalOperator; exact Matrix.PosSemidef.diagonal (fun d => ht_nonneg d)
  have hreord_psd : (reorderedCQ blocks).PosSemidef := by
    rw [hreord]; exact g73a_blockDiag_psd hpsd
  have htr_eq : (reorderedCQ blocks).trace.re = (cqClassicalOperator blocks).trace.re := by
    rw [hreord, g73a_blockDiag_trace]; unfold cqClassicalOperator; rw [Matrix.trace_diagonal]
  unfold smoothFixedMin
  apply sSup_le
  rintro _ ⟨τ, hτ, hτtr, hτn, rfl⟩
  have hτd : ∀ d, 0 ≤ (τ d d).re := fun d => (Complex.nonneg_iff.mp hτ.diag_nonneg).1
  set τ' := g73a_blockDiag (fun d => (((τ d d).re : ℝ) : ℂ) • shat d) with hτ'
  have hτ'_psd : τ'.PosSemidef :=
    g73a_blockDiag_psd (fun d => (hshat_psd d).smul (Complex.zero_le_real.mpr (hτd d)))
  apply le_sSup_of_le (b := fixedMin τ' (referenceMarginal blocks))
  · refine ⟨τ', hτ'_psd, ?_, ?_, rfl⟩
    · rw [htr_eq, hτ', g73a_blockDiag_trace]
      refine le_trans ?_ hτtr
      rw [Complex.re_sum, Matrix.trace, Complex.re_sum]
      apply Finset.sum_le_sum; intro d _
      rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      exact mul_le_of_le_one_right (hτd d) (hshat_tr d)
    · rw [htr_eq]
      refine le_trans ?_ hτn
      have hdiff : τ' - reorderedCQ blocks = g73a_blockDiag
          (fun d => ((((τ d d).re - (t d).re : ℝ)) : ℂ) • shat d) := by
        rw [hreord, hτ', g73a_blockDiag_sub]
        congr 1; funext d
        rw [hblocks_eq d, ← sub_smul]; push_cast; rfl
      rw [hdiff]
      refine le_trans (g73a_blockDiag_traceNorm _ _ hshat_psd hshat_tr ?_) ?_
      · rw [← hdiff]; exact hτ'_psd.1.sub hreord_psd.1
      · refine le_trans (le_of_eq ?_) (g73a_diag_le (hτ.1.sub hrho_psd.1))
        apply Finset.sum_congr rfl; intro d _
        unfold cqClassicalOperator
        rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, Complex.sub_re]
  · unfold fixedMin
    apply sSup_le_sSup
    rintro _ ⟨r, rfl, hr⟩
    refine ⟨r, rfl, ?_⟩
    set c : ℝ := Real.rpow 2 (-r) with hc
    have hc0 : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
    set sr : U → ℝ := fun u => ∑ x, (t (x, u)).re with hsr
    have hsig : ∀ u, referenceMarginal blocks u u = ((sr u : ℝ) : ℂ) := by
      intro u; unfold referenceMarginal; rw [Matrix.diagonal_apply_eq]
      simp only [hsr]; push_cast
      exact Finset.sum_congr rfl (fun x _ => ht_real (x, u))
    have hsig_off : ∀ u u', u ≠ u' → referenceMarginal blocks u u' = 0 := by
      intro u u' h; unfold referenceMarginal; rw [Matrix.diagonal_apply_ne _ h]
    have hdiagle : ∀ d, (τ d d).re ≤ c * sr d.2 := by
      rintro ⟨x, u⟩
      have h := hr.diag_nonneg (i := (x, u))
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
      rw [show Matrix.kronecker (1 : Matrix X X ℂ) (referenceMarginal blocks) (x, u) (x, u) =
        (1 : Matrix X X ℂ) x x * referenceMarginal blocks u u from rfl, Matrix.one_apply_eq,
        one_mul, hsig] at h
      have := (Complex.nonneg_iff.mp h).1
      simp only [Complex.sub_re, ← Complex.ofReal_mul, Complex.ofReal_re] at this
      linarith
    have heq : ((c : ℝ) : ℂ) • Matrix.kronecker (1 : Matrix (X × Q) (X × Q) ℂ)
        (referenceMarginal blocks) - τ' =
        g73a_blockDiag (fun d => (((c * sr d.2 : ℝ)) : ℂ) • (1 : Matrix Q Q ℂ) -
          (((τ d d).re : ℝ) : ℂ) • shat d) := by
      ext ⟨⟨x, q⟩, u⟩ ⟨⟨x', q'⟩, u'⟩
      rw [hτ']
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.kronecker_apply, g73a_blockDiag,
        smul_eq_mul]
      by_cases h2 : u = u'
      · subst h2
        by_cases h1 : x = x'
        · subst h1
          by_cases h3 : q = q'
          · subst h3; simp [hsig]
          · simp [Matrix.one_apply, h3, hsig]
        · simp [Matrix.one_apply, h1]
      · simp [hsig_off _ _ h2, h2]
    show ((c : ℝ) : ℂ) • Matrix.kronecker (1 : Matrix (X × Q) (X × Q) ℂ)
        (referenceMarginal blocks) - τ' |>.PosSemidef
    rw [heq]
    apply g73a_blockDiag_psd
    intro d
    have e : (((c * sr d.2 : ℝ)) : ℂ) • (1 : Matrix Q Q ℂ) - (((τ d d).re : ℝ) : ℂ) • shat d =
        (((c * sr d.2 - (τ d d).re : ℝ)) : ℂ) • (1 : Matrix Q Q ℂ) +
          (((τ d d).re : ℝ) : ℂ) • (1 - shat d) := by
      rw [smul_sub]; push_cast; rw [sub_smul]; abel
    rw [e]
    apply Matrix.PosSemidef.add
    · exact Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by linarith [hdiagle d]))
    · exact (hone_sub d).smul (Complex.zero_le_real.mpr (hτd d))


end
