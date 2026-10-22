-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P11.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:31:07.131366+00:00
-- url     : https://prove2.me/submissions/12c3a922-5c60-4942-b8f4-ab45d6d5c384

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P11
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P11

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open scoped MatrixOrder

lemma g73q_sqrt_psd {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) :
    (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma g73q_sqrt_mul_sqrt {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ}
    (hQ : Q.PosSemidef) : cfc Real.sqrt Q * cfc Real.sqrt Q = Q := by
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [← cfc_mul Real.sqrt Real.sqrt Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma g73q_tr_psd_mul {n : Type*} [Fintype n] [DecidableEq n] {P Q : Matrix n n ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace.re := by
  have hR : (cfc Real.sqrt Q)ᴴ = cfc Real.sqrt Q := (g73q_sqrt_psd Q).1.eq
  have h := (hP.conjTranspose_mul_mul_same (cfc Real.sqrt Q)).trace_nonneg
  rw [hR, Matrix.trace_mul_comm, ← Matrix.mul_assoc, g73q_sqrt_mul_sqrt hQ,
    Matrix.trace_mul_comm] at h
  exact (Complex.nonneg_iff.mp h).1

lemma g73q_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
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

lemma g73q_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma g73q_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

/-- sign witness with both 1 - Z and 1 + Z positive -/
lemma g73q_sign {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∃ Z : Matrix n n ℂ, (1 - Z).PosSemidef ∧ (1 + Z).PosSemidef ∧
      (Z * H).trace.re = QAlgorithms.traceNorm H := by
  have hsa : IsSelfAdjoint H := hH.isSelfAdjoint
  have hfin := H.finite_real_spectrum
  set g : ℝ → ℝ := fun t => if 0 ≤ t then 1 else -1 with hg
  refine ⟨cfc g H, ?_, ?_, ?_⟩
  · have : 1 - cfc g H = cfc (fun t => 1 - g t) H := by
      rw [cfc_sub (fun _ => (1:ℝ)) g H (hfin.continuousOn _) (hfin.continuousOn _), cfc_const_one ℝ H]
    rw [this]; apply g73q_cfc_psd; intro t; simp only [hg]; split_ifs <;> norm_num
  · have : 1 + cfc g H = cfc (fun t => 1 + g t) H := by
      rw [cfc_add H (fun _ => (1:ℝ)) g (hfin.continuousOn _) (hfin.continuousOn _), cfc_const_one ℝ H]
    rw [this]; apply g73q_cfc_psd; intro t; simp only [hg]; split_ifs <;> norm_num
  · rw [g73q_traceNorm_herm hH, ← Complex.add_re, ← Matrix.trace_add,
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
lemma g73q_abs_tr_le {n : Type*} [Fintype n] [DecidableEq n] {Z E : Matrix n n ℂ}
    (h1 : (1 - Z).PosSemidef) (h2 : (1 + Z).PosSemidef) (hE : E.PosSemidef) :
    |(Z * E).trace.re| ≤ E.trace.re := by
  have a := g73q_tr_psd_mul h1 hE
  have b := g73q_tr_psd_mul h2 hE
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at a
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, Complex.add_re] at b
  rw [abs_le]; constructor <;> linarith

/-- diagonal entries are dominated by the trace norm -/
lemma g73q_diag_le {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : M.IsHermitian) : ∑ i, |(M i i).re| ≤ QAlgorithms.traceNorm M := by
  rw [g73q_traceNorm_herm hM]
  set P := cfc (fun t : ℝ => max t 0) M
  set N := cfc (fun t : ℝ => max (-t) 0) M
  have hP : P.PosSemidef := g73q_cfc_psd M _ (fun t => le_max_right _ _)
  have hN : N.PosSemidef := g73q_cfc_psd M _ (fun t => le_max_right _ _)
  have hPN : P - N = M := g73q_parts M hM
  rw [← hPN]
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have a : 0 ≤ (P i i).re := (Complex.nonneg_iff.mp hP.diag_nonneg).1
  have b : 0 ≤ (N i i).re := (Complex.nonneg_iff.mp hN.diag_nonneg).1
  rw [Matrix.sub_apply, Complex.sub_re, abs_le]; constructor <;> linarith

/-- a PSD matrix is dominated by its trace -/
lemma g73q_le_trace {n : Type*} [Fintype n] [DecidableEq n] {S : Matrix n n ℂ}
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


lemma g73q_re_tr_le {n : Type*} [Fintype n] [DecidableEq n] {Z H : Matrix n n ℂ}
    (h1 : (1 - Z).PosSemidef) (h2 : (1 + Z).PosSemidef) (hH : H.IsHermitian) :
    (Z * H).trace.re ≤ QAlgorithms.traceNorm H := by
  rw [g73q_traceNorm_herm hH]
  have hP : (cfc (fun t : ℝ => max t 0) H).PosSemidef := g73q_cfc_psd H _ (fun t => le_max_right _ _)
  have hN : (cfc (fun t : ℝ => max (-t) 0) H).PosSemidef := g73q_cfc_psd H _ (fun t => le_max_right _ _)
  have a := g73q_abs_tr_le h1 h2 hP
  have b := g73q_abs_tr_le h1 h2 hN
  conv_lhs => rw [← g73q_parts H hH]
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  have := le_abs_self ((Z * cfc (fun t : ℝ => max t 0) H).trace.re)
  have := neg_abs_le ((Z * cfc (fun t : ℝ => max (-t) 0) H).trace.re)
  linarith

lemma g73q_herm_smul {n : Type*} {S : Matrix n n ℂ} (hS : S.IsHermitian) (a : ℝ) :
    (((a : ℂ)) • S).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hS.eq]
  simp [Complex.conj_ofReal]

lemma g73q_tr_real {n : Type*} [Fintype n] {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    S.trace = ((S.trace.re : ℝ) : ℂ) := by
  have h := Complex.nonneg_iff.mp hS.trace_nonneg
  apply Complex.ext
  · simp
  · simp [h.2]

lemma g73q_tr_nonneg {n : Type*} [Fintype n] {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    0 ≤ S.trace.re := (Complex.nonneg_iff.mp hS.trace_nonneg).1

section g73qBlocks
variable {C E : Type*} [Fintype C] [Fintype E]

def g73q_E (c : C) : Matrix E (C × E) ℂ := fun e a => if a.1 = c ∧ a.2 = e then 1 else 0

lemma g73q_E_mul (c : C) : (g73q_E (E := E) c) * (g73q_E (E := E) c)ᴴ = 1 := by
  ext e e'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g73q_E, Matrix.one_apply]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
  · by_cases h : e = e' <;> simp [h, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

def g73q_emb (c : C) (S : Matrix E E ℂ) : Matrix (C × E) (C × E) ℂ :=
  (g73q_E (E := E) c)ᴴ * S * g73q_E (E := E) c

lemma g73q_emb_apply (c : C) (S : Matrix E E ℂ) (a b : C × E) :
    g73q_emb c S a b = if a.1 = c ∧ b.1 = c then S a.2 b.2 else 0 := by
  simp only [g73q_emb, Matrix.mul_apply, Matrix.conjTranspose_apply, g73q_E]
  by_cases ha : a.1 = c <;> by_cases hb : b.1 = c <;>
    simp [ha, hb, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]

lemma g73q_emb_trace (c : C) (S : Matrix E E ℂ) : (g73q_emb c S).trace = S.trace := by
  rw [g73q_emb, Matrix.trace_mul_comm, ← Matrix.mul_assoc, g73q_E_mul, Matrix.one_mul]

lemma g73q_emb_psd (c : C) {S : Matrix E E ℂ} (hS : S.PosSemidef) : (g73q_emb c S).PosSemidef :=
  hS.conjTranspose_mul_mul_same _

lemma g73q_emb_smul (c : C) (z : ℂ) (S : Matrix E E ℂ) :
    g73q_emb c (z • S) = z • g73q_emb c S := by
  simp [g73q_emb, Matrix.mul_smul, Matrix.smul_mul]

lemma g73q_block_eq_sum (r : CQProbabilityBlocks C E) :
    blockMatrix r = ∑ c, g73q_emb c (r c) := by
  ext a b
  rw [Matrix.sum_apply, Finset.sum_eq_single a.1]
  · rw [g73q_emb_apply]; simp only [blockMatrix]
    by_cases h : a.1 = b.1
    · simp [h]
    · simp [h, Ne.symm h]
  · intro c _ hc; rw [g73q_emb_apply, if_neg]; rintro ⟨h, -⟩; exact hc h.symm
  · intro h; exact absurd (Finset.mem_univ _) h

lemma g73q_block_sub (r s : CQProbabilityBlocks C E) :
    blockMatrix r - blockMatrix s = blockMatrix (fun c => r c - s c) := by
  ext a b; simp only [blockMatrix, Matrix.sub_apply]; split_ifs <;> simp

lemma g73q_block_add (r s : CQProbabilityBlocks C E) :
    blockMatrix (fun c => r c + s c) = blockMatrix r + blockMatrix s := by
  ext a b; simp only [blockMatrix, Matrix.add_apply]; split_ifs <;> simp

lemma g73q_block_herm {r : CQProbabilityBlocks C E} (h : ∀ c, (r c).IsHermitian) :
    (blockMatrix r).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, blockMatrix]
  by_cases hab : a.1 = b.1
  · rw [if_pos hab, if_pos hab.symm, hab, ← Matrix.conjTranspose_apply, (h b.1).eq]
  · rw [if_neg hab, if_neg (Ne.symm hab)]; simp

lemma g73q_block_psd_part {r : CQProbabilityBlocks C E} (hr : IsNormalizedCQ r) (c : C) :
    (r c).PosSemidef := by
  have h := hr.1.mul_mul_conjTranspose_same (g73q_E (E := E) c)
  convert h using 1
  ext e e'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g73q_E, blockMatrix]
  rw [Finset.sum_eq_single (c, e')]
  · rw [Finset.sum_eq_single (c, e)]
    · simp
    · intro b _ hb
      have : ¬ (b.1 = c ∧ b.2 = e) := fun h => hb (Prod.ext h.1 h.2)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    have : ¬ (b.1 = c ∧ b.2 = e') := fun h => hb (Prod.ext h.1 h.2)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma g73q_push_psd {D : Type*} {r : CQProbabilityBlocks C E} (hr : IsNormalizedCQ r)
    (g : C → D) (d : D) : (classicalPushforward r g d).PosSemidef := by
  unfold classicalPushforward
  apply Matrix.posSemidef_sum
  intro c _
  split_ifs
  · exact g73q_block_psd_part hr c
  · exact Matrix.PosSemidef.zero

lemma g73q_block_smul_le [DecidableEq (C × E)] {Z : Matrix (C × E) (C × E) ℂ}
    (h1 : (1 - Z).PosSemidef) (h2 : (1 + Z).PosSemidef)
    (a : C → ℝ) (S : C → Matrix E E ℂ) (hS : ∀ c, (S c).PosSemidef) :
    (Z * blockMatrix (fun c => (a c : ℂ) • S c)).trace.re ≤ ∑ c, |a c| * (S c).trace.re := by
  rw [g73q_block_eq_sum, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro c _
  rw [g73q_emb_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hb := g73q_abs_tr_le h1 h2 (g73q_emb_psd c (hS c))
  rw [g73q_emb_trace] at hb
  calc a c * (Z * g73q_emb c (S c)).trace.re ≤ |a c| * |(Z * g73q_emb c (S c)).trace.re| := by
        rw [← abs_mul]; exact le_abs_self _
    _ ≤ |a c| * (S c).trace.re := mul_le_mul_of_nonneg_left hb (abs_nonneg _)

lemma g73q_block_tr_le [DecidableEq (C × E)] (d : CQProbabilityBlocks C E)
    (h : ∀ c, (d c).IsHermitian) :
    ∑ c, |(d c).trace.re| ≤ QAlgorithms.traceNorm (blockMatrix d) := by
  refine le_trans ?_ (g73q_diag_le (g73q_block_herm h))
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro c _
  simp only [blockMatrix, if_true, Matrix.trace, Matrix.diag, Complex.re_sum]
  exact Finset.abs_sum_le_sum_abs _ _

end g73qBlocks

section g73qMain
variable {C D E : Type*} [Fintype C] [Fintype E]

lemma g73q_markov_le (r : CQProbabilityBlocks C E) (hr : IsNormalizedCQ r) (g : C → D)
    (α : C → ℝ) :
    cqDistance r (conditionalMarkovReconstruction r g) ≤
      2 * cqDistance r (fun c => (α c : ℂ) • classicalPushforward r g (g c)) := by
  set ρ := classicalPushforward r g with hρ
  set β : C → ℝ := fun c => classicalLabelMass r c / classicalLabelMass ρ (g c) with hβ
  have hcmr : conditionalMarkovReconstruction r g = fun c => (β c : ℂ) • ρ (g c) := rfl
  have hρpsd : ∀ d, (ρ d).PosSemidef := fun d => g73q_push_psd hr g d
  have hrpsd : ∀ c, (r c).PosSemidef := fun c => g73q_block_psd_part hr c
  set F : CQProbabilityBlocks C E := fun c => r c - (α c : ℂ) • ρ (g c) with hF
  set G : CQProbabilityBlocks C E := fun c => (((α c - β c : ℝ)) : ℂ) • ρ (g c) with hG
  have hFh : ∀ c, (F c).IsHermitian := fun c =>
    (hrpsd c).1.sub (g73q_herm_smul (hρpsd (g c)).1 (α c))
  have hDeq : (fun c => r c - (β c : ℂ) • ρ (g c)) = fun c => F c + G c := by
    funext c; simp only [hF, hG]; push_cast; rw [sub_smul]; abel
  have hDh : (blockMatrix (fun c => F c + G c)).IsHermitian :=
    g73q_block_herm (fun c => (hFh c).add (g73q_herm_smul (hρpsd (g c)).1 _))
  unfold cqDistance QAlgorithms.traceDistance
  rw [hcmr, g73q_block_sub, g73q_block_sub, hDeq]
  obtain ⟨Z, h1, h2, hZ⟩ := g73q_sign hDh
  rw [← hZ, g73q_block_add, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  have e1 := g73q_re_tr_le h1 h2 (g73q_block_herm hFh)
  have e2 := g73q_block_smul_le h1 h2 (fun c => α c - β c) (fun c => ρ (g c)) (fun c => hρpsd (g c))
  have e3 := g73q_block_tr_le F hFh
  have e4 : ∑ c, |α c - β c| * (ρ (g c)).trace.re ≤ ∑ c, |(F c).trace.re| := by
    apply Finset.sum_le_sum
    intro c _
    have hq := g73q_tr_nonneg (hρpsd (g c))
    simp only [hF, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, Complex.sub_re,
      Complex.re_ofReal_mul]
    rcases eq_or_lt_of_le hq with h0 | hpos
    · rw [← h0]; simp [abs_nonneg]
    · have : |α c - β c| * (ρ (g c)).trace.re = |(r c).trace.re - α c * (ρ (g c)).trace.re| := by
        rw [← abs_of_pos hpos, ← abs_mul, abs_of_pos hpos, ← abs_neg]
        congr 1
        simp only [hβ, classicalLabelMass]
        field_simp
        ring
      rw [this]
  linarith

end g73qMain

lemma g73q_isom {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (J : Matrix m n ℂ) (hJ : J * Jᴴ = 1) (M : Matrix m m ℂ) (hM : M.IsHermitian) :
    QAlgorithms.traceNorm (Jᴴ * M * J) ≤ QAlgorithms.traceNorm M := by
  have hH : (Jᴴ * M * J).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hM.eq, Matrix.mul_assoc]
  obtain ⟨Z, h1, h2, hZ⟩ := g73q_sign hH
  rw [← hZ]
  have e : (Z * (Jᴴ * M * J)).trace = ((J * Z * Jᴴ) * M).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [e]
  apply g73q_re_tr_le _ _ hM
  · have := h1.mul_mul_conjTranspose_same J
    rwa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJ] at this
  · have := h2.mul_mul_conjTranspose_same J
    rwa [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hJ] at this

section g73q22
variable {X Y T E : Type*} [Fintype X] [Fintype Y] [Fintype T] [Fintype E]

def g73q_J (f : X → Y → T) : Matrix ((X × Y) × E) (((X × T) × Y) × E) ℂ :=
  fun a b => if a = ((b.1.1.1, b.1.2), b.2) ∧ b.1.1.2 = f b.1.1.1 b.1.2 then 1 else 0

lemma g73q_J_mul (f : X → Y → T) : g73q_J (E := E) f * (g73q_J (E := E) f)ᴴ = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g73q_J, Matrix.one_apply]
  rw [Finset.sum_eq_single (((a.1.1, f a.1.1 a.1.2), a.1.2), a.2)]
  · by_cases hab : a = b
    · subst hab; simp
    · have h1 : ¬ (b = ((a.1.1, a.1.2), a.2) ∧ f a.1.1 a.1.2 = f a.1.1 a.1.2) := by
        rintro ⟨h, -⟩; exact hab (by rw [h])
      rw [if_neg hab, if_neg h1]; simp
  · intro a' _ ha'
    have : ¬ (a = ((a'.1.1.1, a'.1.2), a'.2) ∧ a'.1.1.2 = f a'.1.1.1 a'.1.2) := by
      rintro ⟨h1, h2⟩
      apply ha'
      subst h1
      simp only
      rw [← h2]
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma g73q_block_append (s : CQProbabilityBlocks (X × Y) E) (f : X → Y → T) :
    blockMatrix (appendClassicalFunction s f) =
      (g73q_J (E := E) f)ᴴ * blockMatrix s * g73q_J (E := E) f := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g73q_J]
  rw [Finset.sum_eq_single ((b.1.1.1, b.1.2), b.2)]
  · rw [Finset.sum_eq_single ((a.1.1.1, a.1.2), a.2)]
    · by_cases ha : a.1.1.2 = f a.1.1.1 a.1.2
      · by_cases hb : b.1.1.2 = f b.1.1.1 b.1.2
        · have key : a.1 = b.1 ↔ (a.1.1.1, a.1.2) = (b.1.1.1, b.1.2) := by
            constructor
            · intro h; rw [h]
            · intro h
              simp only [Prod.mk.injEq] at h
              exact Prod.ext (Prod.ext h.1 (by rw [ha, hb, h.1, h.2])) h.2
          simp only [ha, hb, and_true, if_true, star_one, one_mul, mul_one]
          simp only [blockMatrix, appendClassicalFunction]
          by_cases h : a.1 = b.1
          · rw [if_pos h, if_pos (key.mp h), if_pos ha]
          · rw [if_neg h, if_neg (fun h' => h (key.mpr h'))]
        · have : ¬ a.1 = b.1 := by
            intro h; rw [h] at ha; exact hb ha
          simp only [blockMatrix, appendClassicalFunction, if_neg this, hb, and_false, if_false,
            mul_zero]
      · simp [blockMatrix, appendClassicalFunction, ha]
    · intro a' _ ha'; simp [ha']
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b' _ hb'; simp [hb']
  · intro h; exact absurd (Finset.mem_univ _) h

lemma g73q_push_append (r : CQProbabilityBlocks (X × Y) E) (f : X → Y → T) (y : Y) :
    classicalPushforward (appendClassicalFunction r f) Prod.snd y =
      classicalPushforward r Prod.snd y := by
  unfold classicalPushforward appendClassicalFunction
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y' _
  by_cases hy : y' = y
  · simp [hy]
  · simp [hy]

lemma g73q_cmr_append (r : CQProbabilityBlocks (X × Y) E) (f : X → Y → T) :
    conditionalMarkovReconstruction (appendClassicalFunction r f) Prod.snd =
      appendClassicalFunction (conditionalMarkovReconstruction r Prod.snd) f := by
  funext c
  unfold conditionalMarkovReconstruction
  simp only [classicalLabelMass]
  rw [g73q_push_append]
  unfold appendClassicalFunction
  by_cases h : c.1.2 = f c.1.1 c.2
  · simp [h]
  · simp [h, classicalLabelMass]

end g73q22

/-- Lemma 2.2, PDF p.4; Appendix A.2, PDF p.19. The added register is computed
from both X and Y; the error remains eps. The comparison state is reconstructed
from the augmented state's own marginals, rather than an arbitrary Markov witness. -/
theorem solution
    {X Y T E : Type*} [Fintype X] [Fintype Y] [Fintype T] [Fintype E]
    [Nonempty X] [Nonempty Y] [Nonempty E]
    (r : CQProbabilityBlocks (X × Y) E) (hr : IsNormalizedCQ r) (f : X → Y → T)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hclose : cqDistance r (conditionalMarkovReconstruction r Prod.snd) ≤ eps) :
    cqDistance (appendClassicalFunction r f) (conditionalMarkovReconstruction (appendClassicalFunction r f) Prod.snd) ≤ eps := by
  have hrpsd : ∀ c, (r c).PosSemidef := fun c => g73q_block_psd_part hr c
  have hDh : ∀ c, (r c - conditionalMarkovReconstruction r Prod.snd c).IsHermitian := fun c =>
    (hrpsd c).1.sub (g73q_herm_smul (g73q_push_psd hr Prod.snd c.2).1 _)
  have happ : (fun c => appendClassicalFunction r f c -
      appendClassicalFunction (conditionalMarkovReconstruction r Prod.snd) f c) =
      appendClassicalFunction (fun c => r c - conditionalMarkovReconstruction r Prod.snd c) f := by
    funext c; unfold appendClassicalFunction; split_ifs <;> simp
  refine le_trans ?_ hclose
  unfold cqDistance QAlgorithms.traceDistance
  rw [g73q_cmr_append, g73q_block_sub, g73q_block_sub, happ, g73q_block_append]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  convert g73q_isom _ (g73q_J_mul f) _ (g73q_block_herm hDh) using 2
  all_goals rfl



end
