-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P28.tomography_spans
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:47:40.738762+00:00
-- url     : https://prove2.me/submissions/b137b7e3-3492-43b9-9289-f30542c4a533

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace X7T
open Matrix

lemma psd {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n ℂ) (hT : T.IsHermitian)
    (c : ℝ) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| ≤ ε → ((c:ℂ) • (1 : Matrix n n ℂ) + (t:ℂ) • T).PosSemidef := by
  set ev := hT.eigenvalues
  set S := ∑ i, |ev i| + 1 with hSdef
  have hS : 0 < S := by positivity
  refine ⟨c / S, div_pos hc hS, fun t ht => ?_⟩
  set U : Matrix n n ℂ := (hT.eigenvectorUnitary : Matrix n n ℂ)
  have hu : U * star U = 1 := Unitary.mul_star_self_of_mem hT.eigenvectorUnitary.2
  have key : (c:ℂ) • (1 : Matrix n n ℂ) + (t:ℂ) • T =
      U * diagonal (fun i => ((c + t * ev i : ℝ) : ℂ)) * Uᴴ := by
    have hd : diagonal (fun i => ((c + t * ev i : ℝ) : ℂ)) =
        (c:ℂ) • 1 + (t:ℂ) • diagonal (RCLike.ofReal ∘ ev) := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [h, Matrix.one_apply]
    conv_lhs => rw [hT.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.star_eq_conjTranspose, hu]
  rw [key]
  apply PosSemidef.mul_mul_conjTranspose_same
  apply PosSemidef.diagonal
  intro i
  simp only [Pi.zero_apply]
  rw [Complex.zero_le_real]
  have h1 : |ev i| ≤ S := by
    have : |ev i| ≤ ∑ j, |ev j| :=
      Finset.single_le_sum (f := fun j => |ev j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  have h2 : |t * ev i| ≤ c := by
    rw [abs_mul]
    calc |t| * |ev i| ≤ (c / S) * S := by
          apply mul_le_mul ht h1 (abs_nonneg _) (by positivity)
      _ = c := by field_simp
  have := neg_abs_le (t * ev i)
  linarith

variable {d : ℕ}

abbrev tL (R : Op (ChoiBasis d)) : Op (Fin d) := QAlgorithms.traceLeft R

lemma onOp_add (G1 G2 : HSMatrix (ChoiBasis d)) (A : Op (ChoiBasis d)) :
    onOperator (G1 + G2) A = onOperator G1 A + onOperator G2 A := by
  ext i j; simp [onOperator, add_mul, Finset.sum_add_distrib]

lemma onOp_sub (G1 G2 : HSMatrix (ChoiBasis d)) (A : Op (ChoiBasis d)) :
    onOperator (G1 - G2) A = onOperator G1 A - onOperator G2 A := by
  ext i j; simp [onOperator, sub_mul, Finset.sum_sub_distrib]

lemma onOp_smul (c : ℂ) (G : HSMatrix (ChoiBasis d)) (A : Op (ChoiBasis d)) :
    onOperator (c • G) A = c • onOperator G A := by
  ext i j; simp [onOperator, mul_assoc, Finset.mul_sum]

lemma pT_add_left (L1 L2 R : Op (Fin d × Fin d)) :
    pairedTensor (L1 + L2) R = pairedTensor L1 R + pairedTensor L2 R := by
  ext p q; simp [pairedTensor, add_mul]

lemma pT_sub_left (L1 L2 R : Op (Fin d × Fin d)) :
    pairedTensor (L1 - L2) R = pairedTensor L1 R - pairedTensor L2 R := by
  ext p q; simp [pairedTensor, sub_mul]

lemma pT_sub_right (L R1 R2 : Op (Fin d × Fin d)) :
    pairedTensor L (R1 - R2) = pairedTensor L R1 - pairedTensor L R2 := by
  ext p q; simp [pairedTensor, mul_sub]

lemma pT_one_one : pairedTensor (1 : Op (Fin d × Fin d)) 1 = (1 : HSMatrix (ChoiBasis d)) := by
  ext p q
  simp only [pairedTensor, Matrix.one_apply]
  obtain ⟨⟨a, b⟩, ⟨c, e⟩⟩ := p
  obtain ⟨⟨a', b'⟩, ⟨c', e'⟩⟩ := q
  simp only [Prod.mk.injEq]
  by_cases h1 : a = a' <;> by_cases h2 : b = b' <;> by_cases h3 : c = c' <;> by_cases h4 : e = e' <;>
    simp [h1, h2, h3, h4]

lemma onOp_11 (A : Op (ChoiBasis d)) : onOperator (pairedTensor 1 1) A = A := by
  rw [pT_one_one]
  ext i j
  simp [onOperator, Matrix.one_apply, Fintype.sum_prod_type]

lemma onOp_W1 (A : Op (ChoiBasis d)) :
    onOperator (pairedTensor (maximallyEntangledDensity d) 1) A =
      Matrix.of (fun i j => (if i.1 = j.1 then (d : ℂ)⁻¹ else 0) * tL A i.2 j.2) := by
  ext i j
  simp [onOperator, pairedTensor, maximallyEntangledDensity, Matrix.one_apply, Fintype.sum_prod_type,
    QAlgorithms.traceLeft]
  by_cases h : i.1 = j.1 <;> simp [h, ite_and, Finset.mul_sum]

lemma onOp_1W (A : Op (ChoiBasis d)) :
    onOperator (pairedTensor 1 (maximallyEntangledDensity d)) A =
      Matrix.of (fun i j => (if i.2 = j.2 then (d : ℂ)⁻¹ else 0) * traceInput A i.1 j.1) := by
  ext i j
  simp [onOperator, pairedTensor, maximallyEntangledDensity, Matrix.one_apply, Fintype.sum_prod_type,
    traceInput]
  by_cases h : i.2 = j.2 <;> simp [h, ite_and, Finset.mul_sum]

lemma onOp_WW (A : Op (ChoiBasis d)) :
    onOperator (pairedTensor (maximallyEntangledDensity d) (maximallyEntangledDensity d)) A =
      Matrix.of (fun i j => (if i.1 = j.1 ∧ i.2 = j.2 then ((d : ℂ)⁻¹ * (d : ℂ)⁻¹) else 0) * A.trace) := by
  ext i j
  simp [onOperator, pairedTensor, maximallyEntangledDensity, Fintype.sum_prod_type, Matrix.trace]
  by_cases h : i.1 = j.1 <;> by_cases h' : i.2 = j.2 <;> simp [h, h', ite_and, Finset.mul_sum, mul_assoc]

lemma Qch : targetProjector d .channels =
    pairedTensor 1 1 - pairedTensor (maximallyEntangledDensity d) 1 +
      pairedTensor (maximallyEntangledDensity d) (maximallyEntangledDensity d) := by
  ext p q
  simp [targetProjector, sector, pairedTensor]
  ring

lemma Qun : targetProjector d .unital =
    pairedTensor 1 1 - pairedTensor (maximallyEntangledDensity d) 1 - pairedTensor 1 (maximallyEntangledDensity d) +
      (2 : ℂ) • pairedTensor (maximallyEntangledDensity d) (maximallyEntangledDensity d) := by
  ext p q
  simp [targetProjector, sector, pairedTensor]
  ring

lemma trace_tL (A : Op (ChoiBasis d)) : (tL A).trace = A.trace := by
  simp [Matrix.trace, QAlgorithms.traceLeft, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma trace_tI (A : Op (ChoiBasis d)) : (traceInput A).trace = A.trace := by
  simp [Matrix.trace, traceInput, Fintype.sum_prod_type]

lemma aux_iff {α : Type*} [AddCommGroup α] (a x y : α) : a - x + y = a ↔ x = y := by
  rw [sub_add_eq_add_sub, sub_eq_iff_eq_add, add_left_cancel_iff, eq_comm]

lemma aux_iff2 {α : Type*} [AddCommGroup α] (a x z y : α) : a - x - z + y = a ↔ x + z = y := by
  rw [sub_sub, aux_iff]

lemma tr_smul_one (c : ℂ) : ((c • (1 : Op (Fin d))).trace) = c * d := by
  simp [Matrix.trace_smul, Matrix.trace_one]

lemma proj_ch (hd : 0 < d) (R : Op (ChoiBasis d)) :
    onOperator (targetProjector d .channels) R = R ↔ ∃ c : ℂ, tL R = c • 1 := by
  have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Qch, onOp_add, onOp_sub, onOp_11, onOp_W1, onOp_WW, aux_iff]
  constructor
  · intro h
    refine ⟨R.trace / d, ?_⟩
    ext b e
    have := congrFun (congrFun h (⟨0,hd⟩, b)) (⟨0,hd⟩, e)
    simp only [Matrix.of_apply] at this
    by_cases hbe : b = e
    · subst hbe; simp at this ⊢; field_simp at this ⊢; linear_combination this
    · simp [hbe] at this ⊢; exact this.resolve_left hd.ne'
  · rintro ⟨c, hc⟩
    have htr : R.trace = c * d := by rw [← trace_tL, hc, tr_smul_one]
    ext i j
    simp only [Matrix.of_apply]
    rw [hc, htr]
    by_cases h1 : i.1 = j.1 <;> by_cases h2 : i.2 = j.2 <;> simp [h1, h2]
    field_simp

lemma proj_un (hd : 0 < d) (R : Op (ChoiBasis d)) :
    onOperator (targetProjector d .unital) R = R ↔
      ∃ c : ℂ, tL R = c • 1 ∧ traceInput R = c • 1 := by
  have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Qun, onOp_add, onOp_sub, onOp_sub, onOp_11, onOp_W1, onOp_1W, onOp_smul, onOp_WW, aux_iff2]
  constructor
  · intro h
    refine ⟨R.trace / d, ?_, ?_⟩
    · ext b e
      have := fun x => congrFun (congrFun h (x, b)) (x, e)
      have hs := Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => this x)
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, if_true, true_and] at hs
      rw [Finset.sum_add_distrib] at hs
      have h3 : ∑ x : Fin d, (if b = e then (d:ℂ)⁻¹ else 0) * traceInput R x x =
          (if b = e then (d:ℂ)⁻¹ else 0) * R.trace := by
        rw [← Finset.mul_sum, ← trace_tI]; rfl
      rw [h3] at hs
      by_cases hbe : b = e
      · subst hbe; simp at hs ⊢; field_simp at hs ⊢; linear_combination hs
      · simp [hbe] at hs ⊢; exact hs.resolve_left hd.ne'
    · ext b e
      have := fun x => congrFun (congrFun h (b, x)) (e, x)
      have hs := Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => this x)
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, if_true, and_true] at hs
      rw [Finset.sum_add_distrib] at hs
      have h3 : ∑ x : Fin d, (if b = e then (d:ℂ)⁻¹ else 0) * tL R x x =
          (if b = e then (d:ℂ)⁻¹ else 0) * R.trace := by
        rw [← Finset.mul_sum, ← trace_tL]; rfl
      rw [h3] at hs
      by_cases hbe : b = e
      · subst hbe; simp at hs ⊢; field_simp at hs ⊢; linear_combination hs
      · simp [hbe] at hs ⊢; exact hs.resolve_left hd.ne'
  · rintro ⟨c, hc, hc'⟩
    have htr : R.trace = c * d := by rw [← trace_tL, hc, tr_smul_one]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [hc, hc', htr]
    by_cases h1 : i.1 = j.1 <;> by_cases h2 : i.2 = j.2 <;> simp [h1, h2]
    field_simp; ring

lemma tL_add (A B : Op (ChoiBasis d)) : tL (A + B) = tL A + tL B := by
  ext b e; simp [QAlgorithms.traceLeft, Finset.sum_add_distrib]
lemma tL_sub (A B : Op (ChoiBasis d)) : tL (A - B) = tL A - tL B := by
  ext b e; simp [QAlgorithms.traceLeft, Finset.sum_sub_distrib]
lemma tL_smul (c : ℂ) (A : Op (ChoiBasis d)) : tL (c • A) = c • tL A := by
  ext b e; simp [QAlgorithms.traceLeft, Finset.mul_sum]
lemma tL_ct (A : Op (ChoiBasis d)) : tL Aᴴ = (tL A)ᴴ := by
  ext b e; simp [QAlgorithms.traceLeft, Matrix.conjTranspose_apply]
lemma tL_one : tL (1 : Op (ChoiBasis d)) = (d : ℂ) • 1 := by
  ext b e; by_cases h : b = e <;> simp [QAlgorithms.traceLeft, Matrix.one_apply, h]
lemma tI_add (A B : Op (ChoiBasis d)) : traceInput (A + B) = traceInput A + traceInput B := by
  ext b e; simp [traceInput, Finset.sum_add_distrib]
lemma tI_sub (A B : Op (ChoiBasis d)) : traceInput (A - B) = traceInput A - traceInput B := by
  ext b e; simp [traceInput, Finset.sum_sub_distrib]
lemma tI_smul (c : ℂ) (A : Op (ChoiBasis d)) : traceInput (c • A) = c • traceInput A := by
  ext b e; simp [traceInput, Finset.mul_sum]
lemma tI_ct (A : Op (ChoiBasis d)) : traceInput Aᴴ = (traceInput A)ᴴ := by
  ext b e; simp [traceInput, Matrix.conjTranspose_apply]
lemma tI_one : traceInput (1 : Op (ChoiBasis d)) = (d : ℂ) • 1 := by
  ext b e; by_cases h : b = e <;> simp [traceInput, Matrix.one_apply, h]

lemma herm_decomp {n : Type*} (R : Matrix n n ℂ) :
    R = (1/2 : ℂ) • (R + Rᴴ) + Complex.I • ((-(Complex.I / 2)) • (R - Rᴴ)) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]; ring

lemma herm1 {n : Type*} (R : Matrix n n ℂ) : ((1/2 : ℂ) • (R + Rᴴ)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  congr 1; simp

lemma herm2 {n : Type*} (R : Matrix n n ℂ) : ((-(Complex.I / 2)) • (R - Rᴴ)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  simp [Complex.conj_I]
  ring

lemma mem_span_herm {n : Type*} {S : Set (Matrix n n ℂ)}
    (h : ∀ H : Matrix n n ℂ, H.IsHermitian → H ∈ Submodule.span ℂ S) (R : Matrix n n ℂ) :
    R ∈ Submodule.span ℂ S := by
  rw [herm_decomp R]
  exact Submodule.add_mem _ (h _ (herm1 R)) (Submodule.smul_mem _ _ (h _ (herm2 R)))

lemma mem_span_diff {n : Type*} {S : Set (Matrix n n ℂ)} (M N : Matrix n n ℂ)
    (hM : M ∈ S) (hN : N ∈ S) (ε : ℝ) (hε : ε ≠ 0) (T : Matrix n n ℂ)
    (hT : N = M + (ε : ℂ) • T) : T ∈ Submodule.span ℂ S := by
  have : T = ((ε : ℂ)⁻¹) • (N - M) := by
    rw [hT, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hε), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span hN) (Submodule.subset_span hM))

lemma real_of_herm {n : Type*} [DecidableEq n] (x : n) (A : Matrix n n ℂ) (c : ℂ)
    (h1 : A = c • 1) (h2 : Aᴴ = A) : c = ((c.re : ℝ) : ℂ) := by
  have : (Aᴴ) x x = A x x := by rw [h2]
  rw [h1] at this
  simp [Matrix.conjTranspose_apply] at this
  apply Complex.ext <;> simp
  have := congrArg Complex.im this
  simp at this; linarith

lemma ch_fwd (R : Op (ChoiBasis d)) (h : R ∈ Submodule.span ℂ (physicalTarget d .channels)) :
    ∃ c : ℂ, tL R = c • 1 := by
  induction h using Submodule.span_induction with
  | mem x hx => exact ⟨1, by rw [one_smul]; exact hx.2⟩
  | zero => exact ⟨0, by ext; simp [QAlgorithms.traceLeft]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [tL_add, ha, hb, add_smul]⟩
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hx
    exact ⟨a * b, by rw [tL_smul, hb, smul_smul]⟩

lemma un_fwd (R : Op (ChoiBasis d)) (h : R ∈ Submodule.span ℂ (physicalTarget d .unital)) :
    ∃ c : ℂ, tL R = c • 1 ∧ traceInput R = c • 1 := by
  induction h using Submodule.span_induction with
  | mem x hx => exact ⟨1, by rw [one_smul]; exact hx.2.1, by rw [one_smul]; exact hx.2.2⟩
  | zero => exact ⟨0, by ext; simp [QAlgorithms.traceLeft], by ext; simp [traceInput]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ha'⟩ := hx; obtain ⟨b, hb, hb'⟩ := hy
    exact ⟨a + b, by rw [tL_add, ha, hb, add_smul], by rw [tI_add, ha', hb', add_smul]⟩
  | smul a x _ hx =>
    obtain ⟨b, hb, hb'⟩ := hx
    exact ⟨a * b, by rw [tL_smul, hb, smul_smul], by rw [tI_smul, hb', smul_smul]⟩

lemma tL_M (hd : 0 < d) :
    tL ((((1 / d : ℝ)) : ℂ) • (1 : Op (ChoiBasis d))) = 1 := by
  have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [tL_smul, tL_one, smul_smul]
  push_cast; rw [one_div, inv_mul_cancel₀ hd', one_smul]

lemma tI_M (hd : 0 < d) :
    traceInput ((((1 / d : ℝ)) : ℂ) • (1 : Op (ChoiBasis d))) = 1 := by
  have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [tI_smul, tI_one, smul_smul]
  push_cast; rw [one_div, inv_mul_cancel₀ hd', one_smul]

lemma herm_sub_real {n : Type*} [DecidableEq n] (H M : Matrix n n ℂ) (hH : H.IsHermitian)
    (hM : M.IsHermitian) (c : ℂ) (hc : c = ((c.re : ℝ) : ℂ)) : (H - c • M).IsHermitian := by
  have hcs : (starRingEnd ℂ) c = c := by rw [hc, Complex.conj_ofReal]
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hH.eq, hM.eq]
  simp [hcs]

lemma one_herm {n : Type*} [DecidableEq n] (r : ℝ) : ((r : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]; simp

lemma ch_herm (hd : 0 < d) (H : Op (ChoiBasis d)) (hH : H.IsHermitian) (c : ℂ) (hc : tL H = c • 1) :
    H ∈ Submodule.span ℂ (physicalTarget d .channels) := by
  have hcr := real_of_herm (⟨0, hd⟩ : Fin d) (tL H) c hc (by rw [← tL_ct, hH.eq])
  set M : Op (ChoiBasis d) := (((1 / d : ℝ)) : ℂ) • 1 with hMdef
  have hMh : M.IsHermitian := one_herm _
  have hML : tL M = 1 := tL_M hd
  have hMI : traceInput M = 1 := tI_M hd
  obtain ⟨ε, hε, hpsd⟩ := psd (H - c • M) (herm_sub_real H M hH hMh c hcr) (1 / d) (by positivity)
  have hM : M ∈ physicalTarget d .channels :=
    ⟨by simpa [hMdef] using hpsd 0 (by simp [hε.le]), hML⟩
  have hN : M + (ε : ℂ) • (H - c • M) ∈ physicalTarget d .channels := by
    refine ⟨hpsd ε (by rw [abs_of_pos hε]), ?_⟩
    show tL _ = 1
    rw [tL_add, hML, tL_smul, tL_sub, tL_smul, hML, hc]; simp
  have hT := mem_span_diff M _ hM hN ε hε.ne' (H - c • M) rfl
  have : H = (H - c • M) + c • M := by rw [sub_add_cancel]
  rw [this]
  exact Submodule.add_mem _ hT (Submodule.smul_mem _ _ (Submodule.subset_span hM))

lemma un_herm (hd : 0 < d) (H : Op (ChoiBasis d)) (hH : H.IsHermitian) (c : ℂ) (hc : tL H = c • 1)
    (hc' : traceInput H = c • 1) :
    H ∈ Submodule.span ℂ (physicalTarget d .unital) := by
  have hcr := real_of_herm (⟨0, hd⟩ : Fin d) (tL H) c hc (by rw [← tL_ct, hH.eq])
  set M : Op (ChoiBasis d) := (((1 / d : ℝ)) : ℂ) • 1 with hMdef
  have hMh : M.IsHermitian := one_herm _
  have hML : tL M = 1 := tL_M hd
  have hMI : traceInput M = 1 := tI_M hd
  obtain ⟨ε, hε, hpsd⟩ := psd (H - c • M) (herm_sub_real H M hH hMh c hcr) (1 / d) (by positivity)
  have hM : M ∈ physicalTarget d .unital :=
    ⟨by simpa [hMdef] using hpsd 0 (by simp [hε.le]), hML, hMI⟩
  have hN : M + (ε : ℂ) • (H - c • M) ∈ physicalTarget d .unital := by
    refine ⟨hpsd ε (by rw [abs_of_pos hε]), ?_, ?_⟩
    · show tL _ = 1
      rw [tL_add, hML, tL_smul, tL_sub, tL_smul, hML, hc]; simp
    · rw [tI_add, hMI, tI_smul, tI_sub, tI_smul, hMI, hc']; simp
  have hT := mem_span_diff M _ hM hN ε hε.ne' (H - c • M) rfl
  have : H = (H - c • M) + c • M := by rw [sub_add_cancel]
  rw [this]
  exact Submodule.add_mem _ hT (Submodule.smul_mem _ _ (Submodule.subset_span hM))

lemma ct_smul_one {n : Type*} [DecidableEq n] (c : ℂ) :
    (c • (1 : Matrix n n ℂ))ᴴ = (starRingEnd ℂ c) • 1 := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]; rfl

lemma ch_bwd (hd : 0 < d) (R : Op (ChoiBasis d)) (h : ∃ c : ℂ, tL R = c • 1) :
    R ∈ Submodule.span ℂ (physicalTarget d .channels) := by
  obtain ⟨c, hc⟩ := h
  rw [herm_decomp R]
  refine Submodule.add_mem _ (ch_herm hd _ (herm1 R) ((1/2 : ℂ) * (c + starRingEnd ℂ c)) ?_)
    (Submodule.smul_mem _ _ (ch_herm hd _ (herm2 R) ((-(Complex.I / 2)) * (c - starRingEnd ℂ c)) ?_))
  · rw [tL_smul, tL_add, tL_ct, hc, ct_smul_one, ← add_smul, smul_smul]
  · rw [tL_smul, tL_sub, tL_ct, hc, ct_smul_one, ← sub_smul, smul_smul]

lemma un_bwd (hd : 0 < d) (R : Op (ChoiBasis d))
    (h : ∃ c : ℂ, tL R = c • 1 ∧ traceInput R = c • 1) :
    R ∈ Submodule.span ℂ (physicalTarget d .unital) := by
  obtain ⟨c, hc, hc'⟩ := h
  rw [herm_decomp R]
  refine Submodule.add_mem _ (un_herm hd _ (herm1 R) ((1/2 : ℂ) * (c + starRingEnd ℂ c)) ?_ ?_)
    (Submodule.smul_mem _ _ (un_herm hd _ (herm2 R) ((-(Complex.I / 2)) * (c - starRingEnd ℂ c)) ?_ ?_))
  · rw [tL_smul, tL_add, tL_ct, hc, ct_smul_one, ← add_smul, smul_smul]
  · rw [tI_smul, tI_add, tI_ct, hc', ct_smul_one, ← add_smul, smul_smul]
  · rw [tL_smul, tL_sub, tL_ct, hc, ct_smul_one, ← sub_smul, smul_smul]
  · rw [tI_smul, tI_sub, tI_ct, hc', ct_smul_one, ← sub_smul, smul_smul]

lemma tL_herm (H : Op (ChoiBasis d)) (hH : H.IsHermitian) : (tL H).IsHermitian := by
  unfold Matrix.IsHermitian; rw [← tL_ct, hH.eq]

lemma ops_all (hd : 0 < d) (R : Op (ChoiBasis d)) :
    R ∈ Submodule.span ℂ (physicalTarget d .operations) := by
  apply mem_span_herm
  intro H hH
  have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  set M : Op (ChoiBasis d) := (((1 / (2 * d) : ℝ)) : ℂ) • 1 with hMdef
  have hML : tL M = (((1/2 : ℝ)) : ℂ) • 1 := by
    rw [hMdef, tL_smul, tL_one, smul_smul]
    congr 1; push_cast; field_simp
  obtain ⟨ε1, h1, hp1⟩ := psd H hH (1 / (2 * d)) (by positivity)
  obtain ⟨ε2, h2, hp2⟩ := psd (tL H) (tL_herm H hH) (1 / 2) (by positivity)
  set ε := min ε1 ε2 with hεdef
  have hε : 0 < ε := lt_min h1 h2
  have hM : M ∈ physicalTarget d .operations := by
    refine ⟨by simpa [hMdef] using hp1 0 (by simp [h1.le]), ?_⟩
    show (1 - tL M).PosSemidef
    have := hp2 0 (by simp [h2.le])
    rw [hML]
    convert this using 1
    ext i j; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; push_cast; ring
  have hN : M + (ε : ℂ) • H ∈ physicalTarget d .operations := by
    refine ⟨hp1 ε (by rw [abs_of_pos hε]; exact min_le_left _ _), ?_⟩
    show (1 - tL (M + (ε : ℂ) • H)).PosSemidef
    have := hp2 (-ε) (by rw [abs_neg, abs_of_pos hε]; exact min_le_right _ _)
    rw [tL_add, hML, tL_smul]
    convert this using 1
    ext i j; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; push_cast; ring
  exact mem_span_diff M _ hM hN ε hε.ne' H rfl

lemma tL_conjA (U : Op (Fin d)) (hU : Uᴴ * U = 1) (M : Op (ChoiBasis d)) :
    tL (Matrix.kronecker U (1 : Op (Fin d)) * M * (Matrix.kronecker U (1 : Op (Fin d)))ᴴ) = tL M := by
  have hU' : ∀ x y, ∑ a, star (U a x) * U a y = if x = y then 1 else 0 := by
    intro x y
    have := congrFun (congrFun hU x) y
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  ext b e
  simp [QAlgorithms.traceLeft, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply, Finset.sum_mul]
  simp only [apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have key : ∀ x, ∑ a, ∑ x2, U a x2 * M (x2, b) (x, e) * (starRingEnd ℂ) (U a x) = M (x, b) (x, e) := by
    intro x
    rw [Finset.sum_comm]
    have h2 : ∀ x2, ∑ a, U a x2 * M (x2, b) (x, e) * (starRingEnd ℂ) (U a x) =
        (if x = x2 then 1 else 0) * M (x2, b) (x, e) := by
      intro x2; rw [← hU' x x2, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp only [RCLike.star_def]; ring
    simp_rw [h2]; simp
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun x _ => key x)

lemma tL_conjB (V : Op (Fin d)) (M : Op (ChoiBasis d)) :
    tL (Matrix.kronecker (1 : Op (Fin d)) V * M * (Matrix.kronecker (1 : Op (Fin d)) V)ᴴ) = V * tL M * Vᴴ := by
  ext b e
  simp [QAlgorithms.traceLeft, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply, Finset.sum_mul, Finset.mul_sum]
  simp only [apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]

lemma tI_conjA (V : Op (Fin d)) (hV : Vᴴ * V = 1) (M : Op (ChoiBasis d)) :
    traceInput (Matrix.kronecker (1 : Op (Fin d)) V * M * (Matrix.kronecker (1 : Op (Fin d)) V)ᴴ) =
      traceInput M := by
  have hV' : ∀ x y, ∑ a, star (V a x) * V a y = if x = y then 1 else 0 := by
    intro x y
    have := congrFun (congrFun hV x) y
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  ext b e
  simp [traceInput, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply, Finset.sum_mul]
  simp only [apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have key : ∀ x1, ∑ x, ∑ x2, V x x2 * M (b, x2) (e, x1) * (starRingEnd ℂ) (V x x1) = M (b, x1) (e, x1) := by
    intro x1
    rw [Finset.sum_comm]
    have h2 : ∀ x2, ∑ x, V x x2 * M (b, x2) (e, x1) * (starRingEnd ℂ) (V x x1) =
        (if x1 = x2 then 1 else 0) * M (b, x2) (e, x1) := by
      intro x2; rw [← hV' x1 x2, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp only [RCLike.star_def]; ring
    simp_rw [h2]; simp
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun x _ => key x)

lemma tI_conjB (U : Op (Fin d)) (M : Op (ChoiBasis d)) :
    traceInput (Matrix.kronecker U (1 : Op (Fin d)) * M * (Matrix.kronecker U (1 : Op (Fin d)))ᴴ) =
      U * traceInput M * Uᴴ := by
  ext b e
  simp [traceInput, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply, Finset.sum_mul, Finset.mul_sum]
  simp only [apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]

lemma kron_split (U V : Op (Fin d)) :
    Matrix.kronecker U V = Matrix.kronecker U (1 : Op (Fin d)) * Matrix.kronecker (1 : Op (Fin d)) V := by
  rw [show Matrix.kronecker U V = Matrix.kronecker (U * 1) (1 * V) by rw [Matrix.mul_one, Matrix.one_mul]]
  exact Matrix.mul_kronecker_mul U 1 1 V

lemma conj_split (X Y A : Op (ChoiBasis d)) :
    (X * Y) * A * (X * Y)ᴴ = X * (Y * A * Yᴴ) * Xᴴ := by
  rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]

lemma su_unit (g : SU d) : (g : Op (Fin d))ᴴ * (g : Op (Fin d)) = 1 ∧
    (g : Op (Fin d)) * (g : Op (Fin d))ᴴ = 1 := by
  have h := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
  rw [← Matrix.star_eq_conjTranspose]
  exact ⟨Unitary.star_mul_self_of_mem h, Unitary.mul_star_self_of_mem h⟩

lemma tL_conj (g : GroupPair d) (R : Op (ChoiBasis d)) :
    tL (conjugateTesterSeed g R) = (g.2 : Op (Fin d)) * tL R * (g.2 : Op (Fin d))ᴴ := by
  unfold conjugateTesterSeed
  simp only
  rw [kron_split, conj_split, tL_conjA _ (su_unit g.1).1, tL_conjB]

lemma tI_conj (g : GroupPair d) (R : Op (ChoiBasis d)) :
    traceInput (conjugateTesterSeed g R) = (g.1 : Op (Fin d)) * traceInput R * (g.1 : Op (Fin d))ᴴ := by
  unfold conjugateTesterSeed
  simp only
  rw [kron_split, conj_split, tI_conjB, tI_conjA _ (su_unit g.2).1]

lemma conj_scalar (U : Op (Fin d)) (hU : U * Uᴴ = 1) (c : ℂ) : U * (c • 1) * Uᴴ = c • 1 := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

lemma conj_mem (hd : 0 < d) (K : TomographyDomain) (g : GroupPair d) (R : Op (ChoiBasis d))
    (hR : R ∈ Submodule.span ℂ (physicalTarget d K)) :
    conjugateTesterSeed g R ∈ Submodule.span ℂ (physicalTarget d K) := by
  cases K with
  | operations => exact ops_all hd _
  | channels =>
    obtain ⟨c, hc⟩ := ch_fwd R hR
    exact ch_bwd hd _ ⟨c, by rw [tL_conj, hc, conj_scalar _ (su_unit g.2).2]⟩
  | unital =>
    obtain ⟨c, hc, hc'⟩ := un_fwd R hR
    exact un_bwd hd _ ⟨c, by rw [tL_conj, hc, conj_scalar _ (su_unit g.2).2],
      by rw [tI_conj, hc', conj_scalar _ (su_unit g.1).2]⟩

end X7T
end QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Claimed50.P28 QAlgorithms.Papers.Independent.Claimed50.P28.X7T in
theorem solution {d : ℕ} (hd : 2 ≤ d) :
    (∀ R : Op (ChoiBasis d), R ∈ tomographyTargetSpan d .operations) ∧
    (∀ R : Op (ChoiBasis d),
      (R ∈ tomographyTargetSpan d .channels ↔ ∃ c : ℂ, QAlgorithms.traceLeft R = c • (1 : Op (Fin d))) ∧
      (R ∈ tomographyTargetSpan d .channels ↔ onOperator (targetProjector d .channels) R = R)) ∧
    (∀ R : Op (ChoiBasis d),
      (R ∈ tomographyTargetSpan d .unital ↔ ∃ c : ℂ, QAlgorithms.traceLeft R = c • (1 : Op (Fin d)) ∧
        traceInput R = c • (1 : Op (Fin d))) ∧
      (R ∈ tomographyTargetSpan d .unital ↔ onOperator (targetProjector d .unital) R = R)) ∧
    (∀ (K : TomographyDomain) (g : GroupPair d) (R : Op (ChoiBasis d)),
      R ∈ tomographyTargetSpan d K → conjugateTesterSeed g R ∈ tomographyTargetSpan d K) := by
  have hd0 : 0 < d := by omega
  refine ⟨fun R => ops_all hd0 R, fun R => ⟨⟨ch_fwd R, ch_bwd hd0 R⟩, ?_⟩,
    fun R => ⟨⟨un_fwd R, un_bwd hd0 R⟩, ?_⟩, fun K g R hR => conj_mem hd0 K g R hR⟩
  · rw [proj_ch hd0]; exact ⟨ch_fwd R, ch_bwd hd0 R⟩
  · rw [proj_un hd0]; exact ⟨un_fwd R, un_bwd hd0 R⟩
