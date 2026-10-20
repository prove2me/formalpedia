-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P37.theoremC20
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:42:24.126356+00:00
-- url     : https://prove2.me/submissions/e50ea80a-c798-4269-adb2-e775e418c63b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37
open scoped Matrix ComplexOrder

lemma g53_cre {z : ℂ} (h : z.im = 0) : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h])

lemma g53_diag_real {n : Type} [Fintype n] {X : Matrix n n ℂ} (hX : X.PosSemidef) (i : n) :
    (X i i).im = 0 ∧ 0 ≤ (X i i).re := by
  have := hX.diag_nonneg (i := i)
  exact ⟨(Complex.nonneg_iff.mp this).2.symm, (Complex.nonneg_iff.mp this).1⟩

lemma g53_exists_diag_pos {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.PosSemidef)
    (hX0 : X ≠ 0) : ∃ m, 0 < (X m m).re := by
  by_contra h
  push Not at h
  apply hX0
  rw [← hX.trace_eq_zero_iff, Matrix.trace]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 := g53_diag_real hX i
  simp only [Matrix.diag]
  rw [g53_cre h1.1, le_antisymm (h i) h1.2, Complex.ofReal_zero]

lemma g53_pd_cduc {n : Type} [Fintype n] [DecidableEq n] (A M X Y : Matrix n n ℂ)
    (hA : ∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re) (hM : M.PosSemidef) (hX : X.PosSemidef) (hX0 : X ≠ 0)
    (hMd : ∀ i, M i i = A i i)
    (hY : ∀ i j, Y i j = if i = j then ∑ k, A i k * X k k else M i j * X i j) (hYh : Y.IsHermitian) :
    Y.PosDef := by
  obtain ⟨m, hm⟩ := g53_exists_diag_pos hX hX0
  let Dr : n → ℝ := fun i => ∑ k, (if k = i then 0 else (A i k).re * (X k k).re)
  have hAX : ∀ i k, A i k * X k k = (((A i k).re * (X k k).re : ℝ) : ℂ) := by
    intro i k
    rw [g53_cre (hA i k).1, g53_cre (g53_diag_real hX k).1]; push_cast; simp
  have hYdec : Y = Matrix.diagonal (fun i => (Dr i : ℂ)) + M ⊙ X := by
    ext i j
    rw [hY, Matrix.add_apply, Matrix.hadamard_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, Matrix.diagonal_apply_eq, hMd, hAX i i,
        Finset.sum_congr rfl (fun k _ => hAX i k)]
      have hreal : ∑ k, (A i k).re * (X k k).re = Dr i + (A i i).re * (X i i).re := by
        have e : ∀ k, (if k = i then (0:ℝ) else (A i k).re * (X k k).re) =
            (A i k).re * (X k k).re - if k = i then (A i k).re * (X k k).re else 0 := by
          intro k; split_ifs <;> simp
        simp only [Dr, e, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        ring
      rw [← Complex.ofReal_sum, hreal]; push_cast; ring
    · rw [if_neg hij, Matrix.diagonal_apply_ne _ hij, zero_add]
  have hDr : ∀ i, 0 ≤ Dr i := fun i => Finset.sum_nonneg fun k _ => by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hA i k).2.le (g53_diag_real hX k).2
  have hDrm : ∀ i, i ≠ m → (A i m).re * (X m m).re ≤ Dr i := by
    intro i hi
    have := Finset.single_le_sum (f := fun k => (if k = i then 0 else (A i k).re * (X k k).re))
      (fun k _ => by
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (hA i k).2.le (g53_diag_real hX k).2) (Finset.mem_univ m)
    simpa [Ne.symm hi] using this
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hYh
  intro v hv
  rw [hYdec, Matrix.add_mulVec, dotProduct_add]
  have h2 : 0 ≤ star v ⬝ᵥ (M ⊙ X) *ᵥ v := (hM.hadamard hX).dotProduct_mulVec_nonneg v
  have h1 : star v ⬝ᵥ Matrix.diagonal (fun i => (Dr i : ℂ)) *ᵥ v = ((∑ i, Dr i * ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.conj_mul', RCLike.star_def]; ring
  rw [h1]
  by_cases hex : ∃ i, i ≠ m ∧ v i ≠ 0
  · obtain ⟨i, him, hvi⟩ := hex
    have hpos : 0 < ∑ i, Dr i * ‖v i‖ ^ 2 := by
      have hle := Finset.single_le_sum (f := fun j => Dr j * ‖v j‖ ^ 2)
        (fun j _ => mul_nonneg (hDr j) (by positivity)) (Finset.mem_univ i)
      have : 0 < Dr i * ‖v i‖ ^ 2 :=
        mul_pos (lt_of_lt_of_le (mul_pos (hA i m).2 hm) (hDrm i him)) (by positivity)
      linarith
    exact add_pos_of_pos_of_nonneg (by exact_mod_cast hpos) h2
  · push Not at hex
    have hvs : v = Pi.single m (v m) := by
      funext i
      by_cases him : i = m
      · subst him; simp
      · rw [hex i him, Pi.single_eq_of_ne him]
    have hvm : v m ≠ 0 := by
      intro h0; apply hv; rw [hvs, h0]; simp
    have hq2 : star v ⬝ᵥ (M ⊙ X) *ᵥ v = ((‖v m‖ ^ 2 * ((A m m).re * (X m m).re) : ℝ) : ℂ) := by
      rw [hvs]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.single_apply, Matrix.hadamard_apply]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [Finset.sum_eq_single m (fun b _ hb => by simp [hb]) (by simp)]
      simp only [if_true]
      rw [hMd, hAX m m, RCLike.star_def]
      push_cast
      rw [← Complex.conj_mul']; ring
    rw [hq2]
    have : 0 < ‖v m‖ ^ 2 * ((A m m).re * (X m m).re) :=
      mul_pos (by positivity) (mul_pos (hA m m).2 hm)
    have h1' : (0 : ℂ) ≤ ((∑ i, Dr i * ‖v i‖ ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast Finset.sum_nonneg fun j _ => mul_nonneg (hDr j) (by positivity)
    exact add_pos_of_nonneg_of_pos h1' (by exact_mod_cast this)
lemma g53_psd_entry {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.PosSemidef) (i j : n) :
    ‖X i j‖ ^ 2 ≤ (X i i).re * (X j j).re := by
  let _ := X.toSeminormedAddCommGroup hX
  let _ := X.toInnerProductSpace hX
  have key : ∀ a b : n, (inner ℂ (Pi.single a (1:ℂ) : n → ℂ) (Pi.single b (1:ℂ))) = X a b := by
    intro a b
    show (X *ᵥ Pi.single b 1) ⬝ᵥ star (Pi.single a (1:ℂ)) = X a b
    simp [dotProduct, Matrix.mulVec, Pi.single_apply]
  have h := inner_mul_inner_self_le (𝕜 := ℂ) (Pi.single i (1:ℂ) : n → ℂ) (Pi.single j (1:ℂ))
  rw [key, key, key, key] at h
  have hji : ‖X j i‖ = ‖X i j‖ := by
    rw [← hX.isHermitian.apply i j]; simp
  rw [hji, ← sq] at h
  simpa using h

lemma g53_pd_duc {n : Type} [Fintype n] [DecidableEq n] (A C X Y : Matrix n n ℂ)
    (hA : ∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re) (hX : X.PosSemidef) (hX0 : X ≠ 0)
    (hC : ∀ i j, i ≠ j → ‖C i j‖ ^ 2 ≤ (A i j).re * (A j i).re)
    (hY : ∀ i j, Y i j = if i = j then ∑ k, A i k * X k k else C i j * X j i) (hYh : Y.IsHermitian) :
    Y.PosDef := by
  obtain ⟨m, hm⟩ := g53_exists_diag_pos hX hX0
  have hAX : ∀ i k, A i k * X k k = (((A i k).re * (X k k).re : ℝ) : ℂ) := by
    intro i k
    rw [g53_cre (hA i k).1, g53_cre (g53_diag_real hX k).1]; push_cast; simp
  have hx : ∀ k, 0 ≤ (X k k).re := fun k => (g53_diag_real hX k).2
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hYh
  intro v hv
  let p : n → n → ℝ := fun i j => Real.sqrt ((A i j).re * (X j j).re) * ‖v i‖
  have hp0 : ∀ i j, 0 ≤ p i j := fun i j => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hpsq : ∀ i j, p i j ^ 2 = (A i j).re * (X j j).re * ‖v i‖ ^ 2 := by
    intro i j
    simp only [p]
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (hA i j).2.le (hx j))]
  let L : n → n → ℝ := fun i j => (if i = j then (∑ k, p i k ^ 2) + p i i * p i i else 0) - p i j * p j i
  have hq : star v ⬝ᵥ Y *ᵥ v = ∑ i, ∑ j, star (v i) * Y i j * v j := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hL : ∀ i j, L i j ≤ (star (v i) * Y i j * v j).re := by
    intro i j
    simp only [L]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, hY, if_pos rfl, Finset.sum_congr rfl (fun k _ => hAX i k), ← Complex.ofReal_sum,
        RCLike.star_def]
      have e : (starRingEnd ℂ) (v i) * ((∑ k, (A i k).re * (X k k).re : ℝ) : ℂ) * v i =
          (((∑ k, (A i k).re * (X k k).re) * ‖v i‖ ^ 2 : ℝ) : ℂ) := by
        rw [show (starRingEnd ℂ) (v i) * ((∑ k, (A i k).re * (X k k).re : ℝ) : ℂ) * v i =
          ((∑ k, (A i k).re * (X k k).re : ℝ) : ℂ) * ((starRingEnd ℂ) (v i) * v i) by ring,
          Complex.conj_mul']
        push_cast; ring
      rw [e, Complex.ofReal_re]
      simp only [hpsq]
      rw [Finset.sum_mul]
      linarith
    · rw [if_neg hij, hY, if_neg hij, zero_sub]
      have h1 := (abs_le.mp (Complex.abs_re_le_norm (star (v i) * (C i j * X j i) * v j))).1
      have hn : ‖star (v i) * (C i j * X j i) * v j‖ = ‖v i‖ * ‖C i j‖ * ‖X j i‖ * ‖v j‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_star]; ring
      have hCb : ‖C i j‖ ≤ Real.sqrt ((A i j).re * (A j i).re) := Real.le_sqrt_of_sq_le (hC i j hij)
      have hXb : ‖X j i‖ ≤ Real.sqrt ((X j j).re * (X i i).re) := Real.le_sqrt_of_sq_le (g53_psd_entry hX j i)
      have hprod : p i j * p j i = ‖v i‖ * Real.sqrt ((A i j).re * (A j i).re) *
          Real.sqrt ((X j j).re * (X i i).re) * ‖v j‖ := by
        have hs : Real.sqrt ((A i j).re * (A j i).re) * Real.sqrt ((X j j).re * (X i i).re) =
            Real.sqrt ((A i j).re * (X j j).re) * Real.sqrt ((A j i).re * (X i i).re) := by
          rw [← Real.sqrt_mul (mul_nonneg (hA i j).2.le (hA j i).2.le),
            ← Real.sqrt_mul (mul_nonneg (hA i j).2.le (hx j))]
          ring_nf
        simp only [p]
        calc Real.sqrt ((A i j).re * (X j j).re) * ‖v i‖ * (Real.sqrt ((A j i).re * (X i i).re) * ‖v j‖)
            = ‖v i‖ * (Real.sqrt ((A i j).re * (X j j).re) * Real.sqrt ((A j i).re * (X i i).re)) * ‖v j‖ := by ring
          _ = _ := by rw [← hs]; ring
      have hbig : ‖v i‖ * ‖C i j‖ * ‖X j i‖ * ‖v j‖ ≤ p i j * p j i := by
        rw [hprod]
        have := mul_le_mul hCb hXb (norm_nonneg _) (Real.sqrt_nonneg _)
        have h2 := mul_le_mul_of_nonneg_left this (norm_nonneg (v i))
        have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (v j))
        calc ‖v i‖ * ‖C i j‖ * ‖X j i‖ * ‖v j‖ = ‖v i‖ * (‖C i j‖ * ‖X j i‖) * ‖v j‖ := by ring
          _ ≤ ‖v i‖ * (Real.sqrt ((A i j).re * (A j i).re) * Real.sqrt ((X j j).re * (X i i).re)) * ‖v j‖ := h3
          _ = _ := by ring
      rw [hn] at h1
      linarith
  have hsumL : ∑ i, ∑ j, L i j = (∑ i, ∑ j, (p i j - p j i) ^ 2) / 2 + ∑ i, p i i ^ 2 := by
    have e1 : ∀ i, ∑ j, L i j = (∑ k, p i k ^ 2) + p i i * p i i - ∑ j, p i j * p j i := by
      intro i
      simp only [L, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [e1, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have e2 : ∑ i, ∑ j, (p i j - p j i) ^ 2 = 2 * ∑ i, ∑ j, p i j ^ 2 - 2 * ∑ i, ∑ j, p i j * p j i := by
      have hs : ∑ i, ∑ j, p j i ^ 2 = ∑ i, ∑ j, p i j ^ 2 := Finset.sum_comm
      have : ∀ i j, (p i j - p j i) ^ 2 = p i j ^ 2 + p j i ^ 2 - 2 * (p i j * p j i) := fun i j => by ring
      simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hs]
      ring
    rw [e2]
    simp only [sq]
    ring
  have hTpos : 0 < (∑ i, ∑ j, (p i j - p j i) ^ 2) / 2 + ∑ i, p i i ^ 2 := by
    have hA0 : 0 ≤ (∑ i, ∑ j, (p i j - p j i) ^ 2) / 2 := by positivity
    have hB0 : 0 ≤ ∑ i, p i i ^ 2 := by positivity
    by_cases hvm : v m = 0
    · obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
        by_contra h; push Not at h; exact hv (funext h)
      have hjm : j ≠ m := fun h => hj (h ▸ hvm)
      have hpm : p m j = 0 := by simp only [p, hvm, norm_zero, mul_zero]
      have hpj : 0 < p j m := mul_pos (Real.sqrt_pos.mpr (mul_pos (hA j m).2 hm)) (norm_pos_iff.mpr hj)
      have : 0 < (p j m - p m j) ^ 2 := by rw [hpm, sub_zero]; positivity
      have hle1 : (p j m - p m j) ^ 2 ≤ ∑ jj, (p j jj - p jj j) ^ 2 :=
        Finset.single_le_sum (f := fun jj => (p j jj - p jj j) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ m)
      have hle2 : ∑ jj, (p j jj - p jj j) ^ 2 ≤ ∑ i, ∑ jj, (p i jj - p jj i) ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ jj, (p i jj - p jj i) ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      linarith
    · have : 0 < p m m ^ 2 := by
        rw [hpsq]; exact mul_pos (mul_pos (hA m m).2 hm) (by positivity)
      have hle : p m m ^ 2 ≤ ∑ i, p i i ^ 2 :=
        Finset.single_le_sum (f := fun i => p i i ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ m)
      linarith
  have hre : 0 < (star v ⬝ᵥ Y *ᵥ v).re := by
    rw [hq, Complex.re_sum]
    have : ∑ i, ∑ j, L i j ≤ ∑ i, (∑ j, star (v i) * Y i j * v j).re := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Complex.re_sum]
      exact Finset.sum_le_sum fun j _ => hL i j
    linarith
  have him : (star v ⬝ᵥ Y *ᵥ v).im = 0 := hYh.im_star_dotProduct_mulVec_self v
  exact Complex.lt_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

lemma g53_kraus_single {n : Type} [Fintype n] [DecidableEq n] {m : ℕ} (E : Fin m → Matrix n n ℂ)
    (a b i j : n) :
    QAlgorithms.krausApply E (Matrix.single a b 1) i j = ∑ k, (E k) i a * star ((E k) j b) := by
  simp only [QAlgorithms.krausApply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, Finset.sum_ite_eq', Finset.sum_ite_eq,
    ite_and]

lemma g53_kraus_psd {n : Type} [Fintype n] [DecidableEq n] {m : ℕ} (E : Fin m → Matrix n n ℂ)
    {X : Matrix n n ℂ} (hX : X.PosSemidef) : (QAlgorithms.krausApply E X).PosSemidef := by
  unfold QAlgorithms.krausApply
  classical
  induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    exact (hX.mul_mul_conjTranspose_same (E k)).add ih

lemma g53_sum_psd {n ι : Type} [Fintype n] (s : Finset ι) (A : ι → Matrix n n ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert k s hk ih => rw [Finset.sum_insert hk]; exact (h k).add ih

noncomputable section
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P37
open QAlgorithms.Papers.Independent.Information100.P23 (Operator)
open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)
open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)
open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)
open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

lemma g53_forward {d : ℕ} (A : Operator d) (hA : ColumnStochastic A) (Φ : Dynamics d)
    (hdiag : ∀ X : Operator d, ∀ i, Φ X i i = ∑ k, A i k * X k k) (hS : StrictlyPositive Φ) :
    MatrixStrictlyPositive A := by
  intro i j
  have hE : (Matrix.single j j (1 : ℂ)).PosSemidef := by
    have := Matrix.posSemidef_vecMulVec_self_star (Pi.single j (1 : ℂ))
    convert this using 1
    ext a b
    simp only [Matrix.vecMulVec_apply, Matrix.single_apply, Pi.single_apply, Pi.star_apply]
    rcases eq_or_ne a j with rfl | ha <;> rcases eq_or_ne b a with rfl | hb <;>
      simp_all [eq_comm]
  have hE0 : Matrix.single j j (1 : ℂ) ≠ 0 := by
    intro h; have := congrFun (congrFun h j) j; simp at this
  have hpd := hS _ hE hE0
  have hpos := hpd.diag_pos (i := i)
  rw [hdiag] at hpos
  have : ∑ k, A i k * Matrix.single j j (1 : ℂ) k k = A i j := by
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [Matrix.single_apply, hb, Ne.symm hb]) (by simp)]
    simp
  rw [this] at hpos
  exact ⟨(hA.1 i j).1, (Complex.pos_iff.mp hpos).1⟩

theorem solution {d : ℕ} (hd : 0 < d) (A : Operator d)
    (hA : ColumnStochastic A) :
    (∀ B : Operator d, IsChannel (cduc A B) → (StrictlyPositive (cduc A B) ↔ MatrixStrictlyPositive A)) ∧
    (∀ C : Operator d, IsChannel (duc A C) → (StrictlyPositive (duc A C) ↔ MatrixStrictlyPositive A)) := by
  constructor
  · intro B hch
    obtain ⟨m, E, -, hE⟩ := hch
    constructor
    · exact g53_forward A hA _ (fun X i => by simp [cduc]) 
    · intro hpos X hX hX0
      let w : Fin m → Fin d → ℂ := fun k i => (E k) i i
      let M : Operator d := ∑ k, Matrix.vecMulVec (w k) (star (w k))
      have hM : M.PosSemidef := g53_sum_psd _ _ fun k => Matrix.posSemidef_vecMulVec_self_star (w k)
      have hMij : ∀ i j, M i j = cduc A B (Matrix.single i j 1) i j := by
        intro i j
        rw [hE, g53_kraus_single]
        simp [M, w, Matrix.sum_apply, Matrix.vecMulVec_apply]
      have hMd : ∀ i, M i i = A i i := by
        intro i; rw [hMij]
        simp [cduc, Matrix.single_apply]
      have hMo : ∀ i j, i ≠ j → M i j = B i j := by
        intro i j hij; rw [hMij]; simp [cduc, hij]
      have hYh : (cduc A B X).IsHermitian := by rw [hE]; exact (g53_kraus_psd E hX).isHermitian
      apply g53_pd_cduc A M X _ hpos hM hX hX0 hMd _ hYh
      intro i j
      by_cases hij : i = j
      · subst hij; simp [cduc]
      · simp [cduc, hij, hMo i j hij]
  · intro C hch
    obtain ⟨m, E, -, hE⟩ := hch
    constructor
    · exact g53_forward A hA _ (fun X i => by simp [duc])
    · intro hpos X hX hX0
      have hYh : (duc A C X).IsHermitian := by rw [hE]; exact (g53_kraus_psd E hX).isHermitian
      have hCb : ∀ i j, i ≠ j → ‖C i j‖ ^ 2 ≤ (A i j).re * (A j i).re := by
        intro i j hij
        have hc : C i j = ∑ k, (E k) i j * star ((E k) j i) := by
          have := g53_kraus_single E j i i j
          rw [← hE] at this
          simp [duc, hij, Matrix.single_apply] at this
          rw [this]
          rfl
        have ha : ∀ i j, ((A i j).re : ℝ) = ∑ k, ‖(E k) i j‖ ^ 2 := by
          intro i j
          have := g53_kraus_single E j j i i
          rw [← hE] at this
          have h2 : A i j = ∑ k, (E k) i j * star ((E k) i j) := by
            rw [← this]; simp [duc, Matrix.single_apply]
          rw [h2, Complex.re_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [RCLike.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
        rw [hc, ha i j, ha j i]
        have h1 : ‖∑ k, (E k) i j * star ((E k) j i)‖ ≤ ∑ k, ‖(E k) i j‖ * ‖(E k) j i‖ := by
          refine le_trans (norm_sum_le _ _) (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
          rw [norm_mul, norm_star]
        have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖(E k) i j‖) (fun k => ‖(E k) j i‖)
        calc ‖∑ k, (E k) i j * star ((E k) j i)‖ ^ 2 ≤ (∑ k, ‖(E k) i j‖ * ‖(E k) j i‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h1 2
          _ ≤ _ := h2
      apply g53_pd_duc A C X _ hpos hX hX0 hCb _ hYh
      intro i j
      simp [duc]
