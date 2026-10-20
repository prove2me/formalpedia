-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P63.degenerateCapacities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:02:47.012573+00:00
-- url     : https://prove2.me/submissions/6750ea01-ff21-489c-a482-6b1fb8226f5c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P63

lemma g53e_tr_mul_le {n : Type} [Fintype n] [DecidableEq n] (P R : Matrix n n ℂ)
    (hP : P.PosSemidef) (hR : R.PosSemidef) : (P * R).trace.re ≤ P.trace.re * R.trace.re := by
  have hs := hP.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hu := Unitary.mul_star_self_of_mem hP.1.eigenvectorUnitary.2
  have htr := hP.1.trace_eq_sum_eigenvalues
  have hev := hP.eigenvalues_nonneg
  generalize (hP.1.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hP.1.eigenvalues = lam at *
  have hR' := hR.conjTranspose_mul_mul_same U
  have h1 : (P * R).trace = (Matrix.diagonal (RCLike.ofReal ∘ lam) * (star U * R * U)).trace := by
    rw [hs]
    rw [show U * Matrix.diagonal (RCLike.ofReal ∘ lam) * star U * R =
      U * (Matrix.diagonal (RCLike.ofReal ∘ lam) * (star U * R)) by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h2 : (star U * R * U).trace = R.trace := by
    rw [Matrix.trace_mul_cycle, hu, one_mul]
  rw [h1, htr, Complex.re_sum, Finset.sum_mul]
  rw [← h2]
  simp only [Matrix.trace, Matrix.diagonal_mul, Matrix.diag, Function.comp, Complex.re_sum]
  apply Finset.sum_le_sum; intro i _
  rw [Matrix.star_eq_conjTranspose] at *
  have hd : ∀ j, 0 ≤ ((Uᴴ * R * U) j j).re := fun j =>
    (Complex.nonneg_iff.mp (hR'.diag_nonneg (i := j))).1
  have him : ((Uᴴ * R * U) i i).im = 0 := (Complex.nonneg_iff.mp (hR'.diag_nonneg (i := i))).2.symm
  have hle : ((Uᴴ * R * U) i i).re ≤ ∑ j, ((Uᴴ * R * U) j j).re :=
    Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)
  simp only [Complex.mul_re]
  simpa using mul_le_mul_of_nonneg_left hle (hev i)

lemma g53e_opt {I O : Type} [Fintype I] [Fintype O] [DecidableEq O]
    (N : Superop I O) (e K : ℝ) (he : 0 ≤ e) (he1 : e < 1)
    (hub : ∀ (M : ℕ) (C : Code I O M), ∑ x, effectProb (C.measurement x) (N (C.word x)) ≤ K)
    (C0 : Code I O ⌊K / (1 - e)⌋₊)
    (hC0 : K ≤ ∑ x, effectProb (C0.measurement x) (N (C0.word x))) :
    optimalMessages N e = ⌊K / (1 - e)⌋₊ := by
  have h1e : 0 < 1 - e := by linarith
  have hM0 := C0.positive
  have hM0r : (0 : ℝ) < (⌊K / (1 - e)⌋₊ : ℕ) := by exact_mod_cast hM0
  apply IsGreatest.csSup_eq
  refine ⟨⟨C0, ?_⟩, ?_⟩
  · unfold averageError
    have hfl : ((⌊K / (1 - e)⌋₊ : ℕ) : ℝ) ≤ K / (1 - e) := Nat.floor_le (by
      by_contra h; push Not at h
      have : ⌊K / (1 - e)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega)
    rw [le_div_iff₀ h1e] at hfl
    have : (1 - e) ≤ ((⌊K / (1 - e)⌋₊ : ℕ) : ℝ)⁻¹ * K := by
      rw [inv_mul_eq_div, le_div_iff₀ hM0r]; linarith
    have h2 := mul_le_mul_of_nonneg_left hC0 (inv_nonneg.mpr hM0r.le)
    linarith
  · rintro M ⟨C, hC⟩
    unfold averageError at hC
    have hMp : (0 : ℝ) < M := by exact_mod_cast C.positive
    have := hub M C
    apply Nat.le_floor
    rw [le_div_iff₀ h1e]
    have h3 : 1 - e ≤ (M : ℝ)⁻¹ * ∑ x, effectProb (C.measurement x) (N (C.word x)) := by linarith
    rw [inv_mul_eq_div, le_div_iff₀ hMp] at h3
    linarith

lemma g53e_ub {I O : Type} [Fintype I] [Fintype O] [DecidableEq O] (N : Superop I O)
    (K : ℝ) (hN : ∀ ρ : Matrix I I ℂ, IsDensityMatrix ρ → (N ρ).PosSemidef ∧ ∀ P : Matrix O O ℂ,
      P.PosSemidef → effectProb P (N ρ) ≤ (P.trace.re) * K)
    (M : ℕ) (C : Code I O M) :
    ∑ x, effectProb (C.measurement x) (N (C.word x)) ≤ (Fintype.card O : ℝ) * K := by
  calc ∑ x, effectProb (C.measurement x) (N (C.word x))
      ≤ ∑ x, (C.measurement x).trace.re * K := by
        apply Finset.sum_le_sum; intro x _
        exact (hN _ (C.state x)).2 _ (C.positiveMeasurement x)
    _ = (Fintype.card O : ℝ) * K := by
        rw [← Finset.sum_mul, ← Complex.re_sum, ← Matrix.trace_sum, C.complete]
        simp

lemma g53e_f0 (d : ℕ) (hd : 0 < d) (a b y y' : Fin d) :
    QuditFidelity.depolarizingMap d hd 0 (Matrix.single a b 1) y y' = if a = y ∧ b = y' then 1 else 0 := by
  simp [QuditFidelity.depolarizingMap, Matrix.single_apply]

lemma g53e_f1 (d : ℕ) (hd : 0 < d) (a b y y' : Fin d) :
    QuditFidelity.depolarizingMap d hd 1 (Matrix.single a b 1) y y' =
      if a = b ∧ y = y' then ((1 / d : ℝ) : ℂ) else 0 := by
  by_cases h1 : a = b <;> by_cases h2 : y = y' <;>
    simp [QuditFidelity.depolarizingMap, Matrix.single_apply, Matrix.trace, Matrix.one_apply, h1, h2]

lemma g53e_N0 (d n : ℕ) (hd : 0 < d) (X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    depolarizingN d n 0 X = X := by
  unfold depolarizingN
  rw [dif_pos hd]
  ext y y'
  simp only [piSuperop, Matrix.of_apply, g53e_f0]
  simp only [Fintype.prod_boole]
  simp only [forall_and, ← funext_iff]
  simp only [mul_ite, mul_one, mul_zero]
  simp [ite_and]

lemma g53e_N1 (d n : ℕ) (hd : 0 < d) (X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    depolarizingN d n 1 X = (((1 / d : ℝ) : ℂ) ^ n * X.trace) • (1 : Matrix _ _ ℂ) := by
  unfold depolarizingN
  rw [dif_pos hd]
  ext y y'
  simp only [piSuperop, Matrix.of_apply, g53e_f1]
  simp only [Fintype.prod_ite_zero]
  simp only [forall_and, ← funext_iff, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [mul_ite, mul_zero]
  by_cases h : y = y'
  · subst h
    simp only [and_true, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.trace, Matrix.diag]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  · simp [h, Matrix.one_apply_ne h]

lemma g53e_sumtr {I O : Type} [Fintype I] [Fintype O] [DecidableEq O] {M : ℕ} (C : Code I O M) :
    ∑ x, (C.measurement x).trace.re = (Fintype.card O : ℝ) := by
  rw [← Complex.re_sum, ← Matrix.trace_sum, C.complete]; simp

lemma g53e_diag_psd {O : Type} [Fintype O] [DecidableEq O] (P : O → Prop) [DecidablePred P] :
    (Matrix.diagonal (fun z => if P z then (1 : ℂ) else 0)).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro z; by_cases h : P z <;> simp [h]

lemma g53e_diag_density {O : Type} [Fintype O] [DecidableEq O] (w : O) :
    IsDensityMatrix (Matrix.diagonal (fun z => if z = w then (1 : ℂ) else 0)) :=
  ⟨g53e_diag_psd _, by simp [Matrix.trace_diagonal]⟩

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Footnote 1, PDF p.4: exact average-error formulas at the identity and completely
randomizing endpoints; zero decoding effects and repeated codewords remain allowed. -/
theorem solution (d n : ℕ) (hd : 2 ≤ d) (e : ℝ) (he : 0 ≤ e) (heone : e < 1) :
    quantumMessages d n 0 e = ⌊(d : ℝ)^n / (1-e)⌋₊ ∧
    quantumMessages d n 1 e = ⌊1 / (1-e)⌋₊ := by
  have hd0 : 0 < d := by omega
  have h1e : 0 < 1 - e := by linarith
  have hcard : (Fintype.card (Fin n → Fin d) : ℝ) = (d : ℝ) ^ n := by simp
  have hcardpos : 0 < Fintype.card (Fin n → Fin d) := Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, hd0⟩⟩
  constructor
  · unfold quantumMessages
    have hub := g53e_ub (depolarizingN d n 0) 1 (fun ρ hρ => by
      rw [g53e_N0 d n hd0]
      refine ⟨hρ.1, fun P hP => ?_⟩
      have := g53e_tr_mul_le P ρ hP hρ.1
      rw [hρ.2] at this; simpa [effectProb] using this)
    rw [hcard, mul_one] at hub
    -- the explicit code
    set O := Fin n → Fin d
    set M0 := ⌊(d : ℝ) ^ n / (1 - e)⌋₊
    have hD : Fintype.card O ≤ M0 := by
      apply Nat.le_floor
      rw [hcard, le_div_iff₀ h1e]
      have : (0 : ℝ) ≤ (d : ℝ) ^ n := by positivity
      nlinarith
    let eo := Fintype.equivFin O
    let φ : O → Fin M0 := fun y => Fin.castLE hD (eo y)
    let ψ : Fin M0 → O := fun x => eo.symm ⟨x.val % Fintype.card O, Nat.mod_lt _ hcardpos⟩
    have hψφ : ∀ y, ψ (φ y) = y := by
      intro y
      have h : (⟨(eo y).val % Fintype.card O, Nat.mod_lt _ hcardpos⟩ : Fin (Fintype.card O)) = eo y :=
        Fin.ext (Nat.mod_eq_of_lt (eo y).2)
      simp only [ψ, φ, Fin.val_castLE]; rw [h]; simp
    have hφinj : Function.Injective φ := by
      intro a b h; rw [← hψφ a, h, hψφ b]
    let C0 : Code O O M0 :=
      { positive := lt_of_lt_of_le hcardpos hD
        word := fun x => Matrix.diagonal (fun z => if z = ψ x then (1 : ℂ) else 0)
        state := fun x => g53e_diag_density _
        measurement := fun x => Matrix.diagonal (fun z => if φ z = x then (1 : ℂ) else 0)
        positiveMeasurement := fun x => g53e_diag_psd _
        complete := by
          ext a b
          rw [Matrix.sum_apply]
          by_cases hab : a = b
          · subst hab; simp [Matrix.diagonal_apply]
          · simp [Matrix.diagonal_apply, hab] }
    refine g53e_opt _ e _ he heone hub C0 ?_
    have hterm : ∀ x, effectProb (C0.measurement x) (depolarizingN d n 0 (C0.word x)) =
        if φ (ψ x) = x then 1 else 0 := by
      intro x
      rw [g53e_N0 d n hd0]
      simp only [effectProb, C0, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      rw [Finset.sum_eq_single (ψ x) (fun b _ hb => by simp [hb]) (by simp)]
      split_ifs <;> simp_all
    simp only [hterm]
    calc (d : ℝ) ^ n = ∑ y : O, (1 : ℝ) := by simp [O]
      _ = ∑ x ∈ Finset.univ.image φ, (if φ (ψ x) = x then (1 : ℝ) else 0) := by
        rw [Finset.sum_image (fun a _ b _ h => hφinj h)]
        apply Finset.sum_congr rfl; intro y _; simp [hψφ]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => by split_ifs <;> norm_num)
  · unfold quantumMessages
    have hval : ∀ ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ, IsDensityMatrix ρ →
        ∀ P : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ,
        effectProb P (depolarizingN d n 1 ρ) = P.trace.re * (1 / (d : ℝ)) ^ n := by
      intro ρ hρ P
      rw [g53e_N1 d n hd0, hρ.2, mul_one, effectProb, Matrix.mul_smul, Matrix.mul_one,
        Matrix.trace_smul, smul_eq_mul, ← Complex.ofReal_pow, Complex.re_ofReal_mul, mul_comm]
    have hK : (Fintype.card (Fin n → Fin d) : ℝ) * (1 / (d : ℝ)) ^ n = 1 := by
      rw [hcard, ← mul_pow, mul_one_div_cancel (by positivity), one_pow]
    have hub := g53e_ub (depolarizingN d n 1) ((1 / (d : ℝ)) ^ n) (fun ρ hρ => by
      refine ⟨?_, fun P hP => le_of_eq (hval ρ hρ P)⟩
      rw [g53e_N1 d n hd0, hρ.2, mul_one]
      exact Matrix.PosSemidef.one.smul (by rw [← Complex.ofReal_pow]; exact_mod_cast (by positivity)))
    rw [hK] at hub
    set M0 := ⌊1 / (1 - e)⌋₊
    have hM0 : 0 < M0 := by
      apply Nat.floor_pos.mpr
      rw [le_div_iff₀ h1e]; linarith
    let w : Fin n → Fin d := fun _ => ⟨0, hd0⟩
    let C0 : Code (Fin n → Fin d) (Fin n → Fin d) M0 :=
      { positive := hM0
        word := fun _ => Matrix.diagonal (fun z => if z = w then (1 : ℂ) else 0)
        state := fun _ => g53e_diag_density _
        measurement := fun x => if x = ⟨0, hM0⟩ then 1 else 0
        positiveMeasurement := fun x => by split_ifs; exacts [Matrix.PosSemidef.one, Matrix.PosSemidef.zero]
        complete := by simp }
    refine g53e_opt _ e _ he heone hub C0 ?_
    simp only [hval _ (C0.state _), ← Finset.sum_mul, g53e_sumtr, hK, le_refl]

end
