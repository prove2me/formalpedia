-- Prove2me | solution 1 for SuperconductingQC.toffoli_mem_closure_singleQubit_CNOT
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T12:43:30.446259+00:00
-- url     : https://prove2.me/submissions/03c8cf83-1b9b-4d06-939e-9e7877383409

import Mathlib
import Definitions.Def_SuperconductingQC_Gates

open scoped Matrix Kronecker

namespace SCTof
open Matrix SuperconductingQC

abbrev Q := Fin 3 → Fin 2

def e3 : Q ≃ Fin 2 × Fin 2 × Fin 2 where
  toFun z := (z 0, z 1, z 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv z := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

lemma sum3 {M : Type*} [AddCommMonoid M] (f : Q → M) :
    ∑ z, f z = ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, f ![a, b, c] := by
  rw [← e3.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

lemma eq_iff3 (x y : Q) : x = y ↔ x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h0, h1, h2⟩; funext i; fin_cases i <;> assumption

/-- block matrices w.r.t. qubit 2 -/
def Bm (F : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) : Matrix Q Q ℂ := fun x y =>
  if x 0 = y 0 ∧ x 1 = y 1 then F (x 0) (x 1) (x 2) (y 2) else 0

lemma Bm_mul (F G : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    Bm F * Bm G = Bm (fun a b => F a b * G a b) := by
  ext x y
  rw [mul_apply, sum3]
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, x = ![a, b, c] := ⟨x 0, x 1, x 2, (e3.left_inv x).symm⟩
  obtain ⟨d, e, f, rfl⟩ : ∃ a b c, y = ![a, b, c] := ⟨y 0, y 1, y 2, (e3.left_inv y).symm⟩
  simp only [Bm]
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;>
    simp [Fin.sum_univ_two, mul_apply]


lemma Bm_star (F : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    star (Bm F) = Bm (fun a b => star (F a b)) := by
  ext x y
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, x = ![a, b, c] := ⟨x 0, x 1, x 2, (e3.left_inv x).symm⟩
  obtain ⟨d, e, f, rfl⟩ : ∃ a b c, y = ![a, b, c] := ⟨y 0, y 1, y 2, (e3.left_inv y).symm⟩
  simp only [Bm, star_apply]
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;> simp

lemma Bm_one : Bm (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  ext x y
  simp only [Bm, one_apply, eq_iff3 x y]
  by_cases h : x 0 = y 0 ∧ x 1 = y 1
  · simp [h]
  · rw [if_neg h, if_neg (by tauto)]

lemma Bm_unitary (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ unitaryGroup (Fin 2) ℂ) :
    Bm (fun _ _ => U) ∈ unitaryGroup Q ℂ := by
  rw [mem_unitaryGroup_iff] at *
  rw [Bm_star, Bm_mul, hU, Bm_one]

lemma onQubit2 (U : Matrix (Fin 2) (Fin 2) ℂ) : onQubit (2 : Fin 3) U = Bm (fun _ _ => U) := by
  ext x y
  simp only [onQubit, Bm]
  congr 1
  apply propext
  constructor
  · intro h; exact ⟨h 0 (by decide), h 1 (by decide)⟩
  · rintro ⟨h0, h1⟩ j hj; fin_cases j
    · exact h0
    · exact h1
    · exact absurd rfl hj

noncomputable def Hm : Matrix (Fin 2) (Fin 2) ℂ := ((Real.sqrt 2)⁻¹ : ℂ) • !![1, 1; 1, -1]
def Xm : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def Zm : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

lemma sq2 : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring

lemma Hm_mul_Hm : Hm * Hm = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Hm, mul_apply, Fin.sum_univ_two, ← mul_assoc] <;> rw [sq2] <;> norm_num

lemma Hm_Z_Hm : Hm * Zm * Hm = Xm := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Hm, Zm, Xm, mul_apply, Fin.sum_univ_two, ← mul_assoc] <;> rw [sq2] <;> norm_num

lemma Hm_unitary : Hm ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff']
  have : star Hm = Hm := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Hm, star_apply, Complex.conj_ofReal]
  rw [this, Hm_mul_Hm]

lemma toffoli_eq : toffoli = Bm (fun a b => if a = 1 ∧ b = 1 then Xm else 1) := by
  ext x y
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, x = ![a, b, c] := ⟨x 0, x 1, x 2, (e3.left_inv x).symm⟩
  obtain ⟨d, e, f, rfl⟩ : ∃ a b c, y = ![a, b, c] := ⟨y 0, y 1, y 2, (e3.left_inv y).symm⟩
  simp only [toffoli, Bm]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> fin_cases f <;>
    simp [Xm, one_apply]

def cczPhase (x : Q) : ℂ := if x 0 = 1 ∧ x 1 = 1 ∧ x 2 = 1 then -1 else 1

lemma ccz_eq : diagonal cczPhase = Bm (fun a b => if a = 1 ∧ b = 1 then Zm else 1) := by
  ext x y
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, x = ![a, b, c] := ⟨x 0, x 1, x 2, (e3.left_inv x).symm⟩
  obtain ⟨d, e, f, rfl⟩ : ∃ a b c, y = ![a, b, c] := ⟨y 0, y 1, y 2, (e3.left_inv y).symm⟩
  simp only [cczPhase, Bm, diagonal_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> fin_cases f <;>
    simp [Zm, one_apply]

lemma H_ccz_H : onQubit (2 : Fin 3) Hm * diagonal cczPhase * onQubit (2 : Fin 3) Hm = toffoli := by
  rw [onQubit2, ccz_eq, Bm_mul, Bm_mul, toffoli_eq]
  congr 1; funext a b
  split_ifs
  · exact Hm_Z_Hm
  · rw [mul_one, Hm_mul_Hm]

/-! phases -/
noncomputable def ω : ℂ := Complex.exp (↑(Real.pi / 4) * Complex.I)

lemma ω8 : ω ^ 8 = 1 := by
  rw [ω, ← Complex.exp_nat_mul]
  have : ((8 : ℕ) : ℂ) * (↑(Real.pi / 4) * Complex.I) = ↑(1 : ℤ) * (2 * ↑Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma ω4 : ω ^ 4 = -1 := by
  rw [ω, ← Complex.exp_nat_mul]
  have : ((4 : ℕ) : ℂ) * (↑(Real.pi / 4) * Complex.I) = ↑Real.pi * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_pi_mul_I]

lemma ωu : star ω * ω = 1 := by
  rw [ω, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  ring_nf; exact Complex.exp_zero

lemma pow_mod8 (n : ℕ) : ω ^ n = ω ^ (n % 8) := by
  conv_lhs => rw [← Nat.mod_add_div n 8, pow_add, pow_mul, ω8, one_pow, mul_one]

noncomputable def Tg (m : ℕ) : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, ω ^ m]

lemma Tg_unitary (m : ℕ) : Tg m ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff', Tg, star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; fin_cases i
  · simp
  · show star (ω ^ m) * ω ^ m = 1
    rw [star_pow, ← mul_pow, ωu, one_pow]

lemma onQubit_Tg (k : Fin 3) (m : ℕ) :
    onQubit k (Tg m) = diagonal (fun x => ω ^ (m * (x k).val)) := by
  ext x y
  simp only [onQubit, Tg, diagonal_apply]
  by_cases hxy : x = y
  · subst hxy; simp only [ite_true, implies_true]
    generalize x k = t; fin_cases t <;> simp
  · rw [if_neg hxy]
    split_ifs with h h'
    · exfalso; apply hxy; funext j; by_cases hj : j = k
      · subst hj; exact h'
      · exact h j hj
    · rfl
    · rfl

lemma diag_unitary (d : Q → ℂ) (hd : ∀ x, star (d x) * d x = 1) : diagonal d ∈ unitaryGroup Q ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1; funext x; exact hd x

/-! CNOT as permutation -/
def σ (i j : Fin 3) (y : Q) : Q := Function.update y j (y j + y i)

def Pm (f : Q → Q) : Matrix Q Q ℂ := fun x y => if x = f y then 1 else 0

lemma σ_invol (i j : Fin 3) (hij : i ≠ j) (y : Q) : σ i j (σ i j y) = y := by
  funext l
  simp only [σ, Function.update_apply]
  by_cases hl : l = j
  · subst hl; simp only [if_true, if_neg hij]
    generalize y l = s; generalize y i = t; fin_cases s <;> fin_cases t <;> decide
  · simp [hl]

lemma onPair_CNOT (i j : Fin 3) (hij : i ≠ j) : onPair i j CNOT = Pm (σ i j) := by
  ext x y
  simp only [onPair, CNOT, Pm]
  have key : ((∀ l, l ≠ i → l ≠ j → x l = y l) ∧ (x i = y i ∧ x j = y j + y i)) ↔ x = σ i j y := by
    constructor
    · rintro ⟨h, hi, hj⟩
      funext l
      simp only [σ, Function.update_apply]
      by_cases hl : l = j
      · subst hl; simp [hj]
      · rw [if_neg hl]; by_cases hl' : l = i
        · subst hl'; exact hi
        · exact h l hl' hl
    · rintro rfl
      refine ⟨fun l hli hlj => ?_, ?_, ?_⟩
      · simp [σ, Function.update_apply, hlj]
      · simp [σ, Function.update_apply, hij]
      · simp [σ]
  by_cases h1 : ∀ l, l ≠ i → l ≠ j → x l = y l
  · rw [if_pos h1]
    by_cases h2 : x i = y i ∧ x j = y j + y i
    · rw [if_pos h2, if_pos (key.mp ⟨h1, h2⟩)]
    · rw [if_neg h2, if_neg (fun h => h2 (key.mpr h).2)]
  · rw [if_neg h1, if_neg (fun h => h1 (key.mpr h).1)]

lemma Pm_conj (f : Q → Q) (hf : ∀ y, f (f y) = y) (d : Q → ℂ) :
    Pm f * diagonal d * Pm f = diagonal (fun x => d (f x)) := by
  ext x y
  rw [mul_apply, Finset.sum_eq_single (f y)]
  · simp only [mul_diagonal, Pm, diagonal_apply, hf, if_true, mul_one]
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy]
  · intro z _ hz; simp [Pm, hz]
  · simp

lemma Pm_unitary (f : Q → Q) (hf : ∀ y, f (f y) = y) : Pm f ∈ unitaryGroup Q ℂ := by
  rw [mem_unitaryGroup_iff']
  have hs : star (Pm f) = Pm f := by
    ext x y
    simp only [star_apply, Pm]
    have : (y = f x) ↔ (x = f y) := ⟨fun h => by rw [h, hf], fun h => by rw [h, hf]⟩
    by_cases h : x = f y
    · rw [if_pos (this.mpr h), if_pos h]; simp
    · rw [if_neg (fun h' => h (this.mp h')), if_neg h]; simp
  rw [hs]
  have := Pm_conj f hf (fun _ => 1)
  rw [diagonal_one, mul_one] at this
  rw [this]

noncomputable def Tm (k : Fin 3) (m : ℕ) : Matrix Q Q ℂ := onQubit k (Tg m)
def Cm (i j : Fin 3) : Matrix Q Q ℂ := onPair i j CNOT

def E (x : Q) : ℕ := (x 0).val + (x 1).val + (x 2).val + 7 * ((σ 0 1 x) 1).val +
  7 * ((σ 0 2 x) 2).val + 7 * ((σ 1 2 x) 2).val + ((σ 1 2 (σ 0 2 x)) 2).val

lemma E_mod (x : Q) : E x % 8 = if x 0 = 1 ∧ x 1 = 1 ∧ x 2 = 1 then 4 else 0 := by
  revert x; decide

lemma Dprod_eq : Tm 0 1 * Tm 1 1 * Tm 2 1 * (Cm 0 1 * Tm 1 7 * Cm 0 1) *
    (Cm 0 2 * Tm 2 7 * Cm 0 2) * (Cm 1 2 * Tm 2 7 * Cm 1 2) *
    (Cm 0 2 * (Cm 1 2 * Tm 2 1 * Cm 1 2) * Cm 0 2) = diagonal cczPhase := by
  simp only [Tm, Cm, onQubit_Tg, onPair_CNOT _ _ (by decide : (0:Fin 3) ≠ 1),
    onPair_CNOT _ _ (by decide : (0:Fin 3) ≠ 2), onPair_CNOT _ _ (by decide : (1:Fin 3) ≠ 2),
    Pm_conj _ (σ_invol 0 1 (by decide)), Pm_conj _ (σ_invol 0 2 (by decide)),
    Pm_conj _ (σ_invol 1 2 (by decide)), diagonal_mul_diagonal]
  congr 1; funext x
  trans ω ^ E x
  · simp only [E, pow_add, one_mul]
  · rw [pow_mod8, E_mod]; unfold cczPhase; split_ifs <;> simp [ω4]

theorem main : ∃ W ∈ Subgroup.closure (singleQubitGates 3 ∪ twoQubitGateInstances 3 CNOT),
    (W : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ) = toffoli := by
  let tU (k : Fin 3) (m : ℕ) : unitaryGroup Q ℂ := ⟨Tm k m, by
    rw [Tm, onQubit_Tg]; exact diag_unitary _ (fun x => by rw [star_pow, ← mul_pow, ωu, one_pow])⟩
  have tM : ∀ k m, tU k m ∈ Subgroup.closure (singleQubitGates 3 ∪ twoQubitGateInstances 3 CNOT) :=
    fun k m => Subgroup.subset_closure (Or.inl ⟨k, Tg m, Tg_unitary m, rfl⟩)
  let cU (i j : Fin 3) (h : i ≠ j) : unitaryGroup Q ℂ := ⟨Cm i j, by
    rw [Cm, onPair_CNOT i j h]; exact Pm_unitary _ (σ_invol i j h)⟩
  have cM : ∀ i j h, cU i j h ∈ Subgroup.closure (singleQubitGates 3 ∪ twoQubitGateInstances 3 CNOT) :=
    fun i j h => Subgroup.subset_closure (Or.inr ⟨i, j, h, rfl⟩)
  let hU : unitaryGroup Q ℂ := ⟨onQubit 2 Hm, by rw [onQubit2]; exact Bm_unitary Hm Hm_unitary⟩
  have hM : hU ∈ Subgroup.closure (singleQubitGates 3 ∪ twoQubitGateInstances 3 CNOT) :=
    Subgroup.subset_closure (Or.inl ⟨2, Hm, Hm_unitary, rfl⟩)
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  refine ⟨hU * (tU 0 1 * tU 1 1 * tU 2 1 * (cU 0 1 h01 * tU 1 7 * cU 0 1 h01) *
    (cU 0 2 h02 * tU 2 7 * cU 0 2 h02) * (cU 1 2 h12 * tU 2 7 * cU 1 2 h12) *
    (cU 0 2 h02 * (cU 1 2 h12 * tU 2 1 * cU 1 2 h12) * cU 0 2 h02)) * hU, ?_, ?_⟩
  · repeat' apply Subgroup.mul_mem
    all_goals first | exact hM | exact tM _ _ | exact cM _ _ h01 | exact cM _ _ h02 | exact cM _ _ h12
  · show onQubit 2 Hm * (Tm 0 1 * Tm 1 1 * Tm 2 1 * (Cm 0 1 * Tm 1 7 * Cm 0 1) *
      (Cm 0 2 * Tm 2 7 * Cm 0 2) * (Cm 1 2 * Tm 2 7 * Cm 1 2) *
      (Cm 0 2 * (Cm 1 2 * Tm 2 1 * Cm 1 2) * Cm 0 2)) * onQubit 2 Hm = toffoli
    rw [Dprod_eq, H_ccz_H]

end SCTof


open SuperconductingQC in
theorem solution :
    ∃ W ∈ Subgroup.closure (singleQubitGates 3 ∪ twoQubitGateInstances 3 CNOT),
      (W : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ) = toffoli :=
  SCTof.main
