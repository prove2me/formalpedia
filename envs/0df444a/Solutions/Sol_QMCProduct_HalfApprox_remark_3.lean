-- Prove2me | solution 1 for QMCProduct.HalfApprox.remark_3
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T22:59:39.238987+00:00
-- url     : https://prove2.me/submissions/010f57cd-0e79-48c5-9f37-652affbb21ab

import Mathlib
import Definitions.Def_QMCProduct_HalfApprox_Algorithm

open QMCProduct.HalfApprox QAlgorithms
open scoped Matrix

namespace QMCgAux

lemma kron_mul {n : ℕ} (A B : Fin n → Matrix Bool Bool ℂ) :
    kronAll A * kronAll B = kronAll (fun q => A q * B q) := by
  ext y z
  simp only [kronAll, Matrix.mul_apply, Matrix.of_apply]
  rw [Fintype.prod_sum]
  refine Fintype.sum_congr _ _ fun x => ?_
  rw [Finset.prod_mul_distrib]

lemma kron_one {n : ℕ} : kronAll (fun _ : Fin n => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext y z
  simp only [kronAll, Matrix.of_apply, Matrix.one_apply]
  by_cases h : y = z
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨q, hq⟩ : ∃ q, y q ≠ z q := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hq])

variable {n : ℕ} (i j : Fin n)

def P2 (A B : Matrix Bool Bool ℂ) : Op n :=
  kronAll (fun q => if q = i then A else if q = j then B else 1)

lemma P2_mul (A B C D : Matrix Bool Bool ℂ) :
    P2 i j A B * P2 i j C D = P2 i j (A * C) (B * D) := by
  unfold P2; rw [kron_mul]; congr 1; funext q; split_ifs <;> simp

lemma P2_one : P2 i j (1 : Matrix Bool Bool ℂ) 1 = (1 : Op n) := by
  unfold P2; rw [← kron_one]; congr 1; funext q; split_ifs <;> rfl

lemma P2_smul (hij : i ≠ j) (c d : ℂ) (A B : Matrix Bool Bool ℂ) :
    P2 i j (c • A) (d • B) = (c * d) • P2 i j A B := by
  ext y z
  simp only [P2, kronAll, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have h : ∀ q, (if q = i then c • A else if q = j then d • B else 1) (y q) (z q) =
      ((if q = i then c else 1) * (if q = j then d else 1)) *
        (if q = i then A else if q = j then B else 1) (y q) (z q) := by
    intro q
    by_cases h1 : q = i
    · subst h1; simp [hij]
    · by_cases h2 : q = j
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [Finset.prod_congr rfl (fun q _ => h q), Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp

lemma XX_eq (hij : i ≠ j) (A B : Matrix Bool Bool ℂ) :
    onSite i A * onSite j B = P2 i j A B := by
  unfold onSite P2; rw [kron_mul]; congr 1; funext q
  by_cases h1 : q = i
  · subst h1; simp [hij]
  · by_cases h2 : q = j
    · subst h2; simp [h1]
    · simp [h1, h2]

-- Pauli algebra on Bool
lemma xx : pauliX * pauliX = 1 := by
  ext a b; cases a <;> cases b <;> simp [pauliX, Matrix.mul_apply]
lemma yy : pauliY * pauliY = 1 := by
  ext a b; cases a <;> cases b <;> simp [pauliY, Matrix.mul_apply]
lemma zz : pauliZ * pauliZ = 1 := by
  ext a b; cases a <;> cases b <;> simp [pauliZ, Matrix.mul_apply]
lemma xy : pauliX * pauliY = Complex.I • pauliZ := by
  ext a b; cases a <;> cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]
lemma yx : pauliY * pauliX = (-Complex.I) • pauliZ := by
  ext a b; cases a <;> cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]
lemma yz : pauliY * pauliZ = Complex.I • pauliX := by
  ext a b; cases a <;> cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]
lemma zy : pauliZ * pauliY = (-Complex.I) • pauliX := by
  ext a b; cases a <;> cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]
lemma zx : pauliZ * pauliX = Complex.I • pauliY := by
  ext a b; cases a <;> cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]
lemma xz : pauliX * pauliZ = (-Complex.I) • pauliY := by
  ext a b; cases a <;> cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]



lemma kron_smul_at {n : ℕ} (f g : Fin n → Matrix Bool Bool ℂ) (q0 : Fin n) (c : ℂ)
    (h0 : g q0 = c • f q0) (h : ∀ q, q ≠ q0 → g q = f q) : kronAll g = c • kronAll f := by
  ext y z
  simp only [kronAll, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.prod_eq_mul_prod_compl q0, Fintype.prod_eq_mul_prod_compl q0, h0,
    Matrix.smul_apply, smul_eq_mul, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun q hq => ?_
  rw [h q (by simpa using hq)]

variable (k : Fin n)

def K (A B C : Matrix Bool Bool ℂ) : Op n :=
  kronAll (fun q => if q = i then A else if q = j then B else if q = k then C else 1)

variable {i j k}

lemma K_mul (A B C A' B' C' : Matrix Bool Bool ℂ) :
    K i j k A B C * K i j k A' B' C' = K i j k (A * A') (B * B') (C * C') := by
  unfold K; rw [kron_mul]; congr 1; funext q; split_ifs <;> simp

lemma K_one : K i j k (1 : Matrix Bool Bool ℂ) 1 1 = (1 : Op n) := by
  unfold K; rw [← kron_one]; congr 1; funext q; split_ifs <;> rfl

lemma K_smul1 (c : ℂ) (A B C : Matrix Bool Bool ℂ) :
    K i j k (c • A) B C = c • K i j k A B C :=
  kron_smul_at _ _ i c (by simp) (fun q hq => by simp [hq])

lemma K_smul2 (hij : i ≠ j) (c : ℂ) (A B C : Matrix Bool Bool ℂ) :
    K i j k A (c • B) C = c • K i j k A B C :=
  kron_smul_at _ _ j c (by simp [hij.symm]) (fun q hq => by simp [hq])

lemma K_smul3 (hik : i ≠ k) (hjk : j ≠ k) (c : ℂ) (A B C : Matrix Bool Bool ℂ) :
    K i j k A B (c • C) = c • K i j k A B C :=
  kron_smul_at _ _ k c (by simp [hik.symm, hjk.symm]) (fun q hq => by simp [hq])

lemma os_eq (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b : Fin n) (A B : Matrix Bool Bool ℂ)
    (hab : a ≠ b) (F : Matrix Bool Bool ℂ → Matrix Bool Bool ℂ → Op n)
    (hF : F A B = kronAll (fun q => if q = a then A else if q = b then B else 1)) :
    onSite a A * onSite b B = F A B := by
  rw [hF]; unfold onSite; rw [kron_mul]; congr 1; funext q
  by_cases h1 : q = a
  · subst h1; simp [hab]
  · by_cases h2 : q = b
    · subst h2; simp [h1]
    · simp [h1, h2]


section conn
variable (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
include hij hik hjk

lemma c_ij (A B : Matrix Bool Bool ℂ) : onSite i A * onSite j B = K i j k A B 1 := by
  unfold onSite K; rw [kron_mul]; congr 1; funext q
  by_cases h1 : q = i
  · subst h1; simp [hij]
  · by_cases h2 : q = j
    · subst h2; simp [h1]
    · by_cases h3 : q = k
      · subst h3; simp [h1, h2]
      · simp [h1, h2, h3]

lemma c_ik (A C : Matrix Bool Bool ℂ) : onSite i A * onSite k C = K i j k A 1 C := by
  unfold onSite K; rw [kron_mul]; congr 1; funext q
  by_cases h1 : q = i
  · subst h1; simp [hik]
  · by_cases h2 : q = j
    · subst h2; simp [h1, hjk]
    · by_cases h3 : q = k
      · subst h3; simp [h1, h2]
      · simp [h1, h2, h3]

lemma c_jk (B C : Matrix Bool Bool ℂ) : onSite j B * onSite k C = K i j k 1 B C := by
  unfold onSite K; rw [kron_mul]; congr 1; funext q
  by_cases h1 : q = i
  · subst h1; simp [hij, hik]
  · by_cases h2 : q = j
    · subst h2; simp [h1, hjk]
    · by_cases h3 : q = k
      · subst h3; simp [h1, h2]
      · simp [h1, h2, h3]
end conn

variable (i j k)
def Tij : Op n := K i j k pauliX pauliX 1 + K i j k pauliY pauliY 1 + K i j k pauliZ pauliZ 1
def Tik : Op n := K i j k pauliX 1 pauliX + K i j k pauliY 1 pauliY + K i j k pauliZ 1 pauliZ
def Tjk : Op n := K i j k 1 pauliX pauliX + K i j k 1 pauliY pauliY + K i j k 1 pauliZ pauliZ
variable {i j k}

section alg
variable (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
include hij hik hjk

lemma sq1 : Tij i j k * Tij i j k = (3 : ℂ) • (1 : Op n) - (2 : ℂ) • Tij i j k := by
  simp only [Tij, add_mul, mul_add, K_mul, xx, yy, zz, xy, yx, yz, zy, zx, xz, Matrix.one_mul,
    K_smul1, K_smul2 hij, K_smul3 hik hjk, smul_smul, K_one, Complex.I_mul_I, neg_mul_neg]
  module
lemma sq2 : Tik i j k * Tik i j k = (3 : ℂ) • (1 : Op n) - (2 : ℂ) • Tik i j k := by
  simp only [Tik, add_mul, mul_add, K_mul, xx, yy, zz, xy, yx, yz, zy, zx, xz, Matrix.one_mul,
    K_smul1, K_smul2 hij, K_smul3 hik hjk, smul_smul, K_one, Complex.I_mul_I, neg_mul_neg]
  module
lemma sq3 : Tjk i j k * Tjk i j k = (3 : ℂ) • (1 : Op n) - (2 : ℂ) • Tjk i j k := by
  simp only [Tjk, add_mul, mul_add, K_mul, xx, yy, zz, xy, yx, yz, zy, zx, xz, Matrix.one_mul,
    K_smul1, K_smul2 hij, K_smul3 hik hjk, smul_smul, K_one, Complex.I_mul_I, neg_mul_neg]
  module
lemma an12 : Tik i j k * Tij i j k = (2 : ℂ) • Tjk i j k - Tij i j k * Tik i j k := by
  simp only [Tij, Tik, Tjk, add_mul, mul_add, K_mul, xx, yy, zz, xy, yx, yz, zy, zx, xz,
    Matrix.one_mul, Matrix.mul_one, K_smul1, K_smul2 hij, K_smul3 hik hjk, smul_smul, K_one]
  module
lemma an13 : Tjk i j k * Tij i j k = (2 : ℂ) • Tik i j k - Tij i j k * Tjk i j k := by
  simp only [Tij, Tik, Tjk, add_mul, mul_add, K_mul, xx, yy, zz, xy, yx, yz, zy, zx, xz,
    Matrix.one_mul, Matrix.mul_one, K_smul1, K_smul2 hij, K_smul3 hik hjk, smul_smul, K_one]
  module
lemma an23 : Tjk i j k * Tik i j k = (2 : ℂ) • Tij i j k - Tik i j k * Tjk i j k := by
  simp only [Tij, Tik, Tjk, add_mul, mul_add, K_mul, xx, yy, zz, xy, yx, yz, zy, zx, xz,
    Matrix.one_mul, Matrix.mul_one, K_smul1, K_smul2 hij, K_smul3 hik hjk, smul_smul, K_one]
  module
end alg

lemma poly_add {m : ℕ} (P Q : Op n) (hP : IsPauliPoly m P) (hQ : IsPauliPoly m Q) :
    IsPauliPoly m (P + Q) := by
  obtain ⟨c1, h1, rfl⟩ := hP
  obtain ⟨c2, h2, rfl⟩ := hQ
  refine ⟨c1 + c2, fun s hs => ?_, ?_⟩
  · by_cases h : c1 s = 0
    · exact h2 s (by simpa [h] using hs)
    · exact h1 s h
  · simp only [Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

lemma poly_smul {m : ℕ} (r : ℝ) (P : Op n) (hP : IsPauliPoly m P) :
    IsPauliPoly m ((r : ℂ) • P) := by
  obtain ⟨c1, h1, rfl⟩ := hP
  refine ⟨r • c1, fun s hs => h1 s (by intro h; simp [h] at hs), ?_⟩
  simp only [Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]

lemma poly_basis {m : ℕ} (s : PauliString n) (hs : pauliDegree s ≤ m) :
    IsPauliPoly m (pauliOp s) := by
  refine ⟨fun t => if t = s then 1 else 0, fun t ht => ?_, ?_⟩
  · by_cases h : t = s
    · subst h; exact hs
    · simp [h] at ht
  · simp [apply_ite (fun x : ℝ => (x : ℂ)), ite_smul]

lemma deg_le (s : PauliString n) (a b : Fin n) (h : ∀ q, q ≠ a → q ≠ b → s q = 0) :
    pauliDegree s ≤ 2 := by
  unfold pauliDegree
  have h' : Finset.univ.filter (fun q => s q ≠ 0) ⊆ {a, b} := by
    intro q hq
    rw [Finset.mem_filter] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hc; push_neg at hc
    exact hq.2 (h q hc.1 hc.2)
  exact (Finset.card_le_card h').trans Finset.card_le_two

def str3 (a b c : Fin 4) : PauliString n :=
  fun q => if q = i then a else if q = j then b else if q = k then c else 0

lemma K_pauli (a b c : Fin 4) :
    K i j k (pauli1 a) (pauli1 b) (pauli1 c) = pauliOp (str3 (i := i) (j := j) (k := k) a b c) := by
  unfold K pauliOp str3; congr 1; funext q; split_ifs <;> simp [pauli1]

lemma p0 : pauli1 0 = 1 := by simp [pauli1]
lemma p1 : pauli1 1 = pauliX := by simp [pauli1]
lemma p2 : pauli1 2 = pauliY := by simp [pauli1]
lemma p3 : pauli1 3 = pauliZ := by simp [pauli1]

section poly
variable (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
include hij hik hjk

lemma polyK (a b c : Fin 4) (h : a = 0 ∨ b = 0 ∨ c = 0) :
    IsPauliPoly 2 (K i j k (pauli1 a) (pauli1 b) (pauli1 c)) := by
  rw [K_pauli]
  refine poly_basis _ ?_
  rcases h with h | h | h
  · refine deg_le _ j k fun q h1 h2 => ?_
    simp only [str3, h1, h2, if_false]; split_ifs <;> simp_all
  · refine deg_le _ i k fun q h1 h2 => ?_
    simp only [str3, h1, h2, if_false]; split_ifs <;> simp_all
  · refine deg_le _ i j fun q h1 h2 => ?_
    simp only [str3, h1, h2, if_false]; split_ifs <;> simp_all

lemma polyT1 : IsPauliPoly 2 (Tij i j k) := by
  unfold Tij
  rw [← p0, ← p1, ← p2, ← p3]
  exact poly_add _ _ (poly_add _ _ (polyK hij hik hjk _ _ _ (by simp))
    (polyK hij hik hjk _ _ _ (by simp))) (polyK hij hik hjk _ _ _ (by simp))
lemma polyT2 : IsPauliPoly 2 (Tik i j k) := by
  unfold Tik
  rw [← p0, ← p1, ← p2, ← p3]
  exact poly_add _ _ (poly_add _ _ (polyK hij hik hjk _ _ _ (by simp))
    (polyK hij hik hjk _ _ _ (by simp))) (polyK hij hik hjk _ _ _ (by simp))
lemma polyT3 : IsPauliPoly 2 (Tjk i j k) := by
  unfold Tjk
  rw [← p0, ← p1, ← p2, ← p3]
  exact poly_add _ _ (poly_add _ _ (polyK hij hik hjk _ _ _ (by simp))
    (polyK hij hik hjk _ _ _ (by simp))) (polyK hij hik hjk _ _ _ (by simp))
lemma polyOne : IsPauliPoly 2 (1 : Op n) := by
  rw [← K_one (i := i) (j := j) (k := k), ← p0]
  exact polyK hij hik hjk _ _ _ (by simp)
end poly

end QMCgAux

open QMCgAux

theorem gramPSD {n : ℕ} (ρt : Op n) (hρ : IsPseudoDensity 2 ρt)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (swapGram (s ρt i j) (s ρt i k) (s ρt j k)).PosSemidef := by
  set T1 := Tij i j k with hT1
  set T2 := Tik i j k with hT2
  set T3 := Tjk i j k with hT3
  have e1 := sq1 hij hik hjk
  have e2 := sq2 hij hik hjk
  have e3 := sq3 hij hik hjk
  have a12 := an12 hij hik hjk
  have a13 := an13 hij hik hjk
  have a23 := an23 hij hik hjk
  have hp1 := polyT1 hij hik hjk
  have hp2 := polyT2 hij hik hjk
  have hp3 := polyT3 hij hik hjk
  have hp0 := polyOne (n := n) hij hik hjk
  -- traces
  set τ1 := (ρt * T1).trace.re with hτ1
  set τ2 := (ρt * T2).trace.re with hτ2
  set τ3 := (ρt * T3).trace.re with hτ3
  have tr1 : (ρt * 1).trace = 1 := by rw [Matrix.mul_one]; exact hρ.2.1
  have hs1 : s ρt i j = (1 + τ1) / 2 := by
    rw [hτ1, hT1]
    unfold s val X Y Z Tij
    rw [c_ij hij hik hjk, c_ij hij hik hjk, c_ij hij hik hjk]
    simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re]; ring
  have hs2 : s ρt i k = (1 + τ2) / 2 := by
    rw [hτ2, hT2]
    unfold s val X Y Z Tik
    rw [c_ik hij hik hjk, c_ik hij hik hjk, c_ik hij hik hjk]
    simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re]; ring
  have hs3 : s ρt j k = (1 + τ3) / 2 := by
    rw [hτ3, hT3]
    unfold s val X Y Z Tjk
    rw [c_jk hij hik hjk, c_jk hij hik hjk, c_jk hij hik hjk]
    simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re]; ring
  rw [hs1, hs2, hs3, Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [swapGram]
  · set y0 := x 0 + (x 1 + x 2 + x 3) / 2
    set y1 := x 1 / 2
    set y2 := x 2 / 2
    set y3 := x 3 / 2
    set P : Op n := (y0 : ℂ) • (1 : Op n) + (y1 : ℂ) • T1 + (y2 : ℂ) • T2 + (y3 : ℂ) • T3 with hP
    have hPoly : IsPauliPoly 2 P :=
      poly_add _ _ (poly_add _ _ (poly_add _ _ (poly_smul _ _ hp0) (poly_smul _ _ hp1))
        (poly_smul _ _ hp2)) (poly_smul _ _ hp3)
    have hPP : P * P = ((y0 ^ 2 + 3 * (y1 ^ 2 + y2 ^ 2 + y3 ^ 2) : ℝ) : ℂ) • (1 : Op n) +
        ((2 * y0 * y1 - 2 * y1 ^ 2 + 2 * y2 * y3 : ℝ) : ℂ) • T1 +
        ((2 * y0 * y2 - 2 * y2 ^ 2 + 2 * y1 * y3 : ℝ) : ℂ) • T2 +
        ((2 * y0 * y3 - 2 * y3 ^ 2 + 2 * y1 * y2 : ℝ) : ℂ) • T3 := by
      rw [hP, hT1, hT2, hT3]
      simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, e1, e2, e3, a12, a13, a23]
      push_cast
      module
    have h := hρ.2.2 P hPoly
    rw [Matrix.mul_assoc, hPP] at h
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
      Complex.add_re, Complex.re_ofReal_mul, tr1, Complex.one_re] at h
    rw [← hτ1, ← hτ2, ← hτ3] at h
    have hq : star x ⬝ᵥ (swapGram ((1 + τ1) / 2) ((1 + τ2) / 2) ((1 + τ3) / 2) *ᵥ x) =
        y0 ^ 2 + 3 * (y1 ^ 2 + y2 ^ 2 + y3 ^ 2) + (2 * y0 * y1 - 2 * y1 ^ 2 + 2 * y2 * y3) * τ1 +
        (2 * y0 * y2 - 2 * y2 ^ 2 + 2 * y1 * y3) * τ2 +
        (2 * y0 * y3 - 2 * y3 ^ 2 + 2 * y1 * y2) * τ3 := by
      simp [swapGram, dotProduct, Matrix.mulVec, Fin.sum_univ_four]
      ring
    rw [hq]; linarith

theorem fact2 {n : ℕ} (ρt : Op n) (hρ : IsPseudoDensity 2 ρt)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlarge : (911 / 1000 : ℝ) < v ρt i j) :
    v ρt i k < 1 / 3 := by
  by_contra hc
  push_neg at hc
  have hG := (Matrix.posSemidef_iff_dotProduct_mulVec.1 (gramPSD ρt hρ i j k hij hik hjk)).2
    ![1, 51 / 50, 89 / 200, -1513 / 11550]
  have hsv : ∀ a b, s ρt a b = (1 - 3 * v ρt a b) / 2 := by
    intro a b; unfold s v; ring
  simp only [hsv] at hG
  simp [swapGram, dotProduct, Matrix.mulVec, Fin.sum_univ_four] at hG
  norm_num at hG
  linarith

lemma os_comm {n : ℕ} (a b : Fin n) (hab : a ≠ b) (A B : Matrix Bool Bool ℂ) :
    onSite a A * onSite b B = onSite b B * onSite a A := by
  unfold onSite; rw [kron_mul, kron_mul]; congr 1; funext q
  by_cases h1 : q = a
  · subst h1; simp [hab]
  · by_cases h2 : q = b
    · subst h2; simp [h1]
    · simp [h1, h2]

lemma v_symm {n : ℕ} (ρt : Op n) (a b : Fin n) (hab : a ≠ b) : v ρt a b = v ρt b a := by
  unfold v val X Y Z
  rw [os_comm a b hab, os_comm a b hab, os_comm a b hab]

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ρt : Op n) (hρ : IsPseudoDensity 2 ρt)
    (e f : Fin n × Fin n) (he : e ∈ large G ρt (911 / 1000 : ℝ))
    (hf : f ∈ large G ρt (911 / 1000 : ℝ)) (hef : e ≠ f) :
    e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
  obtain ⟨a, b⟩ := e
  obtain ⟨c, d⟩ := f
  simp only [large, edges, Finset.mem_filter, Finset.mem_univ, true_and] at he hf
  obtain ⟨⟨hab, -⟩, hve⟩ := he
  obtain ⟨⟨hcd, -⟩, hvf⟩ := hf
  simp only at hab hcd hve hvf ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl
    have hbd : b ≠ d := by rintro rfl; exact hef rfl
    have := fact2 ρt hρ a b d hab.ne hcd.ne hbd hve
    linarith
  · rintro rfl
    have hbc : b ≠ c := by intro h; subst h; exact absurd (hab.trans hcd) (lt_irrefl _)
    have := fact2 ρt hρ a b c hab.ne (by intro h; subst h; exact lt_irrefl _ hcd) hbc hve
    rw [v_symm ρt a c (by intro h; subst h; exact lt_irrefl _ hcd)] at this
    linarith
  · rintro rfl
    have hda : d ≠ a := by intro h; subst h; exact absurd (hab.trans hcd) (lt_irrefl _)
    have := fact2 ρt hρ b d a hcd.ne hab.ne'  hda hvf
    rw [v_symm ρt b a hab.ne'] at this
    linarith
  · rintro rfl
    have hac : a ≠ c := by rintro rfl; exact hef rfl
    have h1 := fact2 ρt hρ b a c hab.ne' hcd.ne' hac (by rw [v_symm ρt b a hab.ne']; exact hve)
    rw [v_symm ρt b c hcd.ne'] at h1
    linarith
