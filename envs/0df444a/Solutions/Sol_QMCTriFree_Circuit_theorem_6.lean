-- Prove2me | solution 1 for QMCTriFree.Circuit.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:03:05.104805+00:00
-- url     : https://prove2.me/submissions/3af6021b-be92-4f4a-b2fa-dbbb2a9111c0

import Mathlib
import Definitions.Def_QMCTriFree_Circuit_Lasserre

set_option autoImplicit false

open QMCProduct.HalfApprox Matrix MeasureTheory ProbabilityTheory

namespace Aux_QMCTriFree_theorem_6

open QMCTriFree.Circuit

theorem pauli1_zero : pauli1 0 = 1 := by
  simp [pauli1]

theorem pauli1_herm (a : Fin 4) : (pauli1 a)ᴴ = pauli1 a := by
  fin_cases a <;> ext i j <;> cases i <;> cases j <;>
    simp [pauli1, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ,
      Matrix.conjTranspose_apply]

theorem pauli1_sq (a : Fin 4) : pauli1 a * pauli1 a = 1 := by
  fin_cases a <;> ext i j <;> cases i <;> cases j <;>
    simp [pauli1, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ,
      Matrix.mul_apply, Fintype.sum_bool]

theorem pauli1_comm (a b : Fin 4) :
    pauli1 a * pauli1 b = pauli1 b * pauli1 a ∨ pauli1 a * pauli1 b = -(pauli1 b * pauli1 a) := by
  fin_cases a <;> fin_cases b <;>
    first
    | (left; ext i j; cases i <;> cases j <;>
        simp [pauli1, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ,
          Matrix.mul_apply, Fintype.sum_bool]; done)
    | (right; ext i j; cases i <;> cases j <;>
        simp [pauli1, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ,
          Matrix.mul_apply, Fintype.sum_bool]; done)

theorem pauli1_comm' (a b : Fin 4) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ pauli1 a * pauli1 b = ε • (pauli1 b * pauli1 a) := by
  rcases pauli1_comm a b with h | h
  · exact ⟨1, Or.inl rfl, by rw [one_smul]; exact h⟩
  · exact ⟨-1, Or.inr rfl, by rw [neg_one_smul]; exact h⟩

theorem kA_mul {n : ℕ} (A B : Fin n → Matrix Bool Bool ℂ) :
    QAlgorithms.kronAll A * QAlgorithms.kronAll B = QAlgorithms.kronAll (fun q => A q * B q) := by
  ext y z
  simp only [QAlgorithms.kronAll, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.prod_mul_distrib]

theorem kA_ct {n : ℕ} (A : Fin n → Matrix Bool Bool ℂ) :
    (QAlgorithms.kronAll A)ᴴ = QAlgorithms.kronAll (fun q => (A q)ᴴ) := by
  ext y z
  simp only [QAlgorithms.kronAll, Matrix.conjTranspose_apply, Matrix.of_apply, star_prod]

theorem kA_one {n : ℕ} :
    QAlgorithms.kronAll (fun _ : Fin n => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext y z
  simp [QAlgorithms.kronAll, Matrix.one_apply, Finset.prod_boole, funext_iff]

theorem kA_smul {n : ℕ} (c : Fin n → ℂ) (A : Fin n → Matrix Bool Bool ℂ) :
    QAlgorithms.kronAll (fun q => c q • A q) = (∏ q, c q) • QAlgorithms.kronAll A := by
  ext y z
  simp [QAlgorithms.kronAll, Finset.prod_mul_distrib]

theorem pauliOp_herm {n : ℕ} (s : PauliString n) : (pauliOp s)ᴴ = pauliOp s := by
  unfold pauliOp
  rw [kA_ct]
  congr 1
  funext q
  exact pauli1_herm _

theorem pauliOp_unit {n : ℕ} (s : PauliString n) : (pauliOp s)ᴴ * pauliOp s = 1 := by
  rw [pauliOp_herm]
  unfold pauliOp
  rw [kA_mul]
  have : (fun q => pauli1 (s q) * pauli1 (s q)) = fun _ => (1 : Matrix Bool Bool ℂ) :=
    funext (fun q => pauli1_sq _)
  rw [this, kA_one]

theorem pauliOp_pm {n : ℕ} (s t : PauliString n) :
    (pauliOp s)ᴴ * pauliOp t = (pauliOp t)ᴴ * pauliOp s ∨
      (pauliOp s)ᴴ * pauliOp t = -((pauliOp t)ᴴ * pauliOp s) := by
  rw [pauliOp_herm, pauliOp_herm]
  unfold pauliOp
  rw [kA_mul, kA_mul]
  choose ε hε hcomm using fun q => pauli1_comm' (s q) (t q)
  have hfun : (fun q => pauli1 (s q) * pauli1 (t q)) =
      fun q => ε q • (pauli1 (t q) * pauli1 (s q)) := funext hcomm
  rw [hfun, kA_smul]
  have hsq : (∏ q, ε q) * (∏ q, ε q) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro q _
    rcases hε q with h | h <;> simp [h]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · left
    rw [h, one_smul]
  · right
    rw [h, neg_one_smul]

theorem deg_site {n : ℕ} (a : Fin 4) (i : Fin n) : pauliDegree (siteStr a i) ≤ 2 := by
  unfold pauliDegree
  have hsub : Finset.univ.filter (fun t => siteStr a i t ≠ 0) ⊆ {i} := by
    intro t ht
    rw [Finset.mem_filter] at ht
    rw [Finset.mem_singleton]
    by_contra h
    apply ht.2
    simp [siteStr, h]
  calc (Finset.univ.filter (fun t => siteStr a i t ≠ 0)).card ≤ ({i} : Finset (Fin n)).card :=
        Finset.card_le_card hsub
    _ ≤ 2 := by simp

theorem site_prod {n : ℕ} (a : Fin 4) (i j : Fin n) (hij : i ≠ j) :
    (pauliOp (siteStr a i))ᴴ * pauliOp (siteStr a j) = pauliOp (pairStr a i j) := by
  rw [pauliOp_herm]
  unfold pauliOp
  rw [kA_mul]
  congr 1
  funext q
  simp only [siteStr, pairStr]
  by_cases hqi : q = i
  · have hqj : q ≠ j := fun h => hij (hqi.symm.trans h)
    rw [if_pos hqi, if_neg hqj, if_pos (Or.inl hqi), pauli1_zero, mul_one]
  · by_cases hqj : q = j
    · rw [if_neg hqi, if_pos hqj, if_pos (Or.inr hqj), pauli1_zero, one_mul]
    · rw [if_neg hqi, if_neg hqj, if_neg (fun h : q = i ∨ q = j => h.elim hqi hqj), pauli1_zero,
        mul_one]

theorem gram {n : ℕ} (A B : Op n) (ψ : QAlgorithms.Qubits n → ℂ) :
    expect (Aᴴ * B) ψ = star (A *ᵥ ψ) ⬝ᵥ (B *ᵥ ψ) := by
  unfold expect
  rw [← Matrix.mulVec_mulVec ψ Aᴴ B, Matrix.dotProduct_mulVec (star ψ) Aᴴ (B *ᵥ ψ),
    ← Matrix.star_mulVec A ψ]

theorem re_dot {n : ℕ} (a b : QAlgorithms.Qubits n → ℂ) :
    (star a ⬝ᵥ b).re = ∑ y, ((a y).re * (b y).re + (a y).im * (b y).im) := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  ring

theorem ex_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Op n)
    (ψ : QAlgorithms.Qubits n → ℂ) : expect (∑ i ∈ s, f i) ψ = ∑ i ∈ s, expect (f i) ψ := by
  unfold expect
  rw [Matrix.sum_mulVec, dotProduct_sum]

theorem ex_smul {n : ℕ} (c : ℂ) (A : Op n) (ψ : QAlgorithms.Qubits n → ℂ) :
    expect (c • A) ψ = c * expect A ψ := by
  unfold expect
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem ex_sub {n : ℕ} (A B : Op n) (ψ : QAlgorithms.Qubits n → ℂ) :
    expect (A - B) ψ = expect A ψ - expect B ψ := by
  unfold expect
  rw [Matrix.sub_mulVec, dotProduct_sub]

theorem ex_neg {n : ℕ} (A : Op n) (ψ : QAlgorithms.Qubits n → ℂ) :
    expect (-A) ψ = -expect A ψ := by
  unfold expect
  rw [Matrix.neg_mulVec, dotProduct_neg]

theorem ex_zero {n : ℕ} (ψ : QAlgorithms.Qubits n → ℂ) : expect (0 : Op n) ψ = 0 := by
  unfold expect
  rw [Matrix.zero_mulVec, dotProduct_zero]

noncomputable def Mψ {n : ℕ} (ψ : QAlgorithms.Qubits n → ℂ) : Matrix (P2 n) (P2 n) ℝ :=
  Matrix.of fun A B => (expect ((pauliOp A.1)ᴴ * pauliOp B.1) ψ).re

theorem Mψ_apply {n : ℕ} (ψ : QAlgorithms.Qubits n → ℂ) (A B : P2 n) :
    Mψ ψ A B = ∑ y, (((pauliOp A.1 *ᵥ ψ) y).re * ((pauliOp B.1 *ᵥ ψ) y).re +
      ((pauliOp A.1 *ᵥ ψ) y).im * ((pauliOp B.1 *ᵥ ψ) y).im) := by
  unfold Mψ
  rw [Matrix.of_apply, gram, re_dot]

theorem Mψ_symm {n : ℕ} (ψ : QAlgorithms.Qubits n → ℂ) (A B : P2 n) : Mψ ψ A B = Mψ ψ B A := by
  rw [Mψ_apply, Mψ_apply]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  ring

theorem Mψ_feasible {n : ℕ} (ψ : UnitVec n) : IsFeasible (Mψ ψ.1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · let G : Matrix (QAlgorithms.Qubits n ⊕ QAlgorithms.Qubits n) (P2 n) ℝ :=
      Matrix.of fun k A => Sum.elim (fun y => ((pauliOp A.1 *ᵥ ψ.1) y).re)
        (fun y => ((pauliOp A.1 *ᵥ ψ.1) y).im) k
    have hG : Mψ ψ.1 = Gᴴ * G := by
      ext A B
      rw [Mψ_apply, Matrix.mul_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      simp [G, Matrix.conjTranspose_apply]
    rw [hG]
    exact Matrix.posSemidef_conjTranspose_mul_self G
  · intro A B A' B' h
    show (expect ((pauliOp A.1)ᴴ * pauliOp B.1) ψ.1).re =
      (expect ((pauliOp A'.1)ᴴ * pauliOp B'.1) ψ.1).re
    rw [h]
  · intro A B A' B' h
    show (expect ((pauliOp A.1)ᴴ * pauliOp B.1) ψ.1).re =
      -(expect ((pauliOp A'.1)ᴴ * pauliOp B'.1) ψ.1).re
    rw [h, ex_neg, Complex.neg_re]
  · intro A B hnh
    rcases pauliOp_pm A.1 B.1 with h | h
    · exfalso
      apply hnh
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      exact h.symm
    · have h1 : Mψ ψ.1 A B = -Mψ ψ.1 B A := by
        show (expect ((pauliOp A.1)ᴴ * pauliOp B.1) ψ.1).re =
          -(expect ((pauliOp B.1)ᴴ * pauliOp A.1) ψ.1).re
        rw [h, ex_neg, Complex.neg_re]
      have h2 := Mψ_symm ψ.1 A B
      linarith
  · intro A
    show (expect ((pauliOp A.1)ᴴ * pauliOp A.1) ψ.1).re = 1
    rw [pauliOp_unit]
    unfold expect
    rw [Matrix.one_mulVec, ψ.2]
    simp

theorem entry_Mψ {n : ℕ} (ψ : QAlgorithms.Qubits n → ℂ) (a : Fin 4) (i j : Fin n) (hij : i ≠ j) :
    entry (Mψ ψ) (siteStr a i) (siteStr a j) = (expect (pauliOp (pairStr a i j)) ψ).re := by
  unfold entry
  rw [dif_pos (deg_site a i), dif_pos (deg_site a j)]
  show (expect ((pauliOp (siteStr a i))ᴴ * pauliOp (siteStr a j)) ψ).re = _
  rw [site_prod a i j hij]

theorem hEdge_expect {n : ℕ} (ψ : UnitVec n) (i j : Fin n) :
    expect (hEdge i j) ψ.1 = ((1 / 2 : ℝ) : ℂ) * (1 - expect (pauliOp (pairStr 1 i j)) ψ.1
      - expect (pauliOp (pairStr 2 i j)) ψ.1 - expect (pauliOp (pairStr 3 i j)) ψ.1) := by
  unfold hEdge
  rw [ex_smul, ex_sub, ex_sub, ex_sub]
  have h1 : expect (1 : Op n) ψ.1 = 1 := by
    unfold expect
    rw [Matrix.one_mulVec, ψ.2]
  rw [h1, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]

theorem obj_eq {n : ℕ} (w : Fin n → Fin n → ℝ) (ψ : UnitVec n) :
    lasserreObj w (Mψ ψ.1) = (expect (qmcH w) ψ.1).re := by
  unfold lasserreObj qmcH
  rw [ex_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ex_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hij : i < j
  · rw [if_pos hij, if_pos hij, ex_smul, hEdge_expect, entry_Mψ _ _ _ _ hij.ne,
      entry_Mψ _ _ _ _ hij.ne, entry_Mψ _ _ _ _ hij.ne, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
    simp only [Complex.sub_re, Complex.one_re]
    ring
  · rw [if_neg hij, if_neg hij, ex_zero, Complex.zero_re]

end Aux_QMCTriFree_theorem_6

open QMCTriFree.Circuit Aux_QMCTriFree_theorem_6 in
theorem solution {n : ℕ} (w : Fin n → Fin n → ℝ) :
    (∀ ψ : UnitVec n, ∃ M : Matrix (P2 n) (P2 n) ℝ,
        IsFeasible M ∧ lasserreObj w M = (expect (qmcH w) ψ.1).re) ∧
      ∀ M : Matrix (P2 n) (P2 n) ℝ, IsOptimal w M → qmcValue w ≤ lasserreObj w M := by
  have partA : ∀ ψ : UnitVec n, ∃ M : Matrix (P2 n) (P2 n) ℝ,
      IsFeasible M ∧ lasserreObj w M = (expect (qmcH w) ψ.1).re :=
    fun ψ => ⟨Mψ ψ.1, Mψ_feasible ψ, obj_eq w ψ⟩
  refine ⟨partA, ?_⟩
  intro M hM
  haveI : Nonempty (UnitVec n) :=
    ⟨⟨Pi.single (fun _ => false) 1, by simp [dotProduct_single]⟩⟩
  unfold qmcValue
  apply ciSup_le
  intro ψ
  obtain ⟨M', hF, hEq⟩ := partA ψ
  rw [← hEq]
  exact hM.2 M' hF
