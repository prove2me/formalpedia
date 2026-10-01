-- Prove2me | solution 1 for RobustMDP.EntropyInner.tilted_optimal
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:53:31.104883+00:00
-- url     : https://prove2.me/submissions/1fbdc29e-9b77-4546-9cc1-21234e7a898f

import Definitions.Def_RobustMDP_EntropyInner_klBall
import Definitions.Def_RobustMDP_EntropyInner_dualFunction
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
open RobustMDP.EntropyInner
namespace CEntropy

theorem positive_dim {n : ℕ} (q : Fin n → ℝ) (hq : q∈stdSimplex ℝ (Fin n)) : 0 < n := by
  by_contra h
  have hn : n=0 := by omega
  subst n
  simpa using hq.2

theorem partition_pos {n : ℕ} (q v : Fin n → ℝ) (hq : q∈stdSimplex ℝ (Fin n))
    (hqpos : ∀ j, 0 < q j) (lam : ℝ) : 0 < ∑ j, q j*Real.exp (v j/lam) := by
  haveI : Nonempty (Fin n) := ⟨⟨0,positive_dim q hq⟩⟩
  exact Finset.sum_pos (fun j _ => mul_pos (hqpos j) (Real.exp_pos _)) Finset.univ_nonempty

theorem partition_shift {n : ℕ} (q v : Fin n → ℝ) (lam mu : ℝ) :
    (∑ j, q j*Real.exp ((v j-mu)/lam-1))=
      (∑ j, q j*Real.exp (v j/lam))*Real.exp (-mu/lam-1) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (v j-mu)/lam-1=v j/lam+(-mu/lam-1) by ring,Real.exp_add]
  ring
end CEntropy

namespace CEntropy

theorem tilted_positive {n : ℕ} (q v : Fin n → ℝ) (hq : q∈stdSimplex ℝ (Fin n))
    (hqpos : ∀ j, 0 < q j) (lam : ℝ) (j : Fin n) : 0 < tiltedDist q v lam j := by
  unfold tiltedDist
  exact div_pos (mul_pos (hqpos j) (Real.exp_pos _)) (partition_pos q v hq hqpos lam)

theorem tilted_simplex {n : ℕ} (q v : Fin n → ℝ) (hq : q∈stdSimplex ℝ (Fin n))
    (hqpos : ∀ j, 0 < q j) (lam : ℝ) : tiltedDist q v lam∈stdSimplex ℝ (Fin n) := by
  refine ⟨fun j => (tilted_positive q v hq hqpos lam j).le,?_⟩
  simp only [tiltedDist,← Finset.sum_div]
  exact div_self (partition_pos q v hq hqpos lam).ne'

theorem log_tilted {n : ℕ} (q v : Fin n → ℝ) (hq : q∈stdSimplex ℝ (Fin n))
    (hqpos : ∀ j, 0 < q j) (lam : ℝ) (j : Fin n) :
    Real.log (tiltedDist q v lam j)=Real.log (q j)+v j/lam-Real.log (∑ i, q i*Real.exp (v i/lam)) := by
  unfold tiltedDist
  rw [Real.log_div (mul_ne_zero (hqpos j).ne' (Real.exp_ne_zero _)) (partition_pos q v hq hqpos lam).ne',
    Real.log_mul (hqpos j).ne' (Real.exp_ne_zero _),Real.log_exp]

theorem kl_nonneg {n : ℕ} (p q : Fin n → ℝ) (hp : p∈stdSimplex ℝ (Fin n))
    (hq : q∈stdSimplex ℝ (Fin n)) (hqpos : ∀ j, 0 < q j) : 0 ≤ klDiv p q := by
  have heach : ∀ j, p j-q j ≤ p j*Real.log (p j/q j) := by
    intro j
    by_cases hj : p j=0
    · simp [hj,(hqpos j).le]
    have hpj : 0 < p j := lt_of_le_of_ne (hp.1 j) (Ne.symm hj)
    have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos (hqpos j) hpj)) hpj.le
    rw [Real.log_div (hqpos j).ne' hj] at hl
    have hid : p j*(q j/p j-1)=q j-p j := by field_simp <;> ring
    rw [hid] at hl
    rw [Real.log_div hj (hqpos j).ne']
    nlinarith
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => heach j)
  simpa only [klDiv,Finset.sum_sub_distrib,hp.2,hq.2,sub_self] using hh

theorem kl_tilted {n : ℕ} (p q v : Fin n → ℝ) (hp : p∈stdSimplex ℝ (Fin n))
    (hq : q∈stdSimplex ℝ (Fin n)) (hqpos : ∀ j, 0 < q j) (lam : ℝ) :
    klDiv p (tiltedDist q v lam)=klDiv p q-(∑ j, p j*v j)/lam+
      Real.log (∑ i, q i*Real.exp (v i/lam)) := by
  calc
    klDiv p (tiltedDist q v lam) = ∑ j, (p j*Real.log (p j/q j)-p j*v j/lam+
        p j*Real.log (∑ i, q i*Real.exp (v i/lam))) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : p j=0
      · simp [hj]
      rw [Real.log_div hj (tilted_positive q v hq hqpos lam j).ne',
        Real.log_div hj (hqpos j).ne',log_tilted q v hq hqpos lam j]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_div,← Finset.sum_mul,hp.2,one_mul]
      rfl
end CEntropy

theorem solution {n : ℕ} (q v : Fin n → ℝ)
    (hq : q∈stdSimplex ℝ (Fin n)) (hq_pos : ∀ j, 0 < q j) (lam : ℝ) (hlam : 0 < lam) :
    (∀ p∈stdSimplex ℝ (Fin n),
      (∑ j, p j*v j)-lam*klDiv p q ≤ lam*Real.log (∑ j, q j*Real.exp (v j/lam))) ∧
    tiltedDist q v lam∈stdSimplex ℝ (Fin n) ∧
    (∑ j, tiltedDist q v lam j*v j)-lam*klDiv (tiltedDist q v lam) q=
      lam*Real.log (∑ j, q j*Real.exp (v j/lam)) := by
  have ht := CEntropy.tilted_simplex q v hq hq_pos lam
  constructor
  · intro p hp
    have hkl := CEntropy.kl_nonneg p (tiltedDist q v lam) hp ht (CEntropy.tilted_positive q v hq hq_pos lam)
    rw [CEntropy.kl_tilted p q v hp hq hq_pos lam] at hkl
    have hh := mul_nonneg hlam.le hkl
    have hid : lam*((∑ j, p j*v j)/lam)=∑ j, p j*v j := by field_simp
    nlinarith
  · refine ⟨ht,?_⟩
    have hkl := CEntropy.kl_tilted (tiltedDist q v lam) q v ht hq hq_pos lam
    have hz : klDiv (tiltedDist q v lam) (tiltedDist q v lam)=0 := by simp [klDiv]
    rw [hz] at hkl
    have hid : lam*((∑ j, tiltedDist q v lam j*v j)/lam)=∑ j, tiltedDist q v lam j*v j := by field_simp
    nlinarith [congrArg (fun z : ℝ => lam*z) hkl]
