-- Prove2me | solution 1 for RobustMDP.EntropyInner.whole_simplex
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:54:24.806948+00:00
-- url     : https://prove2.me/submissions/4339ceeb-7558-4eb7-afb1-20dd27c3baf9

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

theorem solution {n : ℕ} (q v : Fin n → ℝ) (β : ℝ)
    (hq : q∈stdSimplex ℝ (Fin n)) (hq_pos : ∀ j, 0 < q j) (hβ : 0 < β) :
    IsGreatest ((fun p => klDiv p q) '' stdSimplex ℝ (Fin n)) (⨆ i, -Real.log (q i)) ∧
    ((⨆ i, -Real.log (q i)) ≤ β → klBall q β=stdSimplex ℝ (Fin n) ∧
      IsGreatest ((fun p : Fin n → ℝ => ∑ j, p j*v j) '' klBall q β) (vmax v)) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0,CEntropy.positive_dim q hq⟩⟩
  have hb : ∀ p∈stdSimplex ℝ (Fin n), klDiv p q ≤ ⨆ i, -Real.log (q i) := by
    intro p hp
    have hsum : klDiv p q ≤ ∑ j, p j*(⨆ i, -Real.log (q i)) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : p j=0
      · simp [hj]
      have hpj : 0 < p j := lt_of_le_of_ne (hp.1 j) (Ne.symm hj)
      have hl : Real.log (p j) ≤ 0 := by
        simpa using Real.log_le_log hpj (mem_Icc_of_mem_stdSimplex hp j).2
      rw [Real.log_div hj (hq_pos j).ne']
      apply mul_le_mul_of_nonneg_left _ hpj.le
      have hmax := le_ciSup (Set.finite_range (fun i => -Real.log (q i))).bddAbove j
      linarith
    simpa only [← Finset.sum_mul,hp.2,one_mul] using hsum
  have hdirac : ∀ j : Fin n, klDiv (Pi.single j 1) q= -Real.log (q j) := by
    intro j
    simp [klDiv,Pi.single_apply,Real.log_inv]
  constructor
  · obtain ⟨j,hj⟩ := exists_eq_ciSup_of_finite (f := fun i => -Real.log (q i))
    refine ⟨⟨Pi.single j 1,single_mem_stdSimplex ℝ j,(hdirac j).trans hj⟩,?_⟩
    rintro z ⟨p,hp,rfl⟩
    exact hb p hp
  · intro hβmax
    have he : klBall q β=stdSimplex ℝ (Fin n) := by
      ext p
      exact ⟨fun h => h.1,fun h => ⟨h,(hb p h).trans hβmax⟩⟩
    refine ⟨he,?_⟩
    rw [he]
    obtain ⟨j,hj⟩ := exists_eq_ciSup_of_finite (f := v)
    refine ⟨⟨Pi.single j 1,single_mem_stdSimplex ℝ j,?_⟩,?_⟩
    · simpa [Pi.single_apply,vmax] using hj
    · rintro z ⟨p,hp,rfl⟩
      calc
        _ ≤ ∑ j, p j*vmax v := Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (le_ciSup (Set.finite_range v).bddAbove j) (hp.1 j))
        _ = _ := by rw [← Finset.sum_mul,hp.2,one_mul]
