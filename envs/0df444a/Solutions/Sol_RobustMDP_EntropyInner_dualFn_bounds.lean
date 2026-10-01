-- Prove2me | solution 1 for RobustMDP.EntropyInner.dualFn_bounds
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:51:50.819725+00:00
-- url     : https://prove2.me/submissions/fe403edf-06d3-4504-81c7-8c0f4fada83a

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
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
    ∀ lam : ℝ, 0 < lam →
      (∑ j, q j*v j)+β*lam ≤ dualFn q v β lam ∧ dualFn q v β lam ≤ vmax v+β*lam := by
  intro lam hlam
  haveI : Nonempty (Fin n) := ⟨⟨0,CEntropy.positive_dim q hq⟩⟩
  let Z := ∑ j, q j*Real.exp (v j/lam)
  have hZ : 0 < Z := CEntropy.partition_pos q v hq hq_pos lam
  have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := q) (p := fun j => v j/lam)
    (fun j _ => (hq_pos j).le) hq.2 (by simp)
  simp only [smul_eq_mul,← mul_div_assoc,← Finset.sum_div] at hj
  have hlo : (∑ j, q j*v j)/lam ≤ Real.log Z := (Real.le_log_iff_exp_le hZ).mpr hj
  have hu : Z ≤ Real.exp (vmax v/lam) := by
    calc
      Z ≤ ∑ j, q j*Real.exp (vmax v/lam) := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
          (le_ciSup (Set.finite_range v).bddAbove j) hlam.le)) (hq_pos j).le)
      _ = Real.exp (vmax v/lam) := by rw [← Finset.sum_mul,hq.2,one_mul]
  have hup : Real.log Z ≤ vmax v/lam := by simpa using Real.log_le_log hZ hu
  unfold dualFn
  change _ ≤ lam*Real.log Z+β*lam ∧ lam*Real.log Z+β*lam ≤ _
  constructor
  · have hh := (div_le_iff₀ hlam).mp hlo
    nlinarith
  · have hh := (le_div_iff₀ hlam).mp hup
    nlinarith

