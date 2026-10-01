-- Prove2me | solution 1 for RobustMDP.EntropyInner.mu_elimination
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:50:26.909799+00:00
-- url     : https://prove2.me/submissions/22c354bf-8288-4c59-ab47-4dbc94836c4d

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
    (hq : q∈stdSimplex ℝ (Fin n)) (hq_pos : ∀ j, 0 < q j) (hβ : 0 < β)
    (lam : ℝ) (hlam : 0 < lam) :
    (∑ j, q j*Real.exp
        ((v j-(lam*Real.log (∑ i, q i*Real.exp (v i/lam))-lam))/lam-1))=1 ∧
    dualObj q v β lam (lam*Real.log (∑ i, q i*Real.exp (v i/lam))-lam)=dualFn q v β lam ∧
    IsLeast (Set.range (fun mu : ℝ => dualObj q v β lam mu)) (dualFn q v β lam) := by
  let Z := ∑ j, q j*Real.exp (v j/lam)
  have hZ : 0 < Z := CEntropy.partition_pos q v hq hq_pos lam
  have hex : ∀ mu : ℝ, (∑ j, q j*Real.exp ((v j-mu)/lam-1))=Real.exp (Real.log Z-mu/lam-1) := by
    intro mu
    rw [CEntropy.partition_shift]
    change Z*Real.exp (-mu/lam-1)=_
    rw [show Real.log Z-mu/lam-1=Real.log Z+(-mu/lam-1) by ring,Real.exp_add,Real.exp_log hZ]
  have harg : Real.log Z-(lam*Real.log Z-lam)/lam-1=0 := by field_simp;ring
  have hnorm : (∑ j, q j*Real.exp ((v j-(lam*Real.log Z-lam))/lam-1))=1 := by rw [hex,harg,Real.exp_zero]
  have hval : dualObj q v β lam (lam*Real.log Z-lam)=dualFn q v β lam := by
    unfold dualObj dualFn
    rw [hnorm]
    dsimp [Z]
    ring
  refine ⟨hnorm,hval,⟨lam*Real.log Z-lam,hval⟩,?_⟩
  rintro _ ⟨mu,rfl⟩
  unfold dualObj dualFn
  dsimp only
  rw [hex]
  change lam*Real.log Z+β*lam ≤ _
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (Real.log Z-mu/lam-1)) hlam.le
  have hid : lam*(Real.log Z-mu/lam-1+1)=lam*Real.log Z-mu := by field_simp;ring
  rw [hid] at he
  linarith

