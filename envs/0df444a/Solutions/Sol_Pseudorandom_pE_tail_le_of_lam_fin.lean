-- Prove2me | solution 1 for Pseudorandom.pE_tail_le_of_lam_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:18.349013+00:00
-- url     : https://prove2.me/submissions/929b082e-c7fd-4e0d-8541-56390c26e70a

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Theorems.Thm_Pseudorandom_rmean_eq_pE
public import Theorems.Thm_Pseudorandom_rmean_mgf_le
public import Theorems.Thm_Pseudorandom_pE_const_mul
public import Theorems.Thm_Pseudorandom_pE_mono


set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
namespace Pseudorandom
theorem _root_.solution {n : ℕ} (P : Fin n → α → ℝ) (hP : IsPMF P)
    (f : (Fin n → α) → ℝ) (c q : Fin n → ℝ) (R : Fin n → Finset α) (L lam t : ℝ)
    (hcL : ∀ i, c i ≤ L) (hf : CoordGap f c) (hfR : CoordRare f R)
    (hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (hlam : 0 ≤ lam) (hlamL : lam * L < 1) :
    pProb P (fun ω => t ≤ f ω - pE P f) ≤
      Real.exp (-(lam * t) + lam ^ 2 * (∑ i, q i * c i ^ 2) / (2 * (1 - lam * L))) := by
  classical
  have hind : ∀ ω, (if t ≤ f ω - pE P f then (1 : ℝ) else 0) ≤
      Real.exp (-(lam * t)) * Real.exp (lam * (f ω - pE P f)) := by
    intro ω
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp
      nlinarith
    · exact (Real.exp_pos _).le
  unfold pProb
  calc _ ≤ pE P (fun ω => Real.exp (-(lam * t)) *
        Real.exp (lam * (f ω - pE P f))) := pE_mono hP hind
    _ = Real.exp (-(lam * t)) * pE P (fun ω => Real.exp (lam * (f ω - pE P f))) :=
        pE_const_mul _ _
    _ ≤ Real.exp (-(lam * t)) *
          Real.exp (lam ^ 2 * (∑ i, q i * c i ^ 2) / (2 * (1 - lam * L))) := by
        gcongr
        have := rmean_mgf_le P hP f c q R L lam hcL hf hfR hq hlam hlamL
        simp only [rmean_eq_pE] at this
        exact this
    _ = _ := (Real.exp_add _ _).symm
end Pseudorandom
