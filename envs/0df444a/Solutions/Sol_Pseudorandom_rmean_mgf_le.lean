-- Prove2me | solution 1 for Pseudorandom.rmean_mgf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:46.050278+00:00
-- url     : https://prove2.me/submissions/4d794f4c-7f61-4c19-84d0-5ed4e2e18a2b

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Theorems.Thm_Pseudorandom_coord_exp_bound
public import Theorems.Thm_Pseudorandom_CoordGap_tail
public import Theorems.Thm_Pseudorandom_CoordRare_tail
public import Theorems.Thm_Pseudorandom_rmean_eq_pE
public import Theorems.Thm_Pseudorandom_IsPMF_tail
public import Theorems.Thm_Pseudorandom_pE_const
public import Theorems.Thm_Pseudorandom_pE_const_mul
public import Theorems.Thm_Pseudorandom_pE_mono
public import Theorems.Thm_Pseudorandom_pE_sub


set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α]
namespace Pseudorandom
theorem _root_.solution : ∀ {n : ℕ} (P : Fin n → α → ℝ) (_hP : IsPMF P)
    (f : (Fin n → α) → ℝ) (c q : Fin n → ℝ) (R : Fin n → Finset α) (L lam : ℝ)
    (_hcL : ∀ i, c i ≤ L) (_hf : CoordGap f c) (_hfR : CoordRare f R)
    (_hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (_hlam : 0 ≤ lam) (_hlamL : lam * L < 1),
    rmean P (fun ω => Real.exp (lam * (f ω - rmean P f))) ≤
      Real.exp (lam ^ 2 * (∑ i, q i * c i ^ 2) / (2 * (1 - lam * L)))
  | 0, P, _, f, c, q, R, L, lam, _, _, _, _, _, _ => by
    simp [rmean]
  | n + 1, P, hP, f, c, q, R, L, lam, hcL, hf, hfR, hq, hlam, hlamL => by
    set P' : Fin n → α → ℝ := fun i => P i.succ
    set M : α → ℝ := fun b => rmean P' (fun ω => f (Fin.cons b ω)) with hM
    have hmean : rmean P f = ∑ a, P 0 a * M a := rfl
    set K := 2 * (1 - lam * L)
    set V' := ∑ i : Fin n, q i.succ * (c i.succ) ^ 2
    have hstep : ∀ b, rmean P' (fun ω => Real.exp (lam * (f (Fin.cons b ω) -
        rmean P f))) ≤ Real.exp (lam * (M b - rmean P f)) *
          Real.exp (lam ^ 2 * V' / K) := by
      intro b
      have hsplit : (fun ω => Real.exp (lam * (f (Fin.cons b ω) - rmean P f))) =
          fun ω => Real.exp (lam * (M b - rmean P f)) *
            Real.exp (lam * (f (Fin.cons b ω) - M b)) := by
        funext ω
        rw [← Real.exp_add]
        ring_nf
      rw [hsplit, rmean_eq_pE, pE_const_mul, ← rmean_eq_pE]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact solution P' hP.tail _ (fun i => c i.succ) (fun i => q i.succ)
        (fun i => R i.succ) L lam (fun i => hcL i.succ) (hf.tail b) (hfR.tail b)
        (fun i => hq i.succ) hlam hlamL
    have hgap : ∀ a b, |M a - M b| ≤ c 0 := by
      intro a b
      simp only [hM]
      rw [rmean_eq_pE, rmean_eq_pE, ← pE_sub]
      have hb : ∀ ω, |f (Fin.cons a ω) - f (Fin.cons b ω)| ≤ c 0 := by
        intro ω
        have := hf 0 (Fin.cons a ω) a b
        simpa [Fin.update_cons_zero] using this
      rw [abs_le]
      constructor
      · have := pE_mono hP.tail (f := fun _ => -c 0)
          (g := fun ω => f (Fin.cons a ω) - f (Fin.cons b ω))
          (fun ω => (abs_le.mp (hb ω)).1)
        rwa [pE_const hP.tail] at this
      · have := pE_mono hP.tail (g := fun _ => c 0)
          (f := fun ω => f (Fin.cons a ω) - f (Fin.cons b ω))
          (fun ω => (abs_le.mp (hb ω)).2)
        rwa [pE_const hP.tail] at this
    have hRM : ∀ a b, a ∉ R 0 → b ∉ R 0 → M a = M b := by
      intro a b ha hb
      simp only [hM]
      congr 1; funext ω
      have := hfR 0 (Fin.cons a ω) a b ha hb
      simpa [Fin.update_cons_zero] using this
    calc rmean P (fun ω => Real.exp (lam * (f ω - rmean P f)))
        = ∑ a, P 0 a * rmean P' (fun ω => Real.exp (lam *
            (f (Fin.cons a ω) - rmean P f))) := rfl
      _ ≤ ∑ a, P 0 a * (Real.exp (lam * (M a - rmean P f)) *
            Real.exp (lam ^ 2 * V' / K)) :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hstep a) (hP.1 0 a)
      _ = (∑ a, P 0 a * Real.exp (lam * (M a - ∑ b, P 0 b * M b))) *
            Real.exp (lam ^ 2 * V' / K) := by
          rw [sum_mul, hmean]; congr 1; funext a; ring
      _ ≤ Real.exp (lam ^ 2 * (q 0 * c 0 ^ 2) / K) * Real.exp (lam ^ 2 * V' / K) := by
          gcongr
          exact coord_exp_bound (P 0) (hP.1 0) (hP.2 0) M (c 0) L lam (q 0) (R 0) hgap hRM
            (hq 0) (hcL 0) hlam hlamL
      _ = _ := by
          rw [← Real.exp_add, Fin.sum_univ_succ]
          congr 1
          simp only [K, V']
          ring
end Pseudorandom
