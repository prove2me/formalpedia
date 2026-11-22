-- Prove2me | solution 1 for Pseudorandom.freedman_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:18.879855+00:00
-- url     : https://prove2.me/submissions/b1a81652-5594-4681-91c2-35f11c861eef

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_Vendor_Freedman
public import Theorems.Thm_Pseudorandom_pE_resample
public import Theorems.Thm_Pseudorandom_Adapted_mono
public import Theorems.Thm_Pseudorandom_Alive_mono
public import Theorems.Thm_Pseudorandom_alive_adapted
public import Theorems.Thm_Pseudorandom_stopped_eq_of_alive
public import Theorems.Thm_Pseudorandom_stopped_adapted
public import Theorems.Thm_Pseudorandom_condAbsInc_adapted
public import Theorems.Thm_Pseudorandom_accInc_adapted
public import Theorems.Thm_Pseudorandom_accInc_eq_sum_of_alive
public import Theorems.Thm_Pseudorandom_exp_step_le
public import Theorems.Thm_Pseudorandom_pE_const
public import Theorems.Thm_Pseudorandom_pE_const_mul
public import Theorems.Thm_Pseudorandom_pE_mono


set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α] {n : ℕ}
variable {P : Fin n → α → ℝ} {X : ℕ → (Fin n → α) → ℝ} {G : ℕ → (Fin n → α) → Prop}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) (hX : IsExposureMartingale P X)
    (hG : ∀ k, Adapted k (G k)) (C s lam : ℝ) (hC : 0 < C) (hs : 0 < s) (hlam : 0 < lam)
    (hinc : ∀ (i : Fin n) ω, Alive G i ω → ∀ a, P i a ≠ 0 →
      |X (i + 1) (Function.update ω i a) - X i ω| ≤ C)
    (hacc : ∀ (i : Fin n) ω, Alive G i ω →
      ∑ j : Fin n with j ≤ i, condAbsInc P X j ω ≤ s) :
    pProb P (fun ω => lam ≤ X n ω - X 0 ω ∧ ∀ i : Fin n, G i ω) ≤
      Real.exp (-(lam ^ 2 / (2 * C * (lam + s)))) := by
  classical
  set θ := lam / (C * (lam + s)) with hθdef
  have hθ0 : 0 < θ := by positivity
  have hθC : θ * C = lam / (lam + s) := by rw [hθdef]; field_simp
  have hθC1 : θ * C < 1 := by rw [hθC, div_lt_one (by positivity)]; linarith
  set ψ := θ ^ 2 * C / (2 * (1 - θ * C)) with hψdef
  have hψ0 : 0 ≤ ψ := div_nonneg (by positivity) (by linarith)
  set Z : ℕ → (Fin n → α) → ℝ := fun k ω =>
    Real.exp (θ * (stopped X G k ω - X 0 ω) - ψ * accInc P X G k ω) with hZ
  have hX0 : ∀ ω ω', X 0 ω = X 0 ω' := fun ω ω' => hX.1 0 ω ω' fun i hi => absurd hi (by omega)
  -- supermartingale step
  have hsuper : ∀ (i : Fin n) ω,
      ∑ a, P i a * Z (i + 1) (Function.update ω i a) ≤ Z i ω := by
    intro i ω
    have hupdY : ∀ a, stopped X G i (Function.update ω i a) = stopped X G i ω := fun a =>
      (stopped_adapted hX.1 hG i).update i le_rfl ω a
    have hupdA : ∀ a, accInc P X G i (Function.update ω i a) = accInc P X G i ω := fun a =>
      (accInc_adapted hX.1 hG i).update i le_rfl ω a
    have hupdAl : ∀ a, (Alive G i (Function.update ω i a) ↔ Alive G i ω) := fun a => by
      have := (alive_adapted hG i).update i le_rfl ω a
      rw [this]
    have hupd0 : ∀ a, X 0 (Function.update ω i a) = X 0 ω := fun a => hX0 _ _
    have hupdD : ∀ a, condAbsInc P X ⟨i, i.2⟩ (Function.update ω i a) = condAbsInc P X i ω :=
      fun a => (condAbsInc_adapted hX.1 i).update i le_rfl ω a
    by_cases hal : Alive G i ω
    · have hYi : stopped X G i ω = X i ω :=
        stopped_eq_of_alive i (by
          rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
          · left; exact h
          · right; exact hal.mono (by omega))
      have hZa : ∀ a, Z (i + 1) (Function.update ω i a) = Z i ω *
          Real.exp (θ * (X (i + 1) (Function.update ω i a) - X i ω) -
            ψ * condAbsInc P X i ω) := by
        intro a
        simp only [hZ, stopped, accInc, dif_pos i.2, (hupdAl a).mpr hal, if_true, hupdA a,
          hupd0 a, hupdD a]
        rw [← Real.exp_add, hYi]
        congr 1; ring
      simp_rw [hZa]
      have hmean : ∑ a, P i a * (X (i + 1) (Function.update ω i a) - X i ω) = 0 := by
        simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul, hP.2 i, one_mul, ← hX.2 i ω]; ring
      have hstep := exp_step_le (P i) (hP.1 i) (hP.2 i)
        (fun a => X (i + 1) (Function.update ω i a) - X i ω) hmean C θ hθ0.le hθC1
        (fun a ha => hinc i ω hal a ha)
      calc ∑ a, P i a * (Z i ω * Real.exp (θ * (X (↑i + 1) (Function.update ω i a) - X (↑i) ω) -
              ψ * condAbsInc P X i ω))
          = Z i ω * Real.exp (-(ψ * condAbsInc P X i ω)) *
              ∑ a, P i a * Real.exp (θ * (X (↑i + 1) (Function.update ω i a) - X (↑i) ω)) := by
            rw [mul_sum]; refine sum_congr rfl fun a _ => ?_
            rw [sub_eq_add_neg, Real.exp_add]; ring
        _ ≤ Z i ω * Real.exp (-(ψ * condAbsInc P X i ω)) *
              Real.exp (ψ * condAbsInc P X i ω) := by
            apply mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = Z i ω := by rw [mul_assoc, ← Real.exp_add]; simp
    · have hZa : ∀ a, Z (i + 1) (Function.update ω i a) = Z i ω := by
        intro a
        have hn : ¬ Alive G i (Function.update ω i a) := fun h => hal ((hupdAl a).mp h)
        simp only [hZ, stopped, accInc, dif_pos i.2, hn, if_false, hupdA a, hupd0 a, hupdY a]
      simp_rw [hZa]
      rw [← sum_mul, hP.2 i, one_mul]
  -- expectation of `Z n` is at most `1`
  have hEZ : ∀ k, k ≤ n → pE P (Z k) ≤ 1 := by
    intro k
    induction k with
    | zero =>
      intro _
      have : Z 0 = fun _ => 1 := by funext ω; simp [hZ, stopped, accInc]
      rw [this, pE_const hP]
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      rw [← pE_resample hP ⟨k, hk'⟩]
      refine le_trans (pE_mono hP fun ω => ?_) (ih (by omega))
      exact hsuper ⟨k, hk'⟩ ω
  -- Markov
  have hev : ∀ ω, (lam ≤ X n ω - X 0 ω ∧ ∀ i : Fin n, G i ω) →
      Real.exp (θ * lam - ψ * s) ≤ Z n ω := by
    rintro ω ⟨hl, hall⟩
    have hYn : stopped X G n ω = X n ω := by
      apply stopped_eq_of_alive
      rcases Nat.eq_zero_or_pos n with h | h
      · left; exact h
      · right; exact fun j hj => hall ⟨j, by omega⟩
    have hAn : accInc P X G n ω ≤ s := by
      rw [accInc_eq_sum_of_alive hall n le_rfl]
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp; exact hs.le
      · have := hacc ⟨n - 1, by omega⟩ ω (fun j hj => hall ⟨j, by omega⟩)
        refine le_of_eq_of_le (sum_congr ?_ fun _ _ => rfl) this
        ext i; simp only [mem_filter, mem_univ, true_and, Fin.le_def]; omega
    simp only [hZ]
    apply Real.exp_le_exp.mpr
    rw [hYn]
    nlinarith [mul_le_mul_of_nonneg_left hl hθ0.le, mul_le_mul_of_nonneg_left hAn hψ0]
  have hprob : pProb P (fun ω => lam ≤ X n ω - X 0 ω ∧ ∀ i : Fin n, G i ω) *
      Real.exp (θ * lam - ψ * s) ≤ 1 := by
    unfold pProb
    rw [mul_comm, ← pE_const_mul]
    refine le_trans (pE_mono hP fun ω => ?_) (hEZ n le_rfl)
    split_ifs with h
    · rw [mul_one]; exact hev ω h
    · rw [mul_zero]; exact (Real.exp_pos _).le
  have hval : θ * lam - ψ * s = lam ^ 2 / (2 * C * (lam + s)) := by
    rw [hψdef, hθC, hθdef]
    have h1 : 1 - lam / (lam + s) = s / (lam + s) := by field_simp; ring
    rw [h1]
    field_simp
    ring
  rw [hval] at hprob
  rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _)]
  exact hprob
end Pseudorandom
