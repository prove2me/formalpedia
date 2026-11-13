-- Prove2me | solution 1 for RamanujanPetersson.ramanujan_petersson
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T01:44:20.509502+00:00
-- url     : https://prove2.me/submissions/273ed5d6-7733-4dec-9e5b-a8c85d5f88b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_RamanujanPetersson_exists_gamma1_cuspForm_qExpansion_eq
import Theorems.Thm_RamanujanPetersson_gamma1_coeff_eq_sum_eigenform_shifts
import Theorems.Thm_RamanujanPetersson_deligne_hecke_root_bound
import Theorems.Thm_RamanujanPetersson_deligne_serre_hecke_root_bound
import Theorems.Thm_RamanujanPetersson_eigen_shift_sum_isBigO

open UpperHalfPlane Filter Asymptotics MatrixGroups ModularForm

set_option autoImplicit false

theorem solution (Γ : Subgroup SL(2, ℤ))
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) (k : ℤ) (hk : 1 ≤ k)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (qExpansion (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty f).coeff n)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (((k : ℝ) - 1) / 2 + ε) := by
  -- root bound at good primes for every normalized eigenform of weight k (N4 for k ≥ 2, N5 for k = 1)
  have hroot_gen : ∀ (L : ℕ), 0 < L → ∀ (χ : DirichletCharacter ℂ L)
      (F : CuspForm ((CongruenceSubgroup.Gamma1 L : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)) k),
      (∀ γ ∈ CongruenceSubgroup.Gamma0 L, (⇑F ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑F) →
      (qExpansion 1 F).coeff 1 = 1 →
      (∀ p n : ℕ, p.Prime →
        (qExpansion 1 F).coeff (p * n) =
          (qExpansion 1 F).coeff p * (qExpansion 1 F).coeff n -
            (if p ∣ L then 0 else
              χ (p : ZMod L) * (p : ℂ) ^ (k - 1) *
                (if p ∣ n then (qExpansion 1 F).coeff (n / p) else 0))) →
      ∀ p : ℕ, p.Prime → ¬ p ∣ L → ∀ α : ℂ,
        α ^ 2 - (qExpansion 1 F).coeff p * α + χ (p : ZMod L) * (p : ℂ) ^ (k - 1) = 0 →
          ‖α‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2) := by
    intro L hL χ F hχ h1 hrec p hp hpL α hα
    have hgood : ∀ q n : ℕ, q.Prime → ¬ q ∣ L →
        (qExpansion 1 F).coeff (q * n) =
          (qExpansion 1 F).coeff q * (qExpansion 1 F).coeff n -
            χ (q : ZMod L) * (q : ℂ) ^ (k - 1) *
              (if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0) := by
      intro q n hq hqL
      have h := hrec q n hq
      rw [if_neg hqL] at h
      exact h
    rcases eq_or_lt_of_le hk with h | h
    · subst h
      have e0 : ((1 : ℤ) - 1) = 0 := by norm_num
      have e1 : ((((1 : ℤ) : ℝ) - 1) / 2) = 0 := by norm_num
      rw [e1, Real.rpow_zero]
      rw [e0, zpow_zero, mul_one] at hα
      refine RamanujanPetersson.deligne_serre_hecke_root_bound L hL χ F hχ h1 ?_ p hp hpL α hα
      intro q n hq hqL
      have h := hgood q n hq hqL
      rw [e0, zpow_zero, mul_one] at h
      exact h
    · exact RamanujanPetersson.deligne_hecke_root_bound L hL k (by omega) χ F hχ h1 hgood p hp hpL α hα
  obtain ⟨M, hM, g, hfg⟩ := RamanujanPetersson.exists_gamma1_cuspForm_qExpansion_eq Γ hΓ k f
  obtain ⟨r, c, d, L, χ, F, hdL, hχ, h1, hrec, hbad, hsum⟩ :=
    RamanujanPetersson.gamma1_coeff_eq_sum_eigenform_shifts M hM k hk g
  have hfun : (fun n : ℕ => (qExpansion (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty f).coeff n)
      = fun n : ℕ => ∑ i, c i * (if d i ∣ n then (qExpansion 1 (F i)).coeff (n / d i) else 0) := by
    funext n
    rw [hfg n, hsum n]
  rw [hfun]
  exact RamanujanPetersson.eigen_shift_sum_isBigO k hk ε hε r c d L χ (fun i n => (qExpansion 1 (F i)).coeff n)
    (fun i => (hdL i).1) h1 hrec hbad
    (fun i p hp hpL α hα => hroot_gen (L i) (hdL i).2.1 (χ i) (F i) (hχ i) (h1 i) (hrec i)
      p hp hpL α hα)
