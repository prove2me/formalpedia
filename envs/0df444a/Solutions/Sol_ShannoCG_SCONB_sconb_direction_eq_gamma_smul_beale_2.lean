-- Prove2me | solution 2 for ShannoCG.SCONB.sconb_direction_eq_gamma_smul_beale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T15:28:36.59739+00:00
-- url     : https://prove2.me/submissions/50d5c93d-fea9-4b49-b627-514ab0969268

import Mathlib
import Definitions.Def_ShannoCG_SCONB_bconDirection
import Definitions.Def_ShannoCG_SCONB_bealeDirection
import Definitions.Def_ShannoCG_SCONB_sconbDirection
import Theorems.Thm_ShannoCG_SCONB_restart_step_orth_grad

-- carved verbatim out of submission 0b9a3a3e-0e6e-4506-a994-c388dcf345c8, lines 73-129

section
open Matrix ShannoCG.SCONB

private theorem bfgs_exact {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (p y g : Fin n → ℝ)
    (hexact : p ⬝ᵥ g = 0) :
    -(bfgsUpdate H p y *ᵥ g) = -(H *ᵥ g) + ((y ⬝ᵥ (H *ᵥ g)) / (p ⬝ᵥ y)) • p := by
  simp only [bfgsUpdate, add_mulVec, smul_mulVec, sub_mulVec,
    vecMulVec_mulVec, ← dotProduct_mulVec, hexact]
  ext i
  simp [smul_eq_mul, div_eq_mul_inv]
  <;> ring

private theorem scaled_orth {n : ℕ} (pt yt g : Fin n → ℝ) (hpy : pt ⬝ᵥ yt ≠ 0)
    (horth : pt ⬝ᵥ g = 0) :
    scaledRestart pt yt *ᵥ g = gammaScale pt yt • g - ((yt ⬝ᵥ g) / (yt ⬝ᵥ yt)) • pt := by
  simp only [scaledRestart, add_mulVec, smul_mulVec, sub_mulVec, one_mulVec,
    vecMulVec_mulVec, horth]
  ext i
  simp [gammaScale, smul_eq_mul]
  field_simp
  <;> ring

private theorem scaled_dir {n : ℕ} (pt yt pk yk g : Fin n → ℝ) (hpy : pt ⬝ᵥ yt ≠ 0)
    (hexact_k : pk ⬝ᵥ g = 0) (horth : pt ⬝ᵥ g = 0) (hconj : yk ⬝ᵥ pt = 0) :
    sconbDirection pt yt pk yk g =
      -(gammaScale pt yt • g) + ((yt ⬝ᵥ g) / (yt ⬝ᵥ yt)) • pt
        + ((yk ⬝ᵥ g) / (pk ⬝ᵥ yk) * gammaScale pt yt) • pk := by
  rw [sconbDirection, bfgs_exact _ _ _ _ hexact_k, scaled_orth _ _ _ hpy horth]
  simp only [dotProduct_sub, dotProduct_smul, hconj, smul_zero, sub_zero]
  ext i
  simp [smul_eq_mul, div_eq_mul_inv]
  <;> ring

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (c : Fin n → ℝ)
    (x p d g y : ℕ → Fin n → ℝ) (α : ℕ → ℝ) (t k : ℕ) (htk : t < k)
    (hg : ∀ i, g i = A *ᵥ x i + c)
    (hy : ∀ i, y i = g (i + 1) - g i)
    (hstep : ∀ i, t ≤ i → i ≤ k → x (i + 1) = x i + p i)
    (hpd : ∀ i, t ≤ i → i ≤ k → p i = α i • d i)
    (hexact : ∀ i, t ≤ i → i ≤ k → p i ⬝ᵥ g (i + 1) = 0)
    (hconj : ∀ i, t < i → i ≤ k → p t ⬝ᵥ (A *ᵥ p i) = 0)
    (hpt : p t ≠ 0) (hpk : p k ≠ 0) :
    sconbDirection (p t) (y t) (p k) (y k) (g (k + 1)) =
      gammaScale (p t) (y t) • bealeDirection (g (k + 1)) (d k) (y k) (d t) (y t) := by
  have hyt : y t = A *ᵥ p t := by
    rw [hy, hg, hg, hstep t le_rfl htk.le, mulVec_add]
    abel
  have hyk : y k = A *ᵥ p k := by
    rw [hy, hg, hg, hstep k htk.le le_rfl, mulVec_add]
    abel
  have hpyt : 0 < p t ⬝ᵥ y t := by
    rw [hyt]
    exact hA.dotProduct_mulVec_pos hpt
  have hpyk : 0 < p k ⬝ᵥ y k := by
    rw [hyk]
    exact hA.dotProduct_mulVec_pos hpk
  have horth := ShannoCG.SCONB.restart_step_orth_grad A c x p g t k htk hg hstep (hexact t le_rfl htk.le) hconj
  have hconj' : y k ⬝ᵥ p t = 0 := by
    rw [dotProduct_comm, hyk]
    exact hconj k htk le_rfl
  have hdt : d t ⬝ᵥ y t ≠ 0 := by
    intro h
    have hh := hpyt
    rw [hpd t le_rfl htk.le, smul_dotProduct, h, smul_zero] at hh
    exact lt_irrefl _ hh
  have hdk : d k ⬝ᵥ y k ≠ 0 := by
    intro h
    have hh := hpyk
    rw [hpd k htk.le le_rfl, smul_dotProduct, h, smul_zero] at hh
    exact lt_irrefl _ hh
  have hat : α t ≠ 0 := by
    intro h
    apply hpt
    rw [hpd t le_rfl htk.le, h, zero_smul]
  have hak : α k ≠ 0 := by
    intro h
    apply hpk
    rw [hpd k htk.le le_rfl, h, zero_smul]
  have hyy : y t ⬝ᵥ y t ≠ 0 := by
    intro h
    have hy0 : y t = 0 := dotProduct_self_eq_zero.mp h
    rw [hy0, dotProduct_zero] at hpyt
    exact lt_irrefl _ hpyt
  rw [scaled_dir _ _ _ _ _ (ne_of_gt hpyt) (hexact k htk.le le_rfl) horth hconj']
  rw [hpd t le_rfl htk.le, hpd k htk.le le_rfl]
  ext i
  simp [bealeDirection, gammaScale, smul_dotProduct, smul_eq_mul]
  field_simp
  <;> ring

end
