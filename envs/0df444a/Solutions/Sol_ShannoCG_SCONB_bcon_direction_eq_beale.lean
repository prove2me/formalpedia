-- Prove2me | solution 1 for ShannoCG.SCONB.bcon_direction_eq_beale
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:36:04.181233+00:00
-- url     : https://prove2.me/submissions/5990dd3a-14f8-4441-8b63-6f4a57fa4f37

import Mathlib
import Definitions.Def_ShannoCG_SCONB_bconDirection
import Definitions.Def_ShannoCG_SCONB_bealeDirection
import Definitions.Def_ShannoCG_SCONB_sconbDirection
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

private theorem restart_orth {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (x p g : ℕ → Fin n → ℝ) (t k : ℕ) (htk : t < k)
    (hg : ∀ i, g i = A *ᵥ x i + c)
    (hstep : ∀ i, t ≤ i → i ≤ k → x (i + 1) = x i + p i)
    (hexact_t : p t ⬝ᵥ g (t + 1) = 0)
    (hconj : ∀ i, t < i → i ≤ k → p t ⬝ᵥ (A *ᵥ p i) = 0) :
    p t ⬝ᵥ g (k + 1) = 0 := by
  have hi : ∀ i, t ≤ i → i ≤ k → p t ⬝ᵥ g (i + 1) = 0 := by
    intro i hti
    induction i, hti using Nat.le_induction with
    | base => intro _; exact hexact_t
    | succ i hti ih =>
      intro hik
      have hgstep : g (i + 1 + 1) = g (i + 1) + A *ᵥ p (i + 1) := by
        rw [hg, hg, hstep (i + 1) (by omega) hik, mulVec_add]
        abel
      rw [hgstep, dotProduct_add, ih (by omega), hconj (i + 1) (by omega) hik]
      simp
  exact hi k htk.le le_rfl

private theorem unscaled_dir {n : ℕ} (pt yt pk yk g : Fin n → ℝ)
    (hexact : pk ⬝ᵥ g = 0) (horth : pt ⬝ᵥ g = 0) (hconj : yk ⬝ᵥ pt = 0) :
    bconDirection pt yt pk yk g = -g + ((yt ⬝ᵥ g) / (pt ⬝ᵥ yt)) • pt
      + ((yk ⬝ᵥ g) / (pk ⬝ᵥ yk)) • pk := by
  have hu : unscaledRestart pt yt *ᵥ g = g - ((yt ⬝ᵥ g) / (pt ⬝ᵥ yt)) • pt := by
    simp only [unscaledRestart, add_mulVec, smul_mulVec, sub_mulVec, one_mulVec,
      vecMulVec_mulVec, horth]
    ext i
    simp [smul_eq_mul, div_eq_mul_inv]
    <;> ring
  rw [bconDirection, bfgs_exact _ _ _ _ hexact, hu]
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
    bconDirection (p t) (y t) (p k) (y k) (g (k + 1)) =
      bealeDirection (g (k + 1)) (d k) (y k) (d t) (y t) := by
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
  have horth := restart_orth A c x p g t k htk hg hstep (hexact t le_rfl htk.le) hconj
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
  rw [unscaled_dir _ _ _ _ _ (hexact k htk.le le_rfl) horth hconj']
  rw [hpd t le_rfl htk.le, hpd k htk.le le_rfl]
  ext i
  simp [bealeDirection, smul_dotProduct, smul_eq_mul]
  field_simp
  <;> ring
