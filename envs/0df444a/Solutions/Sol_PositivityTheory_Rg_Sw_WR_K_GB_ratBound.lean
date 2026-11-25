-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.ratBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:28:16.406257+00:00
-- url     : https://prove2.me/submissions/5276a609-2145-4878-a80b-1a5c48eff887

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBFinal
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_RatBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_cls_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_conj_mem_Ugood
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_contDiff_conj
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_dP_of_spectral
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_dP_pos
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_herm_mem_Ugood
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_herm_spectral
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_length_blocks
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_prod_blocks
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_prod_sqrt_perm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (hC : CauchyW) (hI : Invar) (hB : PBound) (hL : Link) (s : ℂ) (hs : s = 1 ∨ s = -1)
    (p q N : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    ∃ C : ℝ, ∀ y : E n, ‖(Delta^[N] (cls s 0 p q R)) y‖ ≤ C * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
  obtain ⟨hUo, hFc, c₀, C₀, hc₀, hb⟩ := hB n s hs p q R
  set K : ℝ := ((N * n : ℕ) : ℝ) with hK
  set C₁ : ℝ := max C₀ 0 with hC₁
  refine ⟨(Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁, fun y => ?_⟩
  obtain ⟨k, hk, lam, hy⟩ := herm_spectral y
  set w : Fin n → ℝ := fun i => 1 + |lam i| with hw
  have hwpos : ∀ i, 0 < w i := fun i => by simp only [hw]; positivity
  set W : ℝ := ∏ i, w i with hW
  have hWpos : 0 < W := Finset.prod_pos fun i _ => hwpos i
  set d : Mc n := Matrix.diagonal (fun i => (lam i : ℂ)) with hd
  set ρ : Fin n → Fin n → ℝ := fun i j => c₀ * Real.sqrt ((1 + |lam i|) * (1 + |lam j|)) with hρ
  have hρpos : ∀ i j, 0 < ρ i j := fun i j => mul_pos hc₀ (Real.sqrt_pos.2 (mul_pos (hwpos i) (hwpos j)))
  have hlink := (hL n (Fr s p q R) (Ugood s) hUo hFc (herm_mem_Ugood s hs)).1 N y
  rw [cls_zero, hlink, hy]
  set F' : Mc n → ℂ := fun c => Fr s p q R (k * c * kᴴ) with hF'
  set U' : Set (Mc n) := {c | k * c * kᴴ ∈ Ugood s} with hU'
  have hU'o : IsOpen U' := hUo.preimage (contDiff_conj k).continuous
  have hF'c : ContDiffOn ℂ (⊤ : ℕ∞) F' U' := hFc.comp (contDiff_conj k).contDiffOn (fun c hc => hc)
  have hdisc : pdisc d ρ ⊆ U' := fun b hb' => (hb k hk lam b hb').1
  have hdmem : d ∈ U' := hdisc (fun i j => by simp [hρpos i j |>.le])
  have hherm' : ∀ y', herm y' ∈ U' := fun y' => conj_mem_Ugood s k hk _ (herm_mem_Ugood s hs y')
  rw [← hI n (Fr s p q R) (Ugood s) hUo hFc k hk N d hdmem, (hL n F' U' hU'o hF'c hherm').2 N d hdmem]
  have hM : ∀ b ∈ pdisc d ρ, ‖F' b‖ ≤ C₁ * W ^ (-((p + q : ℕ) : ℝ)) := fun b hb' =>
    ((hb k hk lam b hb').2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hWpos.le _))
  have hword : ∀ τ : Fin N → Equiv.Perm (Fin n),
      ‖word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F' d‖ ≤
        ((K / c₀) ^ n / W) ^ N * (C₁ * W ^ (-((p + q : ℕ) : ℝ))) := by
    intro τ
    have h := hC n F' U' hU'o hF'c d ρ hρpos hdisc _ hM ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k))
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [List.map_flatMap]
    simp only [List.map_map, Function.comp_def]
    rw [prod_blocks N (fun j k => (((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)).length : ℝ) /
      ρ (τ j k) k)]
    rw [length_blocks]
    show ∏ j, ∏ k, K / ρ ((τ j) k) k = ((K / c₀) ^ n / W) ^ N
    have hblock : ∀ j, ∏ k, K / ρ ((τ j) k) k = (K / c₀) ^ n / W := by
      intro j
      have hs := prod_sqrt_perm (τ j) w hwpos
      simp only [hw] at hs
      simp only [hρ]
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, hs, div_pow]
      simp only [hW, hw]
      field_simp
    rw [Finset.prod_congr rfl fun j _ => hblock j, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsgn : ∀ τ : Fin N → Equiv.Perm (Fin n), ‖(((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ))‖ = 1 := by
    intro τ
    have h : ∀ j, |((Equiv.Perm.sign (τ j) : ℤ))| = 1 := fun j => by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (τ j)) with h | h <;> simp [h]
    have h2 : |∏ j, ((Equiv.Perm.sign (τ j) : ℤ))| = 1 := by
      rw [Finset.abs_prod, Finset.prod_eq_one fun j _ => h j]
    rw [Complex.norm_intCast]
    exact_mod_cast h2
  have hdP : dP y ≤ W ^ (2 : ℝ) := by
    rw [dP_of_spectral y k hk lam hy, Real.rpow_two, hW, ← Finset.prod_pow]
    refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
    simp only [hw]
    have : lam i ^ 2 = |lam i| ^ 2 := (sq_abs _).symm
    nlinarith [abs_nonneg (lam i)]
  have hWe : ∀ e : ℝ, 0 ≤ e → W ^ (-e) ≤ (dP y) ^ (-e / 2) := by
    intro e he
    have h1 : W ^ (-e) = (W ^ (2 : ℝ)) ^ (-e / 2) := by
      rw [← Real.rpow_mul hWpos.le]; ring_nf
    rw [h1]
    exact Real.rpow_le_rpow_of_nonpos (dP_pos y) hdP (by linarith)
  calc ‖∑ τ : Fin N → Equiv.Perm (Fin n), (((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ)) *
          word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F' d‖
      ≤ ∑ τ : Fin N → Equiv.Perm (Fin n), ((K / c₀) ^ n / W) ^ N * (C₁ * W ^ (-((p + q : ℕ) : ℝ))) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
        rw [norm_mul, hsgn τ, one_mul]; exact hword τ
    _ = (Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁ *
          (W ^ (-((p + q + N : ℕ) : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : W ^ (-((p + q + N : ℕ) : ℝ)) = W ^ (-((p + q : ℕ) : ℝ)) * (W ^ N)⁻¹ := by
          rw [show (-((p + q + N : ℕ) : ℝ)) = (-((p + q : ℕ) : ℝ)) + (-(N : ℝ)) by push_cast; ring,
            Real.rpow_add hWpos, Real.rpow_neg hWpos.le, Real.rpow_natCast, Real.rpow_neg hWpos.le, Real.rpow_natCast]
        rw [this, div_pow]; ring
    _ ≤ (Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁ *
          (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
        refine mul_le_mul_of_nonneg_left (hWe _ (by positivity)) ?_
        refine mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (pow_nonneg (div_nonneg (by positivity) hc₀.le) _) _))
          (le_max_right _ _)
end PositivityTheory.Rg.Sw.WR.K.GB
