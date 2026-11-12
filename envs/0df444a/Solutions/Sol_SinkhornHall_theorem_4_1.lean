-- Prove2me | solution 1 for SinkhornHall.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T00:17:47.945227+00:00
-- url     : https://prove2.me/submissions/559bf842-77b9-4ecd-8ba9-1ef0714f5dec

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Theorems.Thm_SinkhornHall_step2_output_exists
import Theorems.Thm_SinkhornHall_log_kappa_sinkhorn_le
import Theorems.Thm_SinkhornHall_corollary_2_6_edge
import Theorems.Thm_SinkhornHall_step2_output_hall_blocker

open Finset SinkhornHall

private lemma sinkhorn_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j) :
    ∀ ℓ : ℕ, (∀ i, 0 < (sinkhorn A ℓ).1 i) ∧ (∀ j, 0 < (sinkhorn A ℓ).2 j)
  | 0 => by
      refine ⟨fun _ => zero_lt_one, fun j => ?_⟩
      obtain ⟨i₀, hi₀⟩ := hcol j
      have ht_pos : 0 < ∑ i, A i j * (1 : Fin n → ℝ) i :=
        (mul_pos hi₀ zero_lt_one).trans_le
          (Finset.single_le_sum (f := fun i => A i j * (1 : Fin n → ℝ) i)
            (fun i _ => mul_nonneg (hA i j) zero_le_one) (Finset.mem_univ i₀))
      exact div_pos zero_lt_one ht_pos
  | ℓ + 1 => by
      obtain ⟨_, hy_pos⟩ := sinkhorn_pos A hA hrow hcol ℓ
      have hx'_pos : ∀ i, 0 < rowNorm A 1 (sinkhorn A ℓ).2 i := by
        intro i
        obtain ⟨j₀, hj₀⟩ := hrow i
        have hs_pos : 0 < ∑ j, A i j * (sinkhorn A ℓ).2 j :=
          (mul_pos hj₀ (hy_pos j₀)).trans_le
            (Finset.single_le_sum (f := fun j => A i j * (sinkhorn A ℓ).2 j)
              (fun j _ => mul_nonneg (hA i j) (hy_pos j).le) (Finset.mem_univ j₀))
        exact div_pos zero_lt_one hs_pos
      refine ⟨hx'_pos, fun j => ?_⟩
      obtain ⟨i₀, hi₀⟩ := hcol j
      have ht_pos : 0 < ∑ i, A i j * rowNorm A 1 (sinkhorn A ℓ).2 i :=
        (mul_pos hi₀ (hx'_pos i₀)).trans_le
          (Finset.single_le_sum (f := fun i => A i j * rowNorm A 1 (sinkhorn A ℓ).2 i)
            (fun i _ => mul_nonneg (hA i j) (hx'_pos i).le) (Finset.mem_univ i₀))
      exact div_pos zero_lt_one ht_pos

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j)
    (hpm : ¬ HasPerfectMatching A) (ℓ : ℕ)
    (hℓ : (1 / 4 : ℝ) * (n : ℝ) ^ 2 * Real.log ((numEdges A : ℝ) * Amax A / Amin A) ≤ ℓ) :
    (∃ X, IsStep2Output (sinkhorn A ℓ).1 (sinkhorn A ℓ).2 X) ∧
      ∀ X, IsStep2Output (sinkhorn A ℓ).1 (sinkhorn A ℓ).2 X → IsHallBlocker A X := by
  have hn2 : 2 ≤ n := by
    rcases n with _ | _ | n'
    · exfalso
      exact hpm ⟨Equiv.refl (Fin 0), fun i => i.elim0⟩
    · exfalso
      obtain ⟨j₀, hj₀⟩ := hrow 0
      have hj0 : j₀ = 0 := Fin.eq_zero j₀
      rw [hj0] at hj₀
      exact hpm ⟨Equiv.refl (Fin 1), fun i => by rw [Fin.eq_zero i]; exact hj₀⟩
    · omega
  have hn_pos : 0 < n := by omega
  have h2_edges : 1 < numEdges A := by
    classical
    let E : Finset (Fin n × Fin n) := Finset.univ.filter (fun p : Fin n × Fin n => 0 < A p.1 p.2)
    have hE_card : E.card = numEdges A := by
      unfold numEdges
      congr 1
    let f : Fin n → Fin n × Fin n := fun i => (i, Classical.choose (hrow i))
    have hf_maps : Set.MapsTo f (Finset.univ : Finset (Fin n)) E := by
      intro i _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Classical.choose_spec (hrow i)⟩
    have hf_inj : Set.InjOn f (Finset.univ : Finset (Fin n)) :=
      fun i₁ _ i₂ _ h => (Prod.mk.inj h).1
    have hle : (Finset.univ : Finset (Fin n)).card ≤ E.card :=
      Finset.card_le_card_of_injOn f hf_maps hf_inj
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    omega
  obtain ⟨hx_pos, hy_pos⟩ := sinkhorn_pos A hA hrow hcol ℓ
  refine ⟨step2_output_exists hn_pos (sinkhorn A ℓ).1 (sinkhorn A ℓ).2 hx_pos hy_pos, ?_⟩
  rintro X ⟨σ, τ, k, hσ, hτ, hk, rfl⟩
  have hκ : kappa A 1 1 (sinkhorn A ℓ).1 (sinkhorn A ℓ).2 ≤ Amin A :=
    (log_kappa_sinkhorn_le A hA hrow hcol hpm).2 ℓ hℓ
  have hedge0 := corollary_2_6_edge A hA hrow hcol h2_edges 1 1
    (fun _ => zero_lt_one) (fun _ => zero_lt_one) rfl
    (sinkhorn A ℓ).1 (sinkhorn A ℓ).2 hx_pos hy_pos hκ
  let x := (sinkhorn A ℓ).1
  let y := (sinkhorn A ℓ).2
  have hrhs_eq :
      (∏ i, x i ^ ((1 : Fin n → ℝ) i / ∑ i', (1 : Fin n → ℝ) i')) *
        (∏ j, y j ^ ((1 : Fin n → ℝ) j / ∑ j', (1 : Fin n → ℝ) j')) =
      ((∏ i, x i) * ∏ j, y j) ^ ((1 : ℝ) / n) := by
    have hpx_pos : 0 < ∏ i, x i := Finset.prod_pos fun i _ => hx_pos i
    have hpy_pos : 0 < ∏ j, y j := Finset.prod_pos fun j _ => hy_pos j
    have hL_pos : 0 < (∏ i, x i ^ ((1 : Fin n → ℝ) i / ∑ i', (1 : Fin n → ℝ) i')) *
        (∏ j, y j ^ ((1 : Fin n → ℝ) j / ∑ j', (1 : Fin n → ℝ) j')) :=
      mul_pos (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx_pos i) _)
        (Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hy_pos j) _)
    have hR_pos : 0 < ((∏ i, x i) * ∏ j, y j) ^ ((1 : ℝ) / n) :=
      Real.rpow_pos_of_pos (mul_pos hpx_pos hpy_pos) _
    refine Real.log_injOn_pos hL_pos hR_pos ?_
    have hsum1 : ∑ _ : Fin n, (1 : ℝ) = (n : ℝ) := by simp
    simp only [Pi.one_apply, hsum1]
    rw [Real.log_mul (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx_pos i) _).ne'
        (Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hy_pos j) _).ne',
      Real.log_prod fun i _ => (Real.rpow_pos_of_pos (hx_pos i) _).ne',
      Real.log_prod fun j _ => (Real.rpow_pos_of_pos (hy_pos j) _).ne',
      Real.log_rpow (mul_pos hpx_pos hpy_pos),
      Real.log_mul hpx_pos.ne' hpy_pos.ne',
      Real.log_prod fun i _ => (hx_pos i).ne',
      Real.log_prod fun j _ => (hy_pos j).ne']
    have hx_sum : ∑ i, Real.log (x i ^ ((1 : ℝ) / n)) =
        ((1 : ℝ) / n) * ∑ i, Real.log (x i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Real.log_rpow (hx_pos i), mul_comm]
    have hy_sum : ∑ j, Real.log (y j ^ ((1 : ℝ) / n)) =
        ((1 : ℝ) / n) * ∑ j, Real.log (y j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [Real.log_rpow (hy_pos j), mul_comm]
    rw [hx_sum, hy_sum]
    ring
  have hedge : ∀ i j, 0 < A i j → x i * y j < ((∏ i', x i') * ∏ j', y j') ^ ((1 : ℝ) / n) := by
    intro i j hij
    rw [← hrhs_eq]
    exact hedge0 i j hij
  exact (step2_output_hall_blocker A hA hrow hcol x y hx_pos hy_pos hedge σ τ k hσ hτ hk).2
