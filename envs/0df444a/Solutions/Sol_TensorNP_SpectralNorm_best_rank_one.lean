-- Prove2me | solution 1 for TensorNP.SpectralNorm.best_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:21:04.155683+00:00
-- url     : https://prove2.me/submissions/7c1509b6-29c2-487d-a12f-3ea4ea9169a1

import Mathlib
import Definitions.Def_TensorNP_SpectralNorm_Tensor

namespace Aux_TensorNP_SpectralNorm_best_rank_one

open TensorNP.SpectralNorm

lemma sumsq_of_unit {n : ℕ} (u : Fin n → ℝ) (h : l2norm u = 1) : ∑ i, u i ^ 2 = 1 := by
  unfold l2norm at h
  rwa [Real.sqrt_eq_one] at h

lemma l2norm_pos {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) : 0 < l2norm x := by
  unfold l2norm
  apply Real.sqrt_pos.2
  by_contra hle
  push_neg at hle
  have h0 : ∑ i, x i ^ 2 = 0 := le_antisymm hle (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at h0
  apply hx
  funext i
  have := h0 i (Finset.mem_univ _)
  simpa using this

lemma normalize {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) :
    l2norm (fun i => x i / l2norm x) = 1 := by
  have hp := l2norm_pos x hx
  set nx := l2norm x with hnx
  have hsq : nx ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  rw [show l2norm (fun i => x i / nx) = Real.sqrt (∑ i, (x i / nx) ^ 2) from rfl,
    Real.sqrt_eq_one]
  simp only [div_pow]
  rw [← Finset.sum_div, ← hsq]
  exact div_self (pow_pos hp 2).ne'

lemma tri_scale {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ) (x : Fin l → ℝ) (y : Fin m → ℝ)
    (z : Fin n → ℝ) (α β γ : ℝ) :
    trilinear A (fun i => x i / α) (fun j => y j / β) (fun k => z k / γ) =
      trilinear A x y z / (α * β * γ) := by
  unfold trilinear
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro k _
  ring

lemma tri_neg {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ) (x : Fin l → ℝ) (y : Fin m → ℝ)
    (z : Fin n → ℝ) : trilinear A (fun i => -x i) y z = -trilinear A x y z := by
  unfold trilinear
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

lemma frob_expand {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ) (σ : ℝ) (u : Fin l → ℝ)
    (v : Fin m → ℝ) (w : Fin n → ℝ) :
    frobSq (fun i j k => A i j k - σ * outer3 u v w i j k) =
      frobSq A - 2 * σ * trilinear A u v w +
        σ ^ 2 * ((∑ i, u i ^ 2) * (∑ j, v j ^ 2) * (∑ k, w k ^ 2)) := by
  unfold frobSq trilinear outer3
  have e : ∀ i j k, (A i j k - σ * (u i * v j * w k)) ^ 2 =
      A i j k ^ 2 - 2 * σ * (A i j k * u i * v j * w k) + σ ^ 2 * (u i ^ 2 * v j ^ 2 * w k ^ 2) :=
    fun i j k => by ring
  have hprod : ∑ i, ∑ j, u i ^ 2 * v j ^ 2 * ∑ k, w k ^ 2 =
      (∑ i, u i ^ 2) * (∑ j, v j ^ 2) * (∑ k, w k ^ 2) := by
    calc ∑ i, ∑ j, u i ^ 2 * v j ^ 2 * ∑ k, w k ^ 2
        = ∑ i, (u i ^ 2 * ∑ j, v j ^ 2) * ∑ k, w k ^ 2 :=
          Finset.sum_congr rfl (fun i _ => by rw [← Finset.sum_mul, ← Finset.mul_sum])
      _ = (∑ i, u i ^ 2) * (∑ j, v j ^ 2) * (∑ k, w k ^ 2) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hprod]

lemma unit_compact (n : ℕ) : IsCompact {u : Fin n → ℝ | l2norm u = 1} := by
  have hc : Continuous (fun u : Fin n → ℝ => l2norm u) := by unfold l2norm; fun_prop
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_eq hc continuous_const)
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨1, fun u hu => ?_⟩
  simp only [Set.mem_setOf_eq] at hu
  have hs := sumsq_of_unit u hu
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs]
  have : u i ^ 2 ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (f := fun i => u i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [abs_nonneg (u i), sq_abs (u i)]

lemma unit_nonempty (n : ℕ) (hn : 0 < n) : ∃ u : Fin n → ℝ, l2norm u = 1 := by
  refine ⟨Pi.single ⟨0, hn⟩ 1, ?_⟩
  unfold l2norm
  rw [Real.sqrt_eq_one]
  simp [Pi.single_apply]

end Aux_TensorNP_SpectralNorm_best_rank_one

open Aux_TensorNP_SpectralNorm_best_rank_one in
open TensorNP.SpectralNorm in
theorem solution {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (A : Fin a → Fin b → Fin c → ℝ) :
    IsGreatest {t : ℝ | ∃ (u : Fin a → ℝ) (v : Fin b → ℝ) (w : Fin c → ℝ),
        l2norm u = 1 ∧ l2norm v = 1 ∧ l2norm w = 1 ∧ t = trilinear A u v w} (specNorm A) ∧
      IsLeast {t : ℝ | ∃ (σ : ℝ) (u : Fin a → ℝ) (v : Fin b → ℝ) (w : Fin c → ℝ),
          0 ≤ σ ∧ l2norm u = 1 ∧ l2norm v = 1 ∧ l2norm w = 1 ∧
          t = frobSq (fun i j k => A i j k - σ * outer3 u v w i j k)}
        (frobSq A - specNorm A ^ 2) ∧
      ∀ (σ : ℝ) (u : Fin a → ℝ) (v : Fin b → ℝ) (w : Fin c → ℝ),
        0 ≤ σ → l2norm u = 1 → l2norm v = 1 → l2norm w = 1 →
        frobSq (fun i j k => A i j k - σ * outer3 u v w i j k) = frobSq A - specNorm A ^ 2 →
        σ = specNorm A := by
  set K := {u : Fin a → ℝ | l2norm u = 1} ×ˢ ({v : Fin b → ℝ | l2norm v = 1} ×ˢ
    {w : Fin c → ℝ | l2norm w = 1}) with hK
  have hKc : IsCompact K := (unit_compact a).prod ((unit_compact b).prod (unit_compact c))
  obtain ⟨u0, hu0⟩ := unit_nonempty a ha
  obtain ⟨v0, hv0⟩ := unit_nonempty b hb
  obtain ⟨w0, hw0⟩ := unit_nonempty c hc
  have hKne : K.Nonempty := ⟨(u0, v0, w0), hu0, hv0, hw0⟩
  have hTc : Continuous (fun p : (Fin a → ℝ) × (Fin b → ℝ) × (Fin c → ℝ) =>
      trilinear A p.1 p.2.1 p.2.2) := by unfold trilinear; fun_prop
  obtain ⟨⟨us, vs, ws⟩, ⟨hus, hvs, hws⟩, hmax⟩ := hKc.exists_isMaxOn hKne hTc.continuousOn
  set M := trilinear A us vs ws with hM
  have hle : ∀ u v w, l2norm u = 1 → l2norm v = 1 → l2norm w = 1 → trilinear A u v w ≤ M :=
    fun u v w hu hv hw => isMaxOn_iff.1 hmax (u, v, w) ⟨hu, hv, hw⟩
  have habs : ∀ u v w, l2norm u = 1 → l2norm v = 1 → l2norm w = 1 → |trilinear A u v w| ≤ M := by
    intro u v w hu hv hw
    rw [abs_le]
    constructor
    · have hneg : l2norm (fun i => -u i) = 1 := by
        unfold l2norm at hu ⊢; simpa using hu
      have := hle _ v w hneg hv hw
      rw [tri_neg] at this
      linarith
    · exact hle u v w hu hv hw
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (habs us vs ws hus hvs hws)
  have hne0 : ∀ {n : ℕ} (u : Fin n → ℝ), l2norm u = 1 → u ≠ 0 := by
    intro n u hu h0
    rw [h0] at hu
    unfold l2norm at hu
    simp at hu
  -- specNorm = M
  have hspec : specNorm A = M := by
    unfold specNorm
    apply IsGreatest.csSup_eq
    constructor
    · refine ⟨us, vs, ws, hne0 us hus, hne0 vs hvs, hne0 ws hws, ?_⟩
      rw [hus, hvs, hws, abs_of_nonneg hM0]
      ring
    · rintro t ⟨x, y, z, hx, hy, hz, rfl⟩
      have hpx := l2norm_pos x hx
      have hpy := l2norm_pos y hy
      have hpz := l2norm_pos z hz
      have := habs _ _ _ (normalize x hx) (normalize y hy) (normalize z hz)
      rw [tri_scale, abs_div, abs_of_pos (by positivity : 0 < l2norm x * l2norm y * l2norm z)]
        at this
      exact this
  rw [hspec]
  have hfe : ∀ σ u v w, l2norm u = 1 → l2norm v = 1 → l2norm w = 1 →
      frobSq (fun i j k => A i j k - σ * outer3 u v w i j k) =
        frobSq A - 2 * σ * trilinear A u v w + σ ^ 2 := by
    intro σ u v w hu hv hw
    rw [frob_expand, sumsq_of_unit u hu, sumsq_of_unit v hv, sumsq_of_unit w hw]
    ring
  refine ⟨⟨⟨us, vs, ws, hus, hvs, hws, rfl⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rintro t ⟨u, v, w, hu, hv, hw, rfl⟩
    exact hle u v w hu hv hw
  · refine ⟨M, us, vs, ws, hM0, hus, hvs, hws, ?_⟩
    rw [hfe M us vs ws hus hvs hws]
    ring
  · rintro t ⟨σ, u, v, w, hσ, hu, hv, hw, rfl⟩
    rw [hfe σ u v w hu hv hw]
    have h1 := habs u v w hu hv hw
    have h2 : trilinear A u v w ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_nonneg (σ - trilinear A u v w)]
  · intro σ u v w hσ hu hv hw heq
    rw [hfe σ u v w hu hv hw] at heq
    have h1 := habs u v w hu hv hw
    have h2 : trilinear A u v w ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : (σ - trilinear A u v w) ^ 2 + (M ^ 2 - trilinear A u v w ^ 2) = 0 := by linarith
    have h4 : (σ - trilinear A u v w) ^ 2 = 0 := by nlinarith [sq_nonneg (σ - trilinear A u v w)]
    have h5 : σ = trilinear A u v w := by nlinarith [sq_nonneg (σ - trilinear A u v w)]
    have h6 : trilinear A u v w ^ 2 = M ^ 2 := by nlinarith
    have h7 : trilinear A u v w = M := by
      have := hle u v w hu hv hw
      nlinarith [sq_nonneg (trilinear A u v w + M)]
    linarith
