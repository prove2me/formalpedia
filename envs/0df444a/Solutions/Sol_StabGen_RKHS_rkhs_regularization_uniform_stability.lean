-- Prove2me | solution 1 for StabGen.RKHS.rkhs_regularization_uniform_stability
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T13:37:12.068734+00:00
-- url     : https://prove2.me/submissions/c390e02d-9689-4a2c-ac3f-23ccd85367bb

import Mathlib
import Definitions.Def_StabGen_RKHS_Regularization
import Definitions.Def_FoundationsML_Stability_IsRKHSOf

set_option autoImplicit false

theorem P9c282807_limit_step (M C : ℝ) (hC : 0 ≤ C)
    (h : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) * M ≤ C) : M ≤ C := by
  by_contra hMC0
  have hMC : C < M := not_le.mp hMC0
  have hM : 0 < M := lt_of_le_of_lt hC hMC
  have ht0 : 0 < (M - C) / (2 * M) := div_pos (sub_pos.2 hMC) (by linarith)
  have ht1 : (M - C) / (2 * M) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have h1 := h _ ht0 ht1
  have e : (1 - (M - C) / (2 * M)) * M = (M + C) / 2 := by
    field_simp
    ring
  rw [e] at h1
  linarith

open StabGen.RKHS FoundationsML.Stability in
theorem solution {X Y H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {m : ℕ} (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ)
    (c : ℝ → Y → ℝ) (σ κ lam : ℝ) (S : Fin m → X × Y)
    (i : Fin m) (f f' : H)
    (hRKHS : IsRKHSOf K Φ ev) (hK : ∀ x : X, K x x ≤ κ ^ 2)
    (hσ : SigmaAdmissible (Set.range ev) c σ) (hlam : 0 < lam)
    (hmin : ∀ g : H, regRisk c ev S lam (fun h : H => ‖h‖ ^ 2) f ≤
      regRisk c ev S lam (fun h : H => ‖h‖ ^ 2) g)
    (hmin' : ∀ g : H, truncRegRisk c ev S i lam (fun h : H => ‖h‖ ^ 2) f' ≤
      truncRegRisk c ev S i lam (fun h : H => ‖h‖ ^ 2) g) :
    ∀ z : X × Y,
      |Loss c (ev f) z - Loss c (ev f') z| ≤
        σ ^ 2 * κ ^ 2 / (2 * lam * (m : ℝ)) := by
  intro z
  obtain ⟨hKΦ, hev⟩ := hRKHS
  obtain ⟨hσ0, hconv, hlip⟩ := hσ
  have hm : (0 : ℝ) < m := by exact_mod_cast Fin.pos i
  set Δ : H := f' - f with hΔ
  have hΦ : ∀ x, ‖Φ x‖ ≤ |κ| := by
    intro x
    have h1 : ‖Φ x‖ ^ 2 ≤ κ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← hKΦ]; exact hK x
    have := sq_le_sq.1 h1
    rwa [abs_norm] at this
  have hevb : ∀ x, |ev Δ x| ≤ ‖Δ‖ * |κ| := by
    intro x
    rw [hev]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hΦ x) (norm_nonneg _))
  have hlinD : ∀ x, ev Δ x = ev f' x - ev f x := by
    intro x; simp only [hev, hΔ, inner_sub_left]
  have hlin1 : ∀ (t : ℝ) x, ev (f + t • Δ) x = ev f x + t * ev Δ x := by
    intro t x; simp only [hev, inner_add_left, real_inner_smul_left]
  have hlin2 : ∀ (t : ℝ) x, ev (f' - t • Δ) x = ev f' x - t * ev Δ x := by
    intro t x; simp only [hev, inner_sub_left, real_inner_smul_left]
  have hmem : ∀ g x, ev g x ∈ predictionDomain (Set.range ev) :=
    fun g x => ⟨ev g, ⟨g, rfl⟩, x, rfl⟩
  have hnorm : ∀ t : ℝ, ‖f + t • Δ‖ ^ 2 + ‖f' - t • Δ‖ ^ 2
      = ‖f‖ ^ 2 + ‖f'‖ ^ 2 - 2 * t * (1 - t) * ‖Δ‖ ^ 2 := by
    intro t
    have hf' : f' = f + Δ := by rw [hΔ]; abel
    rw [hf']
    simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm f Δ]
    ring
  set D := ‖Δ‖ with hD
  have key : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) * (2 * lam * D ^ 2) ≤ σ * (D * |κ|) / m := by
    intro t ht0 ht1
    have h1 := hmin (f + t • Δ)
    have h2 := hmin' (f' - t • Δ)
    simp only [regRisk, truncRegRisk, EmpiricalError, Loss] at h1 h2
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h1
    have hP : ∑ j ∈ Finset.univ.erase i, c (ev (f + t • Δ) (S j).1) (S j).2
        + ∑ j ∈ Finset.univ.erase i, c (ev (f' - t • Δ) (S j).1) (S j).2
        ≤ ∑ j ∈ Finset.univ.erase i, c (ev f (S j).1) (S j).2
        + ∑ j ∈ Finset.univ.erase i, c (ev f' (S j).1) (S j).2 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j _
      rw [hlin1, hlin2, hlinD]
      have c1 := (hconv (S j).2).2 (Set.mem_univ (ev f (S j).1)) (Set.mem_univ (ev f' (S j).1))
        (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
      have c2 := (hconv (S j).2).2 (Set.mem_univ (ev f (S j).1)) (Set.mem_univ (ev f' (S j).1))
        ht0.le (by linarith : (0 : ℝ) ≤ 1 - t) (by ring)
      simp only [smul_eq_mul] at c1 c2
      have e1 : ev f (S j).1 + t * (ev f' (S j).1 - ev f (S j).1)
          = (1 - t) * ev f (S j).1 + t * ev f' (S j).1 := by ring
      have e2 : ev f' (S j).1 - t * (ev f' (S j).1 - ev f (S j).1)
          = t * ev f (S j).1 + (1 - t) * ev f' (S j).1 := by ring
      rw [e1, e2]
      linarith
    have hL : c (ev (f + t • Δ) (S i).1) (S i).2 - c (ev f (S i).1) (S i).2
        ≤ σ * (t * (D * |κ|)) := by
      have hl := hlip _ (hmem (f + t • Δ) (S i).1) _ (hmem f (S i).1) (S i).2
      rw [hlin1] at hl ⊢
      have ea : |ev f (S i).1 + t * ev Δ (S i).1 - ev f (S i).1| = t * |ev Δ (S i).1| := by
        rw [add_sub_cancel_left, abs_mul, abs_of_pos ht0]
      rw [ea] at hl
      have hb : t * |ev Δ (S i).1| ≤ t * (D * |κ|) :=
        mul_le_mul_of_nonneg_left (hevb _) ht0.le
      have hb' := mul_le_mul_of_nonneg_left hb hσ0
      exact (le_abs_self _).trans (hl.trans hb')
    have hinv : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
    have hsum := mul_le_mul_of_nonneg_left (add_le_add hL hP) hinv
    have hn := hnorm t
    have E : lam * (2 * t * (1 - t) * D ^ 2) ≤ 1 / (m : ℝ) * (σ * (t * (D * |κ|))) := by
      nlinarith [h1, h2, hsum, hn]
    have E' : t * ((1 - t) * (2 * lam * D ^ 2)) ≤ t * (σ * (D * |κ|) / m) := by
      calc t * ((1 - t) * (2 * lam * D ^ 2)) = lam * (2 * t * (1 - t) * D ^ 2) := by ring
        _ ≤ 1 / (m : ℝ) * (σ * (t * (D * |κ|))) := E
        _ = t * (σ * (D * |κ|) / m) := by ring
    exact le_of_mul_le_mul_left E' ht0
  have hC : 0 ≤ σ * (D * |κ|) / m := by positivity
  have L := P9c282807_limit_step _ _ hC key
  have L' : 2 * lam * D ^ 2 * m ≤ σ * (D * |κ|) := by rwa [le_div_iff₀ hm] at L
  have hDb : 2 * lam * m * D ≤ σ * |κ| := by
    rcases (norm_nonneg Δ).lt_or_eq with hpos | hzero
    · have : D * (2 * lam * m * D) ≤ D * (σ * |κ|) := by linarith
      exact le_of_mul_le_mul_left this hpos
    · rw [← hD] at hzero
      rw [← hzero]
      have : 0 ≤ σ * |κ| := by positivity
      linarith
  have hgoal1 : |Loss c (ev f) z - Loss c (ev f') z| ≤ σ * (D * |κ|) := by
    simp only [Loss]
    have hl := hlip _ (hmem f z.1) _ (hmem f' z.1) z.2
    have e : |ev f z.1 - ev f' z.1| = |ev Δ z.1| := by
      rw [hlinD, abs_sub_comm]
    rw [e] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left (hevb _) hσ0)
  refine hgoal1.trans ?_
  rw [le_div_iff₀ (by positivity)]
  have hk : κ ^ 2 = |κ| ^ 2 := (sq_abs κ).symm
  rw [hk]
  have hsk : 0 ≤ σ * |κ| := by positivity
  have := mul_le_mul_of_nonneg_left hDb hsk
  nlinarith [this]
