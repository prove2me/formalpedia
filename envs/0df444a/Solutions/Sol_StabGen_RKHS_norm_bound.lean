-- Prove2me | solution 1 for StabGen.RKHS.norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T13:59:53.522978+00:00
-- url     : https://prove2.me/submissions/79dffe5c-7be6-4b33-9a7f-8d1df03e8cc3

import Mathlib
import Definitions.Def_StabGen_RKHS_Regularization
import Definitions.Def_FoundationsML_Stability_IsRKHSOf

set_option autoImplicit false

open FoundationsML.Stability in
theorem d7ab6226_key {X Y H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {m : ℕ}
    (Φ : X → H) (ev : H → X → ℝ)
    (c : ℝ → Y → ℝ) (σ lam : ℝ) (S : Fin m → X × Y)
    (i : Fin m) (f Δ : H)
    (hev : ∀ (h : H) (x : X), ev h x = inner ℝ h (Φ x))
    (hσ : StabGen.RKHS.SigmaAdmissible (Set.range ev) c σ)
    (hmin : ∀ g : H, StabGen.RKHS.regRisk c ev S lam (fun h : H => ‖h‖ ^ 2) f ≤
      StabGen.RKHS.regRisk c ev S lam (fun h : H => ‖h‖ ^ 2) g)
    (hmin' : ∀ g : H, StabGen.RKHS.truncRegRisk c ev S i lam (fun h : H => ‖h‖ ^ 2) (f + Δ) ≤
      StabGen.RKHS.truncRegRisk c ev S i lam (fun h : H => ‖h‖ ^ 2) g)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    lam * (2 * t * (1 - t) * ‖Δ‖ ^ 2) ≤ (1 / (m : ℝ)) * (σ * (t * |ev Δ (S i).1|)) := by
  obtain ⟨hσ0, hconv, hlip⟩ := hσ
  have hlin : ∀ (s : ℝ) (x : X), ev (f + s • Δ) x = ev f x + s * ev Δ x := by
    intro s x
    rw [hev, hev, hev, inner_add_left, real_inner_smul_left]
  have hlin1 : ∀ x : X, ev (f + Δ) x = ev f x + ev Δ x := by
    intro x
    rw [hev, hev, hev, inner_add_left]
  have hnorm : ∀ s : ℝ, ‖f + s • Δ‖ ^ 2 = ‖f‖ ^ 2 + 2 * s * inner ℝ f Δ + s ^ 2 * ‖Δ‖ ^ 2 := by
    intro s
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hnorm1 : ‖f + Δ‖ ^ 2 = ‖f‖ ^ 2 + 2 * inner ℝ f Δ + ‖Δ‖ ^ 2 := by
    rw [norm_add_sq_real]
  have h1 := hmin (f + t • Δ)
  have h2 := hmin' (f + (1 - t) • Δ)
  simp only [StabGen.RKHS.regRisk, StabGen.RKHS.truncRegRisk, EmpiricalError, Loss] at h1 h2
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h1
  simp only [hlin, hlin1, hnorm, hnorm1] at h1 h2
  -- convexity termwise
  have hconvsum : ∑ j ∈ Finset.univ.erase i,
      (c (ev f (S j).1 + t * ev Δ (S j).1) (S j).2 +
        c (ev f (S j).1 + (1 - t) * ev Δ (S j).1) (S j).2) ≤
      ∑ j ∈ Finset.univ.erase i,
      (c (ev f (S j).1) (S j).2 + c (ev f (S j).1 + ev Δ (S j).1) (S j).2) := by
    apply Finset.sum_le_sum
    intro j _
    set a := ev f (S j).1
    set d := ev Δ (S j).1
    have e1 := (hconv (S j).2).2 (Set.mem_univ a) (Set.mem_univ (a + d))
      (show (0:ℝ) ≤ 1 - t by linarith) (show (0:ℝ) ≤ t by linarith) (by ring)
    have e2 := (hconv (S j).2).2 (Set.mem_univ a) (Set.mem_univ (a + d))
      (show (0:ℝ) ≤ t by linarith) (show (0:ℝ) ≤ 1 - t by linarith) (by ring)
    simp only [smul_eq_mul] at e1 e2
    have q1 : (1 - t) * a + t * (a + d) = a + t * d := by ring
    have q2 : t * a + (1 - t) * (a + d) = a + (1 - t) * d := by ring
    rw [q1] at e1
    rw [q2] at e2
    linarith
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hconvsum
  -- Lipschitz at i
  have hlipi : c (ev f (S i).1 + t * ev Δ (S i).1) (S i).2 - c (ev f (S i).1) (S i).2 ≤
      σ * (t * |ev Δ (S i).1|) := by
    have hA : ev f (S i).1 + t * ev Δ (S i).1 ∈ StabGen.RKHS.predictionDomain (Set.range ev) :=
      ⟨ev (f + t • Δ), ⟨_, rfl⟩, (S i).1, hlin t _⟩
    have hB : ev f (S i).1 ∈ StabGen.RKHS.predictionDomain (Set.range ev) :=
      ⟨ev f, ⟨_, rfl⟩, (S i).1, rfl⟩
    have := hlip _ hA _ hB (S i).2
    have e : ev f (S i).1 + t * ev Δ (S i).1 - ev f (S i).1 = t * ev Δ (S i).1 := by ring
    rw [e, abs_mul, abs_of_pos ht0] at this
    exact le_trans (le_abs_self _) this
  have hw : 0 ≤ 1 / (m : ℝ) := by positivity
  have hc := mul_le_mul_of_nonneg_left hconvsum hw
  have hl := mul_le_mul_of_nonneg_left hlipi hw
  nlinarith [hc, hl, h1, h2]

open StabGen.RKHS FoundationsML.Stability in
theorem solution {X Y H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {m : ℕ}
    (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ)
    (c : ℝ → Y → ℝ) (σ κ lam : ℝ) (S : Fin m → X × Y)
    (i : Fin m) (f f' : H)
    (hRKHS : IsRKHSOf K Φ ev) (hK : ∀ x : X, K x x ≤ κ ^ 2)
    (hκ : 0 ≤ κ) (hσ : SigmaAdmissible (Set.range ev) c σ) (hlam : 0 < lam)
    (hmin : ∀ g : H, regRisk c ev S lam (fun h : H => ‖h‖ ^ 2) f ≤
      regRisk c ev S lam (fun h : H => ‖h‖ ^ 2) g)
    (hmin' : ∀ g : H, truncRegRisk c ev S i lam (fun h : H => ‖h‖ ^ 2) f' ≤
      truncRegRisk c ev S i lam (fun h : H => ‖h‖ ^ 2) g) :
    ‖f' - f‖ ≤ κ * σ / (2 * lam * (m : ℝ)) := by
  obtain ⟨hKdef, hev⟩ := hRKHS
  have hσ0 : 0 ≤ σ := hσ.1
  have hm : (0 : ℝ) < m := by
    have : 0 < m := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    exact_mod_cast this
  obtain ⟨Δ, rfl⟩ : ∃ Δ, f' = f + Δ := ⟨f' - f, by abel⟩
  have hsub : f + Δ - f = Δ := by abel
  rw [hsub]
  -- bound on the evaluation
  have hΦ : ‖Φ (S i).1‖ ≤ κ := by
    have h1 := hK (S i).1
    rw [hKdef, real_inner_self_eq_norm_sq] at h1
    nlinarith [norm_nonneg (Φ (S i).1)]
  have hd : |ev Δ (S i).1| ≤ ‖Δ‖ * κ := by
    rw [hev]
    exact le_trans (abs_real_inner_le_norm _ _)
      (mul_le_mul_of_nonneg_left hΦ (norm_nonneg _))
  set D := ‖Δ‖ with hD
  have hD0 : 0 ≤ D := norm_nonneg _
  -- for all t in (0,1): 2 lam (1-t) D^2 * m ≤ σ κ D
  have key : ∀ t : ℝ, 0 < t → t < 1 → 2 * lam * (1 - t) * D ^ 2 * m ≤ σ * (κ * D) := by
    intro t ht0 ht1
    have k := d7ab6226_key Φ ev c σ lam S i f Δ hev hσ hmin hmin' t ht0 ht1
    have k2 : lam * (2 * t * (1 - t) * D ^ 2) * m ≤ σ * (t * |ev Δ (S i).1|) := by
      have := mul_le_mul_of_nonneg_right k hm.le
      rw [show 1 / (m : ℝ) * (σ * (t * |ev Δ (S i).1|)) * m = σ * (t * |ev Δ (S i).1|) by
        field_simp] at this
      exact this
    have k3 : σ * (t * |ev Δ (S i).1|) ≤ σ * (t * (D * κ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd ht0.le) hσ0
    have k4 : t * (2 * lam * (1 - t) * D ^ 2 * m) ≤ t * (σ * (κ * D)) := by
      nlinarith [k2, k3]
    exact le_of_mul_le_mul_left k4 ht0
  -- conclude A ≤ B
  have hAB : 2 * lam * D ^ 2 * m ≤ σ * (κ * D) := by
    by_contra hcon
    rw [not_le] at hcon
    set A := 2 * lam * D ^ 2 * m with hA
    set B := σ * (κ * D) with hB
    have hB0 : 0 ≤ B := by positivity
    have hApos : 0 < A := lt_of_le_of_lt hB0 hcon
    have ht0 : 0 < (A - B) / (2 * A) := by
      apply div_pos <;> linarith
    have ht1 : (A - B) / (2 * A) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    have := key _ ht0 ht1
    have hu : ∀ u : ℝ, 2 * lam * u * D ^ 2 * m = u * A := fun u => by rw [hA]; ring
    have e : 2 * lam * (1 - (A - B) / (2 * A)) * D ^ 2 * m = (A + B) / 2 := by
      rw [hu]
      field_simp
      ring
    rw [e] at this
    linarith
  rw [le_div_iff₀ (by positivity)]
  rcases hD0.lt_or_eq with hpos | hzero
  · have : D * (2 * lam * m) * D ≤ κ * σ * D := by nlinarith [hAB]
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]
    simp only [zero_mul]
    positivity
