-- Prove2me | solution 1 for UhlenbeckGauge.boundaryChernSimons_eq_of_eq_on_boundary
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-10T21:39:06.048127+00:00
-- url     : https://prove2.me/submissions/bc696b7a-7e16-4062-8050-4f1d69a22e46

import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge Matrix MeasureTheory
open scoped ContDiff
set_option autoImplicit false

private lemma levi_repeat02 (a b c : Fin 4) : levi a b a c = 0 := by
  unfold levi
  norm_cast
  exact Matrix.det_zero_of_row_eq (i := (0 : Fin 4)) (j := 2) (by decide) rfl

private lemma line_fderiv_eq (f g : R4 → ℂ) (x e : R4)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (h : ∀ᶠ t in nhds (0 : ℝ), f (x + t • e) = g (x + t • e)) :
    fderiv ℝ f x e = fderiv ℝ g x e := by
  have hl : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  have h1 : HasDerivAt (fun t : ℝ => f (x + t • e)) (fderiv ℝ f x e) 0 := by
    have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • e) := by
      simpa using hf.hasFDerivAt
    exact hf'.comp_hasDerivAt (0 : ℝ) hl
  have h2 : HasDerivAt (fun t : ℝ => g (x + t • e)) (fderiv ℝ g x e) 0 := by
    have hg' : HasFDerivAt g (fderiv ℝ g x) (x + (0 : ℝ) • e) := by
      simpa using hg.hasFDerivAt
    exact hg'.comp_hasDerivAt (0 : ℝ) hl
  have h3 : HasDerivAt (fun t : ℝ => g (x + t • e)) (fderiv ℝ f x e) 0 :=
    h1.congr_of_eventuallyEq (h.mono fun t ht => ht.symm)
  exact h3.unique h2

private lemma pd_eq {n : ℕ} (A B : Connection n) (hA : IsSUConnection A)
    (hB : IsSUConnection B) (x : R4) (ρ : Fin 4)
    (hev : ∀ᶠ t in nhds (0 : ℝ),
      A (x + t • Pi.single ρ 1) = B (x + t • Pi.single ρ 1)) (σ : Fin 4) :
    partialDeriv ρ (fun y => A y σ) x = partialDeriv ρ (fun y => B y σ) x := by
  ext k l
  simp only [partialDeriv, Matrix.of_apply]
  apply line_fderiv_eq
  · exact ((hA.1 σ k l).differentiable (by simp)) x
  · exact ((hB.1 σ k l).differentiable (by simp)) x
  · exact hev.mono fun t ht => by rw [ht]

private lemma line_onBoundary (a b x : R4) (μ ρ : Fin 4) (hρμ : ρ ≠ μ)
    (hx : x ∈ Set.Icc a b) (hxμ : x μ = a μ ∨ x μ = b μ)
    (hρ : a ρ < x ρ ∧ x ρ < b ρ) :
    ∀ᶠ t in nhds (0 : ℝ), OnBoxBoundary a b (x + t • Pi.single ρ 1) := by
  have hmem : Set.Ioo (a ρ - x ρ) (b ρ - x ρ) ∈ nhds (0 : ℝ) :=
    Ioo_mem_nhds (by linarith [hρ.1]) (by linarith [hρ.2])
  filter_upwards [hmem] with t ht
  refine ⟨⟨fun j => ?_, fun j => ?_⟩, μ, ?_⟩
  · by_cases hj : j = ρ
    · subst hj; simp; linarith [ht.1]
    · simp [hj]; exact hx.1 j
  · by_cases hj : j = ρ
    · subst hj; simp; linarith [ht.2]
    · simp [hj]; exact hx.2 j
  · simp [Ne.symm hρμ, hxμ]

private lemma current_eq {n : ℕ} (a b : R4) (A B : Connection n) (hA : IsSUConnection A)
    (hB : IsSUConnection B) (hbdry : ∀ x, OnBoxBoundary a b x → A x = B x)
    (μ : Fin 4) (x : R4) (hx : x ∈ Set.Icc a b) (hxμ : x μ = a μ ∨ x μ = b μ)
    (hint : ∀ ρ, ρ ≠ μ → a ρ < x ρ ∧ x ρ < b ρ) :
    chernSimonsCurrent A μ x = chernSimonsCurrent B μ x := by
  have hAx : A x = B x := hbdry x ⟨hx, μ, hxμ⟩
  unfold chernSimonsCurrent
  refine Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun ρ _ =>
    Finset.sum_congr rfl (fun σ _ => ?_)))
  by_cases hρ : ρ = μ
  · subst hρ; simp [levi_repeat02]
  · rw [hAx, pd_eq A B hA hB x ρ ?_ σ]
    exact (line_onBoundary a b x μ ρ hρ hx hxμ (hint ρ hρ)).mono fun t ht => hbdry _ ht

private lemma face_eq {n : ℕ} (a b : R4) (A B : Connection n) (hA : IsSUConnection A)
    (hB : IsSUConnection B) (hbdry : ∀ x, OnBoxBoundary a b x → A x = B x)
    (μ : Fin 4) (c : ℝ) (hc1 : a μ ≤ c) (hc2 : c ≤ b μ) (hc : c = a μ ∨ c = b μ) :
    ∫ y in Set.Icc (a ∘ μ.succAbove) (b ∘ μ.succAbove),
        chernSimonsCurrent A μ (Fin.insertNth μ c y) =
      ∫ y in Set.Icc (a ∘ μ.succAbove) (b ∘ μ.succAbove),
        chernSimonsCurrent B μ (Fin.insertNth μ c y) := by
  have hae : (Set.univ.pi fun i => Set.Ioo ((a ∘ μ.succAbove) i) ((b ∘ μ.succAbove) i))
      =ᵐ[volume] Set.Icc (a ∘ μ.succAbove) (b ∘ μ.succAbove) := by
    rw [volume_pi]
    exact Measure.univ_pi_Ioo_ae_eq_Icc
  rw [← setIntegral_congr_set hae, ← setIntegral_congr_set hae]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun i => measurableSet_Ioo)
    (fun y hy => ?_)
  have hy' : ∀ i, a (μ.succAbove i) < y i ∧ y i < b (μ.succAbove i) :=
    fun i => hy i (Set.mem_univ _)
  apply current_eq a b A B hA hB hbdry μ
  · refine ⟨fun j => ?_, fun j => ?_⟩
    · rcases Fin.eq_self_or_eq_succAbove μ j with rfl | ⟨i, rfl⟩
      · simpa using hc1
      · simpa using (hy' i).1.le
    · rcases Fin.eq_self_or_eq_succAbove μ j with rfl | ⟨i, rfl⟩
      · simpa using hc2
      · simpa using (hy' i).2.le
  · simpa using hc
  · intro ρ hρ
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hρ
    simpa using hy' i

theorem solution {n : ℕ} (a b : R4) (hab : a ≤ b)
    (A B : Connection n) (hA : IsSUConnection A) (hB : IsSUConnection B)
    (hbdry : ∀ x, OnBoxBoundary a b x → A x = B x) :
    boundaryChernSimons a b A = boundaryChernSimons a b B := by
  unfold boundaryChernSimons
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [face_eq a b A B hA hB hbdry μ (b μ) (hab μ) le_rfl (Or.inr rfl),
    face_eq a b A B hA hB hbdry μ (a μ) le_rfl (hab μ) (Or.inl rfl)]
