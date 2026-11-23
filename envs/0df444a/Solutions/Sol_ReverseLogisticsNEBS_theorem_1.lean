-- Prove2me | solution 1 for ReverseLogisticsNEBS.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:32:38.432628+00:00
-- url     : https://prove2.me/submissions/347011f2-2a80-467e-8478-a26174128eab

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_Inst

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ReverseLogisticsNEBS

namespace ReverseLogisticsNEBS.Thm1Proof

theorem prop1_core {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model N Ω) (hM : M.Standing) (t : ℕ)
    (G : Ω → (Fin N → ℝ) → ℝ) (ω : Ω) (x : Fin N → ℝ)
    (a : Inst N) (ha : Inst.Feas true x a) :
    Inst.Feas true x a.semiReduce ∧
    (∀ d, Inst.next x a.semiReduce d = Inst.next x a d) ∧
    ((∃ j, 0 < a.XE j ∧ 0 < a.XR j ∧ 0 < M.cE j) →
      M.instObj t G ω x a.semiReduce < M.instObj t G ω x a) := by
  obtain ⟨hXE0, hXR0, hX0, hc1, hc2, hc3, hc4⟩ := ha
  have hmax1 : ∀ p q : ℝ, max (p - q) 0 = p - min p q := by
    intro p q
    rcases le_total p q with h | h
    · rw [max_eq_right (by linarith), min_eq_left h]; ring
    · rw [max_eq_left (by linarith), min_eq_right h]
  have hmax2 : ∀ p q : ℝ, max (q - p) 0 = q - min p q := by
    intro p q
    rcases le_total p q with h | h
    · rw [max_eq_left (by linarith), min_eq_left h]
    · rw [max_eq_right (by linarith), min_eq_right h]; ring
  have hE : ∀ j, a.semiReduce.XE j = a.XE j - min (a.XE j) (a.XR j) := fun j => hmax1 _ _
  have hR : ∀ j, a.semiReduce.XR j = a.XR j - min (a.XE j) (a.XR j) := fun j => hmax2 _ _
  have hXs : a.semiReduce.X = a.X := rfl
  have hmin0 : ∀ j, 0 ≤ min (a.XE j) (a.XR j) := fun j => le_min (hXE0 j) (hXR0 j)
  have hminR : ∀ j, min (a.XE j) (a.XR j) ≤ a.XR j := fun j => min_le_right _ _
  have hnext : ∀ d, Inst.next x a.semiReduce d = Inst.next x a d := by
    intro d
    funext j
    simp only [Inst.next, Inst.below, hE, hR, hXs]
    split_ifs <;> ring
  have hcE : ∀ j, 0 ≤ M.cE j := by
    intro j
    simp only [Model.cE]
    have h1 := hM.k_pos j
    have h2 := hM.k_le_kE j
    by_cases hj : j.val + 1 < N
    · have := hM.kR_pos j hj; linarith
    · have := hM.k_top j (by omega); linarith
  have hgam : firstLoc x + firstLoc a.semiReduce.XE - firstLoc a.semiReduce.XR =
      firstLoc x + firstLoc a.XE - firstLoc a.XR := by
    unfold firstLoc
    split_ifs
    · rw [hE, hR]; ring
    · ring
  have hint : (∫ z, G z.2 (Inst.next x a.semiReduce z.1) ∂(M.κ t ω)) =
      ∫ z, G z.2 (Inst.next x a z.1) ∂(M.κ t ω) := by
    simp only [hnext]
  have hterm : ∀ j, (M.kE j + M.h j) * a.semiReduce.XE j + (M.kR j - M.h j) * a.semiReduce.XR j +
      M.k j * a.semiReduce.X j + M.H j * x j =
      ((M.kE j + M.h j) * a.XE j + (M.kR j - M.h j) * a.XR j + M.k j * a.X j + M.H j * x j) -
        M.cE j * min (a.XE j) (a.XR j) := by
    intro j
    rw [hE j, hR j, hXs]
    simp only [Model.cE]
    ring
  have hobj : M.instObj t G ω x a.semiReduce =
      M.instObj t G ω x a - ∑ j, M.cE j * min (a.XE j) (a.XR j) := by
    unfold Model.instObj
    rw [hgam, hint, Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib]
    ring
  refine ⟨⟨fun j => le_max_right _ _, fun j => le_max_right _ _, hX0, ?_, ?_, ?_, ?_⟩, hnext, ?_⟩
  · intro i j hij
    rw [hE, hE]
    have := hc3 i j hij
    linarith [hminR i, hmin0 j]
  · intro j hj
    have h2 := hc2 j hj
    rw [hR, hE]
    rcases le_total (a.XE j) (a.XR j) with h | h
    · rw [min_eq_left h, sub_self, add_zero]
      rcases le_total 0 (x j + a.XE j) with h' | h'
      · rw [max_eq_left h'] at h2
        exact le_max_of_le_left (by linarith)
      · rw [max_eq_right h'] at h2
        exact le_max_of_le_right (by linarith [hXE0 j])
    · rw [min_eq_right h, sub_self]
      exact le_max_right _ _
  · intro i j hij
    rw [hR, hE, hE]
    have := hc3 i j hij
    linarith [hmin0 j]
  · intro i j hij
    have h4 := hc4 i j hij
    rw [hR i, hE i, hE j, hXs]
    simp only [if_true] at h4 ⊢
    rw [hR j]
    linarith
  · rintro ⟨j, h1, h2, h3⟩
    rw [hobj]
    have := Finset.sum_pos' (fun j (_ : j ∈ Finset.univ) => mul_nonneg (hcE j) (hmin0 j))
      ⟨j, Finset.mem_univ _, mul_pos h3 (lt_min h1 h2)⟩
    linarith

theorem gamma_anti {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model N Ω) (hM : M.Standing) (t : ℕ) (ω : Ω)
    {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    M.gamma t ω y₂ ≤ M.gamma t ω y₁ := by
  haveI : IsMarkovKernel (M.κ t) := hM.markov t
  have hint : ∀ y : ℝ, Integrable (fun z : ℝ × Ω => max (z.1 - y) 0) (M.κ t ω) := by
    intro y
    have hsub : Integrable (fun z : ℝ × Ω => z.1 - y) (M.κ t ω) :=
      (hM.demand_integrable t ω).sub (integrable_const y)
    have heq : (fun z : ℝ × Ω => max (z.1 - y) 0) =
        fun z => (z.1 - y + |z.1 - y|) / 2 := by
      ext z
      rcases le_total (z.1 - y) 0 with h | h
      · rw [max_eq_right h, abs_of_nonpos h]; ring
      · rw [max_eq_left h, abs_of_nonneg h]; ring
    rw [heq]
    exact (hsub.add hsub.abs).div_const 2
  have hmono : ∫ z, max (z.1 - y₂) 0 ∂(M.κ t ω) ≤ ∫ z, max (z.1 - y₁) 0 ∂(M.κ t ω) :=
    integral_mono (hint y₂) (hint y₁) (fun z => max_le_max_right 0 (by linarith))
  have hH0 : 0 ≤ M.Hext 0 := by
    unfold Model.Hext
    split_ifs with hN
    · exact hM.H_nonneg _
    · exact le_rfl
  unfold Model.gamma
  linarith [mul_le_mul_of_nonneg_left hmono (add_nonneg hM.p_nonneg hH0)]

end ReverseLogisticsNEBS.Thm1Proof

open ReverseLogisticsNEBS.Thm1Proof in
theorem solution {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (M : Model N Ω) (hM : M.Standing) (t : ℕ)
    (G : Ω → (Fin N → ℝ) → ℝ) (ω : Ω) (x : Fin N → ℝ) (hx : ∀ j : Fin N, 0 < j.val → 0 ≤ x j)
    (a : Inst N) (ha : M.IsOptimalInst t G ω x a) :
    ∀ j, 0 < M.cE j → 0 < M.cR j → (a.XE j = 0 ∧ a.X j = 0) ∨ a.XR j = 0 := by
  obtain ⟨hfeas, hint, hopt⟩ := ha
  obtain ⟨hXE0, hXR0, hX0, hc1, hc2, hc3, hc4⟩ := hfeas
  intro j hcEj hcRj
  by_cases hXRj : a.XR j = 0
  · exact Or.inr hXRj
  · left
    have hXRpos : 0 < a.XR j := lt_of_le_of_ne (hXR0 j) (Ne.symm hXRj)
    have hXEj : a.XE j = 0 := by
      by_contra hXEj
      have hXEpos : 0 < a.XE j := lt_of_le_of_ne (hXE0 j) (Ne.symm hXEj)
      obtain ⟨hfeas_s, hnext_s, hlt_s⟩ := prop1_core M hM t G ω x a
        ⟨hXE0, hXR0, hX0, hc1, hc2, hc3, hc4⟩
      have hint_s : M.InstContIntegrable t G ω x a.semiReduce := by
        unfold Model.InstContIntegrable at hint ⊢
        simp only [hnext_s]
        exact hint
      have hle := hopt a.semiReduce hfeas_s hint_s
      have hlt := hlt_s ⟨j, hXEpos, hXRpos, hcEj⟩
      linarith
    refine ⟨hXEj, ?_⟩
    by_contra hXj
    have hXpos : 0 < a.X j := lt_of_le_of_ne (hX0 j) (Ne.symm hXj)
    set δ := min (a.XR j) (a.X j) with hδdef
    have hδpos : 0 < δ := lt_min hXRpos hXpos
    let a' : Inst N := {
      XE := a.XE
      XR := Function.update a.XR j (a.XR j - δ)
      X := Function.update a.X j (a.X j - δ)
    }
    have hXRle : ∀ k, a'.XR k ≤ a.XR k := by
      intro k
      by_cases hk : k = j
      · subst hk; simp [a']; linarith
      · simp [a', hk]
    have hdiff_eq : ∀ k, a'.X k - a'.XR k = a.X k - a.XR k := by
      intro k
      by_cases hk : k = j
      · subst hk; simp only [a', Function.update_self]; ring
      · simp [a', hk]
    have hbelow_eq : ∀ k, Inst.below a'.XR k - Inst.below a'.X k =
        Inst.below a.XR k - Inst.below a.X k := by
      intro k
      unfold Inst.below
      split_ifs with hk0
      · linarith [hdiff_eq ⟨k.val - 1, by omega⟩]
      · ring
    have hnext' : ∀ d, Inst.next x a' d = Inst.next x a d := by
      intro d
      funext k
      unfold Inst.next
      have e1 := hdiff_eq k
      have e2 := hbelow_eq k
      have e3 : a'.XE k = a.XE k := rfl
      have e4 : Inst.below a'.XE k = Inst.below a.XE k := rfl
      linarith
    have hfeas' : Inst.Feas true x a' := by
      refine ⟨hXE0, ?_, ?_, hc1, ?_, ?_, ?_⟩
      · intro k
        by_cases hk : k = j
        · subst hk; simp [a', δ]
        · simp [a', hk, hXR0 k]
      · intro k
        by_cases hk : k = j
        · subst hk; simp [a', δ]
        · simp [a', hk, hX0 k]
      · intro k hk
        exact (hXRle k).trans (hc2 k hk)
      · intro i k hik
        exact (hXRle i).trans (hc3 i k hik)
      · intro i k hik
        have h4 := hc4 i k hik
        simp only [if_true] at h4 ⊢
        have := hdiff_eq k
        have := hXRle i
        simp only [a'] at *
        linarith
    have hint' : M.InstContIntegrable t G ω x a' := by
      unfold Model.InstContIntegrable at hint ⊢
      simp only [hnext']
      exact hint
    have hfirst : firstLoc x + firstLoc a.XE - firstLoc a.XR ≤
        firstLoc x + firstLoc a'.XE - firstLoc a'.XR := by
      unfold firstLoc
      split_ifs with hN
      · have := hXRle ⟨0, hN⟩
        simp only [a'] at this ⊢
        linarith
      · linarith
    have hgam' : M.gamma t ω (firstLoc x + firstLoc a'.XE - firstLoc a'.XR) ≤
        M.gamma t ω (firstLoc x + firstLoc a.XE - firstLoc a.XR) :=
      gamma_anti M hM t ω hfirst
    have hsum' : ∑ k, ((M.kE k + M.h k) * a.XE k + (M.kR k - M.h k) * a.XR k +
          M.k k * a.X k + M.H k * x k) -
        ∑ k, ((M.kE k + M.h k) * a'.XE k + (M.kR k - M.h k) * a'.XR k +
          M.k k * a'.X k + M.H k * x k) = M.cR j * δ := by
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
      · simp only [a', Function.update_self, Model.cR]
        ring
      · intro k _ hkj
        simp [a', hkj]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hint_eq : (∫ z, G z.2 (Inst.next x a' z.1) ∂(M.κ t ω)) =
        ∫ z, G z.2 (Inst.next x a z.1) ∂(M.κ t ω) := by
      simp only [hnext']
    have hlt' : M.instObj t G ω x a' < M.instObj t G ω x a := by
      unfold Model.instObj
      rw [hint_eq]
      have hcRδ : 0 < M.cR j * δ := mul_pos hcRj hδpos
      linarith
    have hle' := hopt a' hfeas' hint'
    linarith
