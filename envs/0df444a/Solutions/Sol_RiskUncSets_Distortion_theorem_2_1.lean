-- Prove2me | solution 1 for RiskUncSets.Distortion.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:02:51.418064+00:00
-- url     : https://prove2.me/submissions/a246314e-eeaf-4574-8e99-c175998d475c

import Mathlib
import Definitions.Def_RiskUncSets_Distortion_Setting

set_option autoImplicit false

namespace Eba91090

open RiskUncSets.Distortion

/-- Supporting linear functional of a coherent risk measure at a point. -/
theorem support_exists {N : ℕ} (μ : (Fin N → ℝ) → ℝ) (hc : IsCoherent μ)
    (X0 : Fin N → ℝ) :
    ∃ g : (Fin N → ℝ) →ₗ[ℝ] ℝ, g X0 = μ X0 ∧ ∀ x, g x ≤ μ x := by
  obtain ⟨⟨_hmono, _htr⟩, hconv, hhom⟩ := hc
  have μ0 : μ 0 = 0 := by
    have h := hhom 0 0 le_rfl
    simpa using h
  have hpos : ∀ c : ℝ, 0 < c → ∀ x, μ (c • x) = c * μ x := fun c hc x => hhom x c hc.le
  have hadd : ∀ x y, μ (x + y) ≤ μ x + μ y := by
    intro x y
    have h1 : x + y = (2:ℝ) • ((1/2:ℝ) • x + (1 - 1/2:ℝ) • y) := by
      rw [smul_add, smul_smul, smul_smul]; norm_num
    rw [h1, hpos 2 (by norm_num)]
    have := hconv x y (1/2) (by norm_num) (by norm_num)
    linarith
  have H : ∀ c : ℝ, c • X0 = 0 → (RingHom.id ℝ) c • μ X0 = 0 := by
    intro c hc
    rcases smul_eq_zero.mp hc with h | h
    · simp [h]
    · simp [h, μ0]
  let f := LinearPMap.mkSpanSingleton' X0 (μ X0) H
  have hf : ∀ x : f.domain, f x ≤ μ x := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have e : f ⟨c • X0, hx⟩ = c * μ X0 := by
      simp only [f]
      rw [LinearPMap.mkSpanSingleton'_apply]
      simp
    show f ⟨c • X0, hx⟩ ≤ μ (c • X0)
    rw [e]
    rcases lt_trichotomy c 0 with h | h | h
    · have h2 := hadd (c • X0) ((-c) • X0)
      rw [← add_smul, add_neg_cancel, zero_smul, μ0, hpos (-c) (by linarith)] at h2
      linarith
    · subst h; simp [μ0]
    · rw [hpos c h]
  obtain ⟨g, hg1, hg2⟩ := exists_extension_of_le_sublinear f μ hpos hadd hf
  refine ⟨g, ?_, hg2⟩
  have hmem : X0 ∈ f.domain := Submodule.mem_span_singleton_self X0
  have := hg1 ⟨X0, hmem⟩
  rw [this]
  exact LinearPMap.mkSpanSingleton'_apply_self X0 (μ X0) H hmem

theorem forward {N : ℕ} (μ : (Fin N → ℝ) → ℝ) (hc : IsCoherent μ) :
    Generates {q | q ∈ stdSimplex ℝ (Fin N) ∧ ∀ Y : Fin N → ℝ, ∑ i, q i * (-Y i) ≤ μ Y} μ := by
  refine ⟨fun q hq => hq.1, ?_⟩
  intro X
  obtain ⟨g, hgX, hg⟩ := support_exists μ hc X
  obtain ⟨⟨hmono, htr⟩, _, hhom⟩ := hc
  have μ0 : μ 0 = 0 := by
    have h := hhom 0 0 le_rfl
    simpa using h
  set q : Fin N → ℝ := fun i => -g (fun j => if i = j then 1 else 0) with hqdef
  have key : ∀ Y : Fin N → ℝ, ∑ i, q i * (-Y i) = g Y := by
    intro Y
    rw [LinearMap.pi_apply_eq_sum_univ g Y]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hqdef, smul_eq_mul]
    ring
  have hqS : q ∈ stdSimplex ℝ (Fin N) := by
    refine ⟨fun i => ?_, ?_⟩
    · have h1 := hg (fun j => if i = j then 1 else 0)
      have h2 := hmono (fun j => if i = j then (1:ℝ) else 0) 0 (by
        intro j; by_cases h : i = j <;> simp [h])
      simp only [hqdef]
      linarith
    · have h1 := hg (fun _ => (1:ℝ))
      have h2 := hg (fun _ => (-1:ℝ))
      have t1 := htr 0 1
      have t2 := htr 0 (-1)
      simp only [Pi.zero_apply, zero_add, μ0] at t1 t2
      rw [← key] at h1 h2
      simp only [mul_neg, mul_one, Finset.sum_neg_distrib, neg_neg] at h1 h2
      linarith
  have hqQ : q ∈ {q | q ∈ stdSimplex ℝ (Fin N) ∧ ∀ Y : Fin N → ℝ, ∑ i, q i * (-Y i) ≤ μ Y} :=
    ⟨hqS, fun Y => by rw [key]; exact hg Y⟩
  constructor
  · rintro _ ⟨r, hr, rfl⟩
    exact hr.2 X
  · intro b hb
    have := hb ⟨q, hqQ, rfl⟩
    simp only at this
    rw [key, hgX] at this
    exact this

theorem backward {N : ℕ} (μ : (Fin N → ℝ) → ℝ) (Q : Set (Fin N → ℝ)) (hQ : Generates Q μ) :
    IsCoherent μ := by
  obtain ⟨hsub, hlub⟩ := hQ
  have hsum : ∀ q ∈ Q, ∑ i, q i = 1 := fun q hq => (hsub hq).2
  have hnn : ∀ q ∈ Q, ∀ i, 0 ≤ q i := fun q hq => (hsub hq).1
  -- upper bound
  have ub : ∀ X, ∀ q ∈ Q, ∑ i, q i * (-X i) ≤ μ X := fun X q hq =>
    (hlub X).1 ⟨q, hq, rfl⟩
  -- least
  have least : ∀ X b, (∀ q ∈ Q, ∑ i, q i * (-X i) ≤ b) → μ X ≤ b := by
    intro X b h
    apply (hlub X).2
    rintro _ ⟨q, hq, rfl⟩
    exact h q hq
  have hne : Q.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have := least 0 (μ 0 - 1) (by simp [h])
    linarith
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro X Y hXY
    apply least
    intro q hq
    refine le_trans ?_ (ub Y q hq)
    apply Finset.sum_le_sum
    intro i _
    have := hnn q hq i
    have := hXY i
    nlinarith
  · intro X c
    have e : ∀ q ∈ Q, ∑ i, q i * (-(X i + c)) = ∑ i, q i * (-X i) - c := by
      intro q hq
      have : ∑ i, q i * (-(X i + c)) = ∑ i, q i * (-X i) - c * ∑ i, q i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_); ring
      rw [this, hsum q hq]; ring
    apply le_antisymm
    · apply least
      intro q hq
      rw [e q hq]
      linarith [ub X q hq]
    · have : μ X ≤ μ (fun i => X i + c) + c := by
        apply least
        intro q hq
        have := ub (fun i => X i + c) q hq
        rw [e q hq] at this
        linarith
      linarith
  · intro X Y t ht0 ht1
    apply least
    intro q hq
    have e : ∑ i, q i * (-(t • X + (1 - t) • Y) i)
        = t * ∑ i, q i * (-X i) + (1 - t) * ∑ i, q i * (-Y i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    have h1 := ub X q hq
    have h2 := ub Y q hq
    have : 0 ≤ 1 - t := by linarith
    nlinarith
  · intro X t ht
    have e : ∀ q : Fin N → ℝ, ∑ i, q i * (-(t • X) i) = t * ∑ i, q i * (-X i) := by
      intro q
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rcases ht.lt_or_eq with ht | ht
    · apply le_antisymm
      · apply least
        intro q hq
        rw [e q]
        exact mul_le_mul_of_nonneg_left (ub X q hq) ht.le
      · have : μ X ≤ μ (t • X) / t := by
          apply least
          intro q hq
          rw [le_div_iff₀ ht]
          have := ub (t • X) q hq
          rw [e q] at this
          linarith
        rw [le_div_iff₀ ht] at this
        linarith
    · subst ht
      obtain ⟨q, hq⟩ := hne
      have h1 := ub (0 • X) q hq
      have h2 := least (0 • X) 0 (fun r _ => by simp)
      simp only [zero_smul, Pi.zero_apply, neg_zero, mul_zero, Finset.sum_const_zero] at h1 h2
      simp only [zero_smul, zero_mul]
      linarith

end Eba91090

open RiskUncSets.Distortion in
theorem solution {N : ℕ} (hN : 0 < N) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i)
    (hp1 : ∑ i, p i = 1) (μ : (Fin N → ℝ) → ℝ) :
    IsCoherent μ ↔
      ∃ Q : Set (Fin N → ℝ), Generates Q μ ∧ ∀ q ∈ Q, ∀ i, p i = 0 → q i = 0 := by
  constructor
  · intro hc
    refine ⟨_, Eba91090.forward μ hc, ?_⟩
    intro q _ i hpi
    exact absurd hpi (hp i).ne'
  · rintro ⟨Q, hQ, _⟩
    exact Eba91090.backward μ Q hQ
