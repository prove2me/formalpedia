-- Prove2me | solution 1 for OTDRO.StrongCvx.maximizer_first_order
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:31:20.868543+00:00
-- url     : https://prove2.me/submissions/f7385831-b4e1-4792-b370-8694fba9cba3

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

namespace Aux_OTDRO_mfo

lemma tangent (ℓ : ℝ → ℝ) (hc : ConvexOn ℝ Set.univ ℓ) (hd : Differentiable ℝ ℓ) (x y : ℝ) :
    ℓ x + deriv ℓ x * (y - x) ≤ ℓ y := by
  rcases lt_trichotomy x y with h | rfl | h
  · have := hc.le_slope_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ y) h (hd x).hasDerivAt
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith
  · simp
  · have := hc.slope_le_of_hasDerivAt (Set.mem_univ y) (Set.mem_univ x) h (hd x).hasDerivAt
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith

end Aux_OTDRO_mfo

open MeasureTheory Aux_OTDRO_mfo in
theorem solution {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d)))
    (hB : Convex ℝ B) (β : EuclideanSpace ℝ (Fin d))
    (hβB : β ∈ B) (hβ : β ≠ 0) (x : EuclideanSpace ℝ (Fin d))
    (lam : ℝ) (hlam : 0 < lam) (hℓ : Differentiable ℝ ℓ)
    (hne : (OTDRO.Dual.maximizers ℓ A δ β lam x).Nonempty) :
    ∀ γ ∈ OTDRO.Dual.maximizers ℓ A δ β lam x,
      γ = deriv ℓ (inner ℝ β x + Real.sqrt δ * γ * OTDRO.Dual.quadInv A β x) / (2 * lam) ∧
      |deriv ℓ (inner ℝ β x)| / (2 * lam) ≤ |γ| := by
  intro γ hγ
  obtain ⟨u, hu⟩ : ∃ u, u = inner ℝ β x := ⟨_, rfl⟩
  obtain ⟨qv, hq⟩ : ∃ qv, qv = OTDRO.Dual.quadInv A β x := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt δ := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hδ
  have hq0 : 0 < qv := by
    rw [hq]
    unfold OTDRO.Dual.quadInv
    have hb : β.ofLp ≠ 0 := by
      intro h; apply hβ
      exact (WithLp.ofLp_eq_zero 2).mp h
    have := (hA.posDef x).inv.dotProduct_mulVec_pos hb
    simpa using this
  -- F as a function of γ
  have hF : ∀ c, OTDRO.Dual.Fobj ℓ A δ c β lam x = ℓ (u + c * (s * qv)) - lam * s * (c ^ 2 * qv - 1) := by
    intro c
    unfold OTDRO.Dual.Fobj
    rw [← hu, ← hq, ← hs, mul_assoc c]
  have hmax : ∀ c, ℓ (u + c * (s * qv)) - lam * s * (c ^ 2 * qv - 1) ≤
      ℓ (u + γ * (s * qv)) - lam * s * (γ ^ 2 * qv - 1) := by
    intro c; rw [← hF, ← hF]; exact hγ c
  rw [← hu, ← hq, ← hs]
  have harg : u + s * γ * qv = u + γ * (s * qv) := by ring
  rw [harg]
  -- (a) first-order condition
  have hder : HasDerivAt (fun c => ℓ (u + c * (s * qv)) - lam * s * (c ^ 2 * qv - 1))
      (deriv ℓ (u + γ * (s * qv)) * (s * qv) - lam * s * (2 * γ * qv)) γ := by
    have h1 : HasDerivAt (fun c => u + c * (s * qv)) (s * qv) γ := by
      simpa using ((hasDerivAt_id γ).mul_const (s * qv)).const_add u
    have h2 := (hℓ (u + γ * (s * qv))).hasDerivAt.comp γ h1
    have h3 : HasDerivAt (fun c : ℝ => lam * s * (c ^ 2 * qv - 1)) (lam * s * (2 * γ * qv)) γ := by
      have := (((hasDerivAt_pow 2 γ).mul_const qv).sub_const 1).const_mul (lam * s)
      refine this.congr_deriv ?_
      push_cast; ring
    exact h2.sub h3
  have hloc : IsLocalMax (fun c => ℓ (u + c * (s * qv)) - lam * s * (c ^ 2 * qv - 1)) γ :=
    Filter.Eventually.of_forall hmax
  have hzero := hloc.hasDerivAt_eq_zero hder
  have hsq : 0 < s * qv := mul_pos hs0 hq0
  have hfoc : deriv ℓ (u + γ * (s * qv)) = 2 * lam * γ := by
    have : (s * qv) * (deriv ℓ (u + γ * (s * qv)) - 2 * lam * γ) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  refine ⟨?_, ?_⟩
  · rw [hfoc]; field_simp
  · -- (b)
    set c := s * qv with hc
    set D := deriv ℓ u with hD
    have t1 := tangent ℓ h2.convex hℓ (u + γ * c) u
    rw [hfoc] at t1
    -- F(γ) - F(0) ≤ lam c γ²
    have up : ℓ (u + γ * c) - ℓ u ≤ 2 * lam * γ * (γ * c) := by nlinarith
    have hm := hmax (D / (2 * lam))
    have t2 := tangent ℓ h2.convex hℓ u (u + D / (2 * lam) * c)
    rw [← hD] at t2
    have e : D * (u + D / (2 * lam) * c - u) = c * D ^ 2 / (2 * lam) := by
      field_simp <;> ring
    rw [e] at t2
    have e2 : lam * s * ((D / (2 * lam)) ^ 2 * qv - 1) = c * D ^ 2 / (4 * lam) - lam * s := by
      rw [hc]; field_simp; ring
    have e3 : lam * s * (γ ^ 2 * qv - 1) = lam * c * γ ^ 2 - lam * s := by rw [hc]; ring
    rw [e2, e3] at hm
    have key : c * D ^ 2 / (4 * lam) ≤ lam * c * γ ^ 2 := by
      have : c * D ^ 2 / (2 * lam) - c * D ^ 2 / (4 * lam) = c * D ^ 2 / (4 * lam) := by
        field_simp; ring
      nlinarith
    have key2 : D ^ 2 ≤ (2 * lam * γ) ^ 2 := by
      have h4 : c * D ^ 2 ≤ c * (2 * lam * γ) ^ 2 := by
        have := (div_le_iff₀ (by positivity : (0:ℝ) < 4 * lam)).mp key
        nlinarith
      exact le_of_mul_le_mul_left h4 hsq
    have := sq_le_sq.mp key2
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * lam)] at this
    rw [div_le_iff₀ (by positivity)]
    linarith
