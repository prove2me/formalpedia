-- Prove2me | solution 1 for PrimalDualSubgrad.DA.eq_2_5
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:03:46.007272+00:00
-- url     : https://prove2.me/submissions/8744ff0e-9609-470d-b312-73c96eaba32b

import Definitions.Def_PrimalDualSubgrad_DA_ProxSetting
open PrimalDualSubgrad.DA

private theorem growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set E} {d : E → ℝ} {σ : ℝ} (hsc : StrongConvexOn Q σ d)
    {xs x : E} (hs : xs ∈ Q) (hx : x ∈ Q)
    (hm : ∀ y ∈ Q, d xs ≤ d y) :
    d xs + σ / 2 * ‖x - xs‖ ^ 2 ≤ d x := by
  have hb : 0 ≤ d x - d xs := sub_nonneg.mpr (hm x hx)
  by_contra h
  let A := σ / 2 * ‖x - xs‖ ^ 2
  let B := d x - d xs
  have hBA : B < A := by dsimp [A, B]; linarith
  have hB : 0 ≤ B := hb
  have hA : 0 < A := lt_of_le_of_lt hB hBA
  let t := (A - B) / (2 * A)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hteq : t * (2 * A) = A - B := by dsimp [t]; field_simp
  have hc := hsc.2 hs hx (sub_nonneg.mpr ht1) ht.le (by ring : 1 - t + t = 1)
  have hmem := hsc.1 hs hx (sub_nonneg.mpr ht1) ht.le (by ring : 1 - t + t = 1)
  have hmin := hm _ hmem
  simp only [smul_eq_mul, norm_sub_rev xs x] at hc
  have hc' : 0 ≤ t * (B - (1 - t) * A) := by dsimp [A, B]; nlinarith [hc]
  have hb' : (1 - t) * A ≤ B := by nlinarith
  nlinarith

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (β : ℝ) (hβ : 0 < β) (s δ : StrongDual ℝ E) :
    V P β (s + δ) ≤ V P β s + δ (π β s - P.x0) + 1 / (2 * P.σ * β) * ‖δ‖ ^ 2 := by
  let y := π β s
  have hy := (hπ β hβ s).1
  have hm := (hπ β hβ s).2
  have hsc : StrongConvexOn P.Q (β * P.σ) (fun x => -(s x) + β * P.d x) := by
    refine ⟨P.convex_Q, ?_⟩
    intro x hx z hz a b ha hb hab
    have hc := mul_le_mul_of_nonneg_left (P.strongConvexOn_d.2 hx hz ha hb hab) hβ.le
    simp only [map_add, map_smul, smul_eq_mul] at *
    nlinarith
  have hmax (r : StrongDual ℝ E) : V P β r = r (π β r - P.x0) - β * P.d (π β r) := by
    have hr := hπ β hβ r
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    · exact ⟨_, ⟨π β r, hr.1, rfl⟩⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hh := hr.2 x hx
      simp only [map_sub] at *
      linarith
    · intro a ha
      exact ⟨_, ⟨π β r, hr.1, rfl⟩, ha⟩
  rw [hmax (s + δ), hmax s]
  let z := π β (s + δ)
  have hz := (hπ β hβ (s + δ)).1
  have hg := growth hsc hy hz hm
  have hd : δ (z - y) ≤ ‖δ‖ * ‖z - y‖ :=
    (le_abs_self _).trans (δ.le_opNorm _)
  have hk : 0 < β * P.σ := mul_pos hβ P.σ_pos
  have hs := mul_nonneg hk.le (sq_nonneg (‖z - y‖ - ‖δ‖ / (β * P.σ)))
  have heq : β * P.σ * (‖z - y‖ - ‖δ‖ / (β * P.σ)) ^ 2 =
      β * P.σ * ‖z - y‖ ^ 2 - 2 * ‖δ‖ * ‖z - y‖ + ‖δ‖ ^ 2 / (β * P.σ) := by
    field_simp [P.σ_pos.ne', hβ.ne']
    <;> ring
  rw [heq] at hs
  have hcoef : 1 / (2 * P.σ * β) * ‖δ‖ ^ 2 = ‖δ‖ ^ 2 / (β * P.σ) / 2 := by
    field_simp [P.σ_pos.ne', hβ.ne']
    <;> ring
  rw [hcoef]
  simp only [ContinuousLinearMap.add_apply, map_sub] at *
  dsimp [y, z] at *
  nlinarith

#print axioms solution
