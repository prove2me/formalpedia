-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P06.weightVectorIntertwiners
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:24:10.87253+00:00
-- url     : https://prove2.me/submissions/08c3a682-3ae1-49e0-9094-9496149477ba

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P06
noncomputable section

open QAlgorithms.Papers.Independent.Support21.P06

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P26 (Adjacent nextPosition)

attribute [local instance] Classical.propDecidable



/-- Weight-vector assertions (3.7a–b), PDF p.10.
Printed: t_i-t_(i+1) in (3.7a). Changed: t_(i+1)-t_i.
Why: the definition on p.8, Proposition 3.2, and the two-box row T_i=q
all require this sign. The membership assertion includes zero; nonvanishing
requires the input vector to be nonzero, as used on p.16.
This correction awaits independent moderation. -/
theorem solution
    (n : ℕ) (hn : 0 < n) (q : ℂ) (hq : GenericParameter q)
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    (A : AffineAction n q V) (t : Fin n → ℂ) (ht : TorusWeight t)
    (i : Adjacent n) (hi : t i.val ≠ t (nextPosition i))
    (m : V) (hm : InWeightSpace A t m) :
    tauWeight A t i m = A.t i m -
      ((q - q⁻¹) * t (nextPosition i) / (t (nextPosition i) - t i.val)) • m ∧
    InWeightSpace A (permuteWeight (simplePerm i) t) (tauWeight A t i m) ∧
    tauWeight A (permuteWeight (simplePerm i) t) i (tauWeight A t i m) =
      tauSquareScalar q t i • m ∧
    (m ≠ 0 → t i.val ≠ q ^ 2 * t (nextPosition i) →
      t i.val ≠ (q⁻¹) ^ 2 * t (nextPosition i) → tauWeight A t i m ≠ 0) := by
  have hq0 : q ≠ 0 := hq.1
  set a : Fin n := i.val with ha
  set b : Fin n := nextPosition i with hb
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [ha, hb, nextPosition] at this
  have hd : t b - t a ≠ 0 := sub_ne_zero.2 (Ne.symm hi)
  set c : ℂ := (q - q⁻¹) * t b / (t b - t a) with hc
  have hc' : c * (t b - t a) = (q - q⁻¹) * t b := by
    rw [hc]; field_simp
  have hτ : ∀ v, tauWeight A t i v = A.t i v - c • v := by
    intro v; simp [tauWeight, hc, ha, hb]
  have hconj : ∀ v, A.t i (A.x a (A.t i v)) = A.x b v := by
    intro v
    have := congrArg (fun f : Module.End ℂ V => f v) (A.conjugation i)
    simpa [Module.End.mul_apply, ha, hb] using this
  have hquad : ∀ v, A.t i (A.t i v) = (q - q⁻¹) • A.t i v + v := by
    intro v
    have := congrArg (fun f : Module.End ℂ V => f v) (A.quadratic i)
    simpa [Module.End.mul_apply] using this
  have hXbT : ∀ v, A.x b (A.t i v) = A.t i (A.x a v) + (q - q⁻¹) • A.x b v := by
    intro v
    rw [← hconj (A.t i v), hquad, map_add, map_smul, map_add, map_smul, hconj]
    abel
  have hXaT : ∀ v, A.x a (A.t i v) = A.t i (A.x b v) - (q - q⁻¹) • A.x b v := by
    intro v
    rw [← hconj v, hquad, hconj]
    abel
  have hma : A.x a m = t a • m := hm a
  have hmb : A.x b m = t b • m := hm b
  have hsw : ∀ j, permuteWeight (simplePerm i) t j = t (Equiv.swap a b j) := by
    intro j; simp [permuteWeight, simplePerm, ha, hb, Equiv.swap_inv]
  -- the scalar c' at the swapped weight
  have hs_a : permuteWeight (simplePerm i) t a = t b := by rw [hsw, Equiv.swap_apply_left]
  have hs_b : permuteWeight (simplePerm i) t b = t a := by rw [hsw, Equiv.swap_apply_right]
  have hW : InWeightSpace A (permuteWeight (simplePerm i) t) (tauWeight A t i m) := by
    intro j
    rw [hτ, hsw]
    by_cases hja : j = a
    · subst hja
      rw [Equiv.swap_apply_left, map_sub, map_smul, hXaT, hmb, hma, map_smul]
      linear_combination (norm := module) hc' • m
    · by_cases hjb : j = b
      · subst hjb
        rw [Equiv.swap_apply_right, map_sub, map_smul, hXbT, hma, hmb, map_smul]
        linear_combination (norm := module) (-hc') • m
      · rw [Equiv.swap_apply_of_ne_of_ne hja hjb, map_sub, map_smul]
        have hmix := congrArg (fun f : Module.End ℂ V => f m)
          (A.mixed i j (by simpa [ha] using hja) (by simpa [hb] using hjb))
        simp only [Module.End.mul_apply] at hmix
        rw [hmix, hm j, map_smul, smul_sub, smul_comm]
  have hda : t a - t b ≠ 0 := sub_ne_zero.2 hi
  set c' : ℂ := (q - q⁻¹) * t a / (t a - t b) with hc'def
  have hτ' : ∀ v, tauWeight A (permuteWeight (simplePerm i) t) i v = A.t i v - c' • v := by
    intro v
    have e1 : permuteWeight (simplePerm i) t (nextPosition i) = t a := by rw [← hb, hs_b]
    have e2 : permuteWeight (simplePerm i) t i.val = t b := by rw [← ha, hs_a]
    simp only [tauWeight, e1, e2, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hc'def]
  have hcc : c + c' = q - q⁻¹ := by
    rw [hc, hc'def]
    have : t a - t b = -(t b - t a) := by ring
    rw [this]
    field_simp
    ring
  have hsc : 1 + c * c' = tauSquareScalar q t i := by
    rw [hc, hc'def, tauSquareScalar, ← ha, ← hb]
    field_simp
    ring
  have h3 : tauWeight A (permuteWeight (simplePerm i) t) i (tauWeight A t i m) =
      tauSquareScalar q t i • m := by
    rw [hτ', hτ, map_sub, map_smul, hquad]
    linear_combination (norm := module) (-hcc) • A.t i m + hsc • m
  refine ⟨?_, hW, h3, ?_⟩
  · rw [hτ]
  · intro hm0 h1 h2 h0
    have hS : tauSquareScalar q t i ≠ 0 := by
      rw [tauSquareScalar, ← ha, ← hb]
      have n1 : q * t b - q⁻¹ * t a ≠ 0 := by
        intro h; apply h1
        have : t a = q ^ 2 * t b := by
          field_simp at h
          linear_combination -h
        exact this
      have n2 : q * t a - q⁻¹ * t b ≠ 0 := by
        intro h; apply h2
        field_simp at h ⊢
        linear_combination h
      exact div_ne_zero (mul_ne_zero n1 n2) (mul_ne_zero hd hda)
    have := h3
    rw [h0, map_zero] at this
    exact hm0 ((smul_eq_zero.1 this.symm).resolve_left hS)


end
