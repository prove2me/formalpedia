-- Prove2me | solution 1 for RamanujanPetersson.exists_gamma1_cuspForm_qExpansion_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T01:46:22.23749+00:00
-- url     : https://prove2.me/submissions/84cc8e42-2512-4a69-a578-7c1e7c7eafca

import Mathlib

open UpperHalfPlane Filter Asymptotics MatrixGroups ModularForm

set_option autoImplicit false

namespace RamanujanPetersson.N1Aux

open Matrix CongruenceSubgroup ConjAct
open scoped Pointwise

/-- `diag(h, 1)` as an element of `GL(2, ℝ)`. -/
noncomputable def dg (h : ℝ) (hh : h ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![h, 0; 0, 1] (by simpa [Matrix.det_fin_two_of] using hh)

lemma dg_val (h : ℝ) (hh : h ≠ 0) :
    ((dg h hh : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![h, 0; 0, 1] := rfl

lemma dg_det (h : ℝ) (hh : h ≠ 0) : (dg h hh).det.val = h := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, dg_val, Matrix.det_fin_two_of]
  ring

lemma dg_smul (h : ℝ) (hh : 0 < h) (τ : ℍ) :
    ((dg h hh.ne' • τ : ℍ) : ℂ) = (h : ℂ) * τ := by
  rw [coe_smul_of_det_pos (by rw [dg_det]; exact hh)]
  simp [num, denom, dg_val]

lemma dg_slash (h : ℝ) (hh : 0 < h) (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) :
    (F ∣[k] dg h hh.ne') τ = (h : ℂ) ^ (k - 1) * F (dg h hh.ne' • τ) := by
  rw [slash_apply]
  have hden : denom (dg h hh.ne') τ = 1 := by simp [denom, dg_val]
  have hdet : 0 < (dg h hh.ne').det.val := by rw [dg_det]; exact hh
  rw [hden, σ, if_pos hdet, ContinuousAlgEquiv.refl_apply, dg_det, abs_of_pos hh]
  simp only [_root_.one_zpow, mul_one]
  ring

lemma zmod_eq_one_iff (n : ℕ) (a : ℤ) : (a : ZMod n) = 1 ↔ (n : ℤ) ∣ a - 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_one, sub_eq_zero]

end RamanujanPetersson.N1Aux

open RamanujanPetersson.N1Aux CongruenceSubgroup ConjAct
open scoped Pointwise

theorem solution (Γ : Subgroup SL(2, ℤ))
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) (k : ℤ)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ M : ℕ, 0 < M ∧ ∃ g : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)) k,
      ∀ n : ℕ, (qExpansion (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty f).coeff n =
        (qExpansion 1 g).coeff n := by
  have : Γ.FiniteIndex := hΓ.finiteIndex
  set h := (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty with hdef
  have hpos : 0 < h := Subgroup.strictWidthInfty_pos _
  have hmemP : h ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
    Subgroup.strictWidthInfty_mem_strictPeriods _
  have hmem := hmemP
  rw [Subgroup.mem_strictPeriods_iff] at hmem
  obtain ⟨u, huΓ, hu⟩ := Subgroup.mem_map.mp hmem
  have hu' : ∀ i j, ((u i j : ℤ) : ℝ) = (!![1, h; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    intro i j
    have := congr_arg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) hu
    simpa using this
  set H : ℤ := u 0 1 with hHdef
  have hH : (H : ℝ) = h := by simpa using hu' 0 1
  have u00 : u 0 0 = 1 := by exact_mod_cast (by simpa using hu' 0 0 : ((u 0 0 : ℤ) : ℝ) = 1)
  have u10 : u 1 0 = 0 := by exact_mod_cast (by simpa using hu' 1 0 : ((u 1 0 : ℤ) : ℝ) = 0)
  have u11 : u 1 1 = 1 := by exact_mod_cast (by simpa using hu' 1 1 : ((u 1 1 : ℤ) : ℝ) = 1)
  have huT : u = ModularGroup.T ^ H := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, u00, u10, u11, hHdef]
  have Hpos : 0 < H := by
    have : (0 : ℝ) < H := hH ▸ hpos
    exact_mod_cast this
  obtain ⟨N, hN0, hNΓ⟩ := hΓ
  set M : ℕ := N * H.toNat with hMdef
  have hMZ : (M : ℤ) = (N : ℤ) * H := by
    rw [hMdef]; push_cast; rw [Int.toNat_of_nonneg Hpos.le]
  have hMpos : 0 < M := by
    rw [hMdef]; exact Nat.mul_pos (Nat.pos_of_ne_zero hN0) (by omega)
  -- the conjugate `dg * x * dg⁻¹` of `x ∈ Γ₁(M)` lies in `Γ`
  have hconj : ∀ x ∈ Gamma1 M, ∃ y ∈ Γ,
      Matrix.SpecialLinearGroup.mapGL ℝ y = dg h hpos.ne' * Matrix.SpecialLinearGroup.mapGL ℝ x *
        (dg h hpos.ne')⁻¹ := by
    intro x hx
    rw [Gamma1_mem] at hx
    obtain ⟨hx00, hx11, hx10⟩ := hx
    rw [zmod_eq_one_iff, hMZ] at hx00 hx11
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hMZ] at hx10
    obtain ⟨c', hc'⟩ : H ∣ x 1 0 := (Dvd.intro_left _ rfl).trans hx10
    have hdet : x 0 0 * x 1 1 - x 0 1 * x 1 0 = 1 := by
      have := x.det_coe
      rwa [Matrix.det_fin_two] at this
    let y : SL(2, ℤ) := ⟨!![x 0 0, H * x 0 1; c', x 1 1], by
      rw [Matrix.det_fin_two_of]
      rw [hc'] at hdet
      linear_combination hdet⟩
    have hy00 : y 0 0 = x 0 0 := rfl
    have hy01 : y 0 1 = H * x 0 1 := rfl
    have hy10 : y 1 0 = c' := rfl
    have hy11 : y 1 1 = x 1 1 := rfl
    refine ⟨y, ?_, ?_⟩
    · have hTmem : ModularGroup.T ^ (H * x 0 1) ∈ Γ := by
        rw [zpow_mul, ← huT]
        exact zpow_mem huΓ _
      have hz : (ModularGroup.T ^ (H * x 0 1))⁻¹ * y ∈ Gamma N := by
        rw [Gamma_mem]
        rw [← zpow_neg]
        simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
          Fin.sum_univ_two, hy00, hy01, hy10, hy11]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [zmod_eq_one_iff]
          obtain ⟨t, ht⟩ := hx00
          obtain ⟨s, hs⟩ := hx10
          refine ⟨t * H - x 0 1 * s * H, ?_⟩
          have hc2 : H * c' = N * H * s := by rw [← hc', hs]
          have hc3 : c' = N * s := by
            have := mul_left_cancel₀ Hpos.ne' (by rw [hc2]; ring : H * c' = H * (N * s))
            exact this
          rw [hc3]
          linear_combination ht
        · rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          obtain ⟨t, ht⟩ := hx11
          exact ⟨-(H * x 0 1 * t * H), by linear_combination (-(H * x 0 1)) * ht⟩
        · rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          obtain ⟨s, hs⟩ := hx10
          have hc2 : H * c' = N * H * s := by rw [← hc', hs]
          have hc3 : c' = N * s := by
            have := mul_left_cancel₀ Hpos.ne' (by rw [hc2]; ring : H * c' = H * (N * s))
            exact this
          exact ⟨s, by rw [hc3]; ring⟩
        · rw [zmod_eq_one_iff]
          obtain ⟨t, ht⟩ := hx11
          exact ⟨t * H, by linear_combination ht⟩
      have := mul_mem hTmem (hNΓ hz)
      simpa using this
    · rw [eq_mul_inv_iff_mul_eq]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix, dg_val, Matrix.mul_apply,
          Fin.sum_univ_two, hy00, hy01, hy10, hy11, ← hH, hc']
      all_goals ring
  have hle : ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      toConjAct (dg h hpos.ne')⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
    obtain ⟨y, hyΓ, hy⟩ := hconj x hx
    exact ⟨y, hyΓ, hy⟩
  let F2 : CuspForm (toConjAct (dg h hpos.ne')⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))) k :=
    (h ^ (1 - k) : ℝ) • CuspForm.translate f (dg h hpos.ne')
  let g : CuspForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
    { toFun := F2
      slash_action_eq' := fun γ hγ => SlashInvariantFormClass.slash_action_eq F2 γ (hle hγ)
      holo' := CuspFormClass.holo F2
      zero_at_cusps' := fun hc => CuspFormClass.zero_at_cusps F2 (hc.mono hle) }
  have hg : ∀ τ : ℍ, g τ = f (dg h hpos.ne' • τ) := by
    intro τ
    change ((h ^ (1 - k) : ℝ) • (⇑f ∣[k] dg h hpos.ne')) τ = _
    rw [Pi.smul_apply, dg_slash h hpos, Complex.real_smul]
    have hh0 : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    push_cast
    rw [← mul_assoc, ← zpow_add₀ hh0]
    simp
  have h1 : (1 : ℝ) ∈ ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples 1
  refine ⟨M, hMpos, g, fun n => ?_⟩
  refine ModularFormClass.qExpansion_coeff_unique (c := fun m => (qExpansion h f).coeff m)
    one_pos h1 (f := g) (fun τ => ?_) n
  have hq : Function.Periodic.qParam h ((dg h hpos.ne' • τ : ℍ) : ℂ) =
      Function.Periodic.qParam 1 (τ : ℂ) := by
    rw [dg_smul h hpos]
    unfold Function.Periodic.qParam
    congr 1
    have hh0 : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    field_simp
    push_cast
    ring
  have := ModularForm.hasSum_qExpansion (f := f) hpos hmemP (dg h hpos.ne' • τ)
  rw [hq, ← hg] at this
  simpa [smul_eq_mul] using this
