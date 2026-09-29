-- Prove2me | solution 1 for UpperHalfPlane.natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/f5f64642-0c6b-5ae6-a94f-fe7ca34653f2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq

set_option autoImplicit false

noncomputable section

p2m_open "UpperHalfPlane P2MW.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq.UpperHalfPlane Filter"
open scoped MatrixGroups Topology

namespace UpperHalfPlane
p2m_export "UpperHalfPlane" "continuous_im ofComplex_apply_of_im_pos denom_ne_zero denom denom_ne_zero_of_im denom_cocycle coe_re J ofComplex_apply im_pos coe_smul_of_det_pos im num coe_specialLinearGroup_apply im_ne_zero ofComplex coe_im"
namespace StabilizerDvdTwoMulOrder
p2m_open "UpperHalfPlane"

theorem coe_mul_GL (γ δ : SL(2, ℤ)) :
    ((γ * δ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) * δ := by
  simp only [map_mul]

theorem denom_mul_of_smul_eq (γ δ : SL(2, ℤ)) (τ : ℍ) (hδ : δ • τ = τ) :
    denom ((γ * δ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = denom γ τ * denom δ τ := by
  have h := denom_cocycle (γ : GL (Fin 2) ℝ) (δ : GL (Fin 2) ℝ) τ.im_ne_zero
  have h2 : ((δ • τ : ℍ) : ℂ) = num (δ : GL (Fin 2) ℝ) τ / denom (δ : GL (Fin 2) ℝ) τ := by
    rw [ModularGroup.sl_moeb, coe_smul_of_det_pos (by simp)]
  rw [← h2, hδ] at h
  rw [coe_mul_GL]
  exact h

theorem bottom_row_eq {c d c' d' : ℤ} (τ : ℍ)
    (h : (c : ℂ) * τ + d = (c' : ℂ) * τ + d') : c = c' ∧ d = d' := by
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    zero_mul, add_zero, UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at him
  have hc : (c : ℝ) = c' := mul_right_cancel₀ τ.im_pos.ne' him
  have hc' : c = c' := by exact_mod_cast hc
  subst hc'
  refine ⟨rfl, ?_⟩
  have := add_left_cancel h
  exact_mod_cast this

def chi (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) : MulAction.stabilizer Γ τ →* ℂ where
  toFun γ := denom (((γ : Γ) : SL(2, ℤ)) : GL (Fin 2) ℝ) τ
  map_one' := by simp
  map_mul' γ δ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, denom_mul_of_smul_eq _ _ _ δ.2]

theorem chi_apply (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) (γ : MulAction.stabilizer Γ τ) :
    chi Γ τ γ = denom (((γ : Γ) : SL(2, ℤ)) : GL (Fin 2) ℝ) τ := rfl

theorem eq_one_of_denom_eq_one (τ : ℍ) (γ : SL(2, ℤ)) (hγ : γ • τ = τ)
    (h1 : denom (γ : GL (Fin 2) ℝ) τ = 1) : γ = 1 := by
  have hrow : (γ 1 0 : ℤ) = 0 ∧ (γ 1 1 : ℤ) = 1 := by
    have := bottom_row_eq (c := γ 1 0) (d := γ 1 1) (c' := 0) (d' := 1) τ
      (by rw [ModularGroup.denom_apply] at h1; push_cast; simpa using h1)
    exact this
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two, hrow.1, hrow.2] at hdet
  simp only [mul_one, mul_zero, sub_zero] at hdet
  have hfix := congrArg (fun z : ℍ => (z : ℂ)) hγ
  simp only [coe_specialLinearGroup_apply] at hfix
  rw [hrow.1, hrow.2, hdet] at hfix
  simp only [eq_intCast, Int.cast_zero, Complex.ofReal_zero, zero_mul, Int.cast_one,
    Complex.ofReal_one, zero_add, div_one, one_mul] at hfix
  have h01 : ((γ 0 1 : ℤ) : ℂ) = 0 := by
    have h' : (τ : ℂ) + ((γ 0 1 : ℤ) : ℝ) = τ := by exact_mod_cast hfix
    have h'' := add_left_cancel (h'.trans (add_zero (τ : ℂ)).symm)
    exact_mod_cast h''
  have h01' : (γ 0 1 : ℤ) = 0 := by exact_mod_cast h01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hrow.1, hrow.2, hdet, h01']

theorem chi_injective (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) : Function.Injective (chi Γ τ) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro γ hγ
  rw [MonoidHom.mem_ker, chi_apply] at hγ
  have hfix : ((γ : Γ) : SL(2, ℤ)) • τ = τ := γ.2
  exact Subtype.ext (Subtype.ext (eq_one_of_denom_eq_one τ _ hfix hγ))

private theorem _root_.UpperHalfPlane.StabilizerDvdTwoMulOrder.finite_stabilizer (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) : Finite (MulAction.stabilizer Γ τ) := by
  have hfin := ProperlyDiscontinuousSMul.finite_stabilizer (Γ := 𝒮ℒ) τ
  have : Finite (MulAction.stabilizer (𝒮ℒ) τ) := hfin
  refine Finite.of_injective
    (fun γ => (⟨⟨Matrix.SpecialLinearGroup.mapGL ℝ ((γ : Γ) : SL(2, ℤ)), ⟨_, rfl⟩⟩, γ.2⟩ :
      MulAction.stabilizer (𝒮ℒ) τ)) ?_
  intro a b h
  have := congrArg (fun x : MulAction.stabilizer (𝒮ℒ) τ => ((x : 𝒮ℒ) : GL (Fin 2) ℝ)) h
  exact Subtype.ext (Subtype.ext (Matrix.SpecialLinearGroup.mapGL_injective this))

p2m_export "UpperHalfPlane.StabilizerDvdTwoMulOrder" "finite_stabilizer"
scoped instance (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) : Finite (MulAction.stabilizer Γ τ) :=
  finite_stabilizer Γ τ

theorem isCyclic_stabilizer (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) :
    IsCyclic (MulAction.stabilizer Γ τ) :=
  isCyclic_of_injective_ringHom (chi Γ τ) (chi_injective Γ τ)

theorem card_dvd_of_forall_chi_zpow_eq_one (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) (n : ℤ)
    (h : ∀ γ : MulAction.stabilizer Γ τ, chi Γ τ γ ^ (2 * n) = 1) :
    (Nat.card (MulAction.stabilizer Γ τ) : ℤ) ∣ 2 * n := by
  haveI := isCyclic_stabilizer Γ τ
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := MulAction.stabilizer Γ τ)
  rw [← hg, Int.natCast_dvd]
  apply orderOf_dvd_of_pow_eq_one
  apply chi_injective Γ τ
  rw [map_pow, map_one]
  have h1 := h g
  rcases Int.natAbs_eq (2 * n) with h2 | h2
  · rw [h2, zpow_natCast] at h1; exact h1
  · rw [h2, zpow_neg, zpow_natCast, inv_eq_one] at h1; exact h1

theorem num_mul_denom_sub (g : GL (Fin 2) ℝ) (z w : ℂ) :
    num g z * denom g w - denom g z * num g w = (g.val.det : ℝ) * (z - w) := by
  simp only [num, denom, Matrix.det_fin_two]
  push_cast
  ring

theorem det_coe_SL (γ : SL(2, ℤ)) : ((γ : GL (Fin 2) ℝ).val.det : ℝ) = 1 :=
  Matrix.SpecialLinearGroup.det_coe _

def moeb (γ : SL(2, ℤ)) (z : ℂ) : ℂ := num (γ : GL (Fin 2) ℝ) z / denom (γ : GL (Fin 2) ℝ) z

theorem coe_smul_eq_moeb (γ : SL(2, ℤ)) (z : ℍ) : ((γ • z : ℍ) : ℂ) = moeb γ z := by
  rw [ModularGroup.sl_moeb, coe_smul_of_det_pos (by simp)]; rfl

theorem moeb_sub (γ : SL(2, ℤ)) (τ : ℍ) (hγ : γ • τ = τ) (z : ℂ)
    (hz : denom (γ : GL (Fin 2) ℝ) z ≠ 0) :
    moeb γ z - τ = (z - τ) / (denom (γ : GL (Fin 2) ℝ) z * denom (γ : GL (Fin 2) ℝ) τ) := by
  have hτ : (τ : ℂ) = moeb γ τ := by rw [← coe_smul_eq_moeb, hγ]
  conv_lhs => rw [hτ]
  simp only [moeb]
  rw [div_sub_div _ _ hz (denom_ne_zero _ τ), num_mul_denom_sub, det_coe_SL]
  push_cast
  ring

theorem continuousAt_moeb (γ : SL(2, ℤ)) (τ : ℍ) : ContinuousAt (moeb γ) τ := by
  apply ContinuousAt.div
  · exact (continuous_const.mul continuous_id).add continuous_const |>.continuousAt
  · exact (continuous_const.mul continuous_id).add continuous_const |>.continuousAt
  · exact denom_ne_zero _ τ

theorem continuous_denom (g : GL (Fin 2) ℝ) : Continuous (fun z : ℂ => denom g z) :=
  (continuous_const.mul continuous_id).add continuous_const

theorem chi_zpow_eq_one (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ)
    (hF : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) (τ : ℍ) (n : ℤ)
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g τ) (hg0 : g τ ≠ 0)
    (hfg : ∀ᶠ z in 𝓝[≠] (τ : ℂ), F (ofComplex z) = (z - τ) ^ n • g z)
    (γ : MulAction.stabilizer Γ τ) :
    chi Γ τ γ ^ (2 * n) = 1 := by
  set γ₀ : SL(2, ℤ) := ((γ : Γ) : SL(2, ℤ)) with hγ₀
  have hfix : γ₀ • τ = τ := γ.2
  set d : ℂ → ℂ := fun z => denom (γ₀ : GL (Fin 2) ℝ) z with hd
  have hdτ : d τ ≠ 0 := denom_ne_zero _ τ
  have hmoebτ : moeb γ₀ τ = τ := by rw [← coe_smul_eq_moeb, hfix]

  have him : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
    eventually_nhdsWithin_of_eventually_nhds
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos)

  have hmt : Tendsto (moeb γ₀) (𝓝[≠] (τ : ℂ)) (𝓝[≠] (τ : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h := (continuousAt_moeb γ₀ τ).tendsto
      rw [hmoebτ] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [him, self_mem_nhdsWithin] with z hz hne
      have hdz : d z ≠ 0 := denom_ne_zero_of_im _ hz.ne'
      intro (habs : moeb γ₀ z = τ)
      have := moeb_sub γ₀ τ hfix z hdz
      rw [habs, sub_self, eq_comm, div_eq_zero_iff] at this
      rcases this with h | h
      · exact hne (sub_eq_zero.mp h)
      · exact mul_ne_zero hdz hdτ h

  have hkey : ∀ᶠ z in 𝓝[≠] (τ : ℂ),
      g z = (d z * d τ) ^ (-n) * g (moeb γ₀ z) := by
    filter_upwards [hfg, hmt.eventually hfg, him, self_mem_nhdsWithin] with z hz hmz hzi hne
    have hdz : d z ≠ 0 := denom_ne_zero_of_im _ hzi.ne'
    have hzτ : (z : ℂ) - τ ≠ 0 := sub_ne_zero.mpr hne

    have hinv : F (ofComplex (moeb γ₀ z)) = F (ofComplex z) := by
      have h1 : ofComplex z = (⟨z, hzi⟩ : ℍ) := by
        ext; exact congrArg _ (ofComplex_apply_of_im_pos hzi)
      have h2 : moeb γ₀ z = ((γ₀ • (⟨z, hzi⟩ : ℍ) : ℍ) : ℂ) := by
        rw [coe_smul_eq_moeb]
      rw [h2, ofComplex_apply, h1]
      exact hF γ₀ (γ : Γ).2 _
    rw [hmz, hz, moeb_sub γ₀ τ hfix z hdz, smul_eq_mul, smul_eq_mul, div_zpow,
      div_mul_eq_mul_div, div_eq_iff (zpow_ne_zero _ (mul_ne_zero hdz hdτ)), mul_assoc] at hinv
    have := mul_left_cancel₀ (zpow_ne_zero n hzτ) hinv

    rw [zpow_neg, eq_inv_mul_iff_mul_eq₀ (zpow_ne_zero _ (mul_ne_zero hdz hdτ)), this, mul_comm]

  have hlim1 : Tendsto g (𝓝[≠] (τ : ℂ)) (𝓝 (g τ)) :=
    hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun z => (d z * d τ) ^ (-n) * g (moeb γ₀ z)) (𝓝[≠] (τ : ℂ))
      (𝓝 ((d τ * d τ) ^ (-n) * g τ)) := by
    apply Tendsto.mul
    · have hc : ContinuousAt (fun z => (d z * d τ) ^ (-n)) τ := by
        apply ContinuousAt.zpow₀
        · exact ((continuous_denom _).mul continuous_const).continuousAt
        · exact Or.inl (mul_ne_zero hdτ hdτ)
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    · have hm : Tendsto (moeb γ₀) (𝓝[≠] (τ : ℂ)) (𝓝 (τ : ℂ)) := by
        have h := (continuousAt_moeb γ₀ τ).tendsto
        rw [hmoebτ] at h
        exact h.mono_left nhdsWithin_le_nhds
      exact hg.continuousAt.tendsto.comp hm
  have heq := tendsto_nhds_unique (hlim1.congr' hkey) hlim2

  rw [eq_comm, mul_eq_right₀ hg0, zpow_neg, inv_eq_one] at heq
  rw [chi_apply, zpow_mul, zpow_two]
  exact heq

theorem main (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ) (hF : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
    (τ : ℍ) (n : ℤ)
    (hn : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = n) :
    (Nat.card (MulAction.stabilizer Γ τ) : ℤ) ∣ 2 * n := by
  by_cases hmer : MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)
  · obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hmer).mp hn
    exact card_dvd_of_forall_chi_zpow_eq_one Γ τ n
      (chi_zpow_eq_one Γ F hF τ n g hg hg0 hfg)
  · rw [meromorphicOrderAt_of_not_meromorphicAt hmer] at hn
    have : n = 0 := by exact_mod_cast hn.symm
    rw [this, mul_zero]
    exact dvd_zero _

end UpperHalfPlane.StabilizerDvdTwoMulOrder
p2m_reactivate "P2MW.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq.UpperHalfPlane P2MW.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq.UpperHalfPlane.StabilizerDvdTwoMulOrder"
p2m_reactivate "P2MW.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq.UpperHalfPlane"

end
p2m_reactivate "P2MW.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq.UpperHalfPlane P2MW.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq.UpperHalfPlane.StabilizerDvdTwoMulOrder"

open _root_.UpperHalfPlane _root_.P2MW.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq.UpperHalfPlane in
open scoped MatrixGroups in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ) (hF : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
    (τ : ℍ) (n : ℤ)
    (hn : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = n) :
    (Nat.card (MulAction.stabilizer Γ τ) : ℤ) ∣ 2 * n :=
  UpperHalfPlane.StabilizerDvdTwoMulOrder.main Γ F hF τ n hn

end S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq
end P2MW
export P2MW.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq (solution)
