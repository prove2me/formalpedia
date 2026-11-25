-- Prove2me | solution 1 for PIW.AdelClassFin.spLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:47:21.13691+00:00
-- url     : https://prove2.me/submissions/e75ff629-6f32-4f1f-9b69-219077c4e4ab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartSplitOfOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSingleLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SplHformZero
import Theorems.Thm_PIW_AdelClassFin_spl_ker
import Theorems.Thm_PIW_AdelClassFin_spl_cross
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PIW_AdelClassFin_cT_mulVec_apply
import Theorems.Thm_PIW_AdelClassFin_hform_add_left
import Theorems.Thm_PIW_AdelClassFin_hform_eq
import Theorems.Thm_PIW_AdelClassFin_hform_mulVec
import Theorems.Thm_PIW_AdelClassFin_hform_single_left
import Theorems.Thm_PIW_AdelClassFin_hform_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.UG NumberField
open scoped Matrix
namespace PIW.AdelClassFin
theorem _root_.solution : SpLat := by
  intro E _ _ _ m k n d D J M V U hp hV hD hΓ hΓD hVJU hU hsurj
  obtain ⟨hH, hdet, hfg, hsp, hint, hdual⟩ := hp
  have hD0 : (D : E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hR : ∀ x ∈ M, ∀ c : E, c ∈ (algebraMap (𝓞 E) E).range → c • x ∈ M := by
    rintro x hx c ⟨a, rfl⟩
    rw [algebraMap_smul]
    exact M.smul_mem a hx
  have hVc : ∀ c : Fin k → E, (∀ i, c i ∈ (algebraMap (𝓞 E) E).range) → V *ᵥ c ∈ M := by
    intro c hc
    have e : V *ᵥ c = ∑ i, c i • (fun r => V r i) := by
      ext r
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => hR _ (hV i) _ (hc i)
  have dec : ∀ z ∈ M, ∃ c : Fin k → E, (∀ i, c i ∈ (algebraMap (𝓞 E) E).range) ∧ ∃ y : Fin n → E,
      U *ᵥ y ∈ M ∧ (D : E) • z = V *ᵥ c + U *ᵥ y := by
    intro z hz
    set c := (cT (starRingEnd E) V * J * V)⁻¹ *ᵥ ((cT (starRingEnd E) V * J) *ᵥ ((D : E) • z)) with hc
    have hci : ∀ i, c i ∈ (algebraMap (𝓞 E) E).range := by
      intro i
      have hg : ∀ j, ((cT (starRingEnd E) V * J) *ᵥ z) j ∈ (algebraMap (𝓞 E) E).range := fun j => by
        rw [cT_mulVec_apply]
        exact hint _ (hV j) _ hz
      rw [hc, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      generalize (cT (starRingEnd E) V * J) *ᵥ z = g at hg ⊢
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Subring.sum_mem _ fun j _ => ?_
      rw [← mul_assoc]
      exact Subring.mul_mem _ (hΓD i j) (hg j)
    obtain ⟨y, hy⟩ := hsurj _ (spl_ker J V hΓ ((D : E) • z))
    have hDz : (D : E) • z ∈ M := by
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem hz D
    refine ⟨c, hci, y, ?_, ?_⟩
    · rw [hy]
      exact M.sub_mem hDz (hVc c hci)
    · rw [hy]
      abel
  have hsplit : ∀ w : Fin m → E, ∃ c, ∃ y, w = V *ᵥ c + U *ᵥ y := by
    intro w
    obtain ⟨y, hy⟩ := hsurj _ (spl_ker J V hΓ w)
    exact ⟨_, y, by rw [hy]; abel⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, dec⟩
  ·
    have hcc : cT (starRingEnd E) (cT (starRingEnd E) U) = U := by
      ext i j
      simp [cT]
    unfold IsHerm at hH ⊢
    rw [cT_mul, cT_mul, hH, hcc, Matrix.mul_assoc]
  ·
    intro h0
    obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have orth : ∀ w, hform (starRingEnd E) J w (U *ᵥ a) = 0 := by
      intro w
      obtain ⟨c, y, rfl⟩ := hsplit w
      rw [hform_add_left, spl_cross J V U hVJU, zero_add, hform_mulVec, hform_eq, ha, dotProduct_zero]
    have hJa : J *ᵥ (U *ᵥ a) = 0 := by
      ext i
      rw [← hform_single_left]
      exact orth _
    have hUa : U *ᵥ a = 0 := by
      by_contra hne
      exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hne, hJa⟩)
    exact ha0 (hU (by rw [hUa, Matrix.mulVec_zero]))
  ·
    refine Submodule.fg_of_fg_map_injective (f := (Matrix.mulVecLin U).restrictScalars (𝓞 E))
      (fun a b h => hU h) ?_
    exact Submodule.FG.of_le hfg (Submodule.map_comap_le _ _)
  ·
    set W : Submodule E (Fin m → E) := LinearMap.range (Matrix.mulVecLin V) ⊔
      (Submodule.span E (M.comap ((Matrix.mulVecLin U).restrictScalars (𝓞 E)) : Set (Fin n → E))).map
        (Matrix.mulVecLin U) with hW
    have hMW : Submodule.span E (M : Set (Fin m → E)) ≤ W := by
      rw [Submodule.span_le]
      intro z hz
      obtain ⟨c, -, y, hyM, hz'⟩ := dec z hz
      refine Submodule.mem_sup.mpr ⟨V *ᵥ ((D : E)⁻¹ • c), ⟨_, rfl⟩, U *ᵥ ((D : E)⁻¹ • y),
        Submodule.mem_map_of_mem (Submodule.smul_mem _ _ (Submodule.subset_span hyM)), ?_⟩
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_add, ← hz', smul_smul, inv_mul_cancel₀ hD0, one_smul]
    rw [hsp, top_le_iff] at hMW
    rw [Submodule.eq_top_iff']
    intro y0
    have h0 : U *ᵥ y0 ∈ W := by rw [hMW]; exact Submodule.mem_top
    obtain ⟨a, ⟨c, rfl⟩, b, hb, hab⟩ := Submodule.mem_sup.mp h0
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hb
    simp only [Matrix.mulVecLin_apply] at hab
    have hP : ∀ v, (cT (starRingEnd E) V * J) *ᵥ (U *ᵥ v) = 0 := fun v => by
      rw [Matrix.mulVec_mulVec, hVJU, Matrix.zero_mulVec]
    have hc0 : c = 0 := by
      have e1 : (cT (starRingEnd E) V * J * V) *ᵥ c = 0 := by
        have := congrArg (fun v => (cT (starRingEnd E) V * J) *ᵥ v) hab
        simp only [Matrix.mulVec_add, hP, add_zero, Matrix.mulVec_mulVec] at this
        exact this
      have := congrArg (fun v => (cT (starRingEnd E) V * J * V)⁻¹ *ᵥ v) e1
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hΓ)] using this
    rw [hc0, Matrix.mulVec_zero, zero_add] at hab
    have : y = y0 := hU hab
    rw [← this]
    exact hy
  ·
    intro x hx y hy
    rw [← hform_mulVec]
    exact hint _ hx _ hy
  ·
    intro w hw
    have h1 : (d : E) • ((D : E) • (U *ᵥ w)) ∈ M := by
      refine hdual _ fun z hz => ?_
      obtain ⟨c, -, y, hyM, hz'⟩ := dec z hz
      have e : hform (starRingEnd E) J z ((D : E) • (U *ᵥ w)) =
          hform (starRingEnd E) J ((D : E) • z) (U *ᵥ w) := by
        have h1 := hform_smul J 1 (D : E) z (U *ᵥ w)
        have h2 := hform_smul J (D : E) 1 z (U *ᵥ w)
        rw [one_smul] at h1 h2
        rw [h1, h2, star_one, star_natCast]
        ring
      rw [e, hz', hform_add_left, spl_cross J V U hVJU, zero_add, hform_mulVec]
      exact hw y hyM
    show U *ᵥ (((d * D : ℕ) : E) • w) ∈ M
    rw [Nat.cast_mul, mul_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]
    exact h1
end PIW.AdelClassFin
