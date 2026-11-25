-- Prove2me | solution 1 for PIW.AdelClassFin.spOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:40.786902+00:00
-- url     : https://prove2.me/submissions/f1bb0335-1ef2-4e8c-a765-65a1b0810be0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartSplitOfOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSingleLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SpComp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SpDen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SplHformZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartBetween
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_BlkMulVecCat
import Theorems.Thm_PIW_AdelClassFin_SpO_catR_apply
import Theorems.Thm_PIW_AdelClassFin_SpO_cat_add
import Theorems.Thm_PIW_AdelClassFin_SpO_blk_mulVec
import Theorems.Thm_PIW_AdelClassFin_SpO_blk_mulVec_cat
import Theorems.Thm_PIW_AdelClassFin_SpO_single_inl
import Theorems.Thm_PIW_AdelClassFin_SpO_single_inr
import Theorems.Thm_PIW_AdelClassFin_SpO_cat_eq_sum
import Theorems.Thm_PIW_AdelClassFin_SpO_entry_eq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PIW_AdelClassFin_cT_star
import Theorems.Thm_PIW_AdelClassFin_gram_eq
import Theorems.Thm_PIW_AdelClassFin_hform_mulVec
import Theorems.Thm_PIW_AdelClassFin_hform_single
import Theorems.Thm_PIW_AdelClassFin_isHerm_iff
import Theorems.Thm_PIW_AdelClassFin_partBetween
import Theorems.Thm_PIW_AdelClassFin_spComp
import Theorems.Thm_PIW_AdelClassFin_spDen
import Theorems.Thm_PIW_AdelClassFin_spLat
import Theorems.Thm_PIW_AdelClassFin_spl_cross
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
open SpO
namespace PIW.AdelClassFin
theorem _root_.solution : SpOne := by
  intro E _ _ _ m k hk ih d hd Γ hΓ
  classical
  by_cases hkm : k ≤ m
  swap
  · refine ⟨∅, Set.finite_empty, ?_⟩
    rintro p ⟨_, v, _, hvΓ⟩
    exfalso
    apply hkm
    have hg : cT (starRingEnd E) (Matrix.of fun r i => v i r) * p.1 * (Matrix.of fun r i => v i r) = Γ :=
      (gram_eq p.1 v).symm.trans (Set.mem_singleton_iff.mp hvΓ)
    refine (spComp E k m (cT (starRingEnd E) (Matrix.of fun r i => v i r) * p.1)
      ((Matrix.of fun r i => v i r) * Γ⁻¹) ?_).1
    rw [← Matrix.mul_assoc, hg, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hΓ)]
  obtain ⟨D, hD1, hDΓ⟩ := spDen E k Γ⁻¹
  have hnm : m - k < m := by omega
  have hdD : 1 ≤ d * D := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨T', hT'f, hT'⟩ := ih (m - k) hnm (d * D) hdD
  let e : Fin k ⊕ Fin (m - k) ≃ Fin m := finSumFinEquiv.trans (finCongr (by omega))
  let N : Submodule (𝓞 E) (Fin (m - k) → E) → Submodule (𝓞 E) (Fin m → E) := fun M' =>
    Submodule.span (𝓞 E) (Set.range fun i : Fin k => (Pi.single (e (Sum.inl i)) (1 : E) : Fin m → E)) ⊔
      M'.map (catR (𝓞 E) e)
  let Jb : Matrix (Fin (m - k)) (Fin (m - k)) E → Matrix (Fin m) (Fin m) E := fun J' =>
    Matrix.of fun r s => Matrix.fromBlocks Γ 0 0 J' (e.symm r) (e.symm s)
  let T : Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E)) :=
    ⋃ q' ∈ {q' | q' ∈ T' ∧ q'.2.FG}, (fun M₀ => (Jb q'.1, M₀)) ''
      {M₀ : Submodule (𝓞 E) (Fin m → E) | N q'.2 ≤ M₀ ∧ ∀ x ∈ M₀, (D : 𝓞 E) • x ∈ N q'.2}
  have hD0 : (D : 𝓞 E) ≠ 0 := by
    intro h0
    have h1 := congrArg (algebraMap (𝓞 E) E) h0
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h1
    omega
  refine ⟨T, ?_, ?_⟩
  · refine Set.Finite.biUnion (hT'f.subset fun q h => h.1) fun q' hq' => ?_
    refine Set.Finite.image _ (partBetween E m (N q'.2) ?_ (D : 𝓞 E) hD0)
    exact (Submodule.fg_span (Set.finite_range _)).sup (hq'.2.map _)
  rintro p ⟨hp, v, hv, hvΓ⟩
  have hg : cT (starRingEnd E) (Matrix.of fun r i => v i r) * p.1 * (Matrix.of fun r i => v i r) = Γ :=
    (gram_eq p.1 v).symm.trans (Set.mem_singleton_iff.mp hvΓ)
  set V : Matrix (Fin m) (Fin k) E := Matrix.of fun r i => v i r with hVdef
  have hPR : (cT (starRingEnd E) V * p.1) * (V * Γ⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, hg, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hΓ)]
  obtain ⟨-, U, hPU, hUinj, hUsurj⟩ := spComp E k m _ _ hPR
  have hVM : ∀ i, (fun r => V r i) ∈ p.2 := fun i => hv i
  obtain ⟨hLat', hdec⟩ := spLat E m k (m - k) d D p.1 p.2 V U hp hVM hD1 (by rw [hg]; exact hΓ)
    (by rw [hg]; exact hDΓ) hPU hUinj hUsurj
  obtain ⟨q', hq', B, hB1, hB2⟩ := hT' _ hLat'
  set W : Matrix (Fin m) (Fin (m - k)) E := U * (B : Matrix (Fin (m - k)) (Fin (m - k)) E) with hWdef
  set A : Matrix (Fin m) (Fin m) E := blk e V W with hAdef
  have hJh : p.1ᴴ = p.1 := (isHerm_iff _).1 hp.1
  have hUV : cT (starRingEnd E) U * p.1 * V = 0 := by
    have h := congrArg Matrix.conjTranspose hPU
    rw [cT_star] at h ⊢
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJh,
      Matrix.conjTranspose_zero, ← Matrix.mul_assoc] at h
    exact h
  have hPW : cT (starRingEnd E) V * p.1 * W = 0 := by
    rw [hWdef, ← Matrix.mul_assoc, hPU, Matrix.zero_mul]
  have hWy : ∀ y, W *ᵥ y = U *ᵥ ((B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ y) := fun y => by
    rw [hWdef, Matrix.mulVec_mulVec]
  have hker : ∀ x, A *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [hAdef, blk_mulVec] at hx
    have h1 := congrArg (fun z => (cT (starRingEnd E) V * p.1) *ᵥ z) hx
    simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, hg, hPW, Matrix.zero_mulVec, add_zero,
      Matrix.mulVec_zero] at h1
    have hΓu : IsUnit Γ := (Matrix.isUnit_iff_isUnit_det Γ).mpr (isUnit_iff_ne_zero.mpr hΓ)
    have hc0 : (fun i => x (e (Sum.inl i))) = 0 :=
      Matrix.mulVec_injective_iff_isUnit.mpr hΓu (by rw [h1, Matrix.mulVec_zero])
    rw [hc0, Matrix.mulVec_zero, zero_add, hWy] at hx
    have hBy : (B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ (fun j => x (e (Sum.inr j))) = 0 :=
      hUinj (by rw [hx, Matrix.mulVec_zero])
    have hy0 : (fun j => x (e (Sum.inr j))) = 0 :=
      Matrix.mulVec_injective_iff_isUnit.mpr (Units.isUnit B) (by rw [hBy, Matrix.mulVec_zero])
    funext r
    obtain ⟨t, rfl⟩ := e.surjective r
    cases t with
    | inl i => exact congrFun hc0 i
    | inr j => exact congrFun hy0 j
  have hAinj : Function.Injective A.mulVec := by
    intro x x' h
    have := hker (x - x') (by rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr h)
    exact sub_eq_zero.mp this
  have hdetA : A.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det A).mp (Matrix.mulVec_injective_iff_isUnit.mp hAinj)).ne_zero
  set A' : GL (Fin m) E := Matrix.GeneralLinearGroup.mkOfDetNeZero A hdetA with hA'def
  have hA'v : (A' : Matrix (Fin m) (Fin m) E) = A := rfl
  have hAcat : ∀ c y, A *ᵥ cat e c y = V *ᵥ c + U *ᵥ ((B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ y) := by
    intro c y
    rw [hAdef, blk_mulVec_cat, hWy]
  have hcol1 : ∀ i, A *ᵥ Pi.single (e (Sum.inl i)) 1 = V *ᵥ Pi.single i 1 := fun i => by
    rw [single_inl, hAcat, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
  have hcol2 : ∀ j, A *ᵥ Pi.single (e (Sum.inr j)) 1 =
      U *ᵥ ((B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ Pi.single j 1) := fun j => by
    rw [single_inr, hAcat, Matrix.mulVec_zero, zero_add]
  set M₀ : Submodule (𝓞 E) (Fin m → E) := p.2.comap (A.mulVecLin.restrictScalars (𝓞 E)) with hM₀
  have hmem : ∀ x, x ∈ M₀ ↔ A *ᵥ x ∈ p.2 := fun x => Iff.rfl
  have hfg' : q'.2.FG := by
    have heq : q'.2 = (p.2.comap (U.mulVecLin.restrictScalars (𝓞 E))).map
        (((B⁻¹ : GL (Fin (m - k)) E) : Matrix (Fin (m - k)) (Fin (m - k)) E).mulVecLin.restrictScalars (𝓞 E)) := by
      ext w
      simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
      constructor
      · intro hw
        refine ⟨(B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ w, (hB2 _).2 ⟨w, hw, rfl⟩, ?_⟩
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨w, hw, rfl⟩ := (hB2 u).1 hu
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
        exact hw
    rw [heq]
    exact hLat'.2.2.1.map _
  have hNle : N q'.2 ≤ M₀ := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, hmem, hcol1, Matrix.mulVec_single_one]
      exact hv i
    · rw [Submodule.map_le_iff_le_comap]
      intro y hy
      rw [Submodule.mem_comap, catR_apply, hmem, hAcat, Matrix.mulVec_zero, zero_add]
      exact (hB2 _).2 ⟨y, hy, rfl⟩
  have hDN : ∀ x ∈ M₀, (D : 𝓞 E) • x ∈ N q'.2 := by
    intro x hx
    obtain ⟨c, hc, y', hy'M, hdecx⟩ := hdec _ ((hmem x).1 hx)
    obtain ⟨y0, hy0, hBy0⟩ := (hB2 y').1 hy'M
    have hxe : (D : 𝓞 E) • x = cat e c 0 + catR (𝓞 E) e y0 := by
      apply hAinj
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, Matrix.mulVec_smul, hdecx, catR_apply,
        cat_add, hAcat, hBy0]
    rw [hxe]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (Submodule.mem_map_of_mem hy0))
    rw [cat_eq_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨a, ha⟩ := hc i
    rw [← ha, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨(Jb q'.1, M₀), Set.mem_biUnion (x := q') ⟨hq', hfg'⟩ (Set.mem_image_of_mem _ ⟨hNle, hDN⟩), A', ?_, ?_⟩
  · show cT (starRingEnd E) (A' : Matrix (Fin m) (Fin m) E) * p.1 * (A' : Matrix (Fin m) (Fin m) E) = Jb q'.1
    rw [hA'v]
    ext r s
    obtain ⟨t, rfl⟩ := e.surjective r
    obtain ⟨t', rfl⟩ := e.surjective s
    rw [entry_eq]
    simp only [Jb, Matrix.of_apply, Equiv.symm_apply_apply]
    rcases t with i | j <;> rcases t' with i' | j'
    · rw [hcol1, hcol1, hform_mulVec, hg, hform_single, Matrix.fromBlocks_apply₁₁]
    · rw [hcol1, hcol2, spl_cross p.1 V U hPU, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    · rw [hcol2, hcol1, spl_cross p.1 U V hUV, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    · rw [hcol2, hcol2, hform_mulVec, hform_mulVec, hB1, hform_single, Matrix.fromBlocks_apply₂₂]
  · intro w
    constructor
    · intro hw
      refine ⟨((A'⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ w, ?_, ?_⟩
      · show A *ᵥ (((A'⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ w) ∈ p.2
        rw [← hA'v, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
        exact hw
      · rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    · rintro ⟨u, hu, rfl⟩
      rw [hA'v]
      exact hu
end PIW.AdelClassFin
