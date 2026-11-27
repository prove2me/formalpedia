-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BModbound.ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:20:42.269418+00:00
-- url     : https://prove2.me/submissions/15969ce3-11f9-403e-91a4-d78cef554f3c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_HaarMeasureGL
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_Imports
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BModbound_ratio_pi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module ValuativeRel MeasureTheory
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BModbound
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound
theorem _root_.solution (V : Submodule k (Matrix (Fin n) (Fin n) k)) (γ : ValueGroupWithZero k) (hγ : γ ≠ 0)
    (φ : V ≃ₗ[k] V) (X Y : AddSubgroup (Matrix (Fin n) (Fin n) k))
    (hX : ∀ y, y ∈ X ↔ y ∈ V ∧ ∀ i j, valuation k (y i j) ≤ γ)
    (hY : ∀ y, y ∈ Y ↔ ∃ x : V, (x : Matrix (Fin n) (Fin n) k) ∈ X ∧ ((φ x : V) : Matrix (Fin n) (Fin n) k) = y) :
    (X ⊓ Y).relIndex X ≠ 0 ∧ (X ⊓ Y).relIndex Y ≠ 0 ∧
      ((X ⊓ Y).relIndex Y : ℝ) / ((X ⊓ Y).relIndex X : ℝ) = (distribHaarChar k (LinearEquiv.det φ) : ℝ) := by
  classical
  let e : V ≃ₗ[k] (Fin (Module.finrank k V) → k) := (Module.finBasis k V).equivFun
  let ι : (Fin (Module.finrank k V) → k) →ₗ[k] Matrix (Fin n) (Fin n) k := V.subtype ∘ₗ e.symm.toLinearMap
  have hι : ∀ c, ι c = ((e.symm c : V) : Matrix (Fin n) (Fin n) k) := fun c => rfl
  have hιinj : Function.Injective ι := fun a b h => e.symm.injective (Subtype.ext h)
  let L : (Fin (Module.finrank k V) → k) ≃ₗ[k] (Fin (Module.finrank k V) → k) := (e.symm.trans φ).trans e
  have hdet : LinearEquiv.det L = LinearEquiv.det φ := LinearEquiv.det_conj φ e
  let X' := X.comap ι.toAddMonoidHom
  let Y' := Y.comap ι.toAddMonoidHom
  have hXV : ∀ y ∈ X, y ∈ V := fun y hy => ((hX y).1 hy).1
  have hYV : ∀ y ∈ Y, y ∈ V := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := (hY y).1 hy
    exact (φ x).2
  have hmap : ∀ W : AddSubgroup (Matrix (Fin n) (Fin n) k), (∀ y ∈ W, y ∈ V) →
      (W.comap ι.toAddMonoidHom).map ι.toAddMonoidHom = W := by
    intro W hW
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact hc
    · intro hy
      refine ⟨e ⟨y, hW y hy⟩, ?_, ?_⟩
      · show ι (e ⟨y, hW y hy⟩) ∈ W
        rw [hι, LinearEquiv.symm_apply_apply]
        exact hy
      · show ι (e ⟨y, hW y hy⟩) = y
        rw [hι, LinearEquiv.symm_apply_apply]
  have hinf : (X ⊓ Y).comap ι.toAddMonoidHom = X' ⊓ Y' := AddSubgroup.comap_inf _ _ _
  have i1 : (X ⊓ Y).relIndex X = (X' ⊓ Y').relIndex X' := by
    rw [← hinf, AddSubgroup.relIndex_comap, hmap X hXV]
  have i2 : (X ⊓ Y).relIndex Y = (X' ⊓ Y').relIndex Y' := by
    rw [← hinf, AddSubgroup.relIndex_comap, hmap Y hYV]

  have hιc : Continuous ι := ι.continuous_on_pi
  let B : Set (Matrix (Fin n) (Fin n) k) := {M | ∀ i j, valuation k (M i j) ≤ γ}
  have hXset : (X' : Set (Fin (Module.finrank k V) → k)) = ι ⁻¹' B := by
    ext c
    show ι c ∈ X ↔ ∀ i j, valuation k (ι c i j) ≤ γ
    rw [hX]
    exact ⟨fun h => h.2, fun h => ⟨by rw [hι]; exact (e.symm c).2, h⟩⟩
  have hBo : IsOpen B := by
    have : B = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) k => M i j) ⁻¹' {x : k | valuation k x ≤ γ} := by
      ext M; simp [B]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GroundTheory.Automorphic.GLnLocal.isOpen_valuation_le k hγ).preimage (continuous_id.matrix_elem i j)
  have hBc : IsCompact B := by
    have h : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => {x : k | valuation k x ≤ γ}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ
    have hs : B = (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => {x : k | valuation k x ≤ γ}) := by
      ext M
      constructor
      · intro h i _ j _
        exact h i j
      · intro h i j
        exact h i (Set.mem_univ _) j (Set.mem_univ _)
    rw [hs]; exact h
  have hXo : IsOpen (X' : Set (Fin (Module.finrank k V) → k)) := hXset ▸ hBo.preimage hιc
  obtain ⟨ρ, hρ⟩ := ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hιinj)
  let cl : (Fin n × Fin n → k) →ₗ[k] Matrix (Fin n) (Fin n) k :=
    { toFun := fun f => Matrix.of fun i j => f (i, j)
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp }
  have hρc : Continuous ρ := by
    have h1 : (ρ : Matrix (Fin n) (Fin n) k → _) = (ρ ∘ₗ cl) ∘ (fun M p => M p.1 p.2) := by
      funext M
      simp only [Function.comp_apply, LinearMap.coe_comp]
      congr 1
    rw [h1]
    exact (ρ ∘ₗ cl).continuous_on_pi.comp (continuous_pi fun p => continuous_id.matrix_elem p.1 p.2)
  have hsub : (X' : Set (Fin (Module.finrank k V) → k)) ⊆ ρ '' B := by
    intro c hc
    rw [hXset] at hc
    exact ⟨ι c, hc, LinearMap.congr_fun hρ c⟩
  have hXc : IsCompact (X' : Set (Fin (Module.finrank k V) → k)) :=
    (hBc.image hρc).of_isClosed_subset (AddSubgroup.isClosed_of_isOpen X' hXo) hsub
  have hYset : (Y' : Set (Fin (Module.finrank k V) → k)) = L '' (X' : Set _) := by
    ext c
    show ι c ∈ Y ↔ _
    rw [hY]
    constructor
    · rintro ⟨x, hx, hxc⟩
      refine ⟨e x, ?_, ?_⟩
      · show ι (e x) ∈ X
        rw [hι, LinearEquiv.symm_apply_apply]; exact hx
      · have h1 : φ x = e.symm c := Subtype.ext (by rw [hxc, hι])
        show e (φ (e.symm (e x))) = c
        rw [LinearEquiv.symm_apply_apply, h1, LinearEquiv.apply_symm_apply]
    · rintro ⟨c0, hc0, rfl⟩
      refine ⟨e.symm c0, hc0, ?_⟩
      show ((φ (e.symm c0) : V) : Matrix (Fin n) (Fin n) k) = ι (e (φ (e.symm c0)))
      rw [hι, LinearEquiv.symm_apply_apply]
  obtain ⟨n1, n2, hr⟩ := ratio_pi X' Y' hXc hXo L hYset
  rw [i1, i2]
  exact ⟨n1, n2, by rw [hr, hdet]⟩
end PositivityTheory.RgUd.T.Nil.Orb.BModbound
