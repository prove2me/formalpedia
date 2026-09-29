-- Prove2me | solution 1 for UpperHalfPlane.finite_stabilizer_and_isCyclic_of_det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/62337da9-d321-56d0-88ef-0c455907c8fe

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_finite_stabilizer_and_isCyclic_of_det_eq_one

set_option autoImplicit false

open Filter UpperHalfPlane
open scoped MatrixGroups Topology Pointwise

namespace StabE1

theorem denom_eq_one_imp {g : GL (Fin 2) ℝ} {τ : ℍ} (h : denom g (τ : ℂ) = 1) :
    g 1 0 = 0 ∧ g 1 1 = 1 := by
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [denom] at him hre
  have hc : g 1 0 = 0 := by
    rcases him with h1 | h1
    · exact h1
    · exact absurd h1 τ.im_ne_zero
  refine ⟨hc, ?_⟩
  simpa [hc] using hre

theorem eq_one_of_smul_eq_of_denom_eq_one {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) {τ : ℍ}
    (hfix : g • τ = τ) (h : denom g (τ : ℂ) = 1) : g = 1 := by
  obtain ⟨hc, hd⟩ := denom_eq_one_imp h
  have hnum : num g (τ : ℂ) = (τ : ℂ) := by
    have := coe_smul_of_det_pos (show 0 < ((Matrix.GeneralLinearGroup.det g : ℝˣ) : ℝ) by
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using hg) τ
    rw [hfix, h, div_one] at this
    exact this.symm
  have him := congrArg Complex.im hnum
  have hre := congrArg Complex.re hnum
  simp [num] at him hre
  have ha : g 0 0 = 1 := by
    have : (g 0 0 - 1) * τ.im = 0 := by rw [sub_mul, one_mul, sub_eq_zero]; exact him
    rcases mul_eq_zero.mp this with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 τ.im_ne_zero
  have hb : g 0 1 = 0 := by simpa [ha] using hre
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem continuous_toGL : Continuous (Matrix.SpecialLinearGroup.toGL : SL(2, ℝ) → GL (Fin 2) ℝ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_subtype_val
  · have : (fun g : SL(2, ℝ) => ((Matrix.SpecialLinearGroup.toGL g)⁻¹ : GL (Fin 2) ℝ).val) =
        fun g : SL(2, ℝ) => ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext g; rw [← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    rw [this]
    simp only [Matrix.SpecialLinearGroup.coe_inv]
    exact continuous_subtype_val.matrix_adjugate

end StabE1

open StabE1 in
theorem solution (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    [hdisc : DiscreteTopology ↥Γ] (τ : ℍ) :
    Finite ↥(MulAction.stabilizer ↥Γ τ) ∧ IsCyclic ↥(MulAction.stabilizer ↥Γ τ) := by
  classical
  have hdet1 : ∀ γ ∈ Γ, (γ : GL (Fin 2) ℝ).val.det = 1 := by
    intro γ hγ
    have := congrArg Units.val (hdet γ hγ)
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
  have hdet' : ∀ γ : ↥Γ, 0 < (γ : GL (Fin 2) ℝ).val.det := fun γ => by
    rw [hdet1 γ γ.prop]; exact one_pos

  let Γ' : Subgroup SL(2, ℝ) := Γ.comap Matrix.SpecialLinearGroup.toGL
  have hΓ'disc : DiscreteTopology ↥Γ' := by
    let f : ↥Γ' → ↥Γ := fun g => ⟨Matrix.SpecialLinearGroup.toGL (g : SL(2, ℝ)), g.prop⟩
    have hfc : Continuous f := (continuous_toGL.comp continuous_subtype_val).subtype_mk _
    have hfi : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.toGL_injective
      exact congrArg Subtype.val h
    exact DiscreteTopology.of_continuous_injective hfc hfi
  haveI := hΓ'disc
  have hpd : ProperlyDiscontinuousSMul ↥Γ' ℍ := inferInstance
  have hfinset : {g : SL(2, ℝ) | g ∈ Γ' ∧ ((g • ({τ} : Set ℍ)) ∩ {τ}).Nonempty}.Finite :=
    (Subgroup.properlyDiscontinuousSMul_iff Γ').mp hpd isCompact_singleton isCompact_singleton
  have hfin : Finite ↥(MulAction.stabilizer ↥Γ τ) := by
    let toSL : ↥(MulAction.stabilizer ↥Γ τ) → SL(2, ℝ) :=
      fun γ => ⟨((γ : ↥Γ) : GL (Fin 2) ℝ).val, hdet1 _ (γ : ↥Γ).prop⟩
    have htoSL : ∀ γ, Matrix.SpecialLinearGroup.toGL (toSL γ) = ((γ : ↥Γ) : GL (Fin 2) ℝ) := by
      intro γ; ext i j; rfl
    have hfix : ∀ γ, (toSL γ) • τ = τ := by
      intro γ
      change Matrix.SpecialLinearGroup.toGL (toSL γ) • τ = τ
      rw [htoSL]
      exact γ.prop
    let ι' : ↥(MulAction.stabilizer ↥Γ τ) → {g : SL(2, ℝ) | g ∈ Γ' ∧ ((g • ({τ} : Set ℍ)) ∩ {τ}).Nonempty} :=
      fun γ => ⟨toSL γ, by
        refine ⟨?_, ⟨τ, ?_, rfl⟩⟩
        · show Matrix.SpecialLinearGroup.toGL _ ∈ Γ
          rw [htoSL]; exact (γ : ↥Γ).prop
        · rw [Set.smul_set_singleton, hfix]; rfl⟩
    haveI : Finite {g : SL(2, ℝ) | g ∈ Γ' ∧ ((g • ({τ} : Set ℍ)) ∩ {τ}).Nonempty} := hfinset.to_subtype
    refine Finite.of_injective ι' fun x y h => ?_
    have h' := congrArg (fun s => (Subtype.val (Subtype.val s))) h
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    exact h'
  haveI := hfin

  let χ : ↥(MulAction.stabilizer ↥Γ τ) →* ℂˣ :=
    { toFun := fun g => Units.mk0 (denom ((g : ↥Γ) : GL (Fin 2) ℝ) (τ : ℂ)) (denom_ne_zero _ _)
      map_one' := by ext; simp [denom]
      map_mul' := by
        intro g h
        ext
        simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul]
        rw [denom_cocycle _ _ τ.im_ne_zero]
        congr 1
        have hh : ((h : ↥Γ) : GL (Fin 2) ℝ) • τ = τ := h.prop
        rw [← coe_smul_of_det_pos (by simpa [Matrix.GeneralLinearGroup.val_det_apply] using hdet' h) τ]
        exact congrArg (fun w : ℍ => denom ((g : ↥Γ) : GL (Fin 2) ℝ) (w : ℂ)) hh }
  have hχinj : Function.Injective χ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have h1 : denom ((g : ↥Γ) : GL (Fin 2) ℝ) (τ : ℂ) = 1 := by
      have := congrArg Units.val hg
      simpa [χ] using this
    have := eq_one_of_smul_eq_of_denom_eq_one (hdet' g) g.prop h1
    exact Subtype.ext (Subtype.ext this)
  refine ⟨hfin, ?_⟩
  exact isCyclic_of_subgroup_isDomain ((Units.coeHom ℂ).comp χ)
    (Units.coeHom_injective.comp hχinj)

end S_UpperHalfPlane_finite_stabilizer_and_isCyclic_of_det_eq_one
end P2MW
export P2MW.S_UpperHalfPlane_finite_stabilizer_and_isCyclic_of_det_eq_one (solution)
