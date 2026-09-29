-- Prove2me | solution 1 for WeierstrassProjModel.kw_a2_sixu_cov
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/d77e9952-695a-5779-b0a0-b6ed2630a5f5

import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_a2_sixu_cov

open MvPolynomial WeierstrassCurve HomogeneousLocalization WeierstrassProjModel
open scoped TensorProduct WeierstrassCurve.Projective

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6400000

noncomputable section

namespace ProjWeierstrassDehomog

section PointDictionary

variable {R : Type*} [CommRing R]

theorem X_eq_zero_and_Y_ne_zero_of_Z_eq_zero [NoZeroDivisors R]
    {V : WeierstrassCurve.Projective R} {P : Fin 3 → R}
    (hP : eval P V.polynomial = 0) (hPz : P 2 = 0) (hP0 : P ≠ 0) :
    P 0 = 0 ∧ P 1 ≠ 0 := by
  have hx : P 0 = 0 := WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero (W' := V) hP hPz
  refine ⟨hx, fun hy => hP0 ?_⟩
  funext i
  fin_cases i
  · exact hx
  · exact hy
  · exact hPz

theorem eq_smul_pointAtInfinity [NoZeroDivisors R]
    {V : WeierstrassCurve.Projective R} {P : Fin 3 → R}
    (hP : eval P V.polynomial = 0) (hPz : P 2 = 0) :
    P = P 1 • ![0, 1, 0] := by
  have hx : P 0 = 0 := WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero (W' := V) hP hPz
  funext i
  fin_cases i <;>
    simp [hx, hPz, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]

open scoped WeierstrassCurve.Projective in

theorem pointClass_eq_pointAtInfinity {F : Type*} [Field F]
    {V : WeierstrassCurve.Projective F} {P : Fin 3 → F}
    (hP : eval P V.polynomial = 0) (hPz : P 2 = 0) (hP0 : P ≠ 0) :
    (⟦P⟧ : WeierstrassCurve.Projective.PointClass F) = ⟦![0, 1, 0]⟧ := by
  have hx : P 0 = 0 := WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero (W' := V) hP hPz
  have hy : P 1 ≠ 0 := by
    intro hy
    exact hP0 (by funext i; fin_cases i <;> assumption)
  refine Quotient.sound ⟨Units.mk0 (P 1) hy, ?_⟩
  funext i
  fin_cases i <;>
    simp [hx, hPz, Units.smul_def, Pi.smul_apply, smul_eq_mul]

end PointDictionary

end ProjWeierstrassDehomog

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in
local notation "gen" => kw_lrChart_gen W

set_option quotPrecheck false in
local notation "dehom" => kw_lrChart_dehom W

variable (F : Type u) [Field F] [Algebra R F]

set_option quotPrecheck false in
local notation "W_F" => kw_lrApt_WF W F

abbrev kw_lrBihom_wR : Fin 3 ⊕ Fin 3 → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

local notation "wR" => @kw_lrBihom_wR

theorem kw_lrBihom_isWeightedHomogeneous_Xl (k : Fin 3) :
    (X (Sum.inl k) : MvPolynomial (Fin 3 ⊕ Fin 3) R).IsWeightedHomogeneous kw_lrBihom_wR 0 :=
  isWeightedHomogeneous_X R kw_lrBihom_wR _

theorem kw_lrBihom_isWeightedHomogeneous_Xr (k : Fin 3) :
    (X (Sum.inr k) : MvPolynomial (Fin 3 ⊕ Fin 3) R).IsWeightedHomogeneous kw_lrBihom_wR 1 :=
  isWeightedHomogeneous_X R kw_lrBihom_wR _

theorem kw_lrBihom_isWeightedHomogeneous_Xl_pow (k : Fin 3) (n : ℕ) :
    (X (Sum.inl k) ^ n : MvPolynomial (Fin 3 ⊕ Fin 3) R).IsWeightedHomogeneous kw_lrBihom_wR 0 := by
  simpa using (kw_lrBihom_isWeightedHomogeneous_Xl (R := R) k).pow n

theorem kw_lrBihom_isWeightedHomogeneous_Xr_pow (k : Fin 3) (n : ℕ) :
    (X (Sum.inr k) ^ n : MvPolynomial (Fin 3 ⊕ Fin 3) R).IsWeightedHomogeneous kw_lrBihom_wR n := by
  simpa using (kw_lrBihom_isWeightedHomogeneous_Xr (R := R) k).pow n

local macro "peel_bihom_R" : tactic =>
  `(tactic| repeat' first
    | with_reducible apply IsWeightedHomogeneous.add
    | with_reducible exact isWeightedHomogeneous_C _ _
    | with_reducible refine IsWeightedHomogeneous.mul ?_ (kw_lrBihom_isWeightedHomogeneous_Xl _)
    | with_reducible refine IsWeightedHomogeneous.mul ?_ (kw_lrBihom_isWeightedHomogeneous_Xr _)
    | with_reducible refine IsWeightedHomogeneous.mul ?_ (kw_lrBihom_isWeightedHomogeneous_Xl_pow _ _)
    | with_reducible refine IsWeightedHomogeneous.mul ?_ (kw_lrBihom_isWeightedHomogeneous_Xr_pow _ _))

theorem kw_lrSymBihom_lrSymX_wR : (kw_lrSym_X W).IsWeightedHomogeneous wR 2 := by
  unfold kw_lrSym_X; peel_bihom_R

theorem kw_lrSymBihom_lrSymY_wR : (kw_lrSym_Y W).IsWeightedHomogeneous wR 2 := by
  unfold kw_lrSym_Y; peel_bihom_R

theorem kw_lrSymBihom_lrSymZ_wR : (kw_lrSym_Z W).IsWeightedHomogeneous wR 2 := by
  unfold kw_lrSym_Z; peel_bihom_R

set_option quotPrecheck false in
local notation "mk₆" => Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal

theorem kw_lrChart_ev'_mk (i j : Fin 3) (a : MvPolynomial (Fin 3 ⊕ Fin 3) R) :
    kw_lrChart_ev' W i j (mk₆ a) = kw_lrChart_ev W i j a := by
  rfl

theorem kw_lrSixU_inl (i j k : Fin 3) :
    kw_lrSixU W i j (Sum.inl k) = kw_lrChart_u W i j k := by
  rfl

theorem kw_lrSixU_inr (i j k : Fin 3) :
    kw_lrSixU W i j (Sum.inr k) = kw_lrSymChart_u W i j k := by
  rfl

local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R

local notation "δ" => (aeval (Sum.elim X X) : P₆ →ₐ[R] MvPolynomial (Fin 3) R)

section Diag

theorem kw_lrSym_X_diag : δ (kw_lrSym_X W) = C (2:R) * kw_lrSym_dblX W := by
  simp only [kw_lrSym_X, kw_lrSym_dblX,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
    aeval_X, aeval_C, Sum.elim_inl, Sum.elim_inr, MvPolynomial.algebraMap_eq]
  ring

theorem kw_lrSym_Y_diag : δ (kw_lrSym_Y W) = C (2:R) * kw_lrSym_dblY W := by
  simp only [kw_lrSym_Y, kw_lrSym_dblY,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
    aeval_X, aeval_C, Sum.elim_inl, Sum.elim_inr, MvPolynomial.algebraMap_eq]
  ring

theorem kw_lrSym_Z_diag : δ (kw_lrSym_Z W) = C (2:R) * kw_lrSym_dblZ W := by
  simp only [kw_lrSym_Z, kw_lrSym_dblZ,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
    aeval_X, aeval_C, Sum.elim_inl, Sum.elim_inr, MvPolynomial.algebraMap_eq]
  ring

end Diag

theorem kw_lrApt_gen_self (i : Fin 3) : gen i i = 1 := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [kw_lrChart_gen_val, HomogeneousLocalization.val_one]
  exact Localization.mk_self
    (⟨mk₃ (X i : MvPolynomial (Fin 3) R), 1, pow_one _⟩ : Submonoid.powers _)

theorem kw_lrApt_chartEval_self (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F) :
    kw_lrApt_chartEval W F i ψ i = 1 := by
  unfold kw_lrApt_chartEval
  rw [kw_lrApt_gen_self W i, map_one]

theorem kw_lrApt_chartEval_ne_zero (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F) :
    kw_lrApt_chartEval W F i ψ ≠ 0 := by
  intro h
  exact one_ne_zero ((kw_lrApt_chartEval_self W F i ψ).symm.trans (congr_fun h i))

theorem kw_lrApt_aeval_chartEval (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F) :
    (aeval (kw_lrApt_chartEval W F i ψ) : MvPolynomial (Fin 3) R →ₐ[R] F)
      = ψ.comp (dehom i) := by
  refine MvPolynomial.algHom_ext fun m => ?_
  show aeval _ (X m) = ψ (aeval _ (X m))
  rw [aeval_X, aeval_X]; rfl

theorem kw_lrApt_eval_chartEval (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F)
    (p : MvPolynomial (Fin 3) R) :
    eval (kw_lrApt_chartEval W F i ψ) (MvPolynomial.map (algebraMap R F) p) = ψ (dehom i p) := by
  have h := congr_fun (congr_arg DFunLike.coe (kw_lrApt_aeval_chartEval W F i ψ)) p
  rw [AlgHom.comp_apply] at h
  rw [MvPolynomial.eval_map, ← aeval_def, h]

theorem kw_lrApt_chartEval_equation (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F) :
    (W_F).Equation (kw_lrApt_chartEval W F i ψ) := by

  show eval _ (W_F).polynomial = 0
  rw [show (W_F).polynomial = MvPolynomial.map (algebraMap R F) W.toProjective.polynomial
        from Projective.map_polynomial (W' := W.toProjective) (f := algebraMap R F),
    kw_lrApt_eval_chartEval W F i ψ, kw_lrChart_dehom_polynomial W i, map_zero]

section SENonsingularInline

theorem kw_lrApt_WF_Δ : (W.baseChange F).Δ = algebraMap R F W.Δ := W.map_Δ _

variable {F}

theorem kw_lrApt_nonsingular_of_equation_of_ne_zero (hΔ : algebraMap R F W.Δ ≠ 0)
    {P : Fin 3 → F} (hP : (W_F).Equation P) (hne : P ≠ 0) : (W_F).Nonsingular P := by
  have hP' : eval P (W_F).polynomial = 0 := hP
  by_cases hPz : P 2 = 0
  ·

    obtain ⟨_hPx, hPy⟩ :=
      ProjWeierstrassDehomog.X_eq_zero_and_Y_ne_zero_of_Z_eq_zero (V := W_F) hP' hPz hne
    have hsmul := ProjWeierstrassDehomog.eq_smul_pointAtInfinity (V := W_F) hP' hPz
    rw [hsmul]
    exact (Projective.nonsingular_smul _ (isUnit_iff_ne_zero.mpr hPy)).mpr
      Projective.nonsingular_zero
  ·
    refine (Projective.nonsingular_of_Z_ne_zero hPz).mpr ?_
    refine (Affine.equation_iff_nonsingular_of_Δ_ne_zero ?_).mp ?_
    · exact (kw_lrApt_WF_Δ W F).symm ▸ hΔ
    · exact (Projective.equation_of_Z_ne_zero hPz).mp hP

end SENonsingularInline

theorem kw_lrApt_ne_zero_of_nonsingular {P : Fin 3 → F} (hP : (W_F).Nonsingular P) : P ≠ 0 := by
  rintro rfl
  rcases hP with ⟨_, hX | hY | hZ⟩
  · exact hX (by rw [Projective.eval_polynomialX]; simp)
  · exact hY (by rw [Projective.eval_polynomialY]; simp)
  · exact hZ (by rw [Projective.eval_polynomialZ]; simp)

section Coeff

theorem kw_lrSixUCov_WF_a₁ : (W_F).a₁ = algebraMap R F W.a₁ := rfl
theorem kw_lrSixUCov_WF_a₂ : (W_F).a₂ = algebraMap R F W.a₂ := rfl
theorem kw_lrSixUCov_WF_a₃ : (W_F).a₃ = algebraMap R F W.a₃ := rfl
theorem kw_lrSixUCov_WF_a₄ : (W_F).a₄ = algebraMap R F W.a₄ := rfl
theorem kw_lrSixUCov_WF_a₆ : (W_F).a₆ = algebraMap R F W.a₆ := rfl

end Coeff

section N1

local macro "simp_N1" : tactic =>
  `(tactic| simp only [kw_lrAdd_X, kw_lrAdd_Y, kw_lrAdd_Z, kw_lrAdd_starX,
      kw_lrAdd_starY, kw_lrAdd_starZ, kw_lrAdd_c₁₂, kw_lrAdd_c₂₁,
      Projective.addX, Projective.addY, Projective.addZ, Projective.negAddY, Projective.negY,
      kw_lrSixUCov_WF_a₁, kw_lrSixUCov_WF_a₂, kw_lrSixUCov_WF_a₃, kw_lrSixUCov_WF_a₄,
      kw_lrSixUCov_WF_a₆,
      map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, aeval_X, aeval_C,
      Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one])

theorem kw_lrSixUCov_aeval_lrAdd_X (P Q : Fin 3 → F) :
    aeval (Sum.elim P Q) (kw_lrAdd_X W) = -(W_F).addX P Q := by
  simp_N1; ring

theorem kw_lrSixUCov_aeval_lrAdd_Y (P Q : Fin 3 → F) :
    aeval (Sum.elim P Q) (kw_lrAdd_Y W) = -(W_F).addY P Q := by
  rw [show (W_F).addY P Q
      = -(W_F).negAddY P Q - (W_F).a₁ * (W_F).addX P Q - (W_F).a₃ * (W_F).addZ P Q from
    (W_F).negY_eq _ _ _]
  simp only [kw_lrAdd_Y, kw_lrAdd_starY, kw_lrAdd_starX, kw_lrAdd_starZ,
    kw_lrAdd_c₁₂, kw_lrAdd_c₂₁, Projective.negAddY, Projective.addX, Projective.addZ,
    kw_lrSixUCov_WF_a₁, kw_lrSixUCov_WF_a₂, kw_lrSixUCov_WF_a₃, kw_lrSixUCov_WF_a₄,
    kw_lrSixUCov_WF_a₆,
    map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, aeval_X, aeval_C,
    Sum.elim_inl, Sum.elim_inr]
  ring

theorem kw_lrSixUCov_aeval_lrAdd_Z (P Q : Fin 3 → F) :
    aeval (Sum.elim P Q) (kw_lrAdd_Z W) = -(W_F).addZ P Q := by
  simp_N1; ring

theorem kw_lrSixUCov_aeval_lrAdd_vec (P Q : Fin 3 → F) (k : Fin 3) :
    aeval (Sum.elim P Q) (kw_lrAdd_vec W k) = -(W_F).addXYZ P Q k := by
  fin_cases k
  · exact kw_lrSixUCov_aeval_lrAdd_X W F P Q
  · exact kw_lrSixUCov_aeval_lrAdd_Y W F P Q
  · exact kw_lrSixUCov_aeval_lrAdd_Z W F P Q

end N1

section N3

local macro "simp_N3" : tactic =>
  `(tactic| simp only [kw_lrSym_dblX, kw_lrSym_dblY, kw_lrSym_dblZ,
      Projective.dblX, Projective.dblZ, Projective.negDblY, Projective.negY,
      kw_lrSixUCov_WF_a₁, kw_lrSixUCov_WF_a₂, kw_lrSixUCov_WF_a₃, kw_lrSixUCov_WF_a₄,
      kw_lrSixUCov_WF_a₆,
      map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one, aeval_X, aeval_C])

theorem kw_lrSixUCov_aeval_dblZ {P : Fin 3 → F} (hP : (W_F).Equation P) :
    aeval P (kw_lrSym_dblZ W) = (W_F).dblZ P := by
  have heq := (Projective.equation_iff P).mp hP
  simp only [kw_lrSixUCov_WF_a₁, kw_lrSixUCov_WF_a₂, kw_lrSixUCov_WF_a₃,
    kw_lrSixUCov_WF_a₄, kw_lrSixUCov_WF_a₆] at heq
  linear_combination (norm := (simp_N3; ring1))
    (-(3:F) * P 0 * (algebraMap R F W.a₁) - (6:F) * P 1
      - (3:F) * P 2 * (algebraMap R F W.a₃)) * heq

theorem kw_lrSixUCov_aeval_dblX {P : Fin 3 → F} (hP : (W_F).Equation P) :
    aeval P (kw_lrSym_dblX W) = (W_F).dblX P := by
  have heq := (Projective.equation_iff P).mp hP
  simp only [kw_lrSixUCov_WF_a₁, kw_lrSixUCov_WF_a₂, kw_lrSixUCov_WF_a₃,
    kw_lrSixUCov_WF_a₄, kw_lrSixUCov_WF_a₆] at heq
  linear_combination (norm := (simp_N3; ring1))
    ((P 0 * (algebraMap R F W.a₁)^3 + (4:F) * P 0 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂)
      + (9:F) * P 0 * (algebraMap R F W.a₃) + (2:F) * P 1 * (algebraMap R F W.a₁)^2
      + (8:F) * P 1 * (algebraMap R F W.a₂) + P 2 * (algebraMap R F W.a₁)^2 * (algebraMap R F W.a₃)
      + (4:F) * P 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃))) * heq

theorem kw_lrSixUCov_aeval_dblY {P : Fin 3 → F} (hP : (W_F).Equation P) :
    aeval P (kw_lrSym_dblY W) = (W_F).dblY P := by
  have heq := (Projective.equation_iff P).mp hP
  simp only [kw_lrSixUCov_WF_a₁, kw_lrSixUCov_WF_a₂, kw_lrSixUCov_WF_a₃,
    kw_lrSixUCov_WF_a₄, kw_lrSixUCov_WF_a₆] at heq
  rw [show (W_F).dblY P
      = -(W_F).negDblY P - (W_F).a₁ * (W_F).dblX P - (W_F).a₃ * (W_F).dblZ P from
    (W_F).negY_eq _ _ _]
  linear_combination (norm := (simp_N3; ring1))
    ((-(1:F)) * P 0 * (algebraMap R F W.a₁)^4
      - (6:F) * P 0 * (algebraMap R F W.a₁)^2 * (algebraMap R F W.a₂)
      - (8:F) * P 0 * (algebraMap R F W.a₂)^2 - (3:F) * P 0 * (algebraMap R F W.a₄)
      - P 1 * (algebraMap R F W.a₁)^3
      - (4:F) * P 1 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂)
      + (12:F) * P 1 * (algebraMap R F W.a₃)
      - P 2 * (algebraMap R F W.a₁)^3 * (algebraMap R F W.a₃)
      - P 2 * (algebraMap R F W.a₁)^2 * (algebraMap R F W.a₄)
      - (4:F) * P 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₃)
      - (4:F) * P 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₄)
      + (6:F) * P 2 * (algebraMap R F W.a₃)^2 + (9:F) * P 2 * (algebraMap R F W.a₆)) * heq

theorem kw_lrSixUCov_aeval_sym_dbl_vec {P : Fin 3 → F} (hP : (W_F).Equation P) (k : Fin 3) :
    aeval P (![kw_lrSym_dblX W, kw_lrSym_dblY W, kw_lrSym_dblZ W] k)
      = (W_F).dblXYZ P k := by
  fin_cases k
  · exact kw_lrSixUCov_aeval_dblX W F hP
  · exact kw_lrSixUCov_aeval_dblY W F hP
  · exact kw_lrSixUCov_aeval_dblZ W F hP

end N3

section S

theorem kw_lrSixUCov_aeval_weighted_scaling {σ S : Type*} [CommSemiring S] [Algebra R S]
    (w : σ → ℕ) {φ : MvPolynomial σ R} {n : ℕ} (hφ : φ.IsWeightedHomogeneous w n)
    (t : S) (x : σ → S) :
    aeval (fun i => t ^ w i * x i) φ = t ^ n * aeval x φ := by
  classical
  rw [aeval_def, aeval_def]
  simp only [eval₂_eq]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hsum : ∑ i ∈ d.support, d i * w i = n := by
    have h := hφ (mem_support_iff.mp hd)
    rw [Finsupp.weight_apply] at h
    simpa [Finsupp.sum, smul_eq_mul, nsmul_eq_mul] using h
  have hprod : (∏ i ∈ d.support, (t ^ w i * x i) ^ d i)
      = t ^ n * ∏ i ∈ d.support, x i ^ d i := by
    rw [← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [mul_pow, ← pow_mul, Nat.mul_comm (w i) (d i)]
  rw [hprod]; exact mul_left_comm _ _ _

theorem kw_lrSixUCov_aeval_lrSym_scaleR (P : Fin 3 → F) (u : F) (k : Fin 3) :
    aeval (Sum.elim P (u • P)) (kw_lrSym_vec W k)
      = u ^ 2 * aeval (Sum.elim P P) (kw_lrSym_vec W k) := by
  have hwR : (kw_lrSym_vec W k).IsWeightedHomogeneous kw_lrBihom_wR 2 := by
    fin_cases k
    · exact kw_lrSymBihom_lrSymX_wR W
    · exact kw_lrSymBihom_lrSymY_wR W
    · exact kw_lrSymBihom_lrSymZ_wR W
  have h := kw_lrSixUCov_aeval_weighted_scaling (R := R) kw_lrBihom_wR hwR u (Sum.elim P P)
  simp only [kw_lrBihom_wR, Sum.elim_inl, Sum.elim_inr, pow_one, pow_zero, one_mul] at h
  rw [← h]; congr 1; ext m; cases m <;> simp [Pi.smul_apply, smul_eq_mul]

end S

section Five

theorem kw_lrSixUCov_aeval_diag (P : Fin 3 → F) :
    (aeval (Sum.elim P P) : MvPolynomial (Fin 3 ⊕ Fin 3) R →ₐ[R] F)
      = (aeval P).comp (aeval (Sum.elim X X)) := by
  refine MvPolynomial.algHom_ext fun m => ?_
  cases m <;> simp [aeval_X, Sum.elim_inl, Sum.elim_inr]

theorem kw_lrSixUCov_aeval_lrSym_diag (P : Fin 3 → F) (k : Fin 3) :
    aeval (Sum.elim P P) (kw_lrSym_vec W k)
      = 2 * aeval P (![kw_lrSym_dblX W, kw_lrSym_dblY W, kw_lrSym_dblZ W] k) := by
  have h0 := DFunLike.congr_fun (kw_lrSixUCov_aeval_diag (R := R) F P) (kw_lrSym_vec W k)
  rw [AlgHom.comp_apply] at h0
  rw [h0]
  have h2 : (algebraMap R F) (2:R) = (2:F) := map_ofNat _ 2
  fin_cases k
  · show aeval P (aeval (Sum.elim X X) (kw_lrSym_X W)) = 2 * aeval P (kw_lrSym_dblX W)
    rw [kw_lrSym_X_diag, map_mul, aeval_C, h2]
  · show aeval P (aeval (Sum.elim X X) (kw_lrSym_Y W)) = 2 * aeval P (kw_lrSym_dblY W)
    rw [kw_lrSym_Y_diag, map_mul, aeval_C, h2]
  · show aeval P (aeval (Sum.elim X X) (kw_lrSym_Z W)) = 2 * aeval P (kw_lrSym_dblZ W)
    rw [kw_lrSym_Z_diag, map_mul, aeval_C, h2]

end Five

section A

theorem kw_lrSixUCov_psiTens_comp_ev (i j : Fin 3)
    (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F) :
    (Algebra.TensorProduct.productMap ψᵢ ψⱼ).comp (kw_lrChart_ev W i j)
      = aeval (Sum.elim (kw_lrApt_chartEval W F i ψᵢ) (kw_lrApt_chartEval W F j ψⱼ)) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rcases v with m | m
  · simp only [AlgHom.comp_apply, kw_lrChart_ev, aeval_X, Sum.elim_inl, kw_lrChart_inL,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.productMap_apply_tmul,
      map_one, mul_one, kw_lrApt_chartEval]
  · simp only [AlgHom.comp_apply, kw_lrChart_ev, aeval_X, Sum.elim_inr, kw_lrChart_inR,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.productMap_apply_tmul,
      map_one, one_mul, kw_lrApt_chartEval]

theorem kw_lrSixUCov_psiTens_sixU (i j : Fin 3)
    (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F) (l : Fin 3 ⊕ Fin 3) :
    (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l)
      = aeval (Sum.elim (kw_lrApt_chartEval W F i ψᵢ) (kw_lrApt_chartEval W F j ψⱼ))
          (Sum.elim (kw_lrAdd_vec W) (kw_lrSym_vec W) l) := by
  have h := DFunLike.congr_fun (kw_lrSixUCov_psiTens_comp_ev W F i j ψᵢ ψⱼ)
  rcases l with k | k
  · rw [kw_lrSixU_inl, kw_lrChart_u, kw_lrChart_ev'_mk, Sum.elim_inl]
    exact h (kw_lrAdd_vec W k)
  · rw [kw_lrSixU_inr, kw_lrSymChart_u, kw_lrChart_ev'_mk, Sum.elim_inr]
    exact h (kw_lrSym_vec W k)

end A

section W

variable [W.IsElliptic] [Invertible (2:R)]

omit [Invertible (2:R)] in

theorem kw_lrSixUCov_hDelta : algebraMap R F W.Δ ≠ 0 :=
  (W.isUnit_Δ.map (algebraMap R F)).ne_zero

omit [W.IsElliptic] in
include W in

theorem kw_lrSixUCov_two_ne_zero : (2:F) ≠ 0 := by
  have _ := W
  have h := (isUnit_of_invertible (2:R)).map (algebraMap R F)
  rw [map_ofNat] at h
  exact h.ne_zero

theorem kw_lrSixUCoverage_proof : KwLRSixUCoverage W := by
  intro i j
  by_contra hne

  obtain ⟨𝔪, h𝔪max, h𝔪le⟩ := Ideal.exists_le_maximal _ hne
  let κ : Type u := (𝒜 i) ⊗[R] (𝒜 j) ⧸ 𝔪

  letI : Field κ := Ideal.Quotient.field 𝔪
  letI : Algebra R κ := Ideal.Quotient.algebra R
  haveI : Nontrivial κ := GroupWithZero.toNontrivial
  let π : (𝒜 i) ⊗[R] (𝒜 j) →ₐ[R] κ := Ideal.Quotient.mkₐ R 𝔪

  have hz : ∀ l, π (kw_lrSixU W i j l) = 0 := fun l =>
    (Ideal.Quotient.eq_zero_iff_mem).mpr (h𝔪le (Ideal.subset_span ⟨l, rfl⟩))

  let ψᵢ : (𝒜 i) →ₐ[R] κ := π.comp (kw_lrChart_inL W i j)
  let ψⱼ : (𝒜 j) →ₐ[R] κ := π.comp (kw_lrChart_inR W i j)
  set P := kw_lrApt_chartEval W κ i ψᵢ with hPdef
  set Q := kw_lrApt_chartEval W κ j ψⱼ with hQdef
  have hPeq : (kw_lrApt_WF W κ).Equation P := kw_lrApt_chartEval_equation W κ i ψᵢ
  have hQeq : (kw_lrApt_WF W κ).Equation Q := kw_lrApt_chartEval_equation W κ j ψⱼ
  have hPnz : P ≠ 0 := kw_lrApt_chartEval_ne_zero W κ i ψᵢ
  have hQnz : Q ≠ 0 := kw_lrApt_chartEval_ne_zero W κ j ψⱼ
  have hΔ := kw_lrSixUCov_hDelta W κ
  have hPns : (kw_lrApt_WF W κ).Nonsingular P :=
    kw_lrApt_nonsingular_of_equation_of_ne_zero W hΔ hPeq hPnz
  have hQns : (kw_lrApt_WF W κ).Nonsingular Q :=
    kw_lrApt_nonsingular_of_equation_of_ne_zero W hΔ hQeq hQnz

  have hprod : Algebra.TensorProduct.productMap ψᵢ ψⱼ = π := by
    apply Algebra.TensorProduct.ext
    · ext a
      simp only [ψᵢ, kw_lrChart_inL, AlgHom.comp_apply,
        Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
    · ext b
      show (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (1 ⊗ₜ[R] b) = π (1 ⊗ₜ[R] b)
      simp only [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul, ψⱼ,
        kw_lrChart_inR, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply]

  have haev : ∀ l, aeval (Sum.elim P Q) (Sum.elim (kw_lrAdd_vec W) (kw_lrSym_vec W) l) = 0 := by
    intro l
    rw [← kw_lrSixUCov_psiTens_sixU W κ i j ψᵢ ψⱼ l, hprod]
    exact hz l

  have hadd0 : (kw_lrApt_WF W κ).addXYZ P Q = 0 := funext fun k => by
    have := haev (Sum.inl k)
    rw [Sum.elim_inl, kw_lrSixUCov_aeval_lrAdd_vec W κ P Q k] at this
    exact neg_eq_zero.mp this

  have hequiv : P ≈ Q := by
    by_contra hne'
    have hns := Projective.nonsingular_add hPns hQns
    rw [Projective.add_of_not_equiv hne'] at hns
    exact kw_lrApt_ne_zero_of_nonsingular W κ hns hadd0

  obtain ⟨u, huQ⟩ := Setoid.symm hequiv
  have hu : IsUnit (u : κ) := u.isUnit

  have hsymPP : ∀ k, aeval (Sum.elim P P) (kw_lrSym_vec W k) = 0 := by
    intro k
    have hs := haev (Sum.inr k)
    simp only [Sum.elim_inr, ← huQ, Units.smul_def] at hs
    have hsc := kw_lrSixUCov_aeval_lrSym_scaleR W κ P (u : κ) k
    rw [hs] at hsc
    exact (mul_eq_zero.mp hsc.symm).resolve_left (pow_ne_zero 2 hu.ne_zero)

  have hdblP : ∀ k, aeval P (![kw_lrSym_dblX W, kw_lrSym_dblY W, kw_lrSym_dblZ W] k) = 0 := by
    intro k
    have h5 := kw_lrSixUCov_aeval_lrSym_diag W κ P k
    rw [hsymPP k] at h5
    exact (mul_eq_zero.mp h5.symm).resolve_left (kw_lrSixUCov_two_ne_zero W κ)

  have hdbl0 : (kw_lrApt_WF W κ).dblXYZ P = 0 := funext fun k => by
    rw [← kw_lrSixUCov_aeval_sym_dbl_vec W κ hPeq k]; exact hdblP k

  have hdblns : (kw_lrApt_WF W κ).Nonsingular ((kw_lrApt_WF W κ).dblXYZ P) := by
    have h := Projective.nonsingular_add hPns hPns
    rwa [Projective.add_of_equiv (Setoid.refl P)] at h
  exact kw_lrApt_ne_zero_of_nonsingular W κ hdblns hdbl0

end W

end

theorem solution.{u} {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] [Invertible (2 : R)] :
    KwLRSixUCoverage W :=
  kw_lrSixUCoverage_proof W

end S_WeierstrassProjModel_kw_a2_sixu_cov
end P2MW
export P2MW.S_WeierstrassProjModel_kw_a2_sixu_cov (solution)
