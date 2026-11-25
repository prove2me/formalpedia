-- Prove2me | solution 1 for SpectralRepresentation.exists_spectral_projection_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:55:52.83358+00:00
-- url     : https://prove2.me/submissions/69d8c0f8-4981-4a9c-ab32-c9f2fbce7f48

module
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence
public import Definitions.Def_BasicResults_Spectral_Projection
public import Theorems.Thm_SpectralRepresentation_stepDown_continuous
public import Theorems.Thm_SpectralRepresentation_stepDown_nonneg
public import Theorems.Thm_SpectralRepresentation_stepDown_le_one
public import Theorems.Thm_SpectralRepresentation_stepDown_eq_one
public import Theorems.Thm_SpectralRepresentation_stepDown_antitone
public import Theorems.Thm_SpectralRepresentation_stepDown_ramp_bound
public import Theorems.Thm_SpectralRepresentation_cfc_comm_of_comm
public import Theorems.Thm_SpectralRepresentation_commute_of_tendsto
public import Theorems.Thm_SpectralRepresentation_exists_continuousLinearMap_tendsto
public import Theorems.Thm_SpectralRepresentation_isPositive_of_tendsto
public import Theorems.Thm_SpectralRepresentation_isSymmetric_of_tendsto
public import Theorems.Thm_SpectralRepresentation_reApplyInnerSelf_mono

attribute [local fun_prop] SpectralRepresentation.stepDown_continuous

set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap
open SpectralRepresentation
open Filter Topology
open scoped InnerProductSpace
variable {H₁ H₂ : Type*}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
namespace SpectralRepresentation
theorem _root_.solution [Nontrivial H₁]
    (S : H₁ →L[ℂ] H₂) {c : ℝ} (hc0 : 0 ≤ c) :
    ∃ E : H₁ →L[ℂ] H₁,
      (∀ x : H₁, c * ‖E x‖ ≤ ‖S (E x)‖) ∧ ‖S.comp (1 - E)‖ ≤ c ∧
        ∀ J : H₁ →L[ℝ] H₁, (∀ x, J (((adjoint S).comp S) x) = ((adjoint S).comp S) (J x)) →
          ∀ x, J (E x) = E (J x) := by
  classical
  set P : H₁ →L[ℂ] H₁ := (adjoint S).comp S with hPdef
  have hPsa : IsSelfAdjoint P := by
    rw [hPdef, ContinuousLinearMap.isSelfAdjoint_iff', ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  set T : ℕ → (H₁ →L[ℂ] H₁) := fun n => cfc (stepDown (c ^ 2) n) P with hTdef
  have hTpos : ∀ n, (T n).IsPositive := by
    intro n
    have h0 : (0 : H₁ →L[ℂ] H₁) ≤ T n :=
      cfc_nonneg (fun s _ => stepDown_nonneg (c ^ 2) n s)
    rwa [ContinuousLinearMap.le_def, sub_zero] at h0
  have hTanti : Antitone T := fun m n hmn => by
    show cfc (stepDown (c ^ 2) n) P ≤ cfc (stepDown (c ^ 2) m) P
    exact (cfc_le_iff (stepDown (c ^ 2) n) (stepDown (c ^ 2) m) P
      (stepDown_continuous (c ^ 2) n).continuousOn
      (stepDown_continuous (c ^ 2) m).continuousOn).mpr
      fun s _ => stepDown_antitone (c ^ 2) s hmn
  obtain ⟨E, hEtend⟩ := exists_continuousLinearMap_tendsto hTpos hTanti
  -- `‖S u‖² = re⟪P u, u⟫`.
  have hSnorm : ∀ u : H₁, ‖S u‖ ^ 2 = RCLike.re (⟪P u, u⟫_ℂ) := fun u => by
    rw [hPdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
      inner_self_eq_norm_sq]
  -- `P` is positive, hence its spectrum is nonnegative.
  have hPpos : P.IsPositive := by
    refine ⟨fun x y => ?_, fun u => ?_⟩
    · show ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ
      rw [← ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.isSelfAdjoint_iff'.mp hPsa]
    · rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← hSnorm u]; positivity
  have hP0 : (0 : H₁ →L[ℂ] H₁) ≤ P := by
    rw [ContinuousLinearMap.le_def, sub_zero]; exact hPpos
  -- Composition of two continuous functions of `P` multiplies the symbols.
  have hcomp : ∀ f g : ℝ → ℝ, Continuous f → Continuous g →
      (cfc f P).comp (cfc g P) = cfc (fun s => f s * g s) P := fun f g hf hg => by
    rw [cfc_mul f g P hf.continuousOn hg.continuousOn]; rfl
  have hcompP : ∀ g : ℝ → ℝ, Continuous g →
      P.comp (cfc g P) = cfc (fun s => s * g s) P := fun g hg => by
    rw [cfc_mul (R := ℝ) (fun s : ℝ => s) g P (by fun_prop) hg.continuousOn,
      cfc_id' (R := ℝ) (a := P) (ha := hPsa)]; rfl
  -- `1 - T n` as a continuous function of `P`.
  have hii : ∀ n, (1 : H₁ →L[ℂ] H₁) - T n = cfc (fun s => 1 - stepDown (c ^ 2) n s) P := by
    intro n
    rw [cfc_sub (fun _ => (1 : ℝ)) (stepDown (c ^ 2) n) P (by fun_prop) (by fun_prop),
      cfc_const _ _ hPsa, map_one]
  -- `(1 - T n) ∘ P ∘ (1 - T n)` as a continuous function of `P`.
  have htriple : ∀ n, (1 - T n).comp (P.comp (1 - T n))
      = cfc (fun s => (1 - stepDown (c ^ 2) n s) ^ 2 * s) P := by
    intro n
    rw [hii n, hcompP (fun s => 1 - stepDown (c ^ 2) n s) (by fun_prop),
      hcomp _ _ (by fun_prop) (by fun_prop)]
    congr 1; ext s; ring
  -- Key per-`n` operator bound: `(1 - T n) P (1 - T n) ≤ c² • 1`.
  have hkey : ∀ n, (1 - T n).comp (P.comp (1 - T n)) ≤ c ^ 2 • (1 : H₁ →L[ℂ] H₁) := by
    intro n
    rw [htriple n, show c ^ 2 • (1 : H₁ →L[ℂ] H₁) = cfc (fun _ : ℝ => c ^ 2) P by
      rw [cfc_const _ _ hPsa, Algebra.algebraMap_eq_smul_one],
      cfc_le_iff _ _ P (by fun_prop) (by fun_prop)]
    intro s hs
    have hs0 : 0 ≤ s := spectrum_nonneg_of_nonneg hP0 hs
    have hg0 : 0 ≤ 1 - stepDown (c ^ 2) n s := by
      have := stepDown_le_one (c ^ 2) n s; linarith
    have hg1 : 1 - stepDown (c ^ 2) n s ≤ 1 := by
      have := stepDown_nonneg (c ^ 2) n s; linarith
    rcases le_total s (c ^ 2) with hsc | hsc
    · have h2 : (1 - stepDown (c ^ 2) n s) ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) hs0, hsc]
    · rw [stepDown_eq_one (c ^ 2) n hsc]; simp; positivity
  have hQsa : ∀ n, IsSelfAdjoint (1 - T n) := fun n => by
    rw [ContinuousLinearMap.isSelfAdjoint_iff', map_sub, ContinuousLinearMap.adjoint_one,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp (hTpos n).isSelfAdjoint]
  refine ⟨E, ?_, ?_, ?_⟩
  · -- bound (a): `c · ‖E x‖ ≤ ‖S (E x)‖`.
    set A : H₁ →L[ℂ] H₁ := cfc (fun s => max (s - c ^ 2) 0) P with hA_def
    have hA0 : (0 : H₁ →L[ℂ] H₁) ≤ A := cfc_nonneg fun s _ => le_max_right _ _
    have hEpos : E.IsPositive := isPositive_of_tendsto hTpos hEtend
    have hE0 : (0 : H₁ →L[ℂ] H₁) ≤ E := by
      rw [ContinuousLinearMap.le_def, sub_zero]; exact hEpos
    have hEsymm : (E : H₁ →ₗ[ℂ] H₁).IsSymmetric :=
      isSymmetric_of_tendsto (fun n => (hTpos n).1) hEtend
    have hDcfc : cfc (fun s => s - c ^ 2) P = P - c ^ 2 • (1 : H₁ →L[ℂ] H₁) := by
      rw [cfc_sub (fun s => s) (fun _ => c ^ 2) P (by fun_prop) (by fun_prop),
        cfc_id' (R := ℝ) (a := P) (ha := hPsa), cfc_const _ _ hPsa, Algebra.algebraMap_eq_smul_one]
    have hcfcT : ∀ n, (P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp (T n)
        = cfc (fun s => (s - c ^ 2) * stepDown (c ^ 2) n s) P := fun n => by
      rw [← hDcfc]
      exact hcomp (fun s => s - c ^ 2) (stepDown (c ^ 2) n) (by fun_prop) (by fun_prop)
    have hnorm : Tendsto (fun n => (P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp (T n)) atTop (𝓝 A) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (g := fun n : ℕ => ((n : ℝ) + 1)⁻¹)
        (fun n => norm_nonneg _) (fun n => ?_) ?_
      · have hsub : (P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp (T n) - A
            = cfc (fun s => (s - c ^ 2) * stepDown (c ^ 2) n s - max (s - c ^ 2) 0) P := by
          rw [hcfcT n, hA_def,
            ← cfc_sub (fun s => (s - c ^ 2) * stepDown (c ^ 2) n s) (fun s => max (s - c ^ 2) 0) P
              (by fun_prop) (by fun_prop)]
        rw [hsub]
        exact norm_cfc_le (by positivity)
          fun s _ => by simpa [Real.norm_eq_abs] using stepDown_ramp_bound (c ^ 2) n s
      · have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simp only [one_div] at h
        exact h
    have hDE : (P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp E = A := by
      ext x
      have hb : Tendsto
          (fun n => ‖(P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp (T n) - A‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.mp hnorm
      have h1 : Tendsto (fun n => ((P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp (T n)) x) atTop
          (𝓝 (((P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp E) x)) := by
        simp only [ContinuousLinearMap.comp_apply]
        exact ((P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).continuous.tendsto _).comp (hEtend x)
      have h2 : Tendsto (fun n => ((P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp (T n)) x) atTop (𝓝 (A x)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hb.mul_const ‖x‖)
        rw [← sub_apply]
        exact ((P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp (T n) - A).le_opNorm x
      exact tendsto_nhds_unique h1 h2
    have hEA : E.comp A = A.comp E := by
      refine commute_of_tendsto (fun n => ?_) hEtend
      show (cfc (stepDown (c ^ 2) n) P).comp A = A.comp (cfc (stepDown (c ^ 2) n) P)
      rw [hA_def, hcomp _ _ (by fun_prop) (by fun_prop), hcomp _ _ (by fun_prop) (by fun_prop)]
      congr 1; ext s; ring
    have hEcomp0 : (0 : H₁ →L[ℂ] H₁) ≤ E.comp A := Commute.mul_nonneg hE0 hA0 hEA
    have hEcompPos : (E.comp A).IsPositive := by
      rw [ContinuousLinearMap.le_def, sub_zero] at hEcomp0; exact hEcomp0
    intro x
    have hsymm_eq : ⟪A x, E x⟫_ℂ = ⟪(E.comp A) x, x⟫_ℂ := by
      rw [ContinuousLinearMap.comp_apply]; exact (hEsymm (A x) x).symm
    have hkey_a : 0 ≤ RCLike.re (⟪(P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)) (E x), E x⟫_ℂ) := by
      rw [show (P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)) (E x) = A x by
            rw [← ContinuousLinearMap.comp_apply, hDE],
        hsymm_eq, ← ContinuousLinearMap.reApplyInnerSelf_apply]
      exact hEcompPos.2 x
    have hexpand : RCLike.re (⟪(P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)) (E x), E x⟫_ℂ)
        = ‖S (E x)‖ ^ 2 - c ^ 2 * ‖E x‖ ^ 2 := by
      rw [sub_apply, inner_sub_left, map_sub, ← hSnorm (E x)]
      congr 1
      rw [smul_apply, one_apply_eq_self,
        RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, RCLike.conj_ofReal,
        RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    have hsqle : c ^ 2 * ‖E x‖ ^ 2 ≤ ‖S (E x)‖ ^ 2 := by
      have h := hkey_a; rw [hexpand] at h; linarith
    exact le_of_sq_le_sq (by rw [mul_pow]; exact hsqle) (norm_nonneg _)
  · -- bound (b): `‖S ∘ (1 - E)‖ ≤ c`.
    refine ContinuousLinearMap.opNorm_le_bound _ hc0 fun y => ?_
    rw [ContinuousLinearMap.comp_apply]
    have hrhs : RCLike.re (⟪(c ^ 2 • (1 : H₁ →L[ℂ] H₁)) y, y⟫_ℂ) = c ^ 2 * ‖y‖ ^ 2 := by
      rw [smul_apply, one_apply_eq_self,
        RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, RCLike.conj_ofReal,
        RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    have hpern : ∀ n, RCLike.re (⟪P ((1 - T n) y), (1 - T n) y⟫_ℂ) ≤ c ^ 2 * ‖y‖ ^ 2 := by
      intro n
      have hmono := reApplyInnerSelf_mono (hkey n) y
      rw [ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.reApplyInnerSelf_apply,
        hrhs, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.adjoint_inner_right,
        ContinuousLinearMap.isSelfAdjoint_iff'.mp (hQsa n)] at hmono
      exact hmono
    have hu : Tendsto (fun n => (1 - T n) y) atTop (𝓝 ((1 - E) y)) := by
      simp only [sub_apply, one_apply_eq_self]
      exact tendsto_const_nhds.sub (hEtend y)
    have hlim : RCLike.re (⟪P ((1 - E) y), (1 - E) y⟫_ℂ) ≤ c ^ 2 * ‖y‖ ^ 2 :=
      le_of_tendsto'
        ((RCLike.continuous_re.tendsto _).comp (((P.continuous.tendsto _).comp hu).inner hu)) hpern
    have hsq : ‖S ((1 - E) y)‖ ^ 2 ≤ (c * ‖y‖) ^ 2 := by
      rw [hSnorm ((1 - E) y), mul_pow]; exact hlim
    exact le_of_sq_le_sq hsq (mul_nonneg hc0 (norm_nonneg _))
  · -- commutation: `E` commutes with any `ℝ`-linear `J` commuting with `P = S*S`.
    intro J hJ x
    have hcomm : ∀ n, J (T n x) = T n (J x) := fun n =>
      cfc_comm_of_comm hPsa J hJ (stepDown_continuous (c ^ 2) n) x
    have l1 : Tendsto (fun n => J (T n x)) atTop (𝓝 (J (E x))) :=
      (J.continuous.tendsto _).comp (hEtend x)
    have l2 : Tendsto (fun n => J (T n x)) atTop (𝓝 (E (J x))) := by
      simp only [hcomm]; exact hEtend (J x)
    exact tendsto_nhds_unique l1 l2
end SpectralRepresentation
