-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.jacobian_transformation_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:04:01.195951+00:00
-- url     : https://prove2.me/submissions/e8a557a7-7a51-4d76-821c-59764ef21b5d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_fIdx_lt
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_fIdx_inj
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_atN_of_lt
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_block_entry_zero_zero
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_phi_eq
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_supp_comp
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_det_comp
import Theorems.Thm_P2M_PI_TwChrOne_Pf_reduction_one__0dd7341336c8
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_one
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain Module
noncomputable section
namespace PI.TwistedEisensteinNonvanishing.W
open Loc LocE
section F
end F
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
section Law
variable (P)
variable {P}
variable {q k₀ r c' n' c n kj : ℕ} (hqq : q = qOf P) (h1 : r = kj + c) (h2 : k₀ ≤ kj) (h3 : kj ≤ n)
  (h4 : r ≤ n' + c') (h5 : k₀ ≤ n')
include hqq h1 h2 h3 h4 h5
end Law
private theorem unitV_eq_mul_of_redP_eq_mul (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b d : E} (ha : IsUnit (redP P a))
    (hd : redP P d = redP P a * redP P b) : unitV ξ d = unitV ξ a * unitV ξ b := by
  by_cases hb : IsUnit (redP P b)
  · have hd' : IsUnit (redP P d) := by rw [hd]; exact ha.mul hb
    unfold unitV
    rw [dif_pos hd', dif_pos ha, dif_pos hb, ← Units.val_mul, ← map_mul]
    congr 2
    ext
    simp [hd]
  · have hd' : ¬ IsUnit (redP P d) := by
      rw [hd]
      intro h
      exact hb (isUnit_of_mul_isUnit_right h)
    unfold unitV
    rw [dif_neg hd', dif_neg hb, mul_zero]
end PI.TwistedEisensteinNonvanishing.W
end
end

set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution : JLawP := by
  intro E K _ _ _ _ P hp hq ξ k₀ r c' n' c n kj h1 h2 h3 h4 h5 κ hκ
  classical
  have hk : k₀ ≤ n := le_trans h2 h3
  have hg : κ.symm ∈ JQ P (qOf P) kj n c := (JQ P (qOf P) kj n c).inv_mem hκ
  have hcomp : ∀ y : HomE E (n' + c') (n + c), κ.toLinearMap ∘ₗ (κ.symm.toLinearMap ∘ₗ y) = y := by
    intro y
    ext x i
    simp

  obtain ⟨M0, hM0⟩ : ∃ M0 : Matrix (Fin (n + c)) (Fin (n' + c')) E, M0 = fun i j =>
      if ∃ t, t < r ∧ i.1 = fIdx k₀ c n t ∧ j.1 = fIdx k₀ c' n' t then 1 else 0 := ⟨_, rfl⟩
  have hent0 : ∀ p p', p < n + c → p' < n' + c' →
      entB (qOf P) k₀ c' n' c n 0 0 (Matrix.toLin' M0) p p' = if p' < r ∧ p = p' then 1 else 0 := by
    intro p p' hp hp'
    have hfp := fIdx_lt hk hp
    have hfp' := fIdx_lt (c := c') h5 hp'
    rw [block_entry_zero_zero, atN_of_lt _ hfp, Matrix.toLin'_apply]
    rw [show (Matrix.mulVec M0 (eN E (n' + c') (fIdx k₀ c' n' p'))) ⟨fIdx k₀ c n p, hfp⟩ =
        M0 ⟨fIdx k₀ c n p, hfp⟩ ⟨fIdx k₀ c' n' p', hfp'⟩ by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single ⟨fIdx k₀ c' n' p', hfp'⟩]
      · simp [eN]
      · intro b _ hb
        simp only [eN]
        rw [if_neg (fun h => hb (Fin.ext h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h]
    rw [hM0]
    beta_reduce
    by_cases hc : p' < r ∧ p = p'
    · rw [if_pos hc, if_pos ⟨p', hc.1, by show fIdx k₀ c n p = fIdx k₀ c n p'; rw [hc.2], rfl⟩]
    · rw [if_neg hc, if_neg]
      rintro ⟨t, ht, e1, e2⟩
      have i1 := fIdx_inj hp (by omega : t < n + c) hk e1
      have i2 := fIdx_inj hp' (by omega : t < n' + c') h5 e2
      exact hc ⟨by omega, by omega⟩
  have hy0 : CondQ P (qOf P) k₀ r c' n' c n (Matrix.toLin' M0) := by
    refine ⟨fun p p' hp hp' => ?_, fun p p' hrp hp hp' => ?_⟩
    · rw [hent0 p p' hp hp']
      split_ifs
      · exact ia_one (P := P)
      · exact ia_zero (P := P)
    · rw [hent0 p p' hp (by omega), if_neg (by omega), zero_div]
      exact ia_zero (P := P)
  have hA0 : AYm (qOf P) k₀ r c' n' c n (Matrix.toLin' M0) = 1 := by
    ext s t
    simp only [AYm, Matrix.of_apply, Matrix.one_apply]
    rw [hent0 _ _ (by have := s.isLt; omega) (by have := t.isLt; omega)]
    by_cases hst : s = t
    · subst hst
      simp
    · rw [if_neg, if_neg hst]
      rintro ⟨-, h⟩
      exact hst (Fin.ext h)
  have hr1 : redP P (1 : E) = 1 := PI.TwChrOne.Pf.reduction_one₂ P

  have hd1 := det_comp rfl h1 h2 h3 h4 h5 hp hg hy0
  have hd2 := det_comp rfl h1 h2 h3 h4 h5 hp hκ (supp_comp rfl h1 h2 h3 h4 h5 hg hy0)
  rw [hcomp, hd1, hA0, Matrix.det_one, hr1, mul_one] at hd2
  have hGA : IsUnit (redP P (GA k₀ r c n κ.symm).det) :=
    ⟨⟨_, _, by rw [mul_comm]; exact hd2.symm, hd2.symm⟩, rfl⟩
  refine ⟨unitV ξ (GA k₀ r c n κ.symm).det, ?_, fun y => ?_⟩
  · unfold unitV
    rw [dif_pos hGA]
    exact Units.ne_zero _
  rw [phi_eq, phi_eq]
  by_cases hy : CondQ P (qOf P) k₀ r c' n' c n y
  · have hgy := supp_comp rfl h1 h2 h3 h4 h5 hg hy
    rw [if_pos hgy, if_pos hy]
    exact unitV_eq_mul_of_redP_eq_mul ξ hGA (det_comp rfl h1 h2 h3 h4 h5 hp hg hy)
  · have hgy : ¬ CondQ P (qOf P) k₀ r c' n' c n (κ.symm.toLinearMap ∘ₗ y) := by
      intro h'
      apply hy
      have h6 := supp_comp rfl h1 h2 h3 h4 h5 hκ h'
      rwa [hcomp y] at h6
    rw [if_neg hgy, if_neg hy, mul_zero]
end PI.TwistedEisensteinNonvanishing.W
