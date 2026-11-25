-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncidenceGeneric_mem_incIdeal_of_aeval_eq_zero_a50fea87279f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:14:49.065871+00:00
-- url     : https://prove2.me/submissions/5fcc95b0-e8f3-44a7-a854-d2cb66cb8630

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncidenceGeneric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_map_genSubst_b65b00dc21c1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_genSubst_eq_zero_of_9eb668df8ce3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IncidenceGeneric
namespace GroundTheory.Heights₂.Heights.IncidenceGeneric
theorem _root_.solution {F : Type*} [Field F] {n k : ℕ}
    (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (c : Fin n → (FractionRing (MvPolynomial (Fin n) F ⧸ P)))
    (g : MvPolynomial (Fin k × Fin n) F) (h : aeval (genSubst (genPt P) c) g = 0) :
    g ∈ incIdeal P k := by
  simp only [incIdeal, Ideal.mem_iInf, RingHom.mem_ker]
  intro v hv
  obtain ⟨x, hx0, hxP, hvx⟩ := hv
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx0
  set a : (MvPolynomial (Fin n) F ⧸ P) := Ideal.Quotient.mk P (X j) with ha_def
  have ha : a ≠ 0 := by
    intro h0
    apply hj
    simpa using hxP _ (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hξj : genPt P j ≠ 0 := by
    show algebraMap (MvPolynomial (Fin n) F ⧸ P) (FractionRing (MvPolynomial (Fin n) F ⧸ P)) a ≠ 0
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff]

  obtain ⟨c', hc'_def⟩ : ∃ c' : Fin n → (FractionRing (MvPolynomial (Fin n) F ⧸ P)), c' = Pi.single j (genPt P j)⁻¹ := ⟨_, rfl⟩
  have hc' : ∑ l, c' l * genPt P l = 1 := by
    rw [Finset.sum_eq_single j (fun l _ hl => by rw [hc'_def, Pi.single_eq_of_ne hl, zero_mul])
      (fun h => absurd (Finset.mem_univ j) h), hc'_def, Pi.single_eq_same, inv_mul_cancel₀ hξj]
  have h' : aeval (genSubst (genPt P) c') g = 0 := aeval_genSubst_eq_zero_of _ c' c hc' g h

  let L := Localization.Away a
  have hθu : IsUnit (algebraMap (MvPolynomial (Fin n) F ⧸ P) (FractionRing (MvPolynomial (Fin n) F ⧸ P)) a) := isUnit_iff_ne_zero.mpr hξj
  let θ : L →+* (FractionRing (MvPolynomial (Fin n) F ⧸ P)) := IsLocalization.Away.lift a hθu
  have hθinj : Function.Injective θ := by
    unfold θ IsLocalization.Away.lift
    rw [IsLocalization.lift_injective_iff]
    intro y z
    rw [(IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors ha)).eq_iff,
      (IsFractionRing.injective (MvPolynomial (Fin n) F ⧸ P) (FractionRing (MvPolynomial (Fin n) F ⧸ P))).eq_iff]
  let ev : (MvPolynomial (Fin n) F ⧸ P) →+* AlgebraicClosure F :=
    Ideal.Quotient.lift P (aeval x).toRingHom (fun p hp => hxP p hp)
  have hev : ∀ p, ev (Ideal.Quotient.mk P p) = aeval x p := fun p => rfl
  have hψu : IsUnit (ev a) := isUnit_iff_ne_zero.mpr (by rw [ha_def, hev, aeval_X]; exact hj)
  let ψ : L →+* AlgebraicClosure F := IsLocalization.Away.lift a hψu
  let ξL : Fin n → L := fun l => algebraMap (MvPolynomial (Fin n) F ⧸ P) L (Ideal.Quotient.mk P (X l))
  let cL : Fin n → L := Pi.single j (IsLocalization.Away.invSelf a)
  have hθξ : ∀ l, θ (ξL l) = genPt P l := fun l => IsLocalization.Away.lift_eq a hθu _
  have hθinv : θ (IsLocalization.Away.invSelf a) = (genPt P j)⁻¹ := by
    have := congrArg θ (IsLocalization.Away.mul_invSelf (S := L) a)
    rw [map_mul, map_one, show θ (algebraMap (MvPolynomial (Fin n) F ⧸ P) L a) = genPt P j from hθξ j] at this
    exact eq_inv_of_mul_eq_one_right this
  have hθc : ∀ l, θ (cL l) = c' l := by
    intro l
    by_cases hl : l = j
    · subst hl; simp [cL, hc'_def, hθinv]
    · simp [cL, hc'_def, Pi.single_eq_of_ne hl]
  have hψξ : ∀ l, ψ (ξL l) = x l := fun l => by
    rw [IsLocalization.Away.lift_eq, hev, aeval_X]

  let f₀ : F →+* MvPolynomial (Fin k × Fin n) L :=
    C.comp ((algebraMap (MvPolynomial (Fin n) F ⧸ P) L).comp (algebraMap F (MvPolynomial (Fin n) F ⧸ P)))
  let Q := eval₂ f₀ (genSubst ξL cL) g
  have hQ : map θ Q = aeval (genSubst (genPt P) c') g := by
    rw [eval₂_comp_left, aeval_def]
    congr 1
    · ext r
      simp [f₀, θ, MvPolynomial.algebraMap_apply, IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n) F ⧸ P) (FractionRing (MvPolynomial (Fin n) F ⧸ P))]
    · funext ij
      simp only [Function.comp_apply, map_genSubst, hθξ, hθc]
  have hQ0 : Q = 0 := by
    apply map_injective θ hθinj
    rw [hQ, h', map_zero]
  have hvQ : eval₂Hom ψ v Q = aeval v g := by
    rw [eval₂_comp_left, aeval_def]
    congr 1
    · ext r
      simp only [f₀, RingHom.coe_comp, Function.comp_apply, eval₂Hom_C]
      rw [IsLocalization.Away.lift_eq, ← Ideal.Quotient.mk_algebraMap, hev, AlgHom.commutes]
    · funext ij
      simp [genSubst, hψξ, hvx ij.1]
  rw [← hvQ, hQ0, map_zero]
end GroundTheory.Heights₂.Heights.IncidenceGeneric
