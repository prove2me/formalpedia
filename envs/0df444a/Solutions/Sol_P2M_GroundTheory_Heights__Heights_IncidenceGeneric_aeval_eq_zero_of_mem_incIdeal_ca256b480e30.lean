-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_eq_zero_of_mem_incIdeal_ca256b480e30
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:55:21.571127+00:00
-- url     : https://prove2.me/submissions/fffbb64b-4aba-42d9-85fd-776460118c3e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncidenceGeneric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_hom_aeval_926da0c2fb59
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_map_genSubst_b65b00dc21c1

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
theorem _root_.solution (h₁ : FGNullstellensatz.Statement) {F : Type} [Field F]
    {n k : ℕ} (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P)) (hc : ∑ j, c j * genPt P j = 1)
    (g : MvPolynomial (Fin k × Fin n) F) (hg : g ∈ incIdeal P k) :
    aeval (genSubst (genPt P) c) g = 0 := by
  simp only [incIdeal, Ideal.mem_iInf, RingHom.mem_ker] at hg

  let e : MvPolynomial (Fin n ⊕ Fin n) F →ₐ[F] FractionRing (MvPolynomial (Fin n) F ⧸ P) :=
    aeval (Sum.elim (genPt P) c)
  let D := e.range
  have : Algebra.FiniteType F D :=
    Algebra.FiniteType.of_surjective e.rangeRestrict e.rangeRestrict_surjective
  have : Algebra.FiniteType F (MvPolynomial (Fin k × Fin n) D) :=
    Algebra.FiniteType.trans (S := D) inferInstance inferInstance
  let ξD : Fin n → D := fun l => ⟨genPt P l, X (Sum.inl l), by simp [e]⟩
  let cD : Fin n → D := fun l => ⟨c l, X (Sum.inr l), by simp [e]⟩
  have hD : ∑ l, cD l * ξD l = 1 := Subtype.ext (by simpa [ξD, cD] using hc)
  let r : MvPolynomial (Fin k × Fin n) D := aeval (genSubst ξD cD) g
  have hr : map D.val.toRingHom r = aeval (genSubst (genPt P) c) g := by
    show map D.val.toRingHom (aeval (genSubst ξD cD) g) = _
    rw [hom_aeval (F := F) (R := MvPolynomial (Fin k × Fin n) D)
      (T := MvPolynomial (Fin k × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ P))) (map D.val.toRingHom) (fun s => by simp [MvPolynomial.algebraMap_apply])]
    rw [show (fun s => map D.val.toRingHom (genSubst ξD cD s)) = genSubst (genPt P) c from
      funext fun ij => by rw [map_genSubst]; rfl]
  rw [← hr]
  suffices r = 0 by rw [this, map_zero]
  refine h₁ F (MvPolynomial (Fin k × Fin n) D) r fun φ => ?_

  let x : Fin n → AlgebraicClosure F := fun l => φ (C (ξD l))
  let cx : Fin n → AlgebraicClosure F := fun l => φ (C (cD l))
  let w : Fin k × Fin n → AlgebraicClosure F := fun ij => φ (X ij)
  let v : Fin k × Fin n → AlgebraicClosure F :=
    fun ij => w ij - (∑ l, w (ij.1, l) * x l) * cx ij.2
  have hφC : ∀ s : F, φ (C (algebraMap F D s)) = algebraMap F (AlgebraicClosure F) s := fun s => by
    rw [← MvPolynomial.algebraMap_apply, AlgHom.commutes]
  have key : ∑ l, cx l * x l = 1 := by
    calc ∑ l, cx l * x l = φ (C (∑ l, cD l * ξD l)) := by simp [cx, x, map_sum]
      _ = 1 := by rw [hD, map_one, map_one]
  have hφr : φ r = aeval v g := by
    rw [show φ r = φ.toRingHom r from rfl,
      hom_aeval (F := F) φ.toRingHom (fun s => φ.commutes s)]
    rw [show (fun s => φ.toRingHom (genSubst ξD cD s)) = v from funext fun ij => by
      simp [genSubst, v, w, x, cx]]
  have hvI : v ∈ incidence P k := by
    refine ⟨x, fun hx => ?_, fun p hp => ?_, fun i => ?_⟩
    · rw [hx] at key
      simp at key
    · have hpD : aeval ξD p = 0 := by
        apply Subtype.ext
        have h1 := hom_aeval (F := F) D.val.toRingHom (fun s => D.val.commutes s) ξD p
        have h2 := hom_aeval (F := F)
          ((algebraMap (MvPolynomial (Fin n) F ⧸ P) (FractionRing (MvPolynomial (Fin n) F ⧸ P))).comp
            (Ideal.Quotient.mk P)) (fun s => by
              rw [RingHom.comp_apply, Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply]) X p
        simp only [aeval_X_left_apply, RingHom.coe_comp, Function.comp_apply,
          Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero] at h2
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_val] at h1
        rw [h1]
        exact h2.symm
      have h3 := hom_aeval (F := F) (φ.toRingHom.comp C) hφC ξD p
      simp only [hpD, map_zero, RingHom.coe_comp, Function.comp_apply] at h3
      exact h3.symm
    · simp only [v, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, key, mul_one,
        sub_self]
  rw [hφr]
  exact hg v hvI
end GroundTheory.Heights₂.Heights.IncidenceGeneric
