-- Prove2me | solution 1 for PI.HtPlacesSumWork.plOf_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:27:08.459749+00:00
-- url     : https://prove2.me/submissions/27b1b162-c61d-48b1-af4c-0c50aae1f6d5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero
import Theorems.Thm_PI_HtPlacesSumWork_valPl_wt_add_eq_zero
import Theorems.Thm_PI_HtPlacesSumWork_valPl_mem_vRing
import Theorems.Thm_PI_HtPlacesSumWork_valPl_max_iff
import Theorems.Thm_PI_HtPlacesSumWork_addv_nonneg_iff
import Theorems.Thm_PI_HtPlacesSumWork_addv_pos_iff
import Theorems.Thm_PI_HtPlacesSumWork_plOf_mem
import Theorems.Thm_PI_HtPlacesSumWork_plOf_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HtPlacesSumWork
open IsDedekindDomain WithZero IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
variable (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
variable {O F L}
variable [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
  [FaithfulSMul O L]
namespace PI.HtPlacesSumWork
theorem _root_.solution (Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal}) :
    fres F L (plOf O L Q) = Q.1.inertiaDeg O := by
  have := Q.2
  have : Q.1.LiesOver (maximalIdeal O) := ⟨(valPl_comap Q.1).symm⟩
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal O) Q.1]
  have hwm := plOf_mem (O := O) Q
  set w := plOf O L Q with hw_def
  letI : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field _
  letI : Field (integralClosure O L ⧸ Q.1) := Ideal.Quotient.field _
  let V := vRing w
  let V0 := V.comap (algebraMap F L)
  have hV0 : ∀ x : F, x ∈ V0 ↔ 0 ≤ (w.comap (algebraMap F L)) x := fun x => Iff.rfl
  let φO : O →+* ResidueField V0 := (residue V0).comp ((algebraMap O F).codRestrict V0
    (fun a => by
      show 0 ≤ w (algebraMap F L (algebraMap O F a))
      rw [← IsScalarTower.algebraMap_apply]; exact (hwm.2 a).1))
  have hφO : ∀ a, φO a = 0 ↔ a ∈ maximalIdeal O := by
    intro a
    simp only [φO, RingHom.comp_apply, residue_eq_zero_iff]
    rw [valPl_max_iff V0 _ hV0]
    show 0 < w (algebraMap F L (algebraMap O F a)) ↔ _
    rw [← IsScalarTower.algebraMap_apply]; exact (hwm.2 a).2
  have hsurjO : Function.Surjective φO := by
    intro r
    obtain ⟨y, rfl⟩ := residue_surjective r
    suffices h : ∃ a : O, algebraMap O F a = (y : F) by
      obtain ⟨a, ha⟩ := h; exact ⟨a, congrArg (residue V0) (Subtype.ext ha)⟩
    rcases ValuationRing.isInteger_or_isInteger O (y : F) with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, ha⟩
    · by_cases hy0 : (y : F) = 0
      · exact ⟨0, by rw [map_zero, hy0]⟩
      have hau : IsUnit a := by
        by_contra hna
        have hpos := (hwm.2 a).2.mpr ((mem_maximalIdeal _).mpr hna)
        rw [IsScalarTower.algebraMap_apply O F L, ha, map_inv₀] at hpos
        have hyv : 0 ≤ w (algebraMap F L y) := y.2
        have hne : algebraMap F L (y : F) ≠ 0 := (map_ne_zero _).mpr hy0
        have hs : w (algebraMap F L y)⁻¹ + w (algebraMap F L y) = 0 := by
          rw [← AddValuation.map_mul, inv_mul_cancel₀ hne, AddValuation.map_one]
        exact (ne_of_gt hpos) (valPl_wt_add_eq_zero hpos.le hyv hs)
      obtain ⟨u, rfl⟩ := hau
      refine ⟨↑u⁻¹, ?_⟩
      have h1 : algebraMap O F (↑u⁻¹ : O) * algebraMap O F (u : O) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      rw [ha] at h1
      exact (eq_inv_of_mul_eq_one_left h1).trans (inv_inv _)
  let i : (O ⧸ maximalIdeal O) ≃+* ResidueField V0 :=
    RingEquiv.ofBijective (Ideal.Quotient.lift _ φO (fun a ha => (hφO a).mpr ha))
      ⟨RingHom.injective _, fun r => by
        obtain ⟨a, ha⟩ := hsurjO r
        exact ⟨Ideal.Quotient.mk _ a, by rw [Ideal.Quotient.lift_mk]; exact ha⟩⟩
  let φB : integralClosure O L →+* ResidueField V :=
    (residue V).comp ((algebraMap (integralClosure O L) L).codRestrict V (plOf_nonneg hwm))
  have hQmem : ∀ b, b ∈ Q.1 ↔ 0 < w (algebraMap (integralClosure O L) L b) := fun b =>
    (addv_pos_iff (valPl_hv Q) b).symm
  have hφB : ∀ b ∈ Q.1, φB b = 0 := fun b hb =>
    (residue_eq_zero_iff _).mpr ((valPl_max_iff V w (valPl_mem_vRing w) _).mpr ((hQmem b).mp hb))
  have hsurjB : Function.Surjective φB := by
    intro r
    obtain ⟨y, rfl⟩ := residue_surjective r
    have hyv : (valPl_hv Q).valuation L (y : L) ≤ 1 := (addv_nonneg_iff (valPl_hv Q) _).mp y.2
    obtain ⟨n, d, hnd⟩ :=
      HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (v := valPl_hv Q) (y : L) hyv
    obtain ⟨e, i0, hi0, hde⟩ := Ideal.IsMaximal.exists_inv Q.2 d.2
    refine ⟨n * e, ?_⟩
    have h1 : φB d * φB e = 1 := by
      have : ((d : integralClosure O L) * e) = 1 - i0 := by rw [← hde]; ring
      rw [← map_mul, this, map_sub, map_one, hφB i0 hi0, sub_zero]
    have h2 : φB n = residue V y * φB d := by
      simp only [φB, RingHom.comp_apply]
      rw [← map_mul]; congr 1; apply Subtype.ext; exact hnd.symm
    rw [map_mul, h2, mul_assoc, h1, mul_one]
  let j : (integralClosure O L ⧸ Q.1) ≃+* ResidueField V :=
    RingEquiv.ofBijective (Ideal.Quotient.lift _ φB hφB)
      ⟨RingHom.injective _, fun r => by
        obtain ⟨b, hb⟩ := hsurjB r
        exact ⟨Ideal.Quotient.mk _ b, by rw [Ideal.Quotient.lift_mk]; exact hb⟩⟩
  simp only [fres]
  letI := resAlg (F := F) w
  symm
  refine Algebra.finrank_eq_of_equiv_equiv i j ?_
  apply Ideal.Quotient.ringHom_ext
  ext a
  show ResidueField.map (comapIncl V (algebraMap F L)) (φO a) =
    φB (algebraMap O (integralClosure O L) a)
  simp only [φO, φB, RingHom.comp_apply]
  erw [ResidueField.map_residue]
  apply congrArg (residue V)
  apply Subtype.ext
  show algebraMap F L (algebraMap O F a) =
    algebraMap (integralClosure O L) L (algebraMap O (integralClosure O L) a)
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
end PI.HtPlacesSumWork
