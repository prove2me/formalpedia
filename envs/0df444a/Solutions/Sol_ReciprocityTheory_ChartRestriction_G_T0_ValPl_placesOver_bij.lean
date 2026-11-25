-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValPl.placesOver_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:24:10.067906+00:00
-- url     : https://prove2.me/submissions/63cbceeb-87b3-44af-be67-96437be4e2a2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_addv_pos_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_eq_addv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_algebraMap_OL_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_addv_mem_placesOver

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValPl
open IsDedekindDomain WithZero IsLocalRing
variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
variable (O F L)
include F
namespace ReciprocityTheory.ChartRestriction.G.T0.ValPl
theorem _root_.solution : ∃ e : HeightOneSpectrum (integralClosure O L) ≃ PlacesOver O L,
    ∀ v, (e v : AddValuation L (WithTop ℤ)) = addv L v := by
  classical
  let f : HeightOneSpectrum (integralClosure O L) → PlacesOver O L :=
    fun v => ⟨addv L v, addv_mem_placesOver v⟩
  have hinj : Function.Injective f := by
    intro v v' hvv
    have h : addv L v = addv L v' := congrArg Subtype.val hvv
    ext b
    rw [← addv_pos_iff (L := L) v, ← addv_pos_iff (L := L) v', h]
  have hsurj : Function.Surjective f := by
    rintro ⟨w, hw⟩
    have h0 : ∀ b : integralClosure O L, 0 ≤ w (algebraMap (integralClosure O L) L b) := by
      intro b
      have hb : IsIntegral O (algebraMap (integralClosure O L) L b) := b.2
      letI : Algebra O (vRing w) :=
        ((algebraMap O L).codRestrict (vRing w) (fun x => (hw.2 x).1)).toAlgebra
      haveI : IsScalarTower O (vRing w) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      have hb' : IsIntegral (vRing w) (algebraMap (integralClosure O L) L b) := hb.tower_top
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb'
      rw [← hy]
      exact y.2
    let Qw : Ideal (integralClosure O L) :=
      { carrier := {b | 0 < w (algebraMap (integralClosure O L) L b)}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
          exact lt_of_lt_of_le (lt_min ha hb) (w.map_add _ _)
        zero_mem' := by simp
        smul_mem' := fun c b hb => by
          simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, AddValuation.map_mul] at hb ⊢
          exact lt_of_lt_of_le hb (le_add_of_nonneg_left (h0 c)) }
    have hprime : Qw.IsPrime := by
      refine ⟨fun htop => ?_, fun {a b} hab => ?_⟩
      · have h1 : (1 : integralClosure O L) ∈ Qw := htop ▸ Submodule.mem_top
        simp [Qw] at h1
      · change 0 < w (algebraMap _ L (a * b)) at hab
        rw [map_mul, AddValuation.map_mul] at hab
        by_contra hno
        rw [not_or] at hno
        have ha : w (algebraMap _ L a) = 0 :=
          le_antisymm (not_lt.1 (hno.1 : ¬ 0 < w (algebraMap _ L a))) (h0 a)
        have hb : w (algebraMap _ L b) = 0 :=
          le_antisymm (not_lt.1 (hno.2 : ¬ 0 < w (algebraMap _ L b))) (h0 b)
        rw [ha, hb, add_zero] at hab
        exact lt_irrefl _ hab
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hne : Qw ≠ ⊥ := by
      intro hbot
      have hmem : algebraMap O (integralClosure O L) ϖ ∈ Qw := by
        show 0 < w (algebraMap (integralClosure O L) L (algebraMap O _ ϖ))
        rw [← IsScalarTower.algebraMap_apply]
        exact ((hw.2 ϖ).2).2 hϖ.not_isUnit
      rw [hbot, Ideal.mem_bot] at hmem
      have : (algebraMap O L) ϖ = 0 := by
        rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L, hmem, map_zero]
      exact hϖ.ne_zero (algebraMap_OL_injective (F := F) (by rw [this, map_zero]))
    refine ⟨⟨Qw, hprime, hne⟩, Subtype.ext ?_⟩
    exact (eq_addv _ w hw.1 h0 (fun s => Iff.rfl)).symm
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun v => rfl⟩
end ReciprocityTheory.ChartRestriction.G.T0.ValPl
