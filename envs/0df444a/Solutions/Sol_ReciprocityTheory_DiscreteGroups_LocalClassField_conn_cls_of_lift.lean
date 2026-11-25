-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.conn_cls_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:41.394189+00:00
-- url     : https://prove2.me/submissions/c9afb2b1-72d6-4349-9a10-561b9a629c17

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_FinCoh
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_BrUnrA
import Theorems.Thm_ReciprocityTheory_Coh_admissibility_holds
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_admissible_int_rat_sequence


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function
noncomputable section
variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G']
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (δ)
    (hδ : Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ)
    (t : G → ℚ) (ht : IsLocallyConstant t) (m : (Fin 2 → G) → ℤ)
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) :
    ∃ (x : (trivRep G QZ).coch.X 1) (hx : (trivRep G QZ).coch.d 1 x = 0) (y : (trivRep G ℤ).coch.X 2)
      (hy : (trivRep G ℤ).coch.d 2 y = 0), (∀ g, x.1 g = (QuotientAddGroup.mk (t (g 0)) : QZ)) ∧ y.1 = m ∧
      δ 1 ((trivRep G QZ).coch.cls 1 x hx) = (trivRep G ℤ).coch.cls 2 y hy := by
  have hs := admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)
  have hb : @Continuous _ (trivRep G ℚ).V _ _ (fun g : Fin 1 → G => t (g 0)) :=
    IsLocallyConstant.continuous (Y := (trivRep G ℚ).V) (ht.comp_continuous (continuous_apply 0))
  let b : (trivRep G ℚ).coch.X 1 := ⟨fun g => t (g 0), hb⟩
  have hmc : IsLocallyConstant m := by
    apply IsLocallyConstant.desc m (Int.cast : ℤ → ℚ) _ Int.cast_injective
    have h0 : ((Int.cast : ℤ → ℚ) ∘ m) = fun g => t (g 0) + t (g 1) - t (g 0 * g 1) := funext hm
    rw [h0]
    exact ((ht.comp_continuous (continuous_apply 0)).add (ht.comp_continuous (continuous_apply 1))).sub
      (ht.comp_continuous ((continuous_apply 0).mul (continuous_apply 1)))
  let a : (trivRep G ℤ).coch.X 2 := ⟨m, hmc.continuous⟩
  have hba : (trivRep G ℚ).coch.d 1 b = (trivMap G (Int.castAddHom ℚ)).hom.f 2 a := by
    apply Subtype.ext
    funext g
    show Gal.dn (trivRep G ℚ).rho 1 b.1 g = ((m (fun i => g i) : ℤ) : ℚ)
    rw [LowDeg.dn_one_apply]
    show t (g 1) - t (g 0 * g 1) + t (g 0) = _
    rw [hm]; ring
  have ha : (trivRep G ℤ).coch.d 2 a = 0 := by
    apply hs.inj 3
    rw [map_zero, (trivMap G (Int.castAddHom ℚ)).hom.comm, ← hba, (trivRep G ℚ).coch.dd]
  have hc : (trivRep G QZ).coch.d 1 ((trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom.f 1 b) = 0 := by
    rw [← (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom.comm, hba]
    exact (hs.exact 2 _).2 ⟨a, rfl⟩
  exact ⟨_, hc, a, ha, fun g => rfl, rfl, hδ 1 b a hc ha hba⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
