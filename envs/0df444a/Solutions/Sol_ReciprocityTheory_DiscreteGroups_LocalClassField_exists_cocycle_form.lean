-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_cocycle_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:47:37.888959+00:00
-- url     : https://prove2.me/submissions/479f2d39-726d-4dca-a9b1-53e035cb19e2

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_FinCoh
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_BrUnrA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_conn_cls_of_lift
import Theorems.Thm_ReciprocityTheory_Coh_Cx_exists_cls
import Theorems.Thm_ReciprocityTheory_Coh_admissibility_holds
import Theorems.Thm_ReciprocityTheory_Coh_lES_holds
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_admissible_int_rat_sequence
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_conn_int_rat_bijective


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
theorem _root_.solution [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (c : (trivRep G ℤ).H 2) :
    ∃ (t : G → ℚ) (m : (Fin 2 → G) → ℤ) (y : (trivRep G ℤ).coch.X 2) (hy : (trivRep G ℤ).coch.d 2 y = 0),
      IsLocallyConstant t ∧ (∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) ∧ y.1 = m ∧
      c = (trivRep G ℤ).coch.cls 2 y hy := by
  have s := admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)
  obtain ⟨⟨δ, h1, -⟩, -⟩ := lES_holds ℤ _ _ _ _ _ s
  obtain ⟨c', rfl⟩ := (conn_int_rat_bijective G δ h1 1 one_pos).2 c
  obtain ⟨x, hx, rfl⟩ := Cx.exists_cls c'
  let sec : QZ → ℚ := Function.surjInv (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range)
  have hsec : ∀ q : QZ, (QuotientAddGroup.mk (sec q) : QZ) = q :=
    Function.surjInv_eq (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range)
  let t : G → ℚ := fun g => sec (x.1 ![g])
  have hx1 : Continuous x.1 := x.2
  have ht : IsLocallyConstant t := by
    have h0 : IsLocallyConstant fun g : G => x.1 ![g] :=
      (IsLocallyConstant.iff_continuous _).2 (hx1.comp (continuous_pi fun i => by fin_cases i; exact continuous_id))
    exact h0.comp sec
  obtain ⟨χ, hχ⟩ : ∃ χ : G → QZ, ∀ g, χ g = x.1 ![g] := ⟨fun g => x.1 ![g], fun _ => rfl⟩
  have ht' : ∀ g, (QuotientAddGroup.mk (t g) : QZ) = χ g := fun g => (hsec _).trans (hχ g).symm
  have hcoc : ∀ g : Fin 2 → G, χ (g 1) - χ (g 0 * g 1) + χ (g 0) = 0 := by
    intro g
    have h0 := congrFun (LowDeg.dn_eq_zero _ hx) g
    rw [LowDeg.dn_one_apply] at h0
    rw [hχ, hχ, hχ]
    exact h0
  have hex : ∀ g : Fin 2 → G, ∃ k : ℤ, (k : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := by
    intro g
    have h0 : (QuotientAddGroup.mk (t (g 0) + t (g 1) - t (g 0 * g 1)) : QZ) = 0 := by
      rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add, ht', ht', ht', ← hcoc g]
      abel
    exact (QuotientAddGroup.eq_zero_iff _).1 h0
  choose m hm using hex
  obtain ⟨x', hx', y, hy, e1, e2, e3⟩ := conn_cls_of_lift δ h1 t ht m hm
  have hxx : x' = x := by
    apply Subtype.ext
    funext g
    exact (e1 g).trans ((ht' (g 0)).trans ((hχ (g 0)).trans (congrArg x.1 (by funext i; fin_cases i; rfl))))
  subst hxx
  exact ⟨t, m, y, hy, ht, hm, e2, e3⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
