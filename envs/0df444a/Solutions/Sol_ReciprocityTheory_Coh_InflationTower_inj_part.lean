-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTower.inj_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:32:39.864025+00:00
-- url     : https://prove2.me/submissions/c3b67932-8e3e-460f-92c5-43bd83ea850a

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_H_mk
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_Is_nonempty
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_Is_anti
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_Is_stab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
noncomputable section
universe u
open Cx
open ReciprocityTheory.Coh.InflationTower
variable {R : Type u} [CommRing R]
variable (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) (c : ∀ m, (A m).X (k + 1))
namespace ReciprocityTheory.Coh.InflationTower
theorem _root_.solution (L : Cx R) (π : ∀ m, Hom L (A m)) (hT : IsTowerLim A τ L π)
    (hA : ∀ m, IsArtinian R ((A m).H k)) (x : L.H (k + 1)) (hx : ∀ m, (π m).H (k + 1) x = 0) :
    x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hP : ∀ m, ∃ b, (A m).d k b = (π m).f (k+1) z := by
    intro m
    have h := hx m
    rw [H_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h
    obtain ⟨b, hb⟩ := h
    exact ⟨b, hb⟩
  let c : ∀ m, (A m).X (k + 1) := fun m => (π m).f (k+1) z
  have hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m := fun m => hT.compat m (k+1) z
  have hstab : ∀ m, ∃ J, ∀ j, J ≤ j → Is A τ k c j m = Is A τ k c J m :=
    Is_stab A τ k c hT.surj hc hP hA
  let J : ℕ → ℕ := fun m => Classical.choose (hstab m)
  have hJ : ∀ m j, J m ≤ j → Is A τ k c j m = Is A τ k c (J m) m := fun m => Classical.choose_spec (hstab m)
  let S : ∀ m, Set ((A m).X k) := fun m => Is A τ k c (J m) m
  have hS : ∀ m j, S m ⊆ Is A τ k c j m := by
    intro m j
    rcases le_total j (J m) with h | h
    · exact Is_anti A τ k c hc m h
    · rw [hJ m j h]
  have hSsurj : ∀ m, ∀ s ∈ S m, ∃ t ∈ S (m+1), (τ m).f k t = s := fun m s hs =>
    hS m (J (m+1) + 1) hs
  have hS0 : (S 0).Nonempty := Is_nonempty A τ k c hP _ _
  let seq : ∀ m, {b : (A m).X k // b ∈ S m} := fun m =>
    Nat.rec (motive := fun m => {b : (A m).X k // b ∈ S m}) ⟨hS0.some, hS0.some_mem⟩
      (fun m s => ⟨Classical.choose (hSsurj m s.1 s.2), (Classical.choose_spec (hSsurj m s.1 s.2)).1⟩) m
  have hseq : ∀ m, (τ m).f k (seq (m+1)).1 = (seq m).1 := fun m =>
    (Classical.choose_spec (hSsurj m (seq m).1 (seq m).2)).2
  obtain ⟨b, hb⟩ := hT.lift k (fun m => (seq m).1) hseq
  have hdb : L.d k b = z := by
    rw [← sub_eq_zero]
    apply hT.ext
    intro m
    have h0 : (A m).d k (seq m).1 = c m := hS m 0 (seq m).2
    rw [map_sub, (π m).comm, hb, h0, sub_self]
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  exact ⟨b, hdb⟩
end ReciprocityTheory.Coh.InflationTower
