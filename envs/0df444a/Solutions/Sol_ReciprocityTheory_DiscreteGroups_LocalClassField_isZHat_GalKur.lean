-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.isZHat_GalKur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:11:39.8378+00:00
-- url     : https://prove2.me/submissions/d3cbdf5e-9bbb-41d8-a01b-099dd76458e7

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kn_le_Kur
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_le_Kur
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_degLK_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_of_frobK_fixed
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_subG_eq
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finiteDimensional_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isOpen_subG
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_anti
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_le_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) :
    IsZHat (GalLK p K (MaximalUnramifiedExtension p K)) (frobLK p K (MaximalUnramifiedExtension p K)) := by
  constructor
  · set C : Subgroup (GalLK p K (MaximalUnramifiedExtension p K)) :=
      (Subgroup.zpowers (frobLK p K (MaximalUnramifiedExtension p K))).topologicalClosure with hC
    have hCcl : IsClosed (C : Set (GalLK p K (MaximalUnramifiedExtension p K))) := Subgroup.isClosed_topologicalClosure _
    set H : Subgroup (GK p K) := C.comap (QuotientGroup.mk' (subG p K (MaximalUnramifiedExtension p K))) with hH
    have hHcl : IsClosed (H : Set (GK p K)) := hCcl.preimage continuous_quot_mk
    obtain ⟨M, hKM, hM⟩ := exists_subG_eq H hHcl
    have hNH : subG p K (MaximalUnramifiedExtension p K) ≤ subG p K M := by
      rw [hM]
      intro σ hσ
      change (QuotientGroup.mk σ : GalLK p K (MaximalUnramifiedExtension p K)) ∈ C
      rw [(QuotientGroup.eq_one_iff σ).2 hσ]
      exact C.one_mem
    have hMur : M ≤ MaximalUnramifiedExtension p K := by
      have := (subG_le_iff hKM).1 hNH
      rwa [sup_eq_right.2 le_Kur] at this
    have hfr : frobK p K ∈ subG p K M := by
      rw [hM]
      change frobLK p K (MaximalUnramifiedExtension p K) ∈ C
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _)
    have hMK : M ≤ K := fun x hx => mem_of_frobK_fixed hK (hMur hx) (hfr x hx)
    have htop : H = ⊤ := by
      rw [← hM, eq_top_iff]
      intro σ _ x hx
      exact σ.commutes ⟨x, hMK hx⟩
    have hCtop : C = ⊤ := by
      rw [eq_top_iff]
      intro g _
      obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
      have : σ ∈ H := by rw [htop]; trivial
      exact this
    rw [dense_iff_closure_eq]
    have h1 : closure (Subgroup.zpowers (frobLK p K (MaximalUnramifiedExtension p K)) : Set (GalLK p K (MaximalUnramifiedExtension p K))) =
        (C : Set (GalLK p K (MaximalUnramifiedExtension p K))) := rfl
    rw [h1, hCtop]
    rfl
  · intro k hk
    refine ⟨(subG p K (Kn p K k)).map (QuotientGroup.mk' (subG p K (MaximalUnramifiedExtension p K))), ?_, ?_⟩
    · exact QuotientGroup.isOpenMap_coe _ (isOpen_subG (finiteDimensional_Kn p K hK hk))
    · rw [Subgroup.index_map, QuotientGroup.ker_mk', sup_eq_left.2 (subG_anti (Kn_le_Kur hk)),
        MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _), Subgroup.index_top, mul_one]
      exact degLK_Kn hK hk
end ReciprocityTheory.DiscreteGroups.LocalClassField
