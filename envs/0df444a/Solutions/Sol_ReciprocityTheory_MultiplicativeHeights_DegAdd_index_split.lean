-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DegAdd.index_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:33:10.063468+00:00
-- url     : https://prove2.me/submissions/97a36013-7370-47c5-9885-f7558d5798ba

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_Lemmata_GeneralBFactBisAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_range_fin_append

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DegAdd
open NumberField
namespace ReciprocityTheory.MultiplicativeHeights.DegAdd
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hb : ∀ i, b i ∈ L) (hc : ∀ j, c j ∈ L)
    (hdis : Disjoint (Submodule.span K (Set.range b)) (Submodule.span K (Set.range c))) :
    (Submodule.span (𝓞 K) (Set.range (Fin.append b c))).toAddSubgroup.relIndex L.toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex (satSub L b).toAddSubgroup *
      (satSub L b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex
        L.toAddSubgroup := by
  set Sb := Submodule.span (𝓞 K) (Set.range b)
  set Sc := Submodule.span (𝓞 K) (Set.range c)
  set S := satSub L b
  have hA : Submodule.span (𝓞 K) (Set.range (Fin.append b c)) = Sb ⊔ Sc := by
    rw [range_fin_append, Submodule.span_union]
  have hSbS : Sb ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨hb i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hScL : Sc ≤ L := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hc j
  have hSL : S ≤ L := inf_le_left
  have hmeet : ∀ x, x ∈ Sb ⊔ Sc → x ∈ S → x ∈ Sb := by
    intro x hx1 hx2
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx1
    have hyK : y ∈ Submodule.span K (Set.range b) :=
      Submodule.span_le_restrictScalars (𝓞 K) K _ hy
    have hzK : z ∈ Submodule.span K (Set.range c) :=
      Submodule.span_le_restrictScalars (𝓞 K) K _ hz
    have hxK : y + z ∈ Submodule.span K (Set.range b) := hx2.2
    have hz' : z ∈ Submodule.span K (Set.range b) := by
      have h := Submodule.sub_mem _ hxK hyK
      simpa using h
    have hz0 : z = 0 := Submodule.disjoint_def.mp hdis z hz' hzK
    simpa [hz0] using hy
  have hinf : (Sb ⊔ Sc).toAddSubgroup ⊓ S.toAddSubgroup = Sb.toAddSubgroup := by
    ext x
    constructor
    · intro h
      exact hmeet x (AddSubgroup.mem_inf.mp h).1 (AddSubgroup.mem_inf.mp h).2
    · intro h
      exact AddSubgroup.mem_inf.mpr ⟨(le_sup_left : Sb ≤ Sb ⊔ Sc) h, hSbS h⟩
  have key : (Sb ⊔ Sc).toAddSubgroup.relIndex (S ⊔ Sc).toAddSubgroup =
      Sb.toAddSubgroup.relIndex S.toAddSubgroup := by
    have hsup : (S ⊔ Sc).toAddSubgroup = S.toAddSubgroup ⊔ (Sb ⊔ Sc).toAddSubgroup := by
      rw [← Submodule.sup_toAddSubgroup, ← sup_assoc, sup_eq_left.mpr hSbS]
    rw [hsup, AddSubgroup.relIndex_sup_right, ← hinf, AddSubgroup.inf_relIndex_right]
  have le1 : (Sb ⊔ Sc).toAddSubgroup ≤ (S ⊔ Sc).toAddSubgroup :=
    fun x hx => (sup_le_sup_right hSbS Sc) hx
  have le2 : (S ⊔ Sc).toAddSubgroup ≤ L.toAddSubgroup := fun x hx => (sup_le hSL hScL) hx
  rw [hA, ← AddSubgroup.relIndex_mul_relIndex _ _ _ le1 le2, key]
end ReciprocityTheory.MultiplicativeHeights.DegAdd
