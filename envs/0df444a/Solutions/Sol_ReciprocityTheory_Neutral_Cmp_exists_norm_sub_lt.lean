-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.exists_norm_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:30:36.54368+00:00
-- url     : https://prove2.me/submissions/06df9e62-27e9-4f3e-9753-6206fcc325f7

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Kloc
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) (x : Kloc F ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : F, ‖(x : PadicAlgCl p) - ι (algebraMap F Ω y)‖ < ε := by
  classical
  let f : F →+* PadicAlgCl p := ι.comp (algebraMap F Ω)
  let S : Subfield (PadicAlgCl p) := f.fieldRange.topologicalClosure
  have hQ : ∀ c : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) c ∈ S := by
    intro c
    show _ ∈ closure (f.fieldRange : Set (PadicAlgCl p))
    refine Metric.mem_closure_iff.2 fun δ hδ => ?_
    obtain ⟨q, hq⟩ := Padic.rat_dense p c hδ
    refine ⟨f q, RingHom.mem_fieldRange.2 ⟨q, rfl⟩, ?_⟩
    rw [dist_eq_norm, map_ratCast f, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), ← map_sub]
    convert hq using 1
    exact PadicAlgCl.norm_extends ..
  let L : IntermediateField ℚ_[p] (PadicAlgCl p) := S.toIntermediateField hQ
  have hle : Kloc F ι ≤ L := IntermediateField.adjoin_le_iff.2 (by
    rintro _ ⟨y, rfl⟩
    show _ ∈ closure (f.fieldRange : Set (PadicAlgCl p))
    exact subset_closure (RingHom.mem_fieldRange.2 ⟨y, rfl⟩))
  have hx : (x : PadicAlgCl p) ∈ closure (f.fieldRange : Set (PadicAlgCl p)) := hle x.2
  obtain ⟨b, hb1, hb⟩ := Metric.mem_closure_iff.1 hx ε hε
  obtain ⟨y, rfl⟩ := RingHom.mem_fieldRange.1 hb1
  exact ⟨y, by rw [← dist_eq_norm]; exact hb⟩
end ReciprocityTheory.Neutral.Cmp
