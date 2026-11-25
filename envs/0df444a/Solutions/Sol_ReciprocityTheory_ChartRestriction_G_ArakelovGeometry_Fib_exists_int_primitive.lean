-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.exists_int_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:37:44.990798+00:00
-- url     : https://prove2.me/submissions/5aa295a2-1774-4963-8e88-059fd0d660fb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}
variable [DecidableEq ι] (G : Gen x e)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open Polynomial IntermediateField
private lemma exists_int_primitive_element_pair {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero E] [Finite (IntermediateField F E)] (α β : E) :
    ∃ n : ℤ, α ∈ F⟮α + (n : E) * β⟯ ∧ β ∈ F⟮α + (n : E) * β⟯ := by
  obtain ⟨a, b, hab, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℤ => F⟮α + (n : E) * β⟯)
  have ha : α + (a : E) * β ∈ F⟮α + (b : E) * β⟯ := by
    rw [← heq]; exact IntermediateField.mem_adjoin_simple_self F _
  have hb : α + (b : E) * β ∈ F⟮α + (b : E) * β⟯ := IntermediateField.mem_adjoin_simple_self F _
  have hne : (a : E) - b ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hab
  have hβ : β ∈ F⟮α + (b : E) * β⟯ := by
    have hsub := sub_mem ha hb
    have h1 : (α + (a : E) * β) - (α + (b : E) * β) = ((a : E) - b) * β := by ring
    rw [h1] at hsub
    have hc : (a : E) - b ∈ F⟮α + (b : E) * β⟯ := sub_mem (intCast_mem _ a) (intCast_mem _ b)
    have := mul_mem (inv_mem hc) hsub
    rwa [← mul_assoc, inv_mul_cancel₀ hne, one_mul] at this
  refine ⟨b, ?_, hβ⟩
  have := sub_mem hb (mul_mem (intCast_mem _ b) hβ)
  simpa using this
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
end
end
end

set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open Polynomial IntermediateField
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero F]
    [CharZero E] [FiniteDimensional F E] {ι : Type*} [Fintype ι] (v : ι → E)
    (hv : adjoin F (Set.range v) = ⊤) : ∃ c : ι → ℤ, F⟮∑ i, (c i : E) * v i⟯ = ⊤ := by
  classical
  haveI hfinite : Finite (IntermediateField F E) := by
    first
    | exact inferInstance
    | exact Field.finite_intermediateField_of_exists_primitive_element F E
        (Field.exists_primitive_element F E)
    | exact Field.finite_intermediateField_of_exists_primitive_element
        (Field.exists_primitive_element F E)
    | exact (Field.exists_primitive_element_iff_finite_intermediateField F E).mp
        ⟨inferInstance, Field.exists_primitive_element F E⟩
    | exact Field.exists_primitive_element_iff_finite_intermediateField.mp
        ⟨inferInstance, Field.exists_primitive_element F E⟩
  have key : ∀ s : Finset ι, ∃ c : ι → ℤ, ∀ i ∈ s, v i ∈ F⟮∑ j, (c j : E) * v j⟯ := by
    intro s
    refine Finset.induction_on s ⟨0, by simp⟩ ?_
    intro j s _ ih
    obtain ⟨c, hc⟩ := ih
    obtain ⟨n, hα, hβ⟩ := exists_int_primitive_element_pair (F := F) (∑ i, (c i : E) * v i) (v j)
    refine ⟨c + Pi.single j n, ?_⟩
    have h2 : ∑ i, (((Pi.single j n : ι → ℤ) i : ℤ) : E) * v i = (n : E) * v j := by
      rw [Fintype.sum_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]
      simp
    have hsum : ∑ i, (((c + Pi.single j n : ι → ℤ) i : ℤ) : E) * v i =
        ∑ i, (c i : E) * v i + (n : E) * v j := by
      simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib, h2]
    rw [hsum]
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hβ
    · exact (IntermediateField.adjoin_simple_le_iff.mpr hα) (hc i hi)
  obtain ⟨c, hc⟩ := key Finset.univ
  refine ⟨c, top_le_iff.mp ?_⟩
  rw [← hv, IntermediateField.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  exact hc i (Finset.mem_univ i)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
