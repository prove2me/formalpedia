-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.exists_integral_completion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:29:12.966058+00:00
-- url     : https://prove2.me/submissions/56840d70-837b-45b4-ae2b-4af62b900aa6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate
import Definitions.Def_ReciprocityTheory_SemistableReduction_DegAddHolds
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_pi_single_one_mem_hStd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {b : Fin k → Fin r → K} (hb : LinearIndependent K b) (hk : k ≤ r) :
    ∃ c : Fin (r - k) → Fin r → K, (∀ j, c j ∈ hStd K r) ∧ LinearIndependent K (Fin.append b c) ∧
      ∀ x, x ∈ Submodule.span K (Set.range (Fin.append b c)) := by
  classical
  set W := Submodule.span K (Set.range b) with hW
  let T := W.mkQ
  let v : Fin r → (Fin r → K) ⧸ W := fun i => T (Pi.single i 1)
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent K (Set.range v)
  have hspan_top : Submodule.span K (Set.range v) = ⊤ := by
    have e1 : Set.range v = T '' Set.range (Pi.basisFun K (Fin r)) := by
      ext y
      simp [v, Set.mem_image, Set.mem_range]
    rw [e1, Submodule.span_image, (Pi.basisFun K (Fin r)).span_eq, Submodule.map_top,
      Submodule.range_mkQ]
  have hsfin : s.Finite := (Set.finite_range v).subset hs
  haveI : Fintype s := hsfin.fintype
  have hcard : Fintype.card s = r - k := by
    have h1 : Fintype.card s = Module.finrank K ((Fin r → K) ⧸ W) := by
      rw [← Set.toFinset_card, ← finrank_span_set_eq_card hli, hspan, hspan_top, finrank_top]
    have hWk : Module.finrank K W = k := by rw [hW, finrank_span_eq_card hb, Fintype.card_fin]
    have h2 := Submodule.finrank_quotient_add_finrank W
    rw [hWk, Module.finrank_fin_fun] at h2
    omega
  let eq : Fin (r - k) ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  have hidx : ∀ y : s, ∃ i, v i = y := fun y => hs y.2
  choose idx hidx' using hidx
  let c : Fin (r - k) → Fin r → K := fun j => Pi.single (idx (eq j)) 1
  have hTc : ∀ j, T (c j) = (eq j : (Fin r → K) ⧸ W) := fun j => hidx' (eq j)
  have hTli : LinearIndependent K (fun j => T (c j)) := by
    rw [show (fun j => T (c j)) = Subtype.val ∘ eq from funext hTc]
    exact hli.comp eq eq.injective
  have hTspan : ∀ y, y ∈ Submodule.span K (Set.range fun j => T (c j)) := by
    intro y
    have e2 : Set.range (fun j => T (c j)) = s := by
      ext z
      constructor
      · rintro ⟨j, rfl⟩; show T (c j) ∈ s; rw [hTc]; exact (eq j).2
      · intro hz; exact ⟨eq.symm ⟨z, hz⟩, by show T (c (eq.symm ⟨z, hz⟩)) = z; rw [hTc]; simp⟩
    rw [e2, hspan, hspan_top]
    trivial
  refine ⟨c, fun j => pi_single_one_mem_hStd _, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    simp only [Fin.append_left, Fin.append_right] at hg
    have h1 : ∑ j, g (Fin.natAdd k j) • T (c j) = 0 := by
      have := congrArg T hg
      rw [map_add, map_zero, map_sum, map_sum] at this
      have h0 : ∑ i, T (g (Fin.castAdd (r - k) i) • b i) = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      rw [h0, zero_add] at this
      simpa using this
    have h2 := Fintype.linearIndependent_iff.mp hTli _ h1
    have h3 : ∑ i, g (Fin.castAdd (r - k) i) • b i = 0 := by
      rw [← hg]
      simp [h2]
    have h4 := Fintype.linearIndependent_iff.mp hb _ h3
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · exact h4 i
    · exact h2 j
  · intro x
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hTspan (T x))
    have hT0 : T (x - ∑ j, β j • c j) = 0 := by
      rw [map_sub, map_sum]
      simp only [map_smul]
      rw [hβ, sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hT0
    obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hT0
    have hx : x = ∑ i, α i • b i + ∑ j, β j • c j := by rw [hα]; abel
    rw [hx]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span ⟨Fin.castAdd (r - k) i, Fin.append_left b c i⟩
    · exact Submodule.subset_span ⟨Fin.natAdd k j, Fin.append_right b c j⟩
end ReciprocityTheory.ChartRestriction.G.T0
