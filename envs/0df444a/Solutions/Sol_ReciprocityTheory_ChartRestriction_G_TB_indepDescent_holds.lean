-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.indepDescent_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:48:29.069535+00:00
-- url     : https://prove2.me/submissions/2075e0c2-24ff-4004-aff1-63c7760dd30a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_JInjCore
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_rel_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.TB
private theorem exists_finset_linearIndependent_restrict {F Pt : Type} [Field F] {n : ℕ} (w : Fin n → Pt → F)
    (hw : LinearIndependent F w) :
    ∃ S : Finset Pt, LinearIndependent F (fun i (y : S) => w i y) := by
  classical
  let Ker : Finset Pt → Submodule F (Fin n → F) := fun S =>
    LinearMap.ker (Fintype.linearCombination F (fun i (y : S) => w i y))
  have hex : ∃ m, ∃ S : Finset Pt, Module.finrank F (Ker S) = m := ⟨_, ∅, rfl⟩
  obtain ⟨S, hS⟩ := Nat.find_spec hex
  refine ⟨S, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨i1, hi1⟩ := hne
  have hsum : (∑ i, c i • w i) ≠ 0 := fun h =>
    hi1 (Fintype.linearIndependent_iff.mp hw c h i1)
  obtain ⟨y, hy⟩ : ∃ y, (∑ i, c i • w i) y ≠ 0 := by
    by_contra h
    push Not at h
    exact hsum (funext h)
  have hcS : c ∈ Ker S := by
    change Fintype.linearCombination F (fun i (y : S) => w i y) c = 0
    rw [Fintype.linearCombination_apply]
    exact hc
  have hle : Ker (insert y S) ≤ Ker S := by
    intro d hd
    change Fintype.linearCombination F (fun i (z : (insert y S : Finset Pt)) => w i z) d = 0 at hd
    change Fintype.linearCombination F (fun i (z : S) => w i z) d = 0
    rw [Fintype.linearCombination_apply] at hd ⊢
    funext z
    have h3 := congrFun hd ⟨z, Finset.mem_insert_of_mem z.2⟩
    simpa [Finset.sum_apply] using h3
  have hnot : c ∉ Ker (insert y S) := by
    intro hc'
    change Fintype.linearCombination F (fun i (z : (insert y S : Finset Pt)) => w i z) c = 0 at hc'
    rw [Fintype.linearCombination_apply] at hc'
    have h3 := congrFun hc' ⟨y, Finset.mem_insert_self y S⟩
    apply hy
    simpa [Finset.sum_apply] using h3
  have hlt : Ker (insert y S) < Ker S := lt_of_le_of_ne hle fun h => hnot (h ▸ hcS)
  have h4 := Submodule.finrank_lt_finrank_of_lt hlt
  have h5 := Nat.find_min' hex ⟨insert y S, rfl⟩
  omega
example (h : IndepDescentSt) :
    LinearIndependent ℂ (fun _ : Fin 1 => (fun _ => ((1 : ℚ) : ℂ) : Unit → ℂ)) := by
  have hv : Function.Injective (LinearMap.pi (fun _ : Unit => LinearMap.id) : ℚ →ₗ[ℚ] (Unit → ℚ)) := by
    intro x y hxy
    simpa using congrFun hxy ()
  have := h ℚ ℚ (Rat.castHom ℂ) ℚ Unit (LinearMap.pi fun _ => LinearMap.id) (fun _ y => y)
    (fun _ => Function.bijective_id) (fun g f y => by simp) hv 1 (fun _ => 1)
    (linearIndependent_unique_iff.mpr one_ne_zero)
  simpa using this
end ReciprocityTheory.ChartRestriction.G.TB
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
namespace ReciprocityTheory.ChartRestriction.G.TB
theorem _root_.solution : IndepDescentSt := by
  intro K F _ _ _ _ ι C _ _ Pt v act hbij heq hinj n b hb
  have hwF : LinearIndependent F (fun i => v (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    refine rel_zero v act hbij heq hinj b hb Finset.univ a (fun y => ?_) i (Finset.mem_univ i)
    have h1 := congrFun ha y
    simpa [Finset.sum_apply] using h1
  obtain ⟨S, hS⟩ := exists_finset_linearIndependent_restrict (fun i => v (b i)) hwF
  let : Algebra F ℂ := ι.toAlgebra
  have hC : LinearIndependent ℂ (fun i => algebraMap F ℂ ∘ (fun (y : S) => v (b i) y)) :=
    linearIndependent_algebraMap_comp_iff.mpr hS
  apply LinearIndependent.of_comp (LinearMap.funLeft ℂ ℂ (fun y : S => (y : Pt)))
  exact hC
end ReciprocityTheory.ChartRestriction.G.TB
