-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_mem_of_forall_pow_mul_mem_0c53fdd73f20
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:23.571626+00:00
-- url     : https://prove2.me/submissions/ee8d4413-6aba-45c2-8ccb-9a6afd0014ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalForms
variable {Ω : Type*} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalForms
theorem _root_.solution (R : Subalgebra ℤ Ω) {K : ℕ} (f c : Fin K → Ω) (hf : ∀ l, f l ∈ R)
    (hc : ∀ l, c l ∈ R) (hsum : ∑ l, c l * f l = 1) {y : Ω} (hy : ∀ l, ∃ n : ℕ, f l ^ n * y ∈ R) :
    y ∈ R := by
  let I : Ideal R :=
    { carrier := {r | (r : Ω) * y ∈ R}
      add_mem' := fun {a b} ha hb => by
        show ((a + b : R) : Ω) * y ∈ R
        rw [Subalgebra.coe_add, add_mul]
        exact add_mem ha hb
      zero_mem' := by
        show ((0 : R) : Ω) * y ∈ R
        simp
      smul_mem' := fun a b hb => by
        show ((a * b : R) : Ω) * y ∈ R
        rw [Subalgebra.coe_mul, mul_assoc]
        exact mul_mem a.2 hb }
  have hrad : ∀ l, (⟨f l, hf l⟩ : R) ∈ I.radical := fun l => by
    obtain ⟨n, hn⟩ := hy l
    refine ⟨n, ?_⟩
    show ((⟨f l, hf l⟩ ^ n : R) : Ω) * y ∈ R
    simpa using hn
  have h1 : (1 : R) ∈ I.radical := by
    have : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩ := Subtype.ext (by simp [hsum])
    rw [this]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hrad l)
  have hI : I = ⊤ := Ideal.radical_eq_top.1 ((Ideal.eq_top_iff_one _).2 h1)
  have : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using this
end GroundTheory.Heights₂.Heights.Inter.DiagonalForms
