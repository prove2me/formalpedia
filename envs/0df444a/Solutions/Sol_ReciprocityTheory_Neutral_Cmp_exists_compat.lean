-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.exists_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:30:32.187651+00:00
-- url     : https://prove2.me/submissions/626c688d-16e0-4d4c-b89b-247fc5e0998d

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Kloc
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ValuationIntCastLtOneIff
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_Compat_valuation_lt_one_iff
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_lies_over_ratPrime
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_mem_comap_ball
import Theorems.Thm_ReciprocityTheory_Gal_exists_smul_eq_of_over


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
open scoped Pointwise
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
variable (F)
include F
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1) :
    ∃ ι : Ω →+* PadicAlgCl p, Compat p A ι := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
  let ι0 : Ω →+* PadicAlgCl p := (IsAlgClosed.lift (R := ℚ) (S := Ω) (M := PadicAlgCl p) : Ω →ₐ[ℚ] PadicAlgCl p)
  let A0 : ValuationSubring Ω := (PadicAlgCl.valued p).v.valuationSubring.comap ι0
  have h0 : Compat p A0 ι0 := mem_comap_ball ι0
  have hp0 : A0.valuation (p : Ω) < 1 := by
    rw [h0.valuation_lt_one_iff, map_natCast]
    have : ((Valued.v (p : PadicAlgCl p) : NNReal) : ℝ) = ‖(p : PadicAlgCl p)‖ := PadicAlgCl.valuation_coe p _
    rw [← this, PadicAlgCl.valuation_p]
    push_cast
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    exact (div_lt_one (by linarith)).mpr hp1
  obtain ⟨g, hg⟩ := exists_smul_eq_of_over (F := ℚ) (lies_over_ratPrime A0 hp0) (lies_over_ratPrime A hp)
  refine ⟨ι0.comp ((g⁻¹ : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω), fun x => ?_⟩
  rw [← hg]
  have := ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (S := A0) (x := g⁻¹ • x)
  rw [smul_inv_smul] at this
  rw [this, h0]
  rfl
end ReciprocityTheory.Neutral.Cmp
