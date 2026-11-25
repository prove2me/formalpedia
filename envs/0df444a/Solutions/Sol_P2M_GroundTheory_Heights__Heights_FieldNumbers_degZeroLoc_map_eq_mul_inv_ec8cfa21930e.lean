-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_map_eq_mul_inv_ec8cfa21930e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:33.243803+00:00
-- url     : https://prove2.me/submissions/22d65d1d-d902-4c03-8f4a-0b0914a01780

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsNoetherIntegralClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_chartMonomial_0e5f9b074387
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_not_mem_of_notMem_a3f2513e1571
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_div_mem_degZeroLoc_250927a4bb6d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (hQ : DegZeroLocQuot.Statement.{u})
    (hD : MChartDehomog.Statement.{u}) (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime]
    (hPW : P ≤ W) (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) {Ω : Type*} [Field Ω]
    [Algebra F Ω] (φ : FractionRing (MRing ι F ⧸ P) →ₐ[F] Ω) :
    Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))) ≤ (degZeroLoc P {W}).map φ ∧
      ∀ a ∈ (degZeroLoc P {W}).map φ,
        ∃ r ∈ Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))),
        ∃ d ∈ Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))),
          d ≠ 0 ∧ d⁻¹ ∈ (degZeroLoc P {W}).map φ ∧ a = r * d⁻¹ := by
  have huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P := fun k h => hu k (hPW h)
  have hW1 : ∀ W' ∈ ({W} : Set (Ideal (MRing ι F))), W'.IsPrime := fun W' h => by
    rw [Set.mem_singleton_iff.mp h]; infer_instance
  have hmem : ∀ p, φ (chartMap P u p) ∈
      Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))) := fun p => by
    rw [← aeval_range]
    refine ⟨p, ?_⟩
    change aeval _ p = (φ.comp (chartMap P u)) p
    rw [chartMap, comp_aeval]
    simp
  have hq : ∀ g : MRing ι F, g ∉ P → algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P g) ≠ 0 := fun g hg => by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hg
  refine ⟨Algebra.adjoin_le ?_, fun a ha => ?_⟩
  · rintro _ ⟨v, rfl⟩
    refine Subalgebra.mem_map.mpr ⟨_, div_mem_degZeroLoc P {W} (b := blockWeight ι v)
      (isWeightedHomogeneous_X F _ v) (isWeightedHomogeneous_X F (blockWeight ι) ⟨v.1, u v.1⟩)
      (huP v.1) (fun W' h => by rw [Set.mem_singleton_iff.mp h]; exact hu v.1), ?_⟩
    simp [chartMap]
  obtain ⟨a, haA, rfl⟩ := Subalgebra.mem_map.mp ha
  obtain ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ := hQ F K ι P {W} hW1 a haA
  have hm := chartMonomial_not_mem_of_notMem (F := F) W u hu b
  have hm0 := hq _ fun h => hm (hPW h)
  have hg0 := hq g hgP
  refine ⟨φ (chartMap P u f), hmem f, φ (chartMap P u g), hmem g, ?_, ?_, ?_⟩
  · rw [hD F K ι P u huP g b hg, map_ne_zero]
    exact div_ne_zero hg0 hm0
  · rw [hD F K ι P u huP g b hg, ← map_inv₀, inv_div]
    exact Subalgebra.mem_map.mpr ⟨_, div_mem_degZeroLoc P {W} (isMultiHomog_chartMonomial u b) hg
      hgP (fun W' h => by rw [Set.mem_singleton_iff.mp h]; exact hgW W rfl), rfl⟩
  · rw [hD F K ι P u huP f b hf, hD F K ι P u huP g b hg, ← map_inv₀, ← map_mul]
    congr 1
    field_simp
end GroundTheory.Heights₂.Heights.FieldNumbers
