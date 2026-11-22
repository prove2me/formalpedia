-- Prove2me | solution 1 for UpperTheory.Reformulated.B.InvolutionInvariants.invInvariant_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:46.867865+00:00
-- url     : https://prove2.me/submissions/250e8b28-e24b-41be-ab4f-00940ce3ed73

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvolutionInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
attribute [local instance] UpperTheory.Reformulated.B.InvolutionInvariants.instMeasurableSpaceUJ
open MeasureTheory MeasureTheory.Measure in
private theorem UpperTheory.Reformulated.B.InvolutionInvariants.haar_map_inv {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    (h : ∀ g : G, Measure.map (fun x => x * g) (haar : Measure G) = haar) :
    Measure.map (fun x => x⁻¹) (haar : Measure G) = haar := by
  haveI : (haar : Measure G).IsMulRightInvariant := ⟨h⟩
  haveI : (haar : Measure G).Regular := regular_haarMeasure
  obtain ⟨c, hc⟩ : ∃ c : ENNReal, (haar : Measure G).inv = c • haar :=
    ⟨haarScalarFactor (haar : Measure G).inv haar,
      isMulLeftInvariant_eq_smul_of_regular (haar : Measure G).inv haar⟩
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h0 : (haar : Measure G) K ≠ 0 := (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have ht : (haar : Measure G) K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h1 : ∀ s : Set G, (haar : Measure G) s⁻¹ = c * haar s := fun s => by
    rw [← inv_apply, hc, Measure.smul_apply, smul_eq_mul]
  have h2 : c ^ 2 * (haar : Measure G) K = 1 ^ 2 * (haar : Measure G) K := by
    rw [pow_two, mul_assoc, ← h1, ← h1, inv_inv, one_pow, one_mul]
  have h3 : c = 1 :=
    (ENNReal.pow_right_strictMono two_ne_zero).injective ((ENNReal.mul_left_inj h0 ht).1 h2)
  rw [h3, one_smul] at hc
  exact hc
end

set_option autoImplicit false
attribute [local instance] UpperTheory.Reformulated.B.InvolutionInvariants.instMeasurableSpaceUJ
namespace UpperTheory.Reformulated.B.InvolutionInvariants
theorem _root_.solution :
    UpperTheory.Reformulated.B.InvolutionInvariants.Unimodular → UpperTheory.Reformulated.B.InvolutionInvariants.InvInvariant := by
  intro h n ε
  haveI := UpperTheory.Reformulated.B.InvolutionInvariants.aux8 ε
  haveI := UpperTheory.Reformulated.B.InvolutionInvariants.aux9 n ε
  haveI := UpperTheory.Reformulated.B.InvolutionInvariants.laurent_T_neg_one_mul_T_one n ε
  exact UpperTheory.Reformulated.B.InvolutionInvariants.haar_map_inv (G := ↥(UpperTheory.Reformulated.B.InvolutionInvariants.UJ ε)) (h n ε)
end UpperTheory.Reformulated.B.InvolutionInvariants
