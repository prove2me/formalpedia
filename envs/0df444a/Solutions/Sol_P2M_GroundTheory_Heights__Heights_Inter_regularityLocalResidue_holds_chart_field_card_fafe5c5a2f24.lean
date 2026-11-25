-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_chart_field_card_fafe5c5a2f24
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:32:51.216804+00:00
-- url     : https://prove2.me/submissions/1b75bce7-1a4e-4f3e-9323-9ef9aeef4e30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_map_27d117848aaf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_comap_map_eq_1f7d21450244
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chart_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chart_isField


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
theorem _root_.solution {W : Ideal (MRing ι)} [W.IsPrime] (hWmh : IsMultiHomogIdeal W) {T : ∀ k, ι k}
    (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι) ∉ W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞))
    (p : ℕ) [Fact p.Prime] (hp : (C (p : ℤ) : MRing ι) ∈ W) :
    IsField (MRing ι ⧸ (W ⊔ Ideal.span (Set.range fun k => (X ⟨k, T k⟩ : MRing ι) - 1))) ∧
      Finite (MRing ι ⧸ (W ⊔ Ideal.span (Set.range fun k => (X ⟨k, T k⟩ : MRing ι) - 1))) ∧
      Nat.card (MRing ι ⧸ (W ⊔ Ideal.span (Set.range fun k => (X ⟨k, T k⟩ : MRing ι) - 1))) =
        p ^ (Module.length ℤ (MRing ι ⧸ (W ⊔ Ideal.span (Set.range fun k => (X ⟨k, T k⟩ : MRing ι) - 1)))).toNat := by
  classical
  set J := W ⊔ Ideal.span (Set.range fun k => (X ⟨k, T k⟩ : MRing ι) - 1) with hJ
  let π : MRing ι →+* MRingOver (ZMod p) ι := MvPolynomial.map (Int.castRingHom (ZMod p))
  have hπ : Function.Surjective π := MvPolynomial.map_surjective _ ZMod.intCast_surjective
  have hker : RingHom.ker π ≤ W := by
    rw [MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton, Ideal.span_le,
      Set.singleton_subset_iff]
    exact hp
  set Wb := W.map π
  have hWbp : Wb.IsPrime := Ideal.map_isPrime_of_surjective hπ hker
  have hXb : ∀ k, (X ⟨k, T k⟩ : MRingOver (ZMod p) ι) ∉ Wb := by
    intro k h
    have h' : π (X ⟨k, T k⟩) ∈ Wb := by rwa [show π (X ⟨k, T k⟩) = X ⟨k, T k⟩ from map_X _ _]
    have := Ideal.mem_comap.mpr h'
    rw [comap_map_eq π hπ W hker] at this
    exact hT k this
  have hWb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF Wb 0 := by
    refine ⟨⟨hWbp, ?_, fun k => ⟨T k, hXb k⟩⟩, ?_⟩
    · obtain ⟨S, hS, hWS⟩ := hWmh
      refine ⟨π '' S, ?_, ?_⟩
      · rintro _ ⟨f, hf, rfl⟩
        obtain ⟨a, ha⟩ := hS f hf
        exact ⟨a, isMultiHomog_map _ ha⟩
      · show W.map π = _
        rw [hWS, Ideal.map_span]
    · rw [← ringKrullDim_eq_of_ringEquiv (quotEquivMap π hπ W hker), hdim]
  have hmapJ : J.map π = ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal Wb T := by
    rw [hJ, Ideal.map_sup, Ideal.map_span, ← Set.range_comp]
    unfold ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal
    have e : (⇑π ∘ fun k => (X ⟨k, T k⟩ : MRing ι) - 1) = fun k => (X ⟨k, T k⟩ : MRingOver (ZMod p) ι) - 1 := by
      funext k
      simp [π]
    rw [e]
  let eC : MRing ι ⧸ J ≃+* MRingOver (ZMod p) ι ⧸ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal Wb T :=
    (quotEquivMap π hπ J (hker.trans le_sup_left)).trans (Ideal.quotEquivOfEq hmapJ)
  have hF := ReciprocityTheory.ChartRestriction.G.AI.I1.chart_isField hWb (j := T) hXb
  have hfin := ReciprocityTheory.ChartRestriction.G.AI.I1.chart_finite hWb (j := T) hXb
  have : Finite (MRingOver (ZMod p) ι ⧸ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal Wb T) := Module.finite_of_finite (ZMod p)
  refine ⟨MulEquiv.isField hF eC.toMulEquiv, Finite.of_equiv _ eC.symm.toEquiv, ?_⟩
  have hlen : Module.length ℤ (MRing ι ⧸ J) =
      Module.finrank (ZMod p) (MRingOver (ZMod p) ι ⧸ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal Wb T) := by
    rw [LinearEquiv.length_eq eC.toAddEquiv.toIntLinearEquiv,
      Module.length_eq_of_surjective (R := ZMod p) ZMod.intCast_surjective, Module.length_eq_finrank]
  haveI := Fintype.ofFinite (MRingOver (ZMod p) ι ⧸ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal Wb T)
  rw [hlen, ENat.toNat_natCast, Nat.card_congr eC.toEquiv, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
end GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
