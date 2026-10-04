-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingFiberProfile6814.count_of_interpolants_yukon_2f510440a926
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T00:34:21.390449+00:00
-- url     : https://prove2.me/submissions/61bd98f9-8d40-46e8-b54f-46dd03fde0ce

import Definitions.Def_Yukon_e1a1d0c7582a0e3bb14b33e7

import Definitions.Def_Yukon_0c908ad128e35e387549499c

import Definitions.Def_Yukon_eed5b48fe35aa7de80eb9c3e



import Theorems.Thm_ProximityPrize_SubmissionLower_MovingFiberRegularGeometry6814_regular_seed_bound_yukon_a9931c14043d
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_755f5ab5e1dfa660f8e11f09
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_f3d7314030f7069e4d8b829c
import Definitions.Def_Yukon_c64d4480230f512d8aedf66b
import Definitions.Def_Yukon_ef32f3d6934bd47f231d0d68
import Definitions.Def_Yukon_63a16e90b7724a1f71186e13
set_option backward.isDefEq.respectTransparency.types false
private abbrev ProximityPrize.SubmissionLower.MovingFiberRegularGeometry6814.regular_seed_bound := @ProximityPrize.SubmissionLower.MovingFiberRegularGeometry6814.regular_seed_bound_yukon_a9931c14043d
namespace ProximityPrize.SubmissionLower.MovingFiberTotalAvoidance6814
end MovingFiberTotalAvoidance6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingFiberInterpolation6814
end MovingFiberInterpolation6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingFiberThreeSources6811
end MovingFiberThreeSources6811
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingFiberRegularData6814
end MovingFiberRegularData6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.BoundaryTailProvider
end BoundaryTailProvider
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.LocatorHybridCellsC1
end LocatorHybridCellsC1
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.LocatorHybridCells
end LocatorHybridCells
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN327
end RCN327
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN319
end RCN319
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN260
end RCN260
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN243
end RCN243
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN238
end RCN238
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN234
end RCN234
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN222
end RCN222
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN174
end RCN174
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN156
end RCN156
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN146
end RCN146
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN136
end RCN136
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN135
end RCN135
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN130
end RCN130
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN095
end RCN095
end SubmissionLower
end ProximityPrize
namespace MvPolynomial
end MvPolynomial
namespace ProximityPrize.SubmissionLower.MovingFiberProfile6814
open scoped Classical BigOperators
open MvPolynomial RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN174 RCN222 RCN234 RCN238 RCN243 RCN260 RCN319 RCN327
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider
open MovingFiberRegularData6814 MovingFiberThreeSources6811 MovingFiberInterpolation6814 MovingFiberTotalAvoidance6814
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}
attribute [local instance] _root_.ProximityPrize.SubmissionLower.MovingFiberProfile6814.instDecidableEq_proximityPrize
attribute [local instance] _root_.ProximityPrize.SubmissionLower.MovingFiberProfile6814.instDecidableEq_proximityPrize_1
attribute [local instance] _root_.ProximityPrize.SubmissionLower.MovingFiberProfile6814.instCharPGenericFieldOfNatNat
theorem _root_.solution
    (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (cfg : Fin 3 → Params) (hc : ∀ j, (cfg j).WellFormed)
    (scale : ℕ) (hscale : 0 < scale) (hscaleDiv : ∀ j, 3*(cfg j).d ∣ scale)
    (hfree : ∀ (G : Finset K) (fl : FlagDegree) (S' : RCN159.ResidualStage (polynomialEmbedding K) G
      ⇑nodes 2130706433 80889 fl w (cellSupport S.t S.y S.r)), S'.F = S.F →
      MovingFiberRetainedStage6811.HFreeStage S')
    (P : Fin 3 → SecondJetSupport.Poly (K := K))
    (hP : ∀ j, Interpolant (cfg j).m (cfg j).B (cfg j).s (cfg j).U (cfg j).L (cfg j).k (cfg j).n0 nodes u0 u1 (P j))
    (hL : ∀ j, (cfg j).L < wt residualTotalWeights S.F)
    (hHelperGates : ∀ j, S.PairGates ((cfg j).B+(cfg j).s*(S.r-1))
      ((cfg j).U+(cfg j).s*(S.y-1)) ((cfg j).L+(cfg j).s*(S.t-1)))
    (hCoefficientGates : ∀ j, S.PairGates (cfg j).B (cfg j).U (cfg j).L)
    (hidentity : ∀ f : FlagDegree, scale*131073*80890*
      identityCurveDegree f (cellA S.t S.y) (cellB S.y S.r) (cellS S.r) w ≤
        50184*number cfg scale S.t S.y S.r f) :
    S.seeds.card ≤ bound S cfg scale  := by
  classical
  have hshape (j : Fin 3) : ∀ e ∈ (P j).support, 2*e 1+e 3 ≤ (cfg j).B ∧
      e 1+e 2+e 3 ≤ (cfg j).U ∧ e 1+e 2+e 3+e 4 ≤ (cfg j).L := by
    intro e he
    have h := (hP j).2.1 e he
    exact ⟨h.1,h.2.2.1,h.2.2.2.1⟩
  have hS (j : Fin 3) : ∀ e ∈ (P j).support, e 1 ≤ (cfg j).s := fun e he => ((hP j).2.1 e he).2.1
  have factorial (j : Fin 3) (d : ℕ) (hd : d ≤ (cfg j).s) : (d.factorial : K) ≠ 0 :=
    SecondJetOwnShape.factorial_ne d (hd.trans_lt (hc j).2.2.2.2.2.2.2)
  have alternatives (j : Fin 3) := helper_or_divisibility (P j) S.F
    (cfg j).m (cfg j).B (cfg j).s (cfg j).U (cfg j).L (cfg j).k (cfg j).n0 S.r S.y S.t
    nodes u0 u1 (hP j) S.irreducible (hL j) (hc j).1
    (by have := hc j; unfold Params.WellFormed at this; omega)
    (by have := hc j; unfold Params.WellFormed at this; omega)
    (hc j).2.2.2.1 (hc j).2.2.2.2.1
    (by have := S.rpos; omega) (by have := S.ry; omega) (by have := S.yt; omega)
    S.weights (factorial j)
  by_cases hall : ∀ j : Fin 3, (cfg j).n0 ≤ (SecondJetCoefficients.asS (P j)).natDegree ∧
      ∀ d ≤ (cfg j).k, S.F ∣ SecondJetClearedHelper.helper (P j) S.F ((cfg j).s-d) d
  · let source : Fin 3 → Source S.F := fun j => {
      P := P j, B := (cfg j).B, U := (cfg j).U, T := (cfg j).L,
      s := (cfg j).s, k := (cfg j).k, n0 := (cfg j).n0,
      hS := hS j, hshape := hshape j, hBU := (hc j).2.1,
      hUT := (hc j).2.2.1, hdn := (hc j).2.2.2.2.2.1,
      hB := (hc j).2.2.2.2.2.2.1, hn := (hall j).1, hdiv := (hall j).2 }
    let point := selectedPoint (polynomialEmbedding K) S.selected
    let LC := fun j : Fin 3 => surfaceMap (polynomialEmbedding K) (SecondJetCoefficients.asS (P j)).leadingCoeff
    let Good := S.seeds.filter (fun gamma => ∀ j : Fin 3, MvPolynomial.eval (point gamma) (LC j) ≠ 0)
    let Bad := fun j : Fin 3 => S.seeds.filter (fun gamma => MvPolynomial.eval (point gamma) (LC j) = 0)
    let SG := S.restrict Good (Finset.filter_subset _ _)
    have hnum (f : FlagDegree) : MovingFiberRetainedStage6811.numerator source scale S.t S.y S.r f =
        number cfg scale S.t S.y S.r f := rfl
    have h2 : (2 : GenericField K) ≠ 0 := SecondJetOwnShape.two_ne
    have hf (j : Fin 3) : ((source j).k.factorial : GenericField K) ≠ 0 :=
      SecondJetOwnShape.factorial_ne (cfg j).k (by
        have := hc j; unfold Params.WellFormed at this; omega)
    have hgood : ∀ gamma ∈ SG.seeds, ∀ j,
        MvPolynomial.eval (selectedPoint (polynomialEmbedding K) SG.selected gamma)
          ((source j).leading (polynomialEmbedding K)) ≠ 0 := by
      intro gamma hgamma j
      exact (Finset.mem_filter.mp hgamma).2 j
    have hid (f : FlagDegree) : scale*131073*80890*
        identityCurveDegree f (cellA S.t S.y) (cellB S.y S.r) (cellS S.r) w ≤
          50184*MovingFiberRetainedStage6811.numerator source scale S.t S.y S.r f := by
      rw [hnum]
      exact hidentity f
    have hg := MovingFiberRegularGeometry6814.regular_seed_bound
      SG.D SG.t SG.y SG.r scale SG.Dlow SG.Dchar SG.tbound SG.ybound SG.rbound SG.rpos SG.ry SG.yt
      SG.F SG.irreducible SG.rdegree SG.box SG.support SG.selected SG.seeds Finset.univ nodes u0 u1
      nodes.injective.injOn (by simpa only [Finset.card_univ] using hI)
      SG.degree SG.agreement SG.solution SG.regular SG.noPencil
      source hscale hscaleDiv hfree h2 hf hgood hid
    have hGood : Good.card ≤ number cfg scale S.t S.y S.r (originalCumulativeFlag S.F)/scale := by
      apply (Nat.le_div_iff_mul_le hscale).mpr
      rw [← hnum]
      dsimp only [SG,Data.restrict] at hg
      simpa only [Nat.mul_comm] using hg
    have hBad (j : Fin 3) : (Bad j).card ≤ coefficientCap S (cfg j) := by
      let SB := S.restrict (Bad j) (Finset.filter_subset _ _)
      have hnot := SecondJetTotalAvoidance.leading_not_dvd (P j) (hP j).1 S.F (cfg j).L
        (fun e he => (hshape j e he).2.2) (hL j)
      have hrel : IsRelPrime SB.F (SecondJetCoefficients.asS (P j)).leadingCoeff :=
        S.irreducible.isRelPrime_iff_not_dvd.mpr hnot.2
      apply SB.proper_count_left hI _ (cfg j).B (cfg j).U (cfg j).L hrel
        (SecondJetPairBounds.leading_degree_caps (P j) (cfg j).B (cfg j).U (cfg j).L (hshape j))
        (hCoefficientGates j)
      intro gamma hgamma
      have hz : MvPolynomial.eval (point gamma) (LC j) = 0 := (Finset.mem_filter.mp hgamma).2
      change MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (surfaceMap (polynomialEmbedding K) (SecondJetCoefficients.asS (P j)).leadingCoeff) = 0 at hz
      rw [selectedPoint_surface_evaluation] at hz
      dsimp only [SB,Data.restrict]
      exact (polynomialEmbedding_injective K) (by simpa only [map_zero] using hz)
    have hcover : S.seeds ⊆ Good ∪ Finset.univ.biUnion Bad := by
      intro gamma hgamma
      by_cases hg : ∀ j : Fin 3, MvPolynomial.eval (point gamma) (LC j) ≠ 0
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hgamma,hg⟩)
      · have hex : ∃ j : Fin 3, MvPolynomial.eval (point gamma) (LC j) = 0 := by simpa only [not_forall,not_not] using hg
        obtain ⟨j,hj⟩ := hex
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hgamma,hj⟩⟩)
    have hcard : S.seeds.card ≤ Good.card+∑ j : Fin 3, (Bad j).card :=
      ((Finset.card_le_card hcover).trans (Finset.card_union_le _ _)).trans
        (Nat.add_le_add_left Finset.card_biUnion_le _)
    exact (hcard.trans (Nat.add_le_add hGood (Finset.sum_le_sum (fun j _ => hBad j)))).trans (le_max_right _ _)
  · obtain ⟨j,hj⟩ := not_forall.mp hall
    rcases alternatives j with ⟨Q,hrel,hw,hzero⟩ | hret
    · have hb := S.proper_count_left hI Q ((cfg j).B+(cfg j).s*(S.r-1))
        ((cfg j).U+(cfg j).s*(S.y-1)) ((cfg j).L+(cfg j).s*(S.t-1)) hrel
        (SecondJetPairBounds.degree_caps_of_weights Q _ _ _ hw) (hHelperGates j) (by
          intro gamma hgamma
          apply hzero (S.selected gamma) (S.degree gamma hgamma) gamma
            (Finset.univ.filter (fun i => (S.selected gamma).eval (nodes i) = u0 i+gamma*u1 i))
            (S.agreement gamma hgamma) _ (S.solution gamma hgamma)
          intro i hi
          simpa only [mul_comm] using (Finset.mem_filter.mp hi).2)
      exact (hb.trans (Finset.le_sup (f := fun j : Fin 3 => helperCap S (cfg j)) (Finset.mem_univ j))).trans (le_max_left _ _)
    · exact (hj hret).elim
end
end MovingFiberProfile6814
end SubmissionLower
end ProximityPrize
