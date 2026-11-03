-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P18.partialTrace_coherentInformation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-02T20:18:29.660824+00:00
-- url     : https://prove2.me/submissions/83f411c3-4810-4c9f-bfc0-76d89496aad4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18
import Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_purification_independence
import Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_complementary_mutual_identity
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_pureState_marginalEntropy_eq
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_partialTrace_isTraceClassChannel
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_traceSecond_isDensity
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_generalizedRelativeEntropy_swapCoeff

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable


namespace QAlgorithms.Papers.Independent.Claimed50.P18

/-- Products of ℓ² coordinates along two injective reindexings are summable. -/
theorem pcti_summable {K T : Type} (u : Hilbert K) (e1 e2 : T → K)
    (h1 : Function.Injective e1) (h2 : Function.Injective e2) :
    Summable (fun t => u (e1 t) * star (u (e2 t))) := by
  have hs : Summable (fun k => ‖u k‖ ^ 2) := by
    have := (lp.memℓp u).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    simpa using this
  refine Summable.of_norm_bounded ((hs.comp_injective h1).add (hs.comp_injective h2)) ?_
  intro t
  rw [norm_mul, norm_star]
  have := two_mul_le_add_sq ‖u (e1 t)‖ ‖u (e2 t)‖
  simp only [Function.comp]
  nlinarith [norm_nonneg (u (e1 t)), norm_nonneg (u (e2 t))]

theorem pcti_marginals {A B C : Type} (u : Hilbert ((A × B) × C)) :
    let X := rankOne u
    traceSecond (dropMiddle (associateRight X)) = traceSecond (traceSecond X) ∧
    traceFirst (dropMiddle (associateRight X)) = traceFirst X ∧
    traceSecond (traceFirst (associateRight X)) = traceFirst (traceSecond X) ∧
    traceFirst (traceFirst (associateRight X)) = traceFirst X := by
  intro X
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext x y
  · have hs := pcti_summable u (fun t : B × C => ((x, t.1), t.2)) (fun t : B × C => ((y, t.1), t.2))
      (fun s t h => by simp_all [Prod.ext_iff]) (fun s t h => by simp_all [Prod.ext_iff])
    show ∑' c : C, ∑' b : B, u ((x, b), c) * star (u ((y, b), c)) =
      ∑' b : B, ∑' c : C, u ((x, b), c) * star (u ((y, b), c))
    exact Summable.tsum_comm (f := fun b c => u ((x, b), c) * star (u ((y, b), c))) hs
  · have hs := pcti_summable u (fun t : A × B => (t, x)) (fun t : A × B => (t, y))
      (fun s t h => by simp_all [Prod.ext_iff]) (fun s t h => by simp_all [Prod.ext_iff])
    show ∑' a : A, ∑' b : B, u ((a, b), x) * star (u ((a, b), y)) =
      ∑' p : A × B, u (p, x) * star (u (p, y))
    exact (Summable.tsum_prod (f := fun p : A × B => u (p, x) * star (u (p, y))) hs).symm
  · have hs := pcti_summable u (fun t : A × C => ((t.1, x), t.2)) (fun t : A × C => ((t.1, y), t.2))
      (fun s t h => by simp_all [Prod.ext_iff]) (fun s t h => by simp_all [Prod.ext_iff])
    show ∑' c : C, ∑' a : A, u ((a, x), c) * star (u ((a, y), c)) =
      ∑' a : A, ∑' c : C, u ((a, x), c) * star (u ((a, y), c))
    exact Summable.tsum_comm (f := fun a c => u ((a, x), c) * star (u ((a, y), c))) hs
  · have hs := pcti_summable u (fun t : A × B => (t, x)) (fun t : A × B => (t, y))
      (fun s t h => by simp_all [Prod.ext_iff]) (fun s t h => by simp_all [Prod.ext_iff])
    show ∑' b : B, ∑' a : A, u ((a, b), x) * star (u ((a, b), y)) =
      ∑' p : A × B, u (p, x) * star (u (p, y))
    rw [Summable.tsum_prod (f := fun p : A × B => u (p, x) * star (u (p, y))) hs]
    exact Summable.tsum_comm (f := fun a b => u ((a, b), x) * star (u ((a, b), y))) hs

theorem pcti_ereal_toReal (x y : ℝ≥0∞) (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    (((x.toReal - y.toReal : ℝ)) : EReal) = (x : EReal) - (y : EReal) := by
  rw [EReal.coe_sub, EReal.coe_ennreal_toReal hx, EReal.coe_ennreal_toReal hy]

theorem pcti_ereal_neg (d h : ℝ≥0∞) (hh : h ≠ ⊤) :
    (d : EReal) - (h : EReal) = -((h : EReal) - (d : EReal)) := by
  rw [← EReal.coe_ennreal_toReal hh]
  by_cases hd : d = ⊤
  · subst hd; simp
  · rw [← EReal.coe_ennreal_toReal hd, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_neg, neg_sub]

theorem pcti_boundedConjugation_id {I : Type} (X : Matrix I I ℂ) :
    boundedConjugation (LinearIsometry.id : Hilbert I →ₗᵢ[ℂ] Hilbert I).toContinuousLinearMap X = X := by
  ext p q
  simp only [boundedConjugation, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.id_apply,
    lp.single_apply]
  rw [tsum_eq_single p]
  · rw [tsum_eq_single q]
    · simp
    · intro j hj; simp [hj]
  · intro i hi; simp [Pi.single_apply, hi]

theorem pcti_main {A B C : Type}
    [Countable A] [Countable B] [Countable C] (rho : PureState ((A × B) × C))
    (hC : homogeneousEntropy (traceFirst rho.val.coefficients) < ⊤) :
    let ab := traceSecond rho.val.coefficients
    let ac := dropMiddle (associateRight rho.val.coefficients)
    let bc := traceFirst (associateRight rho.val.coefficients)
    let c := traceFirst rho.val.coefficients
    let dAC := generalizedRelativeEntropy ac (productCoeff (traceSecond ac) c)
    let dBC := generalizedRelativeEntropy bc (productCoeff (traceSecond bc) c)
    ((finiteInputCoherentInfo ab (@traceSecond A B) : EReal) =
        (mutualInformation ab (@traceSecond A B) : EReal) - (homogeneousEntropy ab : EReal) ∧
      (mutualInformation ab (@traceSecond A B) : EReal) - (homogeneousEntropy ab : EReal) =
        (dAC : EReal) - (homogeneousEntropy c : EReal) ∧
      (dAC : EReal) - (homogeneousEntropy c : EReal) = -finiteFirstConditionalEntropy (swapCoeff ac)) ∧
    ((finiteInputCoherentInfo ab (@traceFirst A B) : EReal) =
        (mutualInformation ab (@traceFirst A B) : EReal) - (homogeneousEntropy ab : EReal) ∧
      (mutualInformation ab (@traceFirst A B) : EReal) - (homogeneousEntropy ab : EReal) =
        (dBC : EReal) - (homogeneousEntropy c : EReal) ∧
      (dBC : EReal) - (homogeneousEntropy c : EReal) = -finiteFirstConditionalEntropy (swapCoeff bc)) := by
  intro ab ac bc c dAC dBC
  obtain ⟨u, -, hu⟩ := rho.property
  obtain ⟨m1, m2, m3, m4⟩ := pcti_marginals u
  rw [← hu] at m1 m2 m3 m4
  have m1' : traceSecond ac = traceSecond ab := m1
  have m2' : traceFirst ac = c := m2
  have m3' : traceSecond bc = traceFirst ab := m3
  have m4' : traceFirst bc = c := m4
  -- the AB marginal as a state, and the two partial-trace channels
  let sAB : State (A × B) := ⟨ab, traceSecond_isDensity rho.val⟩
  let TrB : Channel (A × B) A := ⟨traceSecond, partialTrace_isTraceClassChannel.1⟩
  let TrA : Channel (A × B) B := ⟨traceFirst, partialTrace_isTraceClassChannel.2⟩
  have hp : Purifies rho sAB.coefficients := rfl
  -- Remark 1 with the given purification (reference C)
  have hIB : mutualInformation ab (@traceSecond A B) = dAC := by
    have := purification_independence sAB TrB rho hp
    rw [← this]
    show _ = generalizedRelativeEntropy ac (productCoeff (traceSecond ac) c)
    rw [m1']
    rfl
  have hIA : mutualInformation ab (@traceFirst A B) = dBC := by
    have := purification_independence sAB TrA rho hp
    rw [← this]
    show _ = generalizedRelativeEntropy bc (productCoeff (traceSecond bc) c)
    rw [m3']
    rfl
  -- entropies: H(AB) = H(C) < ⊤ and both informations are finite by (22)
  have hHab : homogeneousEntropy ab = homogeneousEntropy c := pureState_marginalEntropy_eq rho
  have hcf : homogeneousEntropy c ≠ ⊤ := hC.ne
  have habf : homogeneousEntropy ab ≠ ⊤ := hHab ▸ hcf
  have hcomp : Complementary TrB TrA :=
    ⟨LinearIsometry.id, fun r => by
      simp only [pcti_boundedConjugation_id]; exact ⟨rfl, rfl⟩⟩
  have h22 := complementary_mutual_identity sAB TrB TrA hcomp
  have h2f : 2 * homogeneousEntropy ab ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) habf
  have hIBf : mutualInformation ab (@traceSecond A B) ≠ ⊤ := by
    intro h; apply h2f; rw [← h22]; exact (ENNReal.add_eq_top.2 (Or.inl h))
  have hIAf : mutualInformation ab (@traceFirst A B) ≠ ⊤ := by
    intro h; apply h2f; rw [← h22]; exact (ENNReal.add_eq_top.2 (Or.inr h))
  -- conditional entropies of the swapped marginals
  have hcondAC : finiteFirstConditionalEntropy (swapCoeff ac) =
      (homogeneousEntropy c : EReal) - (dAC : EReal) := by
    have hprod : productCoeff (traceSecond (swapCoeff ac)) (traceFirst (swapCoeff ac)) =
        swapCoeff (productCoeff (traceSecond ac) c) := by
      ext p q
      simp only [productCoeff, swapCoeff]
      rw [← m2']
      exact mul_comm _ _
    unfold finiteFirstConditionalEntropy
    rw [hprod, generalizedRelativeEntropy_swapCoeff]
    congr 3
  have hcondBC : finiteFirstConditionalEntropy (swapCoeff bc) =
      (homogeneousEntropy c : EReal) - (dBC : EReal) := by
    have hprod : productCoeff (traceSecond (swapCoeff bc)) (traceFirst (swapCoeff bc)) =
        swapCoeff (productCoeff (traceSecond bc) c) := by
      ext p q
      simp only [productCoeff, swapCoeff]
      rw [← m4']
      exact mul_comm _ _
    unfold finiteFirstConditionalEntropy
    rw [hprod, generalizedRelativeEntropy_swapCoeff]
    congr 3
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact pcti_ereal_toReal _ _ hIBf habf
  · rw [hIB, hHab]
  · rw [hcondAC]; exact pcti_ereal_neg _ _ hcf
  · exact pcti_ereal_toReal _ _ hIAf habf
  · rw [hIA, hHab]
  · rw [hcondBC]; exact pcti_ereal_neg _ _ hcf

end QAlgorithms.Papers.Independent.Claimed50.P18

open QAlgorithms.Papers.Independent.Claimed50.P18 in
theorem solution {A B C : Type}
    [Countable A] [Countable B] [Countable C] (rho : PureState ((A × B) × C))
    (hC : homogeneousEntropy (traceFirst rho.val.coefficients) < ⊤) :
    let ab := traceSecond rho.val.coefficients
    let ac := dropMiddle (associateRight rho.val.coefficients)
    let bc := traceFirst (associateRight rho.val.coefficients)
    let c := traceFirst rho.val.coefficients
    let dAC := generalizedRelativeEntropy ac (productCoeff (traceSecond ac) c)
    let dBC := generalizedRelativeEntropy bc (productCoeff (traceSecond bc) c)
    ((finiteInputCoherentInfo ab (@traceSecond A B) : EReal) =
        (mutualInformation ab (@traceSecond A B) : EReal) - (homogeneousEntropy ab : EReal) ∧
      (mutualInformation ab (@traceSecond A B) : EReal) - (homogeneousEntropy ab : EReal) =
        (dAC : EReal) - (homogeneousEntropy c : EReal) ∧
      (dAC : EReal) - (homogeneousEntropy c : EReal) = -finiteFirstConditionalEntropy (swapCoeff ac)) ∧
    ((finiteInputCoherentInfo ab (@traceFirst A B) : EReal) =
        (mutualInformation ab (@traceFirst A B) : EReal) - (homogeneousEntropy ab : EReal) ∧
      (mutualInformation ab (@traceFirst A B) : EReal) - (homogeneousEntropy ab : EReal) =
        (dBC : EReal) - (homogeneousEntropy c : EReal) ∧
      (dBC : EReal) - (homogeneousEntropy c : EReal) = -finiteFirstConditionalEntropy (swapCoeff bc)) :=
  pcti_main rho hC
