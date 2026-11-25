-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall.exists_unit_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:08:00.665357+00:00
-- url     : https://prove2.me/submissions/d313bb0e-58e8-43c0-b8c6-b63503fe8731

import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsTorusPointOneLeNormSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_UnitPointLiftBall
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_UnitPointLiftBall_lift_ball
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_UnitPointLiftBall_eval_lift
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_infinite_residues


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall
open MvPolynomial ReciprocityTheory.MultiplicativeHeights
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall
theorem _root_.solution (K₀ : Subfield K) (hK₀ : ResidueFieldInfiniteOn (K₀ : Set K))
    (P δ : MvPolynomial ι K) (hP : ∀ μ, ‖coeff μ P‖ ≤ 1) (hP1 : ∃ μ, ‖coeff μ P‖ = 1)
    (hδ : ∀ μ, ‖coeff μ δ‖ ≤ 1) (hδ1 : ∃ μ, ‖coeff μ δ‖ = 1) :
    ∃ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ = 1) ∧ ‖eval x P‖ = 1 ∧ ‖eval x δ‖ = 1 := by
  classical
  obtain ⟨PO, hPO⟩ := lift_ball P hP
  obtain ⟨δO, hδO⟩ := lift_ball δ hδ
  have mem_le : ∀ a : unitBallRing K, ‖(a : K)‖ ≤ 1 := fun a => by
    have h := a.2
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply] at h
    exact_mod_cast h
  have unit_of_norm : ∀ a : unitBallRing K, ‖(a : K)‖ = 1 → IsUnit a := by
    intro a ha
    have ha0 : (a : K) ≠ 0 := by
      intro h
      rw [h, norm_zero] at ha
      exact zero_ne_one ha
    have hinv : (a : K)⁻¹ ∈ unitBallRing K := by
      rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
      have h1 : ‖(a : K)⁻¹‖ = 1 := by rw [norm_inv, ha, inv_one]
      exact_mod_cast h1.le
    have hm : a * ⟨_, hinv⟩ = 1 := Subtype.ext (by simp [ha0])
    first
      | exact IsUnit.of_mul_eq_one _ hm
      | exact IsUnit.of_mul_eq_one hm
      | exact ⟨⟨a, ⟨_, hinv⟩, hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  have norm_of_unit : ∀ a : unitBallRing K, IsUnit a → ‖(a : K)‖ = 1 := by
    intro a ha
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    have h1 : (a : K) * (b : K) = 1 := by
      have := congrArg (fun z : unitBallRing K => (z : K)) hb
      simpa using this
    have hn : ‖(a : K)‖ * ‖(b : K)‖ = 1 := by rw [← norm_mul, h1, norm_one]
    have ha1 := mem_le a
    have hb1 := mem_le b
    refine le_antisymm ha1 ?_
    nlinarith [norm_nonneg (a : K), norm_nonneg (b : K)]
  have hcoeff : ∀ (Q : MvPolynomial ι (unitBallRing K)) (R : MvPolynomial ι K),
      MvPolynomial.map (unitBallRing K).subtype Q = R → ∀ μ, ((coeff μ Q : unitBallRing K) : K) = coeff μ R := by
    intro Q R hQR μ
    rw [← hQR, MvPolynomial.coeff_map]
    rfl
  have hres_eval : ∀ (Q : MvPolynomial ι (unitBallRing K)) (u : ι → unitBallRing K),
      IsLocalRing.residue (unitBallRing K) (eval u Q) =
        eval (fun i => IsLocalRing.residue (unitBallRing K) (u i))
          (MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) Q) := by
    intro Q u
    induction Q using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  have hbar : ∀ (Q : MvPolynomial ι (unitBallRing K)) (R : MvPolynomial ι K),
      MvPolynomial.map (unitBallRing K).subtype Q = R → (∃ μ, ‖coeff μ R‖ = 1) →
        MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) Q ≠ 0 := by
    intro Q R hQR hR h0
    obtain ⟨μ, hμ⟩ := hR
    have h := congrArg (coeff μ) h0
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at h
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2
      (unit_of_norm _ (by rw [hcoeff Q R hQR μ]; exact hμ)) h
  have hQ : MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) PO *
      MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) δO ≠ 0 :=
    mul_ne_zero (hbar PO P hPO hP1) (hbar δO δ hδO hδ1)
  obtain ⟨S0, hS0T, hS0c⟩ := (infinite_residues K₀ hK₀).exists_subset_card_eq
    ((MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) PO *
      MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) δO).totalDegree + 1)
  have hex : ∃ y : ι → IsLocalRing.ResidueField (unitBallRing K), (∀ i, y i ∈ S0) ∧
      eval y (MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) PO *
        MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) δO) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hQ (MvPolynomial.eq_zero_of_eval_zero_at_prod_finset _ (fun _ => S0)
      (fun i => lt_of_le_of_lt (MvPolynomial.degreeOf_le_totalDegree _ i) (by rw [hS0c]; omega)) hcon)
  obtain ⟨y, hyS, hyQ⟩ := hex
  have hlift : ∀ i, ∃ x : unitBallRing K, (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧
      IsLocalRing.residue (unitBallRing K) x = y i := fun i => hS0T (Finset.mem_coe.2 (hyS i))
  choose u hu0 hu1 hu2 using hlift
  have hy : (fun i => IsLocalRing.residue (unitBallRing K) (u i)) = y := funext hu2
  rw [map_mul] at hyQ
  refine ⟨fun i => (u i : K), fun i => ⟨hu0 i, hu1 i⟩, ?_, ?_⟩
  · rw [← hPO, eval_lift]
    apply norm_of_unit
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hres_eval, hy]
    exact left_ne_zero_of_mul hyQ
  · rw [← hδO, eval_lift]
    apply norm_of_unit
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hres_eval, hy]
    exact right_ne_zero_of_mul hyQ
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall
