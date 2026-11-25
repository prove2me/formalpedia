-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.exists_torus_point_one_le_norm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:02:07.398914+00:00
-- url     : https://prove2.me/submissions/6f461042-79d0-4f66-86b6-c4c1a5a2558c

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsTorusPointOneLeNormSum
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_mem_unitBallRing
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_residue_eq_zero_iff_norm_lt_one
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_infinite_residues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type*} [NormedField K] [IsUltrametricDist K]
    (K₀ : Subfield K) (hK₀ : ResidueFieldInfiniteOn (K₀ : Set K)) {n : ℕ}
    (F : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → K) (ha : ∀ χ, ‖a χ‖ ≤ 1)
    (χ₀ : Fin n → ℤ) (hχ₀ : χ₀ ∈ F) (ha₀ : ‖a χ₀‖ = 1) :
    ∃ τ : Fin n → K, (∀ i, τ i ∈ K₀ ∧ ‖τ i‖ = 1) ∧
      1 ≤ ‖∑ χ ∈ F, a χ * ∏ i, τ i ^ χ i‖ := by
  classical
  let N : ℕ := ∑ χ ∈ F, ∑ i, (χ i).natAbs
  have hN : ∀ χ ∈ F, ∀ i, 0 ≤ χ i + N := by
    intro χ hχ i
    have h1 : (χ i).natAbs ≤ ∑ j, (χ j).natAbs :=
      Finset.single_le_sum (f := fun j => (χ j).natAbs) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : ∑ j, (χ j).natAbs ≤ N :=
      Finset.single_le_sum (f := fun χ : Fin n → ℤ => ∑ j, (χ j).natAbs)
        (fun _ _ => Nat.zero_le _) hχ
    omega
  let e : (Fin n → ℤ) → (Fin n →₀ ℕ) := fun χ =>
    Finsupp.equivFunOnFinite.symm (fun i => (χ i + N).toNat)
  have he : ∀ χ ∈ F, ∀ χ' ∈ F, e χ = e χ' → χ = χ' := by
    intro χ hχ χ' hχ' h
    funext i
    have h3 := congrArg (fun f : Fin n →₀ ℕ => f i) h
    simp only [e, Finsupp.coe_equivFunOnFinite_symm] at h3
    have h1 := hN χ hχ i
    have h2 := hN χ' hχ' i
    omega
  let aO : (Fin n → ℤ) → unitBallRing K := fun χ => ⟨a χ, (mem_unitBallRing _).2 (ha χ)⟩
  let P : MvPolynomial (Fin n) (unitBallRing K) := ∑ χ ∈ F, monomial (e χ) (aO χ)
  have hcoeff : coeff (e χ₀) P = aO χ₀ := by
    simp only [P, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single_of_mem χ₀ hχ₀]
    · simp
    · intro χ hχ hne
      rw [if_neg]
      exact fun h => hne (he χ hχ χ₀ hχ₀ h)
  have hQ : MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) P ≠ 0 := by
    intro h0
    have h4 := congrArg (coeff (e χ₀)) h0
    rw [coeff_map, hcoeff, coeff_zero, residue_eq_zero_iff_norm_lt_one] at h4
    exact absurd ha₀ (ne_of_lt h4)
  obtain ⟨y, hy, hyne⟩ : ∃ y ∈ Set.pi Set.univ (fun _ : Fin n =>
      {y : IsLocalRing.ResidueField (unitBallRing K) | ∃ x : unitBallRing K,
        (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y}),
      eval y (MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) P) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hQ (funext_set _ (fun _ => infinite_residues K₀ hK₀) (fun x hx => by
      rw [hcon x hx, map_zero]))
  choose σ hσK hσ1 hσr using fun i => hy i (Set.mem_univ i)
  refine ⟨fun i => (σ i : K), fun i => ⟨hσK i, hσ1 i⟩, ?_⟩
  have hr : IsLocalRing.residue (unitBallRing K) (eval σ P) ≠ 0 := by
    have hy' : y = fun i => IsLocalRing.residue (unitBallRing K) (σ i) :=
      funext fun i => (hσr i).symm
    have h5 : eval y (MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) P) =
        IsLocalRing.residue (unitBallRing K) (eval σ P) := by
      rw [eval_map, hy', MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, hom_eval₂,
        RingHom.comp_id]
    rwa [h5] at hyne
  have hge : 1 ≤ ‖((eval σ P : unitBallRing K) : K)‖ :=
    not_lt.1 fun h => hr ((residue_eq_zero_iff_norm_lt_one _).2 h)
  have hσ0 : ∀ i, (σ i : K) ≠ 0 := fun i h => by
    have h6 := hσ1 i
    rw [h, norm_zero] at h6
    exact zero_ne_one h6
  have hval : ((eval σ P : unitBallRing K) : K) =
      ∑ χ ∈ F, a χ * ∏ i, (σ i : K) ^ (χ i + N).toNat := by
    simp only [P, map_sum, eval_monomial]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp [e, aO]
  have hterm : ∀ χ ∈ F, ∏ i, (σ i : K) ^ (χ i + N).toNat =
      (∏ i, (σ i : K) ^ χ i) * ∏ i, (σ i : K) ^ N := by
    intro χ hχ
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, Int.toNat_of_nonneg (hN χ hχ i), zpow_add₀ (hσ0 i), zpow_natCast]
  have hsum : ((eval σ P : unitBallRing K) : K) =
      (∑ χ ∈ F, a χ * ∏ i, (σ i : K) ^ χ i) * ∏ i, (σ i : K) ^ N := by
    rw [hval, Finset.sum_mul]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hterm χ hχ, mul_assoc]
  have hnorm1 : ‖∏ i, (σ i : K) ^ N‖ = 1 := by
    rw [norm_prod]
    simp [norm_pow, hσ1]
  rw [hsum, norm_mul, hnorm1, mul_one] at hge
  exact hge
end ReciprocityTheory.MultiplicativeHeights
