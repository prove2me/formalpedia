-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.avgF_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:34:38.520573+00:00
-- url     : https://prove2.me/submissions/75c1ef1c-6187-4c46-8606-a7a4496f15e9

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsReductionOfCoordinateCombination
import Definitions.Def_ReciprocityTheory_DualLattices_AvgFZero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_red_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
section Lift1
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
variable {G : Type} [CommGroup G] [Fintype G] (β : G → O)
private lemma smul_cancel_lemma (hS : HodgeTateSetting p v R O σ cp) {M : Matrix (Ix g) (Ix g) R}
    (hM : M ≠ 0) (s : R) (hs : s • M = 0) : s = 0 := by
  have hnz : NoZeroDivisors R := hS.integers.hom_inj.noZeroDivisors _ (map_zero _) (map_mul _)
  by_contra hne
  apply hM
  ext k l
  have h := congrFun (congrFun hs k) l
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' hne
  · simpa using h'
private lemma sg_mul_lemma_2 (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ'))
    {i : Fin U.m} (hi : U.εT i ≠ 0) (γ γ' : G) :
    U.sg i (β (γ * γ')) = U.sg i (β γ) * U.sg i (β γ') := by
  apply sub_eq_zero.mp
  apply smul_cancel_lemma hS hi
  have e1 := U.εT_eig (β (γ * γ')) i
  rw [hmul, Matrix.map_mul, Matrix.mul_assoc, U.εT_eig, Matrix.mul_smul, U.εT_eig, smul_smul] at e1
  rw [sub_smul, ← e1, mul_comm, sub_self]
private lemma sg_one_lemma_3 (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H) (h1 : H.ρ (β 1) = 1)
    {i : Fin U.m} (hi : U.εT i ≠ 0) : U.sg i (β 1) = 1 := by
  apply sub_eq_zero.mp
  apply smul_cancel_lemma hS hi
  have e1 := U.εT_eig (β 1) i
  rw [h1, Matrix.map_one (algebraMap ℤ_[p] R) (map_zero _) (map_one _), Matrix.one_mul] at e1
  rw [sub_smul, ← e1, one_smul, sub_self]
private lemma sg_inv_lemma_4 (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    {i : Fin U.m} (hi : U.εT i ≠ 0) (γ : G) : U.sg i (β γ) * U.sg i (β γ⁻¹) = 1 := by
  rw [← sg_mul_lemma_2 β hS U hmul hi, mul_inv_cancel, sg_one_lemma_3 β hS U h1 hi]
private lemma orth_lemma_5 (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    (hsep : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1)
    {i k : Fin U.m} (hi : U.εT i ≠ 0) (hk : U.εT k ≠ 0) (hik : i ≠ k) :
    ∑ γ, U.sg i (β γ⁻¹) * U.sg k (β γ) = 0 := by
  have hnz : NoZeroDivisors R := hS.integers.hom_inj.noZeroDivisors _ (map_zero _) (map_mul _)
  obtain ⟨δ, hδ⟩ := hsep i k hi hk hik
  have hne : U.sg i (β δ) - U.sg k (β δ) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hδ
    exact zero_ne_one hδ
  have hA := sg_inv_lemma_4 β hS U hmul h1 hi δ
  have hB := sg_inv_lemma_4 β hS U hmul h1 hk δ
  set S := ∑ γ, U.sg i (β γ⁻¹) * U.sg k (β γ) with hSdef
  have hshift : S = U.sg i (β δ⁻¹) * U.sg k (β δ) * S := by
    rw [hSdef, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft δ⁻¹) _ _ fun γ => ?_
    simp only [Equiv.coe_mulLeft, _root_.mul_inv_rev, inv_inv, sg_mul_lemma_2 β hS U hmul hi,
      sg_mul_lemma_2 β hS U hmul hk]
    linear_combination (-(U.sg i (β γ⁻¹) * U.sg k (β γ))) * hA +
      (-(U.sg i (β γ⁻¹) * U.sg k (β γ) * (U.sg i (β δ) * U.sg i (β δ⁻¹)))) * hB
  have hm : (U.sg i (β δ) - U.sg k (β δ)) * S = 0 := by
    linear_combination (U.sg i (β δ)) * hshift + (U.sg k (β δ) * S) * hA
  exact (mul_eq_zero.mp hm).resolve_left hne
private lemma proj_lemma_6 (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    (hsep : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1)
    (hcardG : IsUnit (Fintype.card G : R)) {i : Fin U.m} (hi : U.εT i ≠ 0) :
    ∑ γ, (((hcardG.unit⁻¹ : Rˣ) : R) * U.sg i (β γ⁻¹)) • (H.ρ (β γ)).map (algebraMap ℤ_[p] R) =
      U.εT i := by
  have hA : ∀ γ, (H.ρ (β γ)).map (algebraMap ℤ_[p] R) = ∑ j, U.sg j (β γ) • U.εT j := by
    intro γ
    have h := congrArg (fun M => (H.ρ (β γ)).map (algebraMap ℤ_[p] R) * M) U.εT_sum
    simp only [Matrix.mul_one, Matrix.mul_sum] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => U.εT_eig _ j
  simp_rw [hA, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, Finset.sum_eq_single i]
  · rw [← Finset.sum_smul]
    have hc : ∀ γ, U.sg i (β γ⁻¹) * U.sg i (β γ) = 1 := fun γ => by
      rw [mul_comm]
      exact sg_inv_lemma_4 β hS U hmul h1 hi γ
    have hsum : ∑ γ, ((hcardG.unit⁻¹ : Rˣ) : R) * U.sg i (β γ⁻¹) * U.sg i (β γ) = 1 := by
      simp_rw [mul_assoc, ← Finset.mul_sum, hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one]
      exact hcardG.val_inv_mul
    rw [hsum, one_smul]
  · intro j _ hji
    by_cases hj : U.εT j = 0
    · simp [hj]
    · rw [← Finset.sum_smul]
      have hsum : ∑ γ, ((hcardG.unit⁻¹ : Rˣ) : R) * U.sg i (β γ⁻¹) * U.sg j (β γ) = 0 := by
        simp_rw [mul_assoc, ← Finset.mul_sum]
        rw [orth_lemma_5 β hS U hmul h1 hsep hi hj (Ne.symm hji), mul_zero]
      rw [hsum, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h
end Lift1
end ReciprocityTheory.PGsh.Up
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
variable {G : Type} [CommGroup G] [Fintype G] (β : G → O)
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    (hsep : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1)
    (hcardG : IsUnit (Fintype.card G : R)) {i : Fin U.m} (hi : U.εT i ≠ 0) (Lr : Ix g → R)
    (F : Nb p g → C) (hF : ∀ t : TT p g, ∃ r : R,
      algebraMap R C (Lr ⬝ᵥ (algebraMap ℤ_[p] R ∘ t)) - F (red p g t) = algebraMap R C (p * r))
    (t : TT p g) : ∃ r : R, avgF β H U i (hcardG.unit⁻¹ : Rˣ) F (red p g t) -
      algebraMap R C ((Lr ᵥ* U.εT i) ⬝ᵥ (algebraMap ℤ_[p] R ∘ t)) = algebraMap R C (p * r) := by
  choose r hr using hF
  set c : R := ((hcardG.unit⁻¹ : Rˣ) : R) with hc
  set T : Ix g → R := algebraMap ℤ_[p] R ∘ t with hT
  have hF' : ∀ γ, F (nbAct H (β γ) (red p g t)) =
      algebraMap R C ((Lr ᵥ* (H.ρ (β γ)).map (algebraMap ℤ_[p] R)) ⬝ᵥ T) -
        algebraMap R C (p * r (H.ρ (β γ) *ᵥ t)) := by
    intro γ
    have h2 : (algebraMap ℤ_[p] R ∘ (H.ρ (β γ) *ᵥ t)) =
        (H.ρ (β γ)).map (algebraMap ℤ_[p] R) *ᵥ T := by
      funext k
      exact RingHom.map_mulVec _ _ _ k
    rw [← red_mulVec, ← Matrix.dotProduct_mulVec, ← h2]
    linear_combination -(hr (H.ρ (β γ) *ᵥ t))
  let L : Matrix (Ix g) (Ix g) R →ₗ[R] R :=
    { toFun := fun M => (Lr ᵥ* M) ⬝ᵥ T
      map_add' := fun M N => by simp only [Matrix.vecMul_add, add_dotProduct]
      map_smul' := fun a M => by simp only [Matrix.vecMul_smul, smul_dotProduct, RingHom.id_apply] }
  have hLε : (Lr ᵥ* U.εT i) ⬝ᵥ T =
      ∑ γ, (c * U.sg i (β γ⁻¹)) * ((Lr ᵥ* (H.ρ (β γ)).map (algebraMap ℤ_[p] R)) ⬝ᵥ T) := by
    have h := congrArg L (proj_lemma_6 β hS U hmul h1 hsep hcardG hi)
    rw [map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    exact h.symm
  refine ⟨-(∑ γ, c * U.sg i (β γ⁻¹) * r (H.ρ (β γ) *ᵥ t)), ?_⟩
  show ∑ γ, algebraMap R C (c * U.sg i (β γ⁻¹)) * F (nbAct H (β γ) (red p g t)) - _ = _
  simp only [hF']
  rw [hLε]
  have hmap : ∑ γ, algebraMap R C (c * U.sg i (β γ⁻¹)) *
      (algebraMap R C ((Lr ᵥ* (H.ρ (β γ)).map (algebraMap ℤ_[p] R)) ⬝ᵥ T) -
        algebraMap R C (p * r (H.ρ (β γ) *ᵥ t))) =
      algebraMap R C (∑ γ, c * U.sg i (β γ⁻¹) *
        ((Lr ᵥ* (H.ρ (β γ)).map (algebraMap ℤ_[p] R)) ⬝ᵥ T - p * r (H.ρ (β γ) *ᵥ t))) := by
    simp only [map_sum, map_mul, map_sub]
  rw [hmap, ← map_sub]
  congr 1
  have e : ∑ γ, c * U.sg i (β γ⁻¹) * (p * r (H.ρ (β γ) *ᵥ t)) =
      (p : R) * ∑ γ, c * U.sg i (β γ⁻¹) * r (H.ρ (β γ) *ᵥ t) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [e]
  ring
end ReciprocityTheory.PGsh.Up
