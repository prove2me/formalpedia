-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.lift_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:27:08.505072+00:00
-- url     : https://prove2.me/submissions/f604a61c-f765-491a-8ef0-13bb90bb2e4a

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsReductionOfCoordinateCombination
import Definitions.Def_ReciprocityTheory_DualLattices_AvgFZero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_avgF_mem
import Theorems.Thm_ReciprocityTheory_PGsh_Up_avgF_eig
import Theorems.Thm_ReciprocityTheory_PGsh_Up_avgF_zero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_avgF_cong
import Theorems.Thm_ReciprocityTheory_PGsh_Up_red_mulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (hS : HodgeTateSetting p v R O σ cp) (hp2 : p ≠ 2) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    (hsep : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1)
    (hcardG : IsUnit (Fintype.card G : R)) {i : Fin U.m} (hi : U.εT i ≠ 0)
    (hnt : ∃ γ, v (algebraMap R C (U.sg i (β γ) - 1)) = 1) (e : R) (lam : Ix g → R)
    (hdiv : ∃ c, cp = e * c) (wH wB : Fin g → R)
    (hrow : (wH ᵥ* H.Ht + wB ᵥ* H.Bt) ᵥ* U.εT i = e • lam) :
    ∃ u : Nb p g → C, (∀ y, v (u y) ≤ 1) ∧
      (∀ y, v (u y - algebraMap R C (∑ k, lam k * ((y k).val : R))) < 1) ∧
      (fun y => algebraMap R C e * u y) ∈ augIdeal H.AA.carrier ∧
      (∀ δ t, u (red p g (H.ρ (β δ) *ᵥ t)) = algebraMap R C (U.sg i (β δ)) * u (red p g t)) := by
  classical
  obtain ⟨c', hc'⟩ := hdiv
  choose fH hfH hrH using fun k => (H.h4 k).1
  choose fB hfB hrB using fun k => (H.h4 k).2
  choose rH hrH' using hrH
  choose rB hrB' using hrB
  obtain ⟨F, hFdef⟩ : ∃ F : Nb p g → C, F = ∑ k, wH k • fH k + ∑ k, wB k • fB k := ⟨_, rfl⟩
  have hFmem : F ∈ H.AA.carrier := by
    rw [hFdef]
    exact H.AA.carrier.add_mem (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hfH k))
      (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hfB k))
  have hFcong : ∀ t : TT p g, ∃ r : R,
      algebraMap R C ((wH ᵥ* H.Ht + wB ᵥ* H.Bt) ⬝ᵥ (algebraMap ℤ_[p] R ∘ t)) - F (red p g t) =
        algebraMap R C (p * r) := by
    intro t
    refine ⟨∑ k, wH k * rH k t + ∑ k, wB k * rB k t, ?_⟩
    have hFt : F (red p g t) = ∑ k, algebraMap R C (wH k) * fH k (red p g t) +
        ∑ k, algebraMap R C (wB k) * fB k (red p g t) := by
      rw [hFdef, Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
      simp only [Pi.smul_apply]
      simp only [Algebra.smul_def]
    have hfH'' : ∀ k, fH k (red p g t) = algebraMap R C ((H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) -
        algebraMap R C (p * rH k t) := fun k => by linear_combination -(hrH' k t)
    have hfB'' : ∀ k, fB k (red p g t) = algebraMap R C ((H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) -
        algebraMap R C (p * rB k t) := fun k => by linear_combination -(hrB' k t)
    have hLT : (wH ᵥ* H.Ht + wB ᵥ* H.Bt) ⬝ᵥ (algebraMap ℤ_[p] R ∘ t) =
        ∑ k, wH k * (H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k +
          ∑ k, wB k * (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k := by
      rw [add_dotProduct, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec]
      rfl
    rw [hFt, hLT]
    simp only [hfH'', hfB'']
    have hmap : (∑ k, algebraMap R C (wH k) * (algebraMap R C ((H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) -
          algebraMap R C (p * rH k t)) +
        ∑ k, algebraMap R C (wB k) * (algebraMap R C ((H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) -
          algebraMap R C (p * rB k t))) =
        algebraMap R C (∑ k, wH k * ((H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k - p * rH k t) +
          ∑ k, wB k * ((H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k - p * rB k t)) := by
      simp only [map_add, map_sum, map_mul, map_sub]
    rw [hmap, ← map_sub]
    congr 1
    have e1 : ∑ k, wH k * (p * rH k t) = (p : R) * ∑ k, wH k * rH k t := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have e2 : ∑ k, wB k * (p * rB k t) = (p : R) * ∑ k, wB k * rB k t := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [e1, e2]
    ring
  have hAmem : avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F ∈ H.AA.carrier :=
    avgF_mem β U i _ hFmem
  have hA0 : avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F 0 = 0 :=
    avgF_zero β hS U hmul h1 hi hnt _ F
  have hAeig := avgF_eig β hS U hmul h1 hi ((hcardG.unit⁻¹ : Rˣ) : R) F
  have hAcong := avgF_cong β hS U hmul h1 hsep hcardG hi (wH ᵥ* H.Ht + wB ᵥ* H.Bt) F hFcong
  have hp2' : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hvcp : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    apply hS.p_ne
    rw [← hS.cp_val, h0, zero_pow (by omega)]
  have hve : v (algebraMap R C cp) ≤ v (algebraMap R C e) := by
    rw [hc', map_mul, map_mul]
    exact mul_le_of_le_one_right zero_le' (hS.integers.map_le_one c')
  have he0 : algebraMap R C e ≠ 0 := by
    intro h0
    have h := hve
    rw [h0, map_zero] at h
    exact hvcp (le_antisymm h zero_le')
  have hcp1 : v (algebraMap R C cp) < 1 := by
    rcases (hS.integers.map_le_one cp).lt_or_eq with h | h
    · exact h
    · exfalso
      have h' := hS.p_lt
      rw [← hS.cp_val, h, one_pow] at h'
      exact lt_irrefl _ h'
  have hpe : v (algebraMap R C (p : R)) < v (algebraMap R C e) := by
    rw [← hS.cp_val]
    have hp3 : 2 ≤ p - 1 := by omega
    calc v (algebraMap R C cp) ^ (p - 1) ≤ v (algebraMap R C cp) ^ 2 :=
          pow_le_pow_of_le_one zero_le' hcp1.le hp3
      _ < v (algebraMap R C cp) := by
          rw [sq]
          exact mul_lt_of_lt_one_right (pos_iff_ne_zero.mpr hvcp) hcp1
      _ ≤ _ := hve
  have hsmall : ∀ r : R, v (algebraMap R C (p * r) / algebraMap R C e) < 1 := by
    intro r
    have hve0 : 0 < v (algebraMap R C e) := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr he0)
    rw [map_div₀, div_lt_one hve0, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le' (hS.integers.map_le_one r)) hpe
  have hrep : ∀ y : Nb p g, ∃ r : R,
      avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F y / algebraMap R C e =
        algebraMap R C (∑ k, lam k * ((y k).val : R)) + algebraMap R C (p * r) / algebraMap R C e := by
    intro y
    obtain ⟨t, ht⟩ : ∃ t : TT p g, t = fun k => (((y k).val : ℕ) : ℤ_[p]) := ⟨_, rfl⟩
    have hy : red p g t = y := by
      funext k
      simp [red, ht, map_natCast, ZMod.natCast_zmod_val]
    have hT : (algebraMap ℤ_[p] R ∘ t) = fun k => ((y k).val : R) := by
      funext k
      rw [ht]
      simp only [Function.comp_apply]
      exact map_natCast _ _
    obtain ⟨r, hr⟩ := hAcong t
    refine ⟨r, ?_⟩
    have hdot : lam ⬝ᵥ (fun k => ((y k).val : R)) = ∑ k, lam k * ((y k).val : R) := rfl
    rw [hy, hrow, hT, smul_dotProduct, smul_eq_mul, hdot] at hr
    have hAy : avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F y =
        algebraMap R C e * algebraMap R C (∑ k, lam k * ((y k).val : R)) + algebraMap R C (p * r) := by
      rw [← map_mul]
      linear_combination hr
    rw [hAy, add_div, mul_div_cancel_left₀ _ he0]
  refine ⟨fun y => avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F y / algebraMap R C e, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨r, hr⟩ := hrep y
    dsimp only
    rw [hr]
    exact le_trans (Valuation.map_add v _ _) (max_le (hS.integers.map_le_one _) (hsmall r).le)
  · intro y
    obtain ⟨r, hr⟩ := hrep y
    dsimp only
    rw [hr, add_sub_cancel_left]
    exact hsmall r
  · have hmemA : avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F ∈ augIdeal H.AA.carrier :=
      Submodule.mem_inf.mpr ⟨hAmem, LinearMap.mem_ker.mpr hA0⟩
    convert hmemA using 1
    funext y
    rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ he0
  · intro δ t
    dsimp only
    rw [red_mulVec, hAeig δ (red p g t), mul_div_assoc]
end ReciprocityTheory.PGsh.Up
