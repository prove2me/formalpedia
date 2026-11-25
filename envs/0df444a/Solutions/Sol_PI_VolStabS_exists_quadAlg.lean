-- Prove2me | solution 1 for PI.VolStabS.exists_quadAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:50:46.956811+00:00
-- url     : https://prove2.me/submissions/cc456099-01b1-4406-a968-196fa614cb27

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensCntQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.VolStabS
open Polynomial
private theorem bijective_algebraMap_add_mul_of_finrank_two {k K : Type} [Field k] [CommRing K]
    [Algebra k K] [Module.Finite k K] (hK : Module.finrank k K = 2) (r : K)
    (h0 : ∀ a b : k, algebraMap k K a + algebraMap k K b * r = 0 → a = 0 ∧ b = 0) :
    Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
  let L : (k × k) →ₗ[k] K :=
    (LinearMap.fst k k k).smulRight (1 : K) + (LinearMap.snd k k k).smulRight r
  have hL : ∀ p : k × k, L p = algebraMap k K p.1 + algebraMap k K p.2 * r := by
    intro p
    simp [L, Algebra.smul_def]
  have hfun : (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) = ⇑L :=
    funext fun p => (hL p).symm
  rw [hfun]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hL] at hp
    obtain ⟨h1, h2⟩ := h0 p.1 p.2 hp
    exact Prod.ext h1 h2
  have H : Module.finrank k (k × k) = Module.finrank k K := by
    rw [hK]
    simp
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank H).mp hinj⟩
private theorem exists_algEquiv_prod_swap (k : Type) [Field k] :
    ∃ σ : (k × k) ≃ₐ[k] (k × k), ∀ x, σ x = x.swap :=
  ⟨{ toFun := Prod.swap
     invFun := Prod.swap
     left_inv := fun x => Prod.swap_swap x
     right_inv := fun x => Prod.swap_swap x
     map_mul' := fun x y => rfl
     map_add' := fun x y => rfl
     commutes' := fun c => rfl }, fun x => rfl⟩
private theorem isQuadInv_and_bijective_of_not_isSquare (k K : Type) [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) (hsq : ¬ IsSquare D)
    (hK : Module.finrank k K = 2) (r : K) (hr : r * r = algebraMap k K D)
    (σ' : K ≃ₐ[k] K) (hσ : σ' r = -r) (hinv : ∀ x, σ' (σ' x) = x) :
    IsQuadInv k K σ' ∧
      Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have h11 : algebraMap k K (1 + 1) = 0 := by
      rw [map_add, map_one]
      linear_combination h
    have h11' : (1 + 1 : k) = 0 := (algebraMap k K).injective (h11.trans (map_zero _).symm)
    exact h2 (by linear_combination h11')
  refine ⟨⟨hinv, Or.inl ⟨Field.toIsField K, hK, ?_⟩⟩, ?_⟩
  · intro hσr
    have h1 : r = -r := by
      simpa [hσr] using hσ
    have hr0 : r = 0 := by
      have h2r : (2 : K) * r = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h2r).resolve_left h2K
    apply hD
    apply (algebraMap k K).injective
    rw [← hr, hr0, mul_zero, map_zero]
  · apply bijective_algebraMap_add_mul_of_finrank_two hK r
    intro a b h
    by_cases hb : b = 0
    · subst hb
      simp only [map_zero, zero_mul, add_zero] at h
      refine ⟨?_, rfl⟩
      apply (algebraMap k K).injective
      rw [h, map_zero]
    · exfalso
      apply hsq
      refine ⟨-a / b, ?_⟩
      apply (algebraMap k K).injective
      have hbK : algebraMap k K b ≠ 0 := (_root_.map_ne_zero _).mpr hb
      have hrc : r = algebraMap k K (-a / b) := by
        rw [map_div₀, map_neg, eq_div_iff hbK]
        linear_combination h
      rw [← hr, hrc, map_mul]
end PI.VolStabS
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open Polynomial
namespace PI.VolStabS
theorem _root_.solution (k : Type) [Field k] [Finite k] (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) :
    ∃ (K : Type) (_ : CommRing K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K) (r : K),
      IsQuadInv k K σ' ∧ r * r = algebraMap k K D ∧ σ' r = -r ∧
      Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
  by_cases hsq : IsSquare D
  · obtain ⟨s, hs⟩ := hsq
    have hs0 : s ≠ 0 := fun h => hD (by rw [hs, h, mul_zero])
    obtain ⟨σ, hσ⟩ := exists_algEquiv_prod_swap k
    refine ⟨k × k, inferInstance, inferInstance, σ, (s, -s), ?_, ?_, ?_, ?_⟩
    · refine ⟨fun x => by rw [hσ, hσ, Prod.swap_swap], Or.inr ⟨AlgEquiv.refl, fun x => ?_⟩⟩
      rw [hσ]
      rfl
    · ext <;> simp [hs]
    · rw [hσ]
      ext <;> simp
    · apply bijective_algebraMap_add_mul_of_finrank_two
      · simp
      · intro a b h
        have e1 : a + b * s = 0 := by
          exact congrArg Prod.fst h
        have e2 : a + b * -s = 0 := by
          exact congrArg Prod.snd h
        have hb : (2 * s) * b = 0 := by linear_combination e1 - e2
        have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_left (mul_ne_zero h2 hs0)
        refine ⟨?_, hb0⟩
        linear_combination e1 - s * hb0
  · have hroot : ∀ b : k, b ^ 2 ≠ D := fun b hb => hsq ⟨b, by rw [← hb, sq]⟩
    have hirr : Irreducible (X ^ 2 - C D : k[X]) := by
      exact X_pow_sub_C_irreducible_of_prime Nat.prime_two hroot
    have : Fact (Irreducible (X ^ 2 - C D : k[X])) := ⟨hirr⟩
    have hf0 : (X ^ 2 - C D : k[X]) ≠ 0 := hirr.ne_zero
    have hfin : Module.finrank k (AdjoinRoot (X ^ 2 - C D : k[X])) = 2 := by
      rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]
    have : Module.Finite k (AdjoinRoot (X ^ 2 - C D : k[X])) := (AdjoinRoot.powerBasis hf0).finite
    have hr : AdjoinRoot.root (X ^ 2 - C D : k[X]) * AdjoinRoot.root (X ^ 2 - C D : k[X]) =
        algebraMap k (AdjoinRoot (X ^ 2 - C D : k[X])) D := by
      have h0 : aeval (AdjoinRoot.root (X ^ 2 - C D : k[X])) (X ^ 2 - C D : k[X]) = 0 := by
        rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      simp only [map_sub, aeval_X_pow, aeval_C] at h0
      linear_combination h0
    have hneg : aeval (-AdjoinRoot.root (X ^ 2 - C D : k[X])) (X ^ 2 - C D : k[X]) = 0 := by
      simp only [map_sub, aeval_X_pow, aeval_C]
      linear_combination hr
    have hneg' : eval₂ (algebraMap k (AdjoinRoot (X ^ 2 - C D : k[X])))
        (-AdjoinRoot.root (X ^ 2 - C D : k[X])) (X ^ 2 - C D : k[X]) = 0 := by
      rw [← aeval_def]
      exact hneg
    obtain ⟨τ, hτr⟩ : ∃ τ : AdjoinRoot (X ^ 2 - C D : k[X]) →ₐ[k] AdjoinRoot (X ^ 2 - C D : k[X]),
        τ (AdjoinRoot.root _) = -AdjoinRoot.root (X ^ 2 - C D : k[X]) := by
      exact ⟨{ AdjoinRoot.lift (algebraMap k _) (-AdjoinRoot.root _) hneg' with
          commutes' := fun c => by simp [AdjoinRoot.algebraMap_eq] }, AdjoinRoot.lift_root hneg'⟩
    have hττ : τ.comp τ = AlgHom.id k _ := by
      apply AdjoinRoot.algHom_ext
      rw [AlgHom.comp_apply, hτr, map_neg, hτr, neg_neg, AlgHom.id_apply]
    let σ' := AlgEquiv.ofAlgHom τ τ hττ hττ
    have hσ : σ' (AdjoinRoot.root (X ^ 2 - C D : k[X])) = -AdjoinRoot.root (X ^ 2 - C D : k[X]) :=
      hτr
    have hinv : ∀ x, σ' (σ' x) = x := fun x => DFunLike.congr_fun hττ x
    obtain ⟨hq, hbij⟩ := isQuadInv_and_bijective_of_not_isSquare k (AdjoinRoot (X ^ 2 - C D : k[X])) h2 D hD hsq hfin
      (AdjoinRoot.root _) hr σ' hσ hinv
    exact ⟨AdjoinRoot (X ^ 2 - C D : k[X]), inferInstance, inferInstance, σ',
      AdjoinRoot.root _, hq, hr, hσ, hbij⟩
end PI.VolStabS
