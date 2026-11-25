-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_RamificationLowerIndex_ramificationIndex_mul_lowerIndex_restrictNormalHom__56df8d42432e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:01:15.415795+00:00
-- url     : https://prove2.me/submissions/72daddd1-ab48-4e20-afae-c94cedd19421

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RamificationLowerIndex
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_eq_addVal_of_adjoin_eq_top
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_eq_top_iff
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_inv
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_le
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_one
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_restrictScalars
import Theorems.Thm_GroundTheory_LocalField_map_maximalIdeal
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_pos
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.lowerIndex_inv
attribute [local simp] GroundTheory.LocalField.lowerIndex_one
attribute [local simp] GroundTheory.LocalField.lowerIndex_restrictScalars
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


section
namespace UpperTheory.Reformulated.B.RamificationLowerIndex
open Polynomial IsLocalRing ValuativeRel
open IsDiscreteValuationRing hiding maximalIdeal
private lemma adjoin_eq_top_of {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Module.Finite R S] (A : Subalgebra R S) (π : S) (hπ : π ∈ A)
    (h1 : ∀ s : S, ∃ a ∈ A, π ∣ s - a) (n : ℕ)
    (hn : π ^ n ∈ (maximalIdeal R).map (algebraMap R S)) : A = ⊤ := by
  have h2 : ∀ m : ℕ, ∀ s : S, ∃ a ∈ A, π ^ m ∣ s - a := by
    intro m
    induction m with
    | zero => intro s; exact ⟨0, A.zero_mem, by simp⟩
    | succ m ih =>
      intro s
      obtain ⟨a, ha, t, ht⟩ := ih s
      obtain ⟨b, hb, u, hu⟩ := h1 t
      refine ⟨a + π ^ m * b, A.add_mem ha (A.mul_mem (A.pow_mem hπ m) hb), u, ?_⟩
      linear_combination ht + π ^ m * hu
  refine eq_top_iff.mpr <| Submodule.le_of_le_smul_of_le_jacobson_bot
    (Module.finite_def.mp inferInstance) (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    (?_ : ⊤ ≤ A.toSubmodule ⊔ maximalIdeal R • ⊤)
  intro s _
  obtain ⟨a, ha, t, ht⟩ := h2 n s
  rw [Ideal.smul_top_eq_map]
  refine Submodule.mem_sup.mpr ⟨a, ha, s - a, ?_, by ring⟩
  rw [Submodule.restrictScalars_mem, ht]
  exact Ideal.mul_mem_right _ _ hn
private lemma exists_generator {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Module.Finite R S] [IsDomain S] [IsDiscreteValuationRing S]
    [Finite (ResidueField S)] (n : ℕ)
    (hn : maximalIdeal S ^ n ≤ (maximalIdeal R).map (algebraMap R S)) :
    ∃ x : S, Algebra.adjoin R {x} = ⊤ := by
  classical
  let _ : Fintype (ResidueField S) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := (ResidueField S)ˣ)
  obtain ⟨x₀, hx₀⟩ := residue_surjective (R := S) (g : ResidueField S)
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible S
  have hm : maximalIdeal S = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hres : ∀ z : S, residue S z = 0 ↔ ϖ ∣ z := fun z => by
    rw [residue_eq_zero_iff, hm, Ideal.mem_span_singleton]
  set q := Fintype.card (ResidueField S) with hq
  have hpow : ∀ z : S, ϖ ∣ z ^ q - z := fun z => by
    rw [← hres, map_sub, map_pow, FiniteField.pow_card, sub_self]
  have hqd : ϖ ∣ (q : S) := by
    rw [← hres, map_natCast, hq, FiniteField.cast_card_eq_zero]
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hex : ∃ x : S, residue S x = g ∧ ¬ ϖ ^ 2 ∣ x ^ q - x := by
    by_cases h : ϖ ^ 2 ∣ x₀ ^ q - x₀
    · refine ⟨x₀ + ϖ, by rw [map_add, hx₀, (hres ϖ).2 dvd_rfl, add_zero], fun h' => ?_⟩
      obtain ⟨k, hk⟩ := (X ^ q : S[X]).binomExpansion x₀ ϖ
      simp only [eval_pow, eval_X, derivative_X_pow, eval_mul, eval_C] at hk
      obtain ⟨c, hc⟩ := hqd
      obtain ⟨u, hu⟩ := h
      obtain ⟨w, hw⟩ := h'
      have : ϖ * 1 = ϖ * (ϖ * (u + c * x₀ ^ (q - 1) + k - w)) := by
        rw [hc] at hk
        linear_combination hu + hk - hw
      exact hϖ.not_isUnit (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ hϖ0 this).symm)
    · exact ⟨x₀, hx₀, h⟩
  obtain ⟨x, hx, hx2⟩ := hex
  obtain ⟨u, hu⟩ := hpow x
  have huu : IsUnit u := by
    by_contra h
    have h3 : u ∈ maximalIdeal S := h
    rw [hm, Ideal.mem_span_singleton] at h3
    exact hx2 (by rw [hu, pow_two]; exact mul_dvd_mul_left _ h3)
  have hxA : x ∈ Algebra.adjoin R {x} := Algebra.self_mem_adjoin_singleton R x
  refine ⟨x, adjoin_eq_top_of _ (x ^ q - x)
    (Subalgebra.sub_mem _ (Subalgebra.pow_mem _ hxA _) hxA) (fun s => ?_) n ?_⟩
  · rw [hu]
    simp only [huu.mul_right_dvd, ← hres]
    by_cases hs : residue S s = 0
    · exact ⟨0, Subalgebra.zero_mem _, by simpa using hs⟩
    · obtain ⟨m, hm'⟩ := hg (Units.mk0 _ hs)
      refine ⟨x ^ m, Subalgebra.pow_mem _ hxA _, ?_⟩
      have := congrArg Units.val hm'
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at this
      rw [map_sub, map_pow, hx, this, sub_self]
  · apply hn
    apply Ideal.pow_mem_pow
    rw [hm, Ideal.mem_span_singleton]
    exact hpow x
private lemma prod_dvd_sub {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    {H : Type*} [Fintype H] (a : H → S) (ha : Function.Injective a) (x y : S)
    (s : S →ₐ[R] S) (g : R[X]) (hr : ∀ t, aeval (a t) g = y) (hx : aeval x g = y) :
    ∏ t, (x - s (a t)) ∣ s y - y := by
  classical
  have hd : ∏ t, (X - C (a t)) ∣ g.map (algebraMap R S) - C y := by
    by_cases h0 : g.map (algebraMap R S) - C y = 0
    · rw [h0]; exact dvd_zero _
    have := (Multiset.prod_X_sub_C_dvd_iff_le_roots h0 (Finset.univ.val.map a)).2 (by
      rw [Multiset.le_iff_subset (Finset.univ.nodup.map ha)]
      intro z hz
      obtain ⟨t, -, rfl⟩ := Multiset.mem_map.1 hz
      rw [mem_roots h0, IsRoot, eval_sub, eval_map_algebraMap, eval_C, hr, sub_self])
    rwa [Multiset.map_map] at this
  have h2 := _root_.map_dvd ((evalRingHom x).comp (mapRingHom (s : S →+* S))) hd
  have h3 : (s : S →+* S).comp (algebraMap R S) = algebraMap R S := s.comp_algebraMap
  simp only [map_prod, map_sub, RingHom.comp_apply, coe_mapRingHom, coe_evalRingHom, map_X,
    map_C, eval_X, eval_C, Polynomial.map_map, h3, eval_map_algebraMap, hx, RingHom.coe_coe] at h2
  exact dvd_sub_comm.1 h2
private lemma dvd_prod {S : Type*} [CommRing S]
    {H : Type*} [Fintype H] (a : H → S) (t₀ : H) (d : S) (s : S →+* S)
    (h : ∀ i, d ∣ s ((∏ t, (X - C (a t))).coeff i) - (∏ t, (X - C (a t))).coeff i) :
    d ∣ ∏ t, (a t₀ - s (a t)) := by
  have h1 : C d ∣ (∏ t, (X - C (a t))).map s - ∏ t, (X - C (a t)) := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [coeff_sub, coeff_map]
    exact h i
  have h2 := _root_.map_dvd (evalRingHom (a t₀)) h1
  have h3 : ∏ t, (a t₀ - a t) = 0 := Finset.prod_eq_zero (Finset.mem_univ t₀) (sub_self _)
  simpa only [Polynomial.map_prod, Polynomial.map_sub, map_prod, map_sub, coe_evalRingHom, map_X,
    map_C, eval_X, eval_C, h3, sub_zero] using h2
private lemma addVal_algebraMap {T S : Type*} [CommRing T] [CommRing S] [IsDomain T] [IsDomain S]
    [IsDiscreteValuationRing T] [IsDiscreteValuationRing S] [Algebra T S] (e : ℕ) (he : e ≠ 0)
    (h : (maximalIdeal T).map (algebraMap T S) = maximalIdeal S ^ e) (z : T) :
    addVal S (algebraMap T S z) = e * addVal T z := by
  by_cases hz : z = 0
  · subst hz
    rw [map_zero, addVal_zero, addVal_zero, ENat.mul_top (by exact_mod_cast he)]
  obtain ⟨π, hπ⟩ := exists_irreducible T
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible S
  rw [hπ.maximalIdeal_eq, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  obtain ⟨w, hw⟩ := h.symm
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hz hπ
  rw [addVal_def' u hπ n, ← Nat.cast_mul]
  refine addVal_def _ (Units.map (algebraMap T S : T →* S) u * w ^ n) hϖ _ ?_
  rw [map_mul, map_pow, ← hw]
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
  ring
private lemma addVal_prod {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {H : Type*} (F : Finset H) (b : H → S) :
    addVal S (∏ t ∈ F, b t) = ∑ t ∈ F, addVal S (b t) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert t F ht ih => rw [Finset.prod_insert ht, Finset.sum_insert ht, addVal_mul, ih]
end UpperTheory.Reformulated.B.RamificationLowerIndex
end

set_option autoImplicit false

open Polynomial IsLocalRing ValuativeRel GroundTheory.LocalField
open IsDiscreteValuationRing hiding maximalIdeal
namespace UpperTheory.Reformulated.B.RamificationLowerIndex.ramificationIndex_mul_lowerIndex_restrictNormalHom
theorem _root_.solution.{u_1, u_2} :
    ∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
      [inst_3 : IsNonarchimedeanLocalField K] [inst_4 : Field L] [inst_5 : ValuativeRel L] [inst_6 : TopologicalSpace L]
      [inst_7 : IsNonarchimedeanLocalField L] [inst_8 : Algebra K L] [inst_9 : ValuativeExtension K L]
      [inst_10 : FiniteDimensional K L] (M : IntermediateField K L) [IsGalois K L] [inst_12 : Normal K ↥M] (σ : Gal(L/K)),
      (↑(GroundTheory.LocalField.ramificationIndex (↥M) L) : ℕ∞) *
          GroundTheory.LocalField.lowerIndex K (↥M) ((AlgEquiv.restrictNormalHom ↥M : Gal(L/K) → Gal(↥M/K)) σ) =
        ∑ τ : Gal(L/↥M), GroundTheory.LocalField.lowerIndex K L (σ * AlgEquiv.restrictScalars K τ) := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ M _ _ σ
  obtain ⟨x, hx⟩ := exists_generator (R := 𝒪[K]) (S := 𝒪[L]) _ (map_maximalIdeal K L).ge
  have hv := addVal_algebraMap (T := 𝒪[M]) (S := 𝒪[L]) _ (ramificationIndex_pos M L).ne'
    (map_maximalIdeal M L)
  set σ' : Gal(M/K) := AlgEquiv.restrictNormalHom M σ with hσ'
  let r : Gal(L/M) → (𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L]) := fun τ => integerAlgEquiv K L (τ.restrictScalars K)
  let s := integerAlgEquiv K L σ
  let a : Gal(L/M) → 𝒪[L] := fun τ => r τ x
  have ha1 : a 1 = x := rfl
  have hamul : ∀ ρ τ, r ρ (a τ) = a (ρ * τ) := fun _ _ => rfl
  have hcomm : ∀ y : 𝒪[M], s (algebraMap 𝒪[M] 𝒪[L] y) =
      algebraMap 𝒪[M] 𝒪[L] (integerAlgEquiv K M σ' y) := fun y =>
    Subtype.ext (AlgEquiv.restrictNormal_commutes σ M (y : M)).symm
  have hfix : ∀ τ (y : 𝒪[M]), r τ (algebraMap 𝒪[M] 𝒪[L] y) = algebraMap 𝒪[M] 𝒪[L] y :=
    fun τ y => Subtype.ext (τ.commutes (y : M))
  have hinj : Function.Injective a := by
    intro τ ρ h
    have h1 : r (ρ⁻¹ * τ) x - x = 0 := by
      change a (ρ⁻¹ * τ) - x = 0
      rw [← hamul, h, hamul, inv_mul_cancel, ha1, sub_self]
    have h2 : lowerIndex K L ((ρ⁻¹ * τ).restrictScalars K) = ⊤ := by
      rw [lowerIndex_eq_addVal_of_adjoin_eq_top hx, addVal_eq_top_iff]
      exact h1
    rw [lowerIndex_restrictScalars, lowerIndex_eq_top_iff, inv_mul_eq_one] at h2
    exact h2.symm
  have hsum : ∑ τ : Gal(L/M), lowerIndex K L (σ * τ.restrictScalars K) =
      addVal 𝒪[L] (∏ τ, (x - s (a τ))) := by
    rw [addVal_prod]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [lowerIndex_eq_addVal_of_adjoin_eq_top hx, ← AddValuation.map_neg, neg_sub]
    rfl
  obtain ⟨y₀, hy₀⟩ := ENat.exists_eq_iInf
    (fun y : 𝒪[M] => addVal 𝒪[M] (integerAlgEquiv K M σ' y - y))
  have hy₁ : lowerIndex K M σ' = addVal 𝒪[M] (integerAlgEquiv K M σ' y₀ - y₀) := hy₀.symm
  rw [hsum, hy₁, ← hv]
  apply le_antisymm
  · rw [addVal_le_iff_dvd, ← ha1]
    refine dvd_prod a 1 _ (s : 𝒪[L] →+* 𝒪[L]) fun i => ?_
    set f : 𝒪[L][X] := ∏ τ, (X - C (a τ)) with hf
    have hfr : ∀ ρ, r ρ (f.coeff i) = f.coeff i := by
      intro ρ
      have : f.map (r ρ : 𝒪[L] →+* 𝒪[L]) = f := by
        rw [hf, Polynomial.map_prod]
        refine Fintype.prod_equiv (Equiv.mulLeft ρ) _ _ fun τ => ?_
        rw [Polynomial.map_sub, map_X, map_C]
        rfl
      conv_rhs => rw [← this, coeff_map]
      rfl
    obtain ⟨m, hm⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := M)
      ((f.coeff i : 𝒪[L]) : L)).2 fun ρ => congrArg Subtype.val (hfr ρ)
    have hm1 : m ∈ 𝒪[M] := by
      have h1 : valuation L (algebraMap M L m) ≤ 1 := by rw [hm]; exact (f.coeff i).2
      exact (Valuation.HasExtension.val_map_le_one_iff (valuation M) (valuation L) m).1 h1
    have hy : f.coeff i = algebraMap 𝒪[M] 𝒪[L] ⟨m, hm1⟩ := Subtype.ext hm.symm
    rw [hy, RingHom.coe_coe, hcomm, ← map_sub]
    apply _root_.map_dvd
    rw [← addVal_le_iff_dvd, ← hy₁]
    exact lowerIndex_le _ _
  · rw [addVal_le_iff_dvd, map_sub, ← hcomm]
    have hz : algebraMap 𝒪[M] 𝒪[L] y₀ ∈ Algebra.adjoin 𝒪[K] {x} := hx ▸ trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨g, hg⟩ := hz
    replace hg : aeval x g = algebraMap 𝒪[M] 𝒪[L] y₀ := hg
    refine prod_dvd_sub a hinj x _ (s : 𝒪[L] →ₐ[𝒪[K]] 𝒪[L]) g (fun τ => ?_) hg
    rw [← hfix τ, ← hg]
    exact aeval_algHom_apply (r τ) x g
end UpperTheory.Reformulated.B.RamificationLowerIndex.ramificationIndex_mul_lowerIndex_restrictNormalHom
