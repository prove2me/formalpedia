-- Prove2me | solution 1 for ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_mul_of_pow_eq_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/11fcd7b9-d011-58d1-ae94-260c9657a3d9

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one
import Theorems.Thm_ValuationSubring_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
import Theorems.Thm_KummerTheory_powerSubgroup_eq_closure_sup_range_of_isSplittingField
import Theorems.Thm_ValuationSubring_exists_forall_mem_inertiaSubgroupIn_apply_eq_and_pow_eq_pow_of_isPrimitiveRoot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_mul_of_pow_eq_prime
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false

namespace KummerIndependence

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) (P : ValuationSubring ℚ̄) (hP : P.LiesOverPrime p)

noncomputable abbrev K : IntermediateField ℚ ℚ̄ := IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)

lemma forall_apply_eq_of_apply_eq {ζ : ℚ̄} (hζ : IsPrimitiveRoot ζ (p ^ N)) (hn : 0 < p ^ N) (τ : Γ)
    (hτ : τ ζ = ζ) : ∀ ζ' : ℚ̄, ζ' ^ p ^ N = 1 → τ ζ' = ζ' := by
  haveI : NeZero (p ^ N) := ⟨hn.ne'⟩
  intro ζ' hζ'
  obtain ⟨k, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hζ'
  rw [map_pow, hτ]

include hp hP in
lemma mem_inertia_of_forall_mem_inertiaField (τ : Γ) (hτ : ∀ y ∈ K P, τ y = y) :
    τ ∈ P.inertiaSubgroupIn ℚ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨O, -, -, -, -, -, hiff, -⟩ :=
    ValuationSubring.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq p P hP
  refine (hiff τ).2 fun x hx => hτ x ?_
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  exact (hiff σ).1 hσ x hx

lemma exists_prod_zpow_mul_pow_eq_of_mem_adjoin (hn : 0 < p ^ N) (K₀ : IntermediateField ℚ ℚ̄) {ζ : ℚ̄}
    (hζ : IsPrimitiveRoot ζ (p ^ N)) (hζK : ζ ∈ K₀) {t : ℕ} (u β : Fin t → ℚ̄) (huK : ∀ i, u i ∈ K₀)
    (hu0 : ∀ i, u i ≠ 0) (hβ : ∀ i, β i ^ p ^ N = u i) (x : ℚ̄) (hxK : x ∈ K₀) (hx0 : x ≠ 0) (γ : ℚ̄)
    (hγx : γ ^ p ^ N = x) (hγ : γ ∈ IntermediateField.adjoin K₀ (Set.range β)) :
    ∃ (a : Fin t → ℤ) (w : ℚ̄), w ∈ K₀ ∧ x = (∏ i, u i ^ a i) * w ^ p ^ N := by
  classical

  let uK : Fin t → (↥K₀)ˣ := fun i => Units.mk0 ⟨u i, huK i⟩ (fun h => hu0 i (congrArg Subtype.val h))
  let S : Finset (↥K₀)ˣ := Finset.univ.image uK
  let f : Polynomial ↥K₀ := ∏ s ∈ S, (Polynomial.X ^ (p ^ N) - Polynomial.C ((s : (↥K₀)ˣ) : ↥K₀))
  have hsplit : (f.map (algebraMap (↥K₀) ℚ̄)).Splits := IsAlgClosed.splits _
  let L' : IntermediateField (↥K₀) ℚ̄ := IntermediateField.adjoin (↥K₀) (f.rootSet ℚ̄)
  haveI : Polynomial.IsSplittingField (↥K₀) (↥L') f := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K₀) (p ^ N) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (↥K₀) ℚ̄) (show IsPrimitiveRoot ζ (p ^ N) from hζ)
      (algebraMap (↥K₀) ℚ̄).injective
  have hμ : (primitiveRoots (p ^ N) (↥K₀)).Nonempty := ⟨⟨ζ, hζK⟩, (mem_primitiveRoots hn).2 hζK'⟩
  have key := KummerTheory.powerSubgroup_eq_closure_sup_range_of_isSplittingField (↥K₀) (↥L') hμ S

  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => Polynomial.X_pow_sub_C_ne_zero hn _
  have hβroot : ∀ i, β i ∈ f.rootSet ℚ̄ := by
    intro i
    rw [Polynomial.mem_rootSet_of_ne hf0, map_prod]
    apply Finset.prod_eq_zero (Finset.mem_image_of_mem uK (Finset.mem_univ i))
    simp [uK, hβ i]
  have hγL : γ ∈ L' := IntermediateField.adjoin.mono _ _ _ (Set.range_subset_iff.2 hβroot) hγ
  have hγ0 : γ ≠ 0 := by intro h0; rw [h0, zero_pow hn.ne'] at hγx; exact hx0 hγx.symm

  let xK : (↥K₀)ˣ := Units.mk0 ⟨x, hxK⟩ (fun h => hx0 (congrArg Subtype.val h))
  have hxmem : xK ∈ groupCohomology.Kummer.powerSubgroup (↥K₀) (↥L') (p ^ N) := by
    refine ⟨Units.mk0 ⟨γ, hγL⟩ (fun h => hγ0 (congrArg Subtype.val h)), Subtype.ext ?_⟩
    change x = ((⟨γ, hγL⟩ : ↥L') ^ p ^ N : ↥L').1
    rw [SubmonoidClass.coe_pow]
    exact hγx.symm
  rw [key, Subgroup.mem_sup] at hxmem
  obtain ⟨y, hy, z, ⟨wK, rfl⟩, hyz⟩ := hxmem
  have hS : (S : Set (↥K₀)ˣ) = Set.range uK := by simp [S]
  rw [hS] at hy
  obtain ⟨a, rfl⟩ := Subgroup.mem_closure_range_iff_of_fintype.mp hy
  refine ⟨a, ((wK : ↥K₀) : ℚ̄), (wK : ↥K₀).2, ?_⟩

  have h := congrArg (fun v : (↥K₀)ˣ => ((v : ↥K₀) : ℚ̄)) hyz
  simp only [powMonoidHom_apply, Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod,
    Units.val_zpow_eq_zpow_val, SubmonoidClass.coe_pow, MulMemClass.coe_mul] at h
  have huK' : ∀ i, (((uK i : (↥K₀)ˣ) : ↥K₀) : ℚ̄) = u i := fun _ => rfl
  have hxK' : (((xK : (↥K₀)ˣ) : ↥K₀) : ℚ̄) = x := rfl
  rw [hxK'] at h
  rw [← h]
  congr 1
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  change algebraMap (↥K₀) ℚ̄ (((uK i : (↥K₀)ˣ) : ↥K₀) ^ a i) = u i ^ a i
  rw [map_zpow₀]
  rfl

include hp hp2 hP in
lemma descent {ζ : ℚ̄} (hζ : IsPrimitiveRoot ζ (p ^ N)) (w : ℚ̄)
    (hw : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ ζ = ζ → σ w = w)
    (hx : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (w ^ p ^ N) = w ^ p ^ N) :
    ∃ w' : ℚ̄, (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ w' = w') ∧ w' ^ p ^ N = w ^ p ^ N :=
  ValuationSubring.exists_forall_mem_inertiaSubgroupIn_apply_eq_and_pow_eq_pow_of_isPrimitiveRoot p hp hp2 N P hP ζ hζ
    w hw hx

include hp hP in
lemma not_exists_prod_zpow_mul_pow_eq (hN : 1 ≤ N) {t : ℕ} (u : Fin t → ℚ̄)
    (hu : ∀ i, P.valuation (u i) = 1) (huI : ∀ i, ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (u i) = u i) :
    ¬ ∃ (a : Fin t → ℤ) (w' : ℚ̄), (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ w' = w') ∧
        (p : ℚ̄) ^ p ^ (N - 1) = (∏ i, u i ^ a i) * w' ^ p ^ N := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  rintro ⟨a, w', hw'I, heq⟩
  obtain ⟨O, hOP, hrat, hdvr, hirr, -, -, hfixO⟩ :=
    ValuationSubring.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq p P hP
  haveI : IsDiscreteValuationRing O := hdvr
  have hp0 : (p : ℚ̄) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero

  set x : ℚ̄ := ∏ i, u i ^ a i with hxdef
  have hxval : P.valuation x = 1 := by
    rw [hxdef, map_prod]
    exact Finset.prod_eq_one fun i _ => by rw [map_zpow₀, hu, one_zpow]
  have hxI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x = x := fun σ hσ => by
    rw [hxdef, map_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [map_zpow₀, huI i σ hσ]
  have hx0 : x ≠ 0 := by intro h0; rw [h0, map_zero] at hxval; exact zero_ne_one hxval
  have hxO : x ∈ O := hfixO x ((P.valuation_le_one_iff x).1 hxval.le) hxI
  have hxiO : x⁻¹ ∈ O := hfixO x⁻¹ ((P.valuation_le_one_iff _).1 (by rw [map_inv₀, hxval, inv_one]))
    (fun σ hσ => by rw [map_inv₀]; exact congrArg (·⁻¹) (hxI σ hσ))
  have hxunit : IsUnit (⟨x, hxO⟩ : O) :=
    IsUnit.of_mul_eq_one (b := ⟨x⁻¹, hxiO⟩) (Subtype.ext (mul_inv_cancel₀ hx0))

  have hpP : (p : ℚ̄) ∈ P := natCast_mem P p
  have hw'pow : w' ^ p ^ N = (p : ℚ̄) ^ p ^ (N - 1) * x⁻¹ := by
    rw [heq, mul_comm x, mul_assoc, mul_inv_cancel₀ hx0, mul_one]
  have hw'P : w' ∈ P := by
    have h1 : P.valuation (w' ^ p ^ N) ≤ 1 := by
      rw [hw'pow, map_mul, map_inv₀, hxval, inv_one, mul_one, map_pow]
      exact pow_le_one' ((P.valuation_le_one_iff _).2 hpP) _
    rw [map_pow] at h1
    exact (P.valuation_le_one_iff _).1 ((pow_le_one_iff (pow_pos hp.pos N).ne').1 h1)
  have hw'O : w' ∈ O := hfixO w' hw'P hw'I

  have hpO : ((p : O) : ℚ̄) = (p : ℚ̄) := by push_cast; rfl
  have hrel : (p : O) ^ p ^ (N - 1) = ⟨x, hxO⟩ * ⟨w', hw'O⟩ ^ p ^ N := by
    apply Subtype.ext
    push_cast
    exact heq
  have hval := congrArg (IsDiscreteValuationRing.addVal O) hrel
  rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hirr,
    IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
    (IsDiscreteValuationRing.addVal_eq_zero_iff).2 hxunit, zero_add] at hval

  have hw'0 : (⟨w', hw'O⟩ : O) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_pos hp.pos N).ne', mul_zero] at hrel
    exact pow_ne_zero _ hirr.ne_zero hrel
  have hvtop : IsDiscreteValuationRing.addVal O ⟨w', hw'O⟩ ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, IsDiscreteValuationRing.addVal O ⟨w', hw'O⟩ = k :=
    ⟨_, (ENat.coe_toNat hvtop).symm⟩
  rw [hk, nsmul_eq_mul, nsmul_eq_mul, mul_one] at hval
  norm_cast at hval
  have hdvd : p ^ N ∣ p ^ (N - 1) := ⟨k, hval⟩
  have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
  omega

include hp in

lemma exists_apply_eq_mul_of_exists_apply_ne (hn : 0 < p ^ N) {ζ : ℚ̄} (hζ : IsPrimitiveRoot ζ (p ^ N))
    (ϖ : ℚ̄) (hϖ : ϖ ^ p ^ N = (p : ℚ̄)) (J : Set Γ) (hJpow : ∀ τ ∈ J, ∀ m : ℕ, τ ^ m ∈ J)
    (hJζ : ∀ τ ∈ J, ∀ ζ' : ℚ̄, ζ' ^ p ^ N = 1 → τ ζ' = ζ')
    (h : ∃ τ ∈ J, τ (ϖ ^ p ^ (N - 1)) ≠ ϖ ^ p ^ (N - 1)) :
    ∃ τ ∈ J, τ ϖ = ζ * ϖ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨τ, hτJ, hτγ⟩ := h
  have hp0 : (p : ℚ̄) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, zero_pow hn.ne'] at hϖ; exact hp0 hϖ.symm

  set η : ℚ̄ := τ ϖ * ϖ⁻¹ with hη
  have hτϖ : τ ϖ = η * ϖ := by rw [hη, inv_mul_cancel_right₀ hϖ0]
  have hηpow : η ^ p ^ N = 1 := by
    rw [hη, mul_pow, ← map_pow, hϖ, map_natCast, inv_pow, hϖ, mul_inv_cancel₀ hp0]
  have hpowϖ : ∀ m : ℕ, (τ ^ m) ϖ = η ^ m * ϖ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hτϖ, map_mul, ih, hJζ _ (hJpow τ hτJ m) η hηpow, pow_succ]
      ring

  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · exfalso; apply hτγ
      subst h0
      simp only [pow_zero, Nat.zero_sub, pow_one] at hϖ ⊢
      rw [hϖ, map_natCast]
    · exact ⟨N - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [Nat.add_sub_cancel] at hτγ

  have hηn : ¬ η ^ p ^ n = 1 := by
    intro h1
    apply hτγ
    have := hpowϖ 1
    rw [pow_one, pow_one] at this
    rw [map_pow, this, mul_pow, h1, one_mul]
  have hηprim : IsPrimitiveRoot η (p ^ (n + 1)) := by
    have hord := orderOf_eq_prime_pow hηn hηpow
    rw [← hord]
    exact IsPrimitiveRoot.orderOf η

  obtain ⟨m, -, hm⟩ := hηprim.eq_pow_of_pow_eq_one hζ.pow_eq_one
  exact ⟨τ ^ m, hJpow τ hτJ m, by rw [hpowϖ, hm]⟩

include hp hp2 hP in
theorem main (ζ : ℚ̄) (hζ : IsPrimitiveRoot ζ (p ^ N)) {t : ℕ} (u β : Fin t → ℚ̄)
    (hu : ∀ i, P.valuation (u i) = 1) (huI : ∀ i, ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (u i) = u i)
    (hβ : ∀ i, β i ^ p ^ N = u i) (ϖ : ℚ̄) (hϖ : ϖ ^ p ^ N = (p : ℚ̄)) :
    ∃ τ ∈ P.inertiaSubgroupIn ℚ,
      (∀ ζ' : ℚ̄, ζ' ^ p ^ N = 1 → τ ζ' = ζ') ∧ (∀ i, τ (β i) = β i) ∧ τ ϖ = ζ * ϖ := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ _
  have hn : 0 < p ^ N := pow_pos hp.pos N
  set I : Subgroup Γ := P.inertiaSubgroupIn ℚ with hIdef

  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have hζ1 : ζ = 1 := by simpa using hζ
    refine ⟨1, I.one_mem, fun _ _ => rfl, fun _ => rfl, ?_⟩
    rw [hζ1, one_mul]; rfl

  set J : Set Γ := {τ | τ ∈ I ∧ (∀ ζ' : ℚ̄, ζ' ^ p ^ N = 1 → τ ζ' = ζ') ∧ ∀ i, τ (β i) = β i} with hJdef
  have hJpow : ∀ τ ∈ J, ∀ m : ℕ, τ ^ m ∈ J := by
    rintro τ ⟨hτI, hτζ, hτβ⟩ m
    refine ⟨I.pow_mem hτI m, fun ζ' hζ' => ?_, fun i => ?_⟩
    · induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ, AlgEquiv.mul_apply, hτζ ζ' hζ', ih]
    · induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ, AlgEquiv.mul_apply, hτβ i, ih]

  suffices hmove : ∃ τ ∈ J, τ (ϖ ^ p ^ (N - 1)) ≠ ϖ ^ p ^ (N - 1) by
    obtain ⟨τ, ⟨hτI, hτζ, hτβ⟩, hτϖ⟩ :=
      exists_apply_eq_mul_of_exists_apply_ne p hp N hn hζ ϖ hϖ J hJpow (fun τ hτ => hτ.2.1) hmove
    exact ⟨τ, hτI, hτζ, hτβ, hτϖ⟩
  by_contra hcon
  push Not at hcon

  set γ : ℚ̄ := ϖ ^ p ^ (N - 1) with hγdef
  set S : Set ℚ̄ := insert ζ (Set.range β) with hSdef
  set E : IntermediateField ℚ ℚ̄ := K P ⊔ IntermediateField.adjoin ℚ S with hEdef
  have hEfix : ∀ τ : Γ, τ ∈ E.fixingSubgroup → τ ∈ J := by
    intro τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    have hS : S ⊆ (E : Set ℚ̄) := fun s hs =>
      (le_sup_right : IntermediateField.adjoin ℚ S ≤ E) (IntermediateField.subset_adjoin _ _ hs)
    refine ⟨?_, forall_apply_eq_of_apply_eq p N hζ hn τ (hτ ζ (hS (Set.mem_insert _ _))),
      fun i => hτ (β i) (hS (Set.mem_insert_of_mem _ ⟨i, rfl⟩))⟩
    exact mem_inertia_of_forall_mem_inertiaField p hp P hP τ (fun y hy => hτ y ((le_sup_left : K P ≤ E) hy))
  have hγE : γ ∈ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    exact fun τ hτ => hcon τ (hEfix τ hτ)

  set K₀ : IntermediateField ℚ ℚ̄ := K P ⊔ IntermediateField.adjoin ℚ {ζ} with hK₀def
  have huK : ∀ i, u i ∈ K₀ := fun i =>
    (le_sup_left : K P ≤ K₀) ((IntermediateField.mem_fixedField_iff _ _).2 (fun σ hσ => huI i σ hσ))
  have hζK : ζ ∈ K₀ := (le_sup_right : IntermediateField.adjoin ℚ {ζ} ≤ K₀)
    (IntermediateField.subset_adjoin _ _ (Set.mem_singleton ζ))
  have hmem : γ ∈ IntermediateField.adjoin K₀ (Set.range β) := by
    have hK₀le : ∀ y ∈ K₀, y ∈ IntermediateField.adjoin K₀ (Set.range β) := fun y hy =>
      (IntermediateField.adjoin K₀ (Set.range β)).algebraMap_mem ⟨y, hy⟩
    have hE : E ≤ (IntermediateField.adjoin K₀ (Set.range β)).restrictScalars ℚ := by
      refine sup_le ?_ ?_
      · intro y hy
        rw [IntermediateField.mem_restrictScalars]
        exact hK₀le y ((le_sup_left : K P ≤ K₀) hy)
      · rw [IntermediateField.adjoin_le_iff]
        intro s hs
        change s ∈ IntermediateField.adjoin K₀ (Set.range β)
        rcases hs with rfl | ⟨i, rfl⟩
        · exact hK₀le _ hζK
        · exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    exact (IntermediateField.mem_restrictScalars ℚ).mp (hE hγE)

  have hu0 : ∀ i, u i ≠ 0 := by
    intro i h0
    have h1 := hu i
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have hxK₀ : (p : ℚ̄) ^ p ^ (N - 1) ∈ K₀ := pow_mem (natCast_mem K₀ p) _
  have hx0' : (p : ℚ̄) ^ p ^ (N - 1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  have hγpow : γ ^ p ^ N = (p : ℚ̄) ^ p ^ (N - 1) := by
    rw [hγdef, ← pow_mul, mul_comm, pow_mul, hϖ]
  obtain ⟨a, w, hwK, hw⟩ :=
    exists_prod_zpow_mul_pow_eq_of_mem_adjoin p N hn K₀ hζ hζK u β huK hu0 hβ _ hxK₀ hx0' γ hγpow hmem
  rw [← hγpow] at hw

  have hprodI : ∀ σ ∈ I, σ (∏ i, u i ^ a i) = ∏ i, u i ^ a i := by
    intro σ hσ
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => by rw [map_zpow₀, huI i σ hσ])
  have hprod0 : (∏ i, u i ^ a i) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => zpow_ne_zero _ (hu0 i))
  have hwfixζ : ∀ σ ∈ I, σ ζ = ζ → σ w = w := by
    intro σ hσ hσζ

    have hle : K₀ ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      refine sup_le ?_ ?_
      · intro y hy
        rw [IntermediateField.mem_fixedField_iff]
        rintro _ ⟨k, rfl⟩
        exact (IntermediateField.mem_fixedField_iff _ _).1 hy _ (I.zpow_mem hσ k)
      · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        change ζ ∈ IntermediateField.fixedField (Subgroup.zpowers σ)
        rw [IntermediateField.mem_fixedField_iff]
        rintro _ ⟨k, rfl⟩

        have h1 : σ⁻¹ ζ = ζ := by
          conv_lhs => rw [← hσζ]
          rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
        induction k using Int.induction_on with
        | zero => rfl
        | succ k ih =>
          dsimp only at ih ⊢
          rw [zpow_add_one, AlgEquiv.mul_apply, hσζ, ih]
        | pred k ih =>
          dsimp only at ih ⊢
          rw [zpow_sub_one, AlgEquiv.mul_apply, h1, ih]
    exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hwK) σ (Subgroup.mem_zpowers σ)
  have hwpowI : ∀ σ ∈ I, σ (w ^ p ^ N) = w ^ p ^ N := by
    intro σ hσ

    have hwval : w ^ p ^ N = γ ^ p ^ N / ∏ i, u i ^ a i := by
      rw [hw, mul_div_cancel_left₀ _ hprod0]
    rw [hwval, map_div₀, hprodI σ hσ, hγpow, map_pow, map_natCast]
  obtain ⟨w', hw'I, hw'⟩ := descent p hp hp2 N P hP hζ w hwfixζ hwpowI

  exact not_exists_prod_zpow_mul_pow_eq p hp N P hP hNpos u hu huI ⟨a, w', hw'I, by rw [hw', ← hγpow, hw]⟩

end KummerIndependence

theorem solution
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N)) {t : ℕ} (u β : Fin t → AlgebraicClosure ℚ)
    (hu : ∀ i, P.valuation (u i) = 1) (huI : ∀ i, ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (u i) = u i)
    (hβ : ∀ i, β i ^ p ^ N = u i) (ϖ : AlgebraicClosure ℚ) (hϖ : ϖ ^ p ^ N = (p : AlgebraicClosure ℚ)) :
    ∃ τ ∈ P.inertiaSubgroupIn ℚ,
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) ∧ (∀ i, τ (β i) = β i) ∧ τ ϖ = ζ * ϖ :=
  KummerIndependence.main p hp hp2 N P hP ζ hζ u β hu huI hβ ϖ hϖ

end S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_mul_of_pow_eq_prime
end P2MW
export P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_mul_of_pow_eq_prime (solution)
