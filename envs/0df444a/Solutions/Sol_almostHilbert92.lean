-- Prove2me | solution 1 for almostHilbert92
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:33.620776+00:00
-- url     : https://prove2.me/submissions/795b01ac-5f32-458d-8746-d7b11e7ff263

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Theorems.Thm_systemOfUnits_IsFundamental_corollary
public import Theorems.Thm_Hilbert92_aux0
public import Theorems.Thm_unit_to_U_mul
public import Theorems.Thm_unit_to_U_inv
public import Theorems.Thm_unit_to_U_prod
public import Theorems.Thm_unit_to_U_pow
public import Theorems.Thm_unit_to_U_zpow
public import Theorems.Thm_unit_to_U_map
public import Theorems.Thm_lh_pow_free
public import Theorems.Thm_Hilbert92_aux1
public import Theorems.Thm_unitlifts_spec
public import Theorems.Thm_u_lemma2
public import Theorems.Thm_Hilbert92_aux2
public import Theorems.Thm_finrank_G
public import Theorems.Thm_Hilbert91
public import Theorems.Thm_P2M_h_exists__3f6441b4d557

set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField nonZeroDivisors
open FiniteDimensional NumberField
variable {s r : ℕ} (p : ℕ) {K : Type*} [Field K]
variable {k : Type*} [Field k] (hp : Nat.Prime p)
open Module Finset
open CyclotomicIntegers (zeta)
variable (G : Type*) [AddCommGroup G]
local notation3 "A" => CyclotomicIntegers p
variable
    [Algebra k K] (hKL : finrank k K = p) (σ : K ≃ₐ[k] K)
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
local notation "G" =>
  Additive (relativeUnitsWithGenerator p hp hKL σ hσ) ⧸
    AddCommGroup.torsion (Additive (relativeUnitsWithGenerator p hp hKL σ hσ))
local notation "mkG" => unitToU p hp hKL σ hσ
variable [NumberField k]
variable [NumberField K]
variable [IsGalois k K]
attribute [local instance] _p2m_local_instance_fee6646a52_507
attribute [local instance] _p2m_local_instance_fee6646a52_512
attribute [local instance] _p2m_local_instance_fee6646a52_515
variable [IsUnramifiedAtInfinitePlaces k K]
local notation "r" => NumberField.Units.rank k
include hp hKL hσ
theorem _root_.solution (hpodd : p ≠ 2) : ∃ η : (𝓞 K)ˣ, Algebra.norm k (η : K) = 1 ∧
      ∀ ε : (𝓞 K)ˣ, (η : K) ≠ ε / (σ ε : K) := by
  classical
  obtain ⟨h, ν, hν, hν'⟩ := h_exists' p (k := k) hp
  by_cases H : ∀ ε : (𝓞 K)ˣ, algebraMap k K ν ^ (p ^ (h - 1)) ≠ ε / (σ ε : K)
  · exact Hilbert92_aux0 p hKL σ h ν hν H
  simp only [ne_eq, not_forall, not_not] at H
  obtain ⟨E, hE⟩ := H
  let NE := Units.map (RingOfIntegers.norm k) E
  obtain ⟨S, hS⟩ := Hilbert91 p (K := K) (k := k) hp hKL σ hσ
  have NE_p_pow : (Units.map (algebraMap (𝓞 k) (𝓞 K)).toMonoidHom NE) = E ^ p := by
    ext
    have hNE : ((Units.map (algebraMap (𝓞 k) (𝓞 K)).toMonoidHom NE : (𝓞 K)ˣ) : K) =
        algebraMap k K (Algebra.norm k (S := K) (E : K)) := by
      change algebraMap k K ((RingOfIntegers.norm k (E : 𝓞 K) : 𝓞 k) : k) = _
      rw [RingOfIntegers.coe_norm]
    simp only [RingOfIntegers.coe_eq_algebraMap, Units.val_pow_eq_pow_val, map_pow]
    rw [hNE]
    rw [← map_pow] at hE
    refine Hilbert92_aux2 p hp hKL σ hσ E _ hE ?_ hpodd
    rw [← pow_mul, ← pow_succ]
    apply (hν.pow_eq_one_iff_dvd _).2
    cases h <;> simp only [pow_zero, zero_le, tsub_eq_zero_of_le, zero_add, pow_one, one_dvd,
      Nat.succ_sub_succ_eq_sub, tsub_zero, dvd_refl]
  let H := unitlifts p hp hKL σ hσ S
  let N : Fin (r + 1) → Additive (𝓞 k)ˣ :=
    fun e ↦ Additive.ofMul (Units.map (RingOfIntegers.norm k) (Additive.toMul (H e)))
  let η : Fin (r + 2) → Additive (𝓞 k)ˣ := Fin.snoc N (Additive.ofMul NE)
  obtain ⟨a, ι, i, ha, ha', ha''⟩ := lh_pow_free p hp ν (k := k) hν' η
  let H2 : Fin (r + 2) → Additive (𝓞 K)ˣ := Fin.snoc H (Additive.ofMul E)
  let J :=
    Additive.toMul (∑ i : Fin (r + 2), ι i • H2 i) *
      (Units.map (algebraMap (𝓞 k) (𝓞 K)).toMonoidHom ν) ^ (-a)
  refine ⟨J, ?_⟩
  constructor
  · apply Hilbert92_aux1 p hKL (r + 2) H2 ν a ι η ha
    intro i
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, toMul_ofMul, Units.coe_map, RingOfIntegers.coe_norm, NE, η, H2]
    | cast i =>
      simp only [Fin.snoc_castSucc, toMul_ofMul, Units.coe_map, RingOfIntegers.coe_norm, NE,
        η, H2, N, H]
  · intro ε hε
    refine hS.corollary p hp _ _ (finrank_G p hp hKL σ hσ) _ (ι ∘ Fin.castSucc) ?_ (mkG ε) ?_
    · by_contra hε'
      simp only [Function.comp_apply, not_exists, not_not] at hε'
      have : i ∉ Set.range Fin.castSucc := by
        rintro ⟨i, rfl⟩
        exact ha' (hε' i)
      rw [← Fin.succAbove_last, Fin.range_succAbove, Set.mem_compl_iff,
        Set.mem_singleton_iff, not_not] at this
      rw [this] at ha'
      cases h with
      | zero =>
          refine ha'' ?_ this
          ext
          simpa only [Units.val_one, map_one, pow_zero, IsPrimitiveRoot.one_right_iff] using hν
      | succ h =>
          obtain ⟨ε', hε'⟩ : ∃ ε' : (𝓞 k)ˣ, ε' ^ p = NE := by
            rw [← (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd] at ha'
            obtain ⟨α, β, hαβ⟩ := ha'
            choose ι' hι' using hε'
            rw [Fin.sum_univ_castSucc] at ha
            simp (config := { zeta := false, proj := false }) only
              [hι', Fin.snoc_castSucc, Fin.snoc_last, mul_smul, η] at ha
            rw [Finset.sum_zsmul, add_comm, ← eq_sub_iff_add_eq, smul_comm, ← zsmul_sub] at ha
            apply_fun ((p : ℤ) • (α • Additive.ofMul NE) + β • ·) at ha
            conv_rhs at ha => rw [smul_comm β, ← zsmul_add]
            rw [smul_smul, smul_smul, ← add_zsmul, mul_comm _ α, hαβ, one_zsmul] at ha
            exact ⟨_, ha.symm⟩
          have hν'' := (hν.pow (pow_pos hp.pos _) (pow_succ _ _)).map_of_injective
            (algebraMap k K).injective
          obtain ⟨ε'', hε''⟩ :
              ∃ ε'' : (𝓞 k)ˣ,
                E = Units.map (algebraMap (𝓞 k) (𝓞 K)).toMonoidHom ε'' := by
              rw [← hε', map_pow, eq_comm, ← mul_inv_eq_one, ← inv_pow,
                ← mul_pow] at NE_p_pow
              apply_fun ((↑) : (𝓞 K)ˣ → K) at NE_p_pow
              have hε'inv : (((Units.map (algebraMap (𝓞 k) (𝓞 K)).toMonoidHom ε')⁻¹ : (𝓞 K)ˣ) : 𝓞 K) =
                  (algebraMap (𝓞 k) (𝓞 K)) ((ε'⁻¹ : (𝓞 k)ˣ) : 𝓞 k) := by
                rw [← map_inv]; rfl
              simp only [Units.val_pow_eq_pow_val, Units.val_mul, map_pow, map_mul, hε'inv, Units.val_one, map_one] at NE_p_pow
              have : NeZero p := ⟨hp.pos.ne'⟩
              obtain ⟨i, -, e⟩ := hν''.eq_pow_of_pow_eq_one NE_p_pow
              use ((ν ^ p ^ h) ^ i * ε')
              rw [map_mul, ← mul_inv_eq_iff_eq_mul]
              ext
              have hνcoe : (algebraMap k K) ((algebraMap (𝓞 k) k) (ν : 𝓞 k)) =
                  (algebraMap (𝓞 K) K) ((algebraMap (𝓞 k) (𝓞 K)) (ν : 𝓞 k)) := rfl
              simpa [hνcoe, hε'inv] using e.symm
          have hε''coe :
              ((algebraMap (𝓞 k) (𝓞 K) (ε'' : 𝓞 k) : 𝓞 K) : K) =
                algebraMap k K (ε'' : k) := rfl
          have hε''coe' :
              (algebraMap (𝓞 K) K) ((Units.map (algebraMap (𝓞 k) (𝓞 K)).toMonoidHom ε'' : (𝓞 K)ˣ) : 𝓞 K) =
                algebraMap k K (ε'' : k) := hε''coe
          simp only [Nat.succ_sub_succ_eq_sub, tsub_zero, ← map_pow, hε'',
            hε''coe', AlgEquiv.commutes] at hE
          replace hE : (algebraMap k K) (((ν : 𝓞 k) : k) ^ p ^ h) = 1 := by
            rwa [div_self (by simp)] at hE
          rw [hE] at hν''
          rw [IsPrimitiveRoot.one_left_iff] at hν''
          exact hp.one_lt.ne.symm hν''
    · rw [← u_lemma2 p hp hKL σ hσ _ _ hε, unit_to_U_mul, toMul_sum, unit_to_U_prod,
        Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, toMul_zsmul, unit_to_U_zpow, unitlifts_spec, Fin.snoc_last,
        toMul_ofMul, RingHom.toMonoidHom_eq_coe, zpow_neg, unit_to_U_inv, Function.comp_apply,
        unit_to_U_map, smul_zero, neg_zero, add_zero, add_eq_left, H2, H]
      apply_fun mkG at NE_p_pow
      simp only [RingHom.toMonoidHom_eq_coe, unit_to_U_map, unit_to_U_pow] at NE_p_pow
      rw [eq_comm, smul_eq_zero] at NE_p_pow
      simp only [hp.ne_zero, false_or] at NE_p_pow
      rw [NE_p_pow, smul_zero]
