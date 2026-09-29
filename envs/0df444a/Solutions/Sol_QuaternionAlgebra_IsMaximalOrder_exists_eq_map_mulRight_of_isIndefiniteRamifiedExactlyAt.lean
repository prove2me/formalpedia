-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/301a90d1-9926-533f-942d-987c32cc9af3

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_BaseChange
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_nrd_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_of_forall_mul_mem_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_Submodule_ofFiniteIdele_diagonal_mul
import Theorems.Thm_Submodule_ofFiniteIdele_eq_ofFiniteIdele_iff
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

noncomputable section

section RatIdele

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace CN1Glue29

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem asIdeal_eq_span_natGenerator (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator w : ℕ) : 𝓞 ℚ)} := by
  set e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) w
  have h1 : w.asIdeal = (w.asIdeal.map e).comap e := (Ideal.comap_map_of_bijective e e.bijective).symm
  rw [h1, ← h, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton]
  congr 2
  simp [e]

theorem valuation_natGenerator_self (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.valuation ℚ ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [show ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ) =
      algebraMap (𝓞 ℚ) ℚ ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  refine HeightOneSpectrum.intValuation_singleton w ?_ (asIdeal_eq_span_natGenerator w)
  exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator w).ne_zero

theorem valuation_natCast_eq_one_of_not_dvd (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (hn : ¬ Rat.HeightOneSpectrum.natGenerator w ∣ n) : w.valuation ℚ (n : ℚ) = 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) from (map_natCast _ _).symm]
  refine (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 ?_
  rwa [natCast_mem_asIdeal_iff]

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem natGenerator_injective {w w' : HeightOneSpectrum (𝓞 ℚ)}
    (h : Rat.HeightOneSpectrum.natGenerator w = Rat.HeightOneSpectrum.natGenerator w') : w = w' := by
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext h

open scoped Classical in
theorem valuation_natGenerator (w₀ w : HeightOneSpectrum (𝓞 ℚ)) :
    w₀.valuation ℚ ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ) =
      if w = w₀ then WithZero.exp (-1 : ℤ) else 1 := by
  by_cases h : w = w₀
  · subst h; rw [if_pos rfl]; exact valuation_natGenerator_self w
  · rw [if_neg h]
    apply valuation_natCast_eq_one_of_not_dvd
    intro hd
    apply h
    have := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w₀)
      (Rat.HeightOneSpectrum.prime_natGenerator w)).1 hd
    exact (natGenerator_injective this).symm

theorem exp_neg_one_zpow (n : ℤ) : (WithZero.exp (-1 : ℤ)) ^ n = WithZero.exp (-n) := by
  rw [WithZero.exp, WithZero.exp, ← WithZero.coe_zpow, ← ofAdd_zsmul, smul_neg, zsmul_eq_mul, mul_one, Int.cast_id]

theorem rat_finiteIdele_eq_valuation (α : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) :
    ∃ r : ℚ, r ≠ 0 ∧ ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      Valued.v (((α : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) w) =
        Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) := by
  classical
  set A : FiniteAdeleRing (𝓞 ℚ) ℚ := (α : FiniteAdeleRing (𝓞 ℚ) ℚ) with hA
  set A' : FiniteAdeleRing (𝓞 ℚ) ℚ := ((α⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) with hA'
  have hAA' : ∀ w, A w * A' w = 1 := by
    intro w
    have : A * A' = 1 := by rw [hA, hA']; exact α.mul_inv
    have := congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => x w) this
    exact this
  have hv0 : ∀ w, Valued.v (A w) ≠ 0 := by
    intro w h0
    have := congrArg Valued.v (hAA' w)
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this

  have hfin : {w : HeightOneSpectrum (𝓞 ℚ) | Valued.v (A w) ≠ 1}.Finite := by
    have h1 : ∀ᶠ w in Filter.cofinite, A w ∈ (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)) := A.2
    have h2 : ∀ᶠ w in Filter.cofinite, A' w ∈ (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)) := A'.2
    have h3 : ∀ᶠ w in Filter.cofinite, Valued.v (A w) = 1 := by
      filter_upwards [h1, h2] with w hw hw'
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hw hw'
      apply le_antisymm hw
      have := congrArg Valued.v (hAA' w)
      rw [map_mul, map_one] at this

      by_contra hlt
      push Not at hlt
      have : Valued.v (A w) * Valued.v (A' w) < 1 := mul_lt_one_of_lt_of_le hlt hw'
      rw [‹Valued.v (A w) * Valued.v (A' w) = 1›] at this
      exact lt_irrefl _ this
    rw [Filter.eventually_cofinite] at h3
    exact h3
  set S : Finset (HeightOneSpectrum (𝓞 ℚ)) := hfin.toFinset with hS
  have hmemS : ∀ w, w ∈ S ↔ Valued.v (A w) ≠ 1 := fun w => by rw [hS, Set.Finite.mem_toFinset]; rfl

  set e : HeightOneSpectrum (𝓞 ℚ) → ℤ := fun w => -(Valued.v (A w)).log with he
  set r : ℚ := ∏ w ∈ S, ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ) ^ (e w) with hr
  have hp0 : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ) ≠ 0 := fun w => by
    exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator w).ne_zero
  refine ⟨r, ?_, ?_⟩
  · rw [hr]; exact Finset.prod_ne_zero_iff.mpr fun w _ => zpow_ne_zero _ (hp0 w)
  · intro w₀
    rw [valued_algebraMap, hr, map_prod]
    simp_rw [map_zpow₀, valuation_natGenerator w₀]
    have hlog : ∀ w, WithZero.exp (-1 : ℤ) ^ (e w) = Valued.v (A w) := by
      intro w
      rw [exp_neg_one_zpow, he, neg_neg, WithZero.exp_log (hv0 w)]
    rw [Finset.prod_eq_single w₀]
    · rw [if_pos rfl, hlog]
    · intro w _ hw
      rw [if_neg hw, one_zpow]
    · intro hw₀
      rw [if_pos rfl, hlog]
      by_contra h
      exact hw₀ ((hmemS w₀).mpr h)

end CN1Glue29

end RatIdele

namespace CN1B

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝔸ℍ" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem asIdeal_eq_span_natGenerator (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator w : ℕ) : 𝓞 ℚ)} := by
  set e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) w
  have h1 : w.asIdeal = (w.asIdeal.map e).comap e := (Ideal.comap_map_of_bijective e e.bijective).symm
  rw [h1, ← h, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton]
  congr 2
  simp [e]

theorem valuation_natGenerator_self (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.valuation ℚ ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [show ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ) =
      algebraMap (𝓞 ℚ) ℚ ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  refine HeightOneSpectrum.intValuation_singleton w ?_ (asIdeal_eq_span_natGenerator w)
  exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator w).ne_zero

theorem valuation_natCast_eq_one_of_not_dvd (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (hn : ¬ Rat.HeightOneSpectrum.natGenerator w ∣ n) : w.valuation ℚ (n : ℚ) = 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) from (map_natCast _ _).symm]
  refine (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 ?_
  rwa [natCast_mem_asIdeal_iff]

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem natGenerator_injective {w w' : HeightOneSpectrum (𝓞 ℚ)}
    (h : Rat.HeightOneSpectrum.natGenerator w = Rat.HeightOneSpectrum.natGenerator w') : w = w' := by
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext h

open Classical in

theorem valuation_natGenerator (w₀ w : HeightOneSpectrum (𝓞 ℚ)) :
    w₀.valuation ℚ ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ) =
      if w = w₀ then WithZero.exp (-1 : ℤ) else 1 := by
  by_cases h : w = w₀
  · subst h; rw [if_pos rfl]; exact valuation_natGenerator_self w
  · rw [if_neg h]
    apply valuation_natCast_eq_one_of_not_dvd
    intro hd
    apply h
    have := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w₀)
      (Rat.HeightOneSpectrum.prime_natGenerator w)).1 hd
    exact (natGenerator_injective this).symm

def bcA : 𝔸ℍ ≃+* ℍ[FiniteAdeleRing (𝓞 ℚ) ℚ, algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) a,
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) b] :=
  (QuaternionAlgebra.baseChangeRight (R := ℚ) (S := FiniteAdeleRing (𝓞 ℚ) ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    rfl (map_zero _) rfl).toRingEquiv

theorem bcA_tmul (z : ℍ[ℚ, a, b]) (s : 𝔸f) :
    bcA (z ⊗ₜ[ℚ] s) = ⟨s * algebraMap ℚ 𝔸f z.re, s * algebraMap ℚ 𝔸f z.imI, s * algebraMap ℚ 𝔸f z.imJ,
      s * algebraMap ℚ 𝔸f z.imK⟩ := by
  show QuaternionAlgebra.baseChangeRight _ _ _ (z ⊗ₜ[ℚ] s) = _
  rw [QuaternionAlgebra.baseChangeRight_tmul]

def coord (w : HeightOneSpectrum (𝓞 ℚ)) :
    ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b] :=
  (QuaternionAlgebra.baseChangeRight (R := ℚ) (S := w.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    rfl (map_zero _) rfl).toRingEquiv

theorem coord_tmul (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ) :
    coord w (z ⊗ₜ[ℚ] r) = ⟨r * algebraMap ℚ _ z.re, r * algebraMap ℚ _ z.imI, r * algebraMap ℚ _ z.imJ,
      r * algebraMap ℚ _ z.imK⟩ := by
  show QuaternionAlgebra.baseChangeRight _ _ _ (z ⊗ₜ[ℚ] r) = _
  rw [QuaternionAlgebra.baseChangeRight_tmul]

theorem coord_formula (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ) :
    coord w (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
      algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
      algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]) := by
  rw [coord_tmul]; ext <;> simp [smul_eq_mul]

theorem eq_coord (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])
    (hφ : ∀ (z : ℍ[ℚ, a, b]) (t : w.adicCompletion ℚ),
      φ (z ⊗ₜ[ℚ] t) = t • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
        algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
        algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]))
    (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : φ x = coord w x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul z t => rw [hφ, coord_formula]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def locNrd (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : w.adicCompletion ℚ :=
  QuaternionAlgebra.nrd (coord w x)

theorem nrd_mul' {K : Type*} [CommRing K] {a' b' : K} (x y : ℍ[K, a', b']) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

theorem locNrd_mul (w : HeightOneSpectrum (𝓞 ℚ)) (x y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    locNrd w (x * y) = locNrd w x * locNrd w y := by
  unfold locNrd; rw [(coord w).map_mul, nrd_mul']

theorem locNrd_one (w : HeightOneSpectrum (𝓞 ℚ)) : locNrd w (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = 1 := by
  unfold locNrd
  have h1 : coord w (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = 1 := map_one (coord w)
  rw [h1, QuaternionAlgebra.nrd_one]

theorem locNrd_tmul_one (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) :
    locNrd w (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) = algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd z) := by
  unfold locNrd
  rw [coord_tmul, QuaternionAlgebra.nrd_mk, QuaternionAlgebra.nrd]
  simp only [one_mul, map_sub, map_add, map_mul, map_pow]

def nrdA (x : 𝔸ℍ) : 𝔸f := QuaternionAlgebra.nrd (bcA x)

theorem nrdA_mul (x y : 𝔸ℍ) : nrdA (x * y) = nrdA x * nrdA y := by
  unfold nrdA; rw [bcA.map_mul, nrd_mul']

theorem nrdA_one : nrdA (1 : 𝔸ℍ) = 1 := by
  unfold nrdA
  have h1 : bcA (1 : 𝔸ℍ) = 1 := map_one bcA
  rw [h1, QuaternionAlgebra.nrd_one]

theorem evalQ_apply (w : HeightOneSpectrum (𝓞 ℚ)) (s : 𝔸f) : Submodule.finiteAdeleEvalAlgHom w s = s w := rfl

theorem algebraMap_apply (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    (algebraMap ℚ 𝔸f r) w = algebraMap ℚ (w.adicCompletion ℚ) r := by
  rw [← evalQ_apply, AlgHom.commutes]

theorem nrdA_apply (w : HeightOneSpectrum (𝓞 ℚ)) (x : 𝔸ℍ) :
    (nrdA x) w = locNrd w (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x) := by

  have hc : (bcA x).re w = (coord w (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x)).re ∧
      (bcA x).imI w = (coord w (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x)).imI ∧
      (bcA x).imJ w = (coord w (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x)).imJ ∧
      (bcA x).imK w = (coord w (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x)).imK := by
    induction x using TensorProduct.induction_on with
    | zero => simp [map_zero]; rfl
    | tmul z s =>
      rw [bcA_tmul, Submodule.finiteAdeleEvalAt_tmul, coord_tmul]
      simp only []
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · rw [← evalQ_apply w, map_mul, evalQ_apply, evalQ_apply, algebraMap_apply]
    | add x y hx hy =>
      obtain ⟨h1, h2, h3, h4⟩ := hx
      obtain ⟨h1', h2', h3', h4'⟩ := hy
      rw [map_add, map_add, map_add]
      simp only [QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
        QuaternionAlgebra.imK_add]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← evalQ_apply w, map_add, evalQ_apply, evalQ_apply, h1, h1']
      · rw [← evalQ_apply w, map_add, evalQ_apply, evalQ_apply, h2, h2']
      · rw [← evalQ_apply w, map_add, evalQ_apply, evalQ_apply, h3, h3']
      · rw [← evalQ_apply w, map_add, evalQ_apply, evalQ_apply, h4, h4']
  obtain ⟨h1, h2, h3, h4⟩ := hc
  unfold nrdA locNrd
  rw [QuaternionAlgebra.nrd, QuaternionAlgebra.nrd, ← h1, ← h2, ← h3, ← h4, ← evalQ_apply w]
  simp only [map_sub, map_add, map_mul, map_pow, AlgHom.commutes]
  rw [evalQ_apply, evalQ_apply, evalQ_apply, evalQ_apply]

private theorem _root_.CN1B.rat_finiteIdele_eq_valuation (α : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ∃ r : ℚ, r ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (((α : FiniteAdeleRing (𝓞 ℚ) ℚ)) w) = Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) :=
  CN1Glue29.rat_finiteIdele_eq_valuation α

p2m_export "CN1B" "rat_finiteIdele_eq_valuation"

def unitOfNrd (x : ℍ[ℚ, a, b]) (hx : QuaternionAlgebra.nrd x ≠ 0) : (ℍ[ℚ, a, b])ˣ where
  val := x
  inv := (QuaternionAlgebra.nrd x)⁻¹ • star x
  val_inv := by
    rw [mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe_nrd]
    ext <;> simp [hx]
  inv_val := by
    rw [smul_mul_assoc, QuaternionAlgebra.star_mul_eq_coe_nrd]
    ext <;> simp [hx]

@[scoped simp] theorem val_unitOfNrd (x : ℍ[ℚ, a, b]) (hx : QuaternionAlgebra.nrd x ≠ 0) :
    ((unitOfNrd x hx : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = x := rfl

theorem nrd_val_inv (B : (ℍ[ℚ, a, b])ˣ) :
    QuaternionAlgebra.nrd ((B⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = (QuaternionAlgebra.nrd (B : ℍ[ℚ, a, b]))⁻¹ := by
  have h : QuaternionAlgebra.nrd (B : ℍ[ℚ, a, b]) * QuaternionAlgebra.nrd ((B⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 1 := by
    rw [← nrd_mul', Units.mul_inv, QuaternionAlgebra.nrd_one]
  exact (eq_inv_of_mul_eq_one_right h)

theorem evalAt_val_mul (w : HeightOneSpectrum (𝓞 ℚ)) (x y : (𝔸ℍ)ˣ) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((x * y : (𝔸ℍ)ˣ) : 𝔸ℍ) =
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x : 𝔸ℍ) * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (y : 𝔸ℍ) := by
  rw [Units.val_mul, map_mul]

theorem locNrd_evalAt_inv (w : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℍ)ˣ) :
    locNrd w (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((x⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ)) *
      locNrd w (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x : 𝔸ℍ)) = 1 := by
  rw [← locNrd_mul, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, locNrd_one]

theorem locNrd_evalAt_diagonal (w : HeightOneSpectrum (𝓞 ℚ)) (γ : (ℍ[ℚ, a, b])ˣ) :
    locNrd w (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ : (𝔸ℍ)ˣ) : 𝔸ℍ)) =
      algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b])) := by
  rw [Submodule.val_finiteIdeleDiagonal_apply, Submodule.finiteAdeleEvalAt_tmul]
  exact locNrd_tmul_one w _

theorem idelic_principal {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) (x : (𝔸ℍ)ˣ) :
    ∃ (δ : (ℍ[ℚ, a, b])ˣ) (u : (𝔸ℍ)ˣ), u ∈ Submodule.finiteIdeleStabilizer Λ ∧
      x = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * u := by
  classical
  have hΛo : QuaternionAlgebra.IsOrder Λ := hΛ.isOrder

  let N : (𝔸f)ˣ :=
    ⟨nrdA (x : 𝔸ℍ), nrdA ((x⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ),
      by rw [← nrdA_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, nrdA_one],
      by rw [← nrdA_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, nrdA_one]⟩
  have hN : ∀ w, ((N : (𝔸f)ˣ) : 𝔸f) w = locNrd w (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x : 𝔸ℍ)) :=
    fun w => nrdA_apply w _
  obtain ⟨r, hr0, hr⟩ := rat_finiteIdele_eq_valuation N
  have hr0' : ∀ w : HeightOneSpectrum (𝓞 ℚ), algebraMap ℚ (w.adicCompletion ℚ) r ≠ 0 := fun w =>
    (map_ne_zero_iff _ (algebraMap ℚ (w.adicCompletion ℚ)).injective).2 hr0

  obtain ⟨β₀, hβ₀⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.exists_nrd_eq hB r hr0
  have hβ₀0 : QuaternionAlgebra.nrd β₀ ≠ 0 := by rw [hβ₀]; exact hr0
  set B₀ : (ℍ[ℚ, a, b])ˣ := unitOfNrd β₀ hβ₀0 with hB₀

  set ε : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ :=
    fun w => (algebraMap ℚ (w.adicCompletion ℚ) r)⁻¹ * locNrd w (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x : 𝔸ℍ)) with hε
  have hεv : ∀ w, Valued.v (ε w) = 1 := by
    intro w
    rw [hε]
    simp only [map_mul, map_inv₀]
    rw [← hN, hr w, inv_mul_cancel₀]
    exact (Valuation.ne_zero_iff _).2 (hr0' w)
  have hε0 : ∀ w, ε w ≠ 0 := fun w h => by
    have := hεv w; rw [h, map_zero] at this; exact zero_ne_one this
  obtain ⟨m, hmS, hm⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_isIndefiniteRamifiedExactlyAt hB hΛ ε hεv
  have hmN : ∀ w, locNrd w (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (m : 𝔸ℍ)) = ε w :=
    fun w => hm w (coord w) (coord_formula w)

  set y : (𝔸ℍ)ˣ := (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀)⁻¹ * x * m⁻¹ with hy
  have hynorm : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (t : w.adicCompletion ℚ),
          φ (z ⊗ₜ[ℚ] t) = t • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
            algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
              ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])) →
        QuaternionAlgebra.nrd (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (y : 𝔸ℍ))) = 1 := by
    intro w φ hφ
    rw [eq_coord w φ hφ]
    change locNrd w (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (y : 𝔸ℍ)) = 1
    have hdiag : locNrd w (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
        (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀)⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ)) = (algebraMap ℚ (w.adicCompletion ℚ) r)⁻¹ := by
      rw [← map_inv, locNrd_evalAt_diagonal, nrd_val_inv, hB₀, val_unitOfNrd, hβ₀, map_inv₀]
    have hminv : locNrd w (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ)) = (ε w)⁻¹ := by
      have := locNrd_evalAt_inv w m
      rw [hmN] at this
      exact eq_inv_of_mul_eq_one_left this
    rw [hy, evalAt_val_mul, evalAt_val_mul, locNrd_mul, locNrd_mul, hdiag, hminv]
    change ε w * (ε w)⁻¹ = 1
    exact mul_inv_cancel₀ (hε0 w)

  obtain ⟨β, u, hβ1, huS, hyeq⟩ :=
    QuaternionAlgebra.IsOrder.exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one_of_forall_isUnit
      hB.1 (fun z hz => QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB z hz) hΛo y hynorm
  refine ⟨B₀ * β, u * m, Subgroup.mul_mem _ huS hmS, ?_⟩
  have hx : x = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] B₀ * y * m := by rw [hy]; group
  rw [hx, hyeq, map_mul]
  group

end CN1B
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt.CN1B"

section Glue
open QuaternionAlgebra

namespace CN1Glue29

variable {a b : ℚ}

theorem star_eq_coe_sub (x : ℍ[ℚ, a, b]) : star x = ((2 * x.re : ℚ) : ℍ[ℚ, a, b]) - x := by
  have h := QuaternionAlgebra.self_add_star' x
  simp only [zero_mul, add_zero] at h
  rw [← h]; abel

theorem star_ratSmul (c : ℚ) (x : ℍ[ℚ, a, b]) : star (c • x) = c • star x := by
  ext <;> simp

theorem star_mem_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : star x ∈ Λ := by
  obtain ⟨-, ⟨t, ht⟩⟩ := IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ hx
  rw [star_eq_coe_sub]
  have : ((2 * x.re : ℚ) : ℍ[ℚ, a, b]) = (t : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [show (2 * x.re : ℚ) = (t : ℚ) from by rw [ht]; rfl, ← Int.cast_smul_eq_zsmul ℚ, Algebra.smul_def, mul_one]; rfl
  rw [this]
  exact Λ.sub_mem (Λ.smul_mem t hΛ.one_mem) hx

theorem star_mem_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (x : ℍ[ℚ, a, b]) : star x ∈ Λ ↔ x ∈ Λ :=
  ⟨fun h => by simpa using star_mem_of_mem hΛ h, star_mem_of_mem hΛ⟩

theorem exists_nat_smul_mem {A : Submodule ℤ ℍ[ℚ, a, b]} (hA : Submodule.span ℚ (A : Set ℍ[ℚ, a, b]) = ⊤) (y : ℍ[ℚ, a, b]) :
    ∃ m : ℕ, m ≠ 0 ∧ ((m : ℚ)) • y ∈ A := by
  have hy : y ∈ Submodule.span ℚ (A : Set ℍ[ℚ, a, b]) := by rw [hA]; exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem z hz => exact ⟨1, one_ne_zero, by rw [Nat.cast_one, one_smul]; exact hz⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact A.zero_mem⟩
  | add z w _ _ hz hw =>
    obtain ⟨m, hm, hmz⟩ := hz
    obtain ⟨m', hm', hmw⟩ := hw
    refine ⟨m * m', mul_ne_zero hm hm', ?_⟩
    have e1 : (((m * m' : ℕ)) : ℚ) • z = ((m' : ℤ)) • (((m : ℚ)) • z) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]; congr 1; push_cast; ring
    have e2 : (((m * m' : ℕ)) : ℚ) • w = ((m : ℤ)) • (((m' : ℚ)) • w) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]; congr 1; push_cast; ring
    rw [smul_add, e1, e2]
    exact A.add_mem (A.smul_mem _ hmz) (A.smul_mem _ hmw)
  | smul c z _ hz =>
    obtain ⟨m, hm, hmz⟩ := hz
    refine ⟨m * c.den, mul_ne_zero hm c.den_nz, ?_⟩
    have hc : ((c.den : ℕ) : ℚ) * c = c.num := by rw [mul_comm]; exact Rat.mul_den_eq_num c
    rw [Nat.cast_mul, smul_smul, mul_assoc, hc, mul_comm, ← smul_smul,
      show ((c.num : ℤ) : ℚ) • ((m : ℚ) • z) = c.num • ((m : ℚ) • z) by rw [← Int.cast_smul_eq_zsmul ℚ]]
    exact A.smul_mem _ hmz

theorem exists_nat_forall_smul_mem {A B : Submodule ℤ ℍ[ℚ, a, b]} (hA : Submodule.span ℚ (A : Set ℍ[ℚ, a, b]) = ⊤) (hB : B.FG) :
    ∃ M : ℕ, M ≠ 0 ∧ ∀ y ∈ B, ((M : ℚ)) • y ∈ A := by
  classical
  obtain ⟨s, hs⟩ := hB
  choose m hm hms using fun y : ℍ[ℚ, a, b] => exists_nat_smul_mem hA y
  refine ⟨∏ g ∈ s, m g, Finset.prod_ne_zero_iff.mpr fun g _ => hm g, ?_⟩
  intro y hy
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hg
    rw [hk, Nat.cast_mul, mul_comm, mul_smul,
      show ((k : ℕ) : ℚ) • ((m g : ℚ) • g) = ((k : ℤ)) • ((m g : ℚ) • g) by rw [← Int.cast_smul_eq_zsmul ℚ]; rfl]
    exact A.smul_mem _ (hms g)
  | zero => rw [smul_zero]; exact A.zero_mem
  | add z w _ _ hz hw => rw [smul_add]; exact A.add_mem hz hw
  | smul c z _ hz => rw [smul_comm]; exact A.smul_mem c hz

def flip (I : Submodule ℤ ℍ[ℚ, a, b]) (M : ℕ) : Submodule ℤ ℍ[ℚ, a, b] where
  carrier := {y | star (((M : ℚ))⁻¹ • y) ∈ I}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, smul_add, star_add] at *
    exact I.add_mem hx hy
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at *
    rw [smul_comm, star_zsmul]
    exact I.smul_mem c hx

theorem mem_flip (I : Submodule ℤ ℍ[ℚ, a, b]) (M : ℕ) (y : ℍ[ℚ, a, b]) :
    y ∈ flip I M ↔ star (((M : ℚ))⁻¹ • y) ∈ I := Iff.rfl

theorem smul_star_mem_flip (I : Submodule ℤ ℍ[ℚ, a, b]) {M : ℕ} (hM : M ≠ 0) {x : ℍ[ℚ, a, b]} (hx : x ∈ I) :
    ((M : ℚ)) • star x ∈ flip I M := by
  rw [mem_flip, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hM : ((M : ℚ)) ≠ 0), one_smul, star_star]
  exact hx

theorem flip_spec {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (I : Submodule ℤ ℍ[ℚ, a, b]) (hIfg : I.FG)
    (hIspan : Submodule.span ℚ (I : Set ℍ[ℚ, a, b]) = ⊤) (hIstab : ∀ x ∈ Λ, ∀ y ∈ I, x * y ∈ I) :
    ∃ M : ℕ, M ≠ 0 ∧ flip I M ≤ Λ ∧ (∀ z ∈ flip I M, ∀ μ ∈ Λ, z * μ ∈ flip I M) ∧
      ∃ n : ℤ, n ≠ 0 ∧ ∀ μ ∈ Λ, n • μ ∈ flip I M := by
  obtain ⟨M, hM, hMI⟩ := exists_nat_forall_smul_mem hΛ.spanTop hIfg
  obtain ⟨n, hn, hnΛ⟩ := exists_nat_forall_smul_mem hIspan hΛ.fg
  have hM0 : ((M : ℚ)) ≠ 0 := by exact_mod_cast hM
  refine ⟨M, hM, ?_, ?_, ⟨(n : ℤ) * M, mul_ne_zero (by exact_mod_cast hn) (by exact_mod_cast hM), ?_⟩⟩
  ·
    intro y hy
    rw [mem_flip] at hy
    have h1 : ((M : ℚ)) • star (((M : ℚ))⁻¹ • y) ∈ Λ := hMI _ hy
    rw [star_ratSmul, smul_smul, mul_inv_cancel₀ hM0, one_smul] at h1
    exact (star_mem_iff hΛ y).mp h1
  ·
    intro z hz μ hμ
    rw [mem_flip] at hz ⊢
    rw [show ((M : ℚ))⁻¹ • (z * μ) = (((M : ℚ))⁻¹ • z) * μ from (smul_mul_assoc _ _ _).symm, star_mul]
    exact hIstab _ (star_mem_of_mem hΛ hμ) _ hz
  ·
    intro μ hμ
    rw [mem_flip]
    have e : ((M : ℚ))⁻¹ • ((((n : ℤ) * M) : ℤ) • μ) = ((n : ℕ) : ℚ) • μ := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
      congr 1
      push_cast
      field_simp
    rw [e, star_ratSmul]
    exact hnΛ _ (star_mem_of_mem hΛ hμ)

theorem mem_iff_smul_star_mem_flip (I : Submodule ℤ ℍ[ℚ, a, b]) {M : ℕ} (hM : M ≠ 0) (y : ℍ[ℚ, a, b]) :
    y ∈ I ↔ ((M : ℚ)) • star y ∈ flip I M := by
  rw [mem_flip, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hM : ((M : ℚ)) ≠ 0), one_smul, star_star]

theorem forall_mem_iff_of_flip_principal {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (I : Submodule ℤ ℍ[ℚ, a, b])
    {M : ℕ} (hM : M ≠ 0) (x₀ : ℍ[ℚ, a, b]) (hJ : ∀ y : ℍ[ℚ, a, b], y ∈ flip I M ↔ ∃ z ∈ Λ, x₀ * z = y) :
    ∀ y : ℍ[ℚ, a, b], y ∈ I ↔ ∃ z ∈ Λ, z * ((((M : ℚ))⁻¹) • star x₀) = y := by
  have hM0 : ((M : ℚ)) ≠ 0 := by exact_mod_cast hM
  intro y
  rw [mem_iff_smul_star_mem_flip I hM, hJ]
  constructor
  · rintro ⟨z, hz, hzy⟩
    refine ⟨star z, star_mem_of_mem hΛ hz, ?_⟩
    have : y = ((M : ℚ))⁻¹ • star (x₀ * z) := by
      rw [hzy, star_ratSmul, star_star, smul_smul, inv_mul_cancel₀ hM0, one_smul]
    rw [this, star_mul, mul_smul_comm]
  · rintro ⟨z, hz, hzy⟩
    refine ⟨star z, star_mem_of_mem hΛ hz, ?_⟩
    rw [← hzy, star_mul, star_ratSmul, star_star, smul_mul_assoc, smul_smul, mul_inv_cancel₀ hM0, one_smul]

theorem smul_star_ne_zero {M : ℕ} (hM : M ≠ 0) {x₀ : ℍ[ℚ, a, b]} (hx : x₀ ≠ 0) : (((M : ℚ))⁻¹) • star x₀ ≠ 0 := by
  have hM0 : ((M : ℚ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hM)
  intro h
  rw [smul_eq_zero] at h
  rcases h with h | h
  · exact hM0 h
  · exact hx (by rw [← star_star x₀, h, star_zero])

end CN1Glue29
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt.CN1B"

end Glue
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt.CN1B"

namespace CN1B

variable {a b : ℚ}

theorem main {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    (I : Submodule ℤ ℍ[ℚ, a, b]) (hIfg : I.FG) (hIspan : Submodule.span ℚ (I : Set ℍ[ℚ, a, b]) = ⊤)
    (hIstab : ∀ x ∈ Λ, ∀ y ∈ I, x * y ∈ I) :
    ∃ x₀ : ℍ[ℚ, a, b], x₀ ≠ 0 ∧ ∀ y : ℍ[ℚ, a, b], y ∈ I ↔ ∃ z ∈ Λ, z * x₀ = y := by
  classical
  have hΛo : QuaternionAlgebra.IsOrder Λ := hΛ.isOrder
  obtain ⟨M, hM, hJΛ, hJmul, n, hn0, hJfull⟩ := CN1Glue29.flip_spec hΛo I hIfg hIspan hIstab
  obtain ⟨x, hx⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_ofFiniteIdele_eq_of_forall_mul_mem_of_isIndefiniteRamifiedExactlyAt hB hΛ
      (CN1Glue29.flip I M) hJΛ hJmul ⟨n, hn0, hJfull⟩
  obtain ⟨δ, u, huS, hxu⟩ := idelic_principal hB hΛ x
  have hJ : CN1Glue29.flip I M = δ • Λ := by
    rw [← hx, hxu, Submodule.ofFiniteIdele_diagonal_mul]
    congr 1
    have h1 : Submodule.ofFiniteIdele Λ u = Submodule.ofFiniteIdele Λ 1 :=
      (Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ hΛo.fg hΛo.spanTop u 1).2
        (by rw [mul_one]; exact Subgroup.inv_mem _ huS)
    rw [h1, Submodule.ofFiniteIdele_one Λ hΛo.fg hΛo.spanTop]
  have hJ' : ∀ y : ℍ[ℚ, a, b], y ∈ CN1Glue29.flip I M ↔ ∃ z ∈ Λ, (δ : ℍ[ℚ, a, b]) * z = y := by
    intro y
    rw [hJ]
    refine (Submodule.mem_smul_pointwise_iff_exists y δ Λ).trans ?_
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  exact ⟨((M : ℚ))⁻¹ • star (δ : ℍ[ℚ, a, b]), CN1Glue29.smul_star_ne_zero hM δ.ne_zero,
    CN1Glue29.forall_mem_iff_of_flip_principal hΛo I hM (δ : ℍ[ℚ, a, b]) hJ'⟩

end CN1B
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt.CN1B"

end
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt.CN1B"

open scoped Quaternion in
open QuaternionAlgebra in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (I : Submodule ℤ ℍ[ℚ, a, b]) (hIfg : I.FG) (hIspan : Submodule.span ℚ (I : Set ℍ[ℚ, a, b]) = ⊤)
    (hIstab : ∀ x ∈ Λ, ∀ y ∈ I, x * y ∈ I) :
    ∃ x₀ : ℍ[ℚ, a, b], x₀ ≠ 0 ∧ ∀ y : ℍ[ℚ, a, b], y ∈ I ↔ ∃ z ∈ Λ, z * x₀ = y :=
  CN1B.main hB Λ hΛ I hIfg hIspan hIstab

end S_QuaternionAlgebra_IsMaximalOrder_exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt (solution)
