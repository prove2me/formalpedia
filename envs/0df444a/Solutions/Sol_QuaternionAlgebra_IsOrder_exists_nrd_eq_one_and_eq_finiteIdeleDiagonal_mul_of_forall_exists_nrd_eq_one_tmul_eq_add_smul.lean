-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_of_forall_exists_nrd_eq_one_tmul_eq_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f5b2928e-c67d-526a-89e1-959c5a911899

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq
import Theorems.Thm_Submodule_eventually_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_exists_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_eq_of_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_Padic_exists_ternary_isotropic_of_norm_eq_one_of_ne_two
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_forall_tmul_eq_add_smul_of_finset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_of_forall_exists_nrd_eq_one_tmul_eq_add_smul
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Quaternion
open IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section

namespace KRCC

section Places

abbrev pgen (w : HeightOneSpectrum (𝓞 ℚ)) : ℕ := Rat.HeightOneSpectrum.natGenerator w

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ pgen w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem asIdeal_eq_span_pgen (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.asIdeal = Ideal.span {((pgen w : ℕ) : 𝓞 ℚ)} := by
  set e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) w
  have h1 : w.asIdeal = (w.asIdeal.map e).comap e := (Ideal.comap_map_of_bijective e e.bijective).symm
  rw [h1, ← h, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton]
  congr 2
  simp [e]

theorem valuation_pgen (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.valuation ℚ ((pgen w : ℕ) : ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [show ((pgen w : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((pgen w : ℕ) : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  refine HeightOneSpectrum.intValuation_singleton w ?_ (asIdeal_eq_span_pgen w)
  exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator w).ne_zero

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem valued_pgen_pow (w : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) :
    Valued.v (((pgen w : ℕ) : w.adicCompletion ℚ) ^ k) = WithZero.exp (-(k : ℤ)) := by
  rw [map_pow, show ((pgen w : ℕ) : w.adicCompletion ℚ) = algebraMap ℚ (w.adicCompletion ℚ) ((pgen w : ℕ) : ℚ)
    from (map_natCast _ _).symm, valued_algebraMap, valuation_pgen, ← WithZero.exp_nsmul]
  simp

theorem pgen_injective : Function.Injective (pgen) := by
  intro w w' h
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext h

theorem valuation_natCast_eq_one_of_not_dvd (w : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : ¬ pgen w ∣ n) :
    w.valuation ℚ (n : ℚ) = 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  refine (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 ?_
  rwa [natCast_mem_asIdeal_iff]

abbrev Ow (w : HeightOneSpectrum (𝓞 ℚ)) : Subring (w.adicCompletion ℚ) :=
  (w.adicCompletionIntegers ℚ).toSubring

theorem mem_Ow_iff (w : HeightOneSpectrum (𝓞 ℚ)) (x : w.adicCompletion ℚ) :
    x ∈ Ow w ↔ Valued.v x ≤ 1 := HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

theorem mem_integers_iff (w : HeightOneSpectrum (𝓞 ℚ)) (x : w.adicCompletion ℚ) :
    x ∈ w.adicCompletionIntegers ℚ ↔ Valued.v x ≤ 1 := HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

theorem exists_pgen_pow_mul_mem (w : HeightOneSpectrum (𝓞 ℚ)) (e : w.adicCompletion ℚ) :
    ∃ k : ℕ, ((pgen w : ℕ) : w.adicCompletion ℚ) ^ k * e ∈ w.adicCompletionIntegers ℚ := by
  by_cases he : e = 0
  · exact ⟨0, by rw [he, mul_zero]; exact (w.adicCompletionIntegers ℚ).zero_mem⟩
  · set m : ℤ := WithZero.log (Valued.v e) with hm
    have hve : Valued.v e = WithZero.exp m := (WithZero.exp_log ((Valuation.ne_zero_iff _).2 he)).symm
    refine ⟨m.toNat, ?_⟩
    rw [mem_integers_iff, map_mul, valued_pgen_pow, hve, ← WithZero.exp_add, ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    have := Int.self_le_toNat m
    omega

theorem natCast_adicCompletion_ne_zero (w : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : n ≠ 0) :
    (n : w.adicCompletion ℚ) ≠ 0 := by
  rw [show (n : w.adicCompletion ℚ) = algebraMap ℚ (w.adicCompletion ℚ) (n : ℚ) from (map_natCast _ _).symm]
  exact (map_ne_zero_iff _ (algebraMap ℚ (w.adicCompletion ℚ)).injective).2 (Nat.cast_ne_zero.2 hn)

theorem inv_natCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : ¬ pgen w ∣ n) :
    (algebraMap ℚ (w.adicCompletion ℚ) ((n : ℚ)⁻¹)) ∈ w.adicCompletionIntegers ℚ := by
  rw [mem_integers_iff, valued_algebraMap, map_inv₀, valuation_natCast_eq_one_of_not_dvd w hn, inv_one]

theorem finite_setOf_dvd {n : ℕ} (hn : n ≠ 0) : {w : HeightOneSpectrum (𝓞 ℚ) | pgen w ∣ n}.Finite := by
  have hsub : {w : HeightOneSpectrum (𝓞 ℚ) | pgen w ∣ n} ⊆ pgen ⁻¹' (↑(Nat.divisors n) : Set ℕ) := by
    intro w hw
    simp only [Set.mem_preimage, Finset.mem_coe, Nat.mem_divisors]
    exact ⟨hw, hn⟩
  exact Set.Finite.subset (Set.Finite.preimage (pgen_injective.injOn) (Finset.finite_toSet _)) hsub

end Places

section Coord

variable {a b : ℚ}

abbrev cst (w : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) : w.adicCompletion ℚ := algebraMap ℚ (w.adicCompletion ℚ) q

def hatQ (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) : ℍ[w.adicCompletion ℚ, cst w a, cst w b] :=
  ⟨cst w x.re, cst w x.imI, cst w x.imJ, cst w x.imK⟩

theorem hatQ_star (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) : hatQ w (star x) = star (hatQ w x) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp [hatQ, map_neg]

theorem nrd_hatQ (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (hatQ w x) = cst w (QuaternionAlgebra.nrd x) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp [hatQ, QuaternionAlgebra.nrd, map_add, map_sub, map_mul, map_pow]

theorem nrd_mul' {K : Type*} [CommRing K] {c₁ c₃ : K} (x y : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

def IsCoord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]) : Prop :=
  ∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
    φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
      algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
      algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])

theorem exists_isCoord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
      IsCoord a b w φ := by
  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := w.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ (w.adicCompletion ℚ) a) (d₂ := (0 : w.adicCompletion ℚ))
    (d₃ := algebraMap ℚ (w.adicCompletion ℚ) b) rfl (map_zero _) rfl AlgEquiv.refl
  exact ⟨φ, fun z r => by rw [hφ]; rfl⟩

variable {w : HeightOneSpectrum (𝓞 ℚ)}
  {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
    ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}

theorem IsCoord.tmul (hφ : IsCoord a b w φ) (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ) :
    φ (z ⊗ₜ[ℚ] r) = r • hatQ w z := by
  rw [hφ]; rfl

theorem IsCoord.tmul_one (hφ : IsCoord a b w φ) (z : ℍ[ℚ, a, b]) :
    φ (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) = hatQ w z := by
  rw [hφ.tmul, one_smul]

def barT (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
    ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])
    (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ :=
  φ.symm (star (φ x))

theorem φ_barT (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : φ (barT φ x) = star (φ x) := by
  rw [barT, RingEquiv.apply_symm_apply]

theorem barT_add (x x' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : barT φ (x + x') = barT φ x + barT φ x' := by
  apply φ.injective
  rw [RingEquiv.map_add, φ_barT, φ_barT, φ_barT, RingEquiv.map_add, star_add]

theorem barT_neg (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : barT φ (-x) = -barT φ x := by
  apply φ.injective
  rw [RingEquiv.map_neg, φ_barT, φ_barT, RingEquiv.map_neg, star_neg]

theorem barT_zero : barT φ (0 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = 0 := by
  apply φ.injective
  rw [φ_barT, RingEquiv.map_zero]
  exact star_zero _

theorem barT_one : barT φ (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = 1 := by
  apply φ.injective
  rw [φ_barT, RingEquiv.map_one, star_one]

theorem barT_mul (x x' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : barT φ (x * x') = barT φ x' * barT φ x := by
  apply φ.injective
  rw [RingEquiv.map_mul, φ_barT, φ_barT, φ_barT, RingEquiv.map_mul, star_mul]

theorem barT_barT (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : barT φ (barT φ x) = x := by
  apply φ.injective
  rw [φ_barT, φ_barT, star_star]

theorem barT_tmul (hφ : IsCoord a b w φ) (z : ℍ[ℚ, a, b]) (c : w.adicCompletion ℚ) :
    barT φ (z ⊗ₜ[ℚ] c) = (star z) ⊗ₜ[ℚ] c := by
  apply φ.injective
  rw [φ_barT, hφ.tmul, hφ.tmul, hatQ_star]
  obtain ⟨z₀, z₁, z₂, z₃⟩ := z
  ext <;> simp [hatQ]

theorem barT_natCast_smul (hφ : IsCoord a b w φ) (M : ℕ) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    barT φ ((M : ℚ) • x) = (M : ℚ) • barT φ x := by
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  induction M with
  | zero => rw [zero_smul, zero_smul, barT_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, barT_add, ih]

theorem mul_barT_of_nrd (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) (hx : QuaternionAlgebra.nrd (φ x) = 1) :
    x * barT φ x = 1 := by
  apply φ.injective
  rw [RingEquiv.map_mul, φ_barT, QuaternionAlgebra.mul_star_eq_coe_nrd, hx, RingEquiv.map_one]
  rfl

theorem barT_mul_of_nrd (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) (hx : QuaternionAlgebra.nrd (φ x) = 1) :
    barT φ x * x = 1 := by
  apply φ.injective
  rw [RingEquiv.map_mul, φ_barT, QuaternionAlgebra.star_mul_eq_coe_nrd, hx, RingEquiv.map_one]
  rfl

theorem nrd_φ_barT (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    QuaternionAlgebra.nrd (φ (barT φ x)) = QuaternionAlgebra.nrd (φ x) := by
  rw [φ_barT, QuaternionAlgebra.nrd_star]

theorem barT_eq_of_mul_eq_one {x x' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ}
    (hx : QuaternionAlgebra.nrd (φ x) = 1) (h : x * x' = 1) : barT φ x = x' := by
  calc barT φ x = barT φ x * (x * x') := by rw [h, mul_one]
    _ = x' := by rw [← mul_assoc, barT_mul_of_nrd x hx, one_mul]

end Coord

section Boxes

variable {a b : ℚ} {O : Submodule ℤ ℍ[ℚ, a, b]}

theorem tmul_mem_localBox {z : ℍ[ℚ, a, b]} (hz : z ∈ O) (w : HeightOneSpectrum (𝓞 ℚ))
    {c : w.adicCompletion ℚ} (hc : c ∈ w.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox O w :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem one_mem_localBox (hO : QuaternionAlgebra.IsOrder O) (w : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ∈ Submodule.localBox O w := by
  rw [Algebra.TensorProduct.one_def]
  exact tmul_mem_localBox hO.one_mem w (w.adicCompletionIntegers ℚ).one_mem

theorem mul_mem_localBox (hO : QuaternionAlgebra.IsOrder O) (w : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ}
    (hx : x ∈ Submodule.localBox O w) (hy : y ∈ Submodule.localBox O w) :
    x * y ∈ Submodule.localBox O w := by
  induction hy using AddSubgroup.closure_induction with
  | mem y' hy' =>
    obtain ⟨z', hz', c', hc', rfl⟩ := hy'
    induction hx using AddSubgroup.closure_induction with
    | mem x' hx' =>
      obtain ⟨z, hz, c, hc, rfl⟩ := hx'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_localBox (hO.mul_mem hz hz') w (Subring.mul_mem _ hc hc')
    | zero => rw [zero_mul]; exact AddSubgroup.zero_mem _
    | add u u' _ _ hu hu' => rw [add_mul]; exact AddSubgroup.add_mem _ hu hu'
    | neg u _ hu => rw [show -u * z' ⊗ₜ[ℚ] c' = -(u * z' ⊗ₜ[ℚ] c') from neg_mul u _]; exact AddSubgroup.neg_mem _ hu
  | zero => rw [mul_zero]; exact AddSubgroup.zero_mem _
  | add u u' _ _ hu hu' => rw [mul_add]; exact AddSubgroup.add_mem _ hu hu'
  | neg u _ hu => rw [show x * -u = -(x * u) from mul_neg x u]; exact AddSubgroup.neg_mem _ hu

theorem natCast_smul_mem_localBox (w : HeightOneSpectrum (𝓞 ℚ)) (M : ℕ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hx : x ∈ Submodule.localBox O w) :
    (M : ℚ) • x ∈ Submodule.localBox O w := by
  rw [Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_mem _ hx M

theorem star_mem (hO : QuaternionAlgebra.IsOrder O) {z : ℍ[ℚ, a, b]} (hz : z ∈ O) : star z ∈ O := by
  obtain ⟨⟨t, n, ht, hn⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hO hz
  have e : star z = (t : ℤ) • (1 : ℍ[ℚ, a, b]) - z := by
    have h1 : z + star z = ((QuaternionAlgebra.trd z : ℚ) : ℍ[ℚ, a, b]) := QuaternionAlgebra.add_star_eq_coe_trd z
    rw [ht] at h1
    have : star z = ((t : ℚ) : ℍ[ℚ, a, b]) - z := by rw [← h1]; abel
    rw [this, ← Int.cast_smul_eq_zsmul ℚ]
    congr 1
    ext <;> simp
  rw [e]
  exact O.sub_mem (O.smul_mem _ hO.one_mem) hz

variable {w : HeightOneSpectrum (𝓞 ℚ)}
  {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
    ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}

theorem barT_mem_localBox (hO : QuaternionAlgebra.IsOrder O) (hφ : IsCoord a b w φ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hx : x ∈ Submodule.localBox O w) :
    barT φ x ∈ Submodule.localBox O w := by
  induction hx using AddSubgroup.closure_induction with
  | mem x' hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    rw [barT_tmul hφ]
    exact tmul_mem_localBox (star_mem hO hz) w hc
  | zero => rw [barT_zero]; exact AddSubgroup.zero_mem _
  | add u u' _ _ hu hu' => rw [barT_add]; exact AddSubgroup.add_mem _ hu hu'
  | neg u _ hu => rw [barT_neg]; exact AddSubgroup.neg_mem _ hu

theorem exists_natCast_smul_mem_of_mem_span (Λ : Submodule ℤ ℍ[ℚ, a, b]) {y : ℍ[ℚ, a, b]}
    (hy : y ∈ Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b])) : ∃ n : ℕ, n ≠ 0 ∧ (n : ℚ) • y ∈ Λ := by
  induction hy using Submodule.span_induction with
  | mem z hz => exact ⟨1, one_ne_zero, by simpa using hz⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add u u' _ _ hu hu' =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hu'
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul ℚ n]
      exact Λ.smul_of_tower_mem n hmu
    · rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul ℚ m]
      exact Λ.smul_of_tower_mem m hnv
  | smul c u _ hu =>
    obtain ⟨n, hn, hnu⟩ := hu
    refine ⟨c.den * n, mul_ne_zero c.den_ne_zero hn, ?_⟩
    have : ((c.den * n : ℕ) : ℚ) • c • u = (c.num : ℚ) • ((n : ℚ) • u) := by
      rw [smul_smul, smul_smul]
      congr 1
      push_cast
      have := Rat.den_mul_eq_num c
      linear_combination (n : ℚ) * this
    rw [this, Int.cast_smul_eq_zsmul ℚ]
    exact Λ.smul_mem _ hnu

theorem exists_natCast_smul_mem_order (hO : QuaternionAlgebra.IsOrder O) (z : ℍ[ℚ, a, b]) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : ℚ) • z ∈ O :=
  exists_natCast_smul_mem_of_mem_span O (by rw [hO.spanTop]; exact Submodule.mem_top)

theorem exists_natCast_smul_mem_localBox (hO : QuaternionAlgebra.IsOrder O) (w : HeightOneSpectrum (𝓞 ℚ))
    (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    ∃ d : ℕ, d ≠ 0 ∧ (d : ℚ) • x ∈ Submodule.localBox O w := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact AddSubgroup.zero_mem _⟩
  | tmul z c =>
    obtain ⟨n, hn, hnz⟩ := exists_natCast_smul_mem_order hO z
    obtain ⟨k, hk⟩ := exists_pgen_pow_mul_mem w c
    refine ⟨n * pgen w ^ k, mul_ne_zero hn (pow_ne_zero _ (Rat.HeightOneSpectrum.prime_natGenerator w).ne_zero), ?_⟩
    have e : ((n * pgen w ^ k : ℕ) : ℚ) • (z ⊗ₜ[ℚ] c)
        = ((n : ℚ) • z) ⊗ₜ[ℚ] (((pgen w : ℕ) : w.adicCompletion ℚ) ^ k * c) := by
      rw [Nat.cast_mul, mul_comm, mul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
        TensorProduct.smul_tmul ((pgen w ^ k : ℕ) : ℚ)]
      congr 1
      rw [Algebra.smul_def, map_natCast, Nat.cast_pow]
    rw [e]
    exact tmul_mem_localBox hnz w hk
  | add x x' hx hx' =>
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨d', hd', hdx'⟩ := hx'
    refine ⟨d * d', mul_ne_zero hd hd', ?_⟩
    rw [smul_add]
    refine AddSubgroup.add_mem _ ?_ ?_
    · rw [Nat.cast_mul, mul_comm, mul_smul]; exact natCast_smul_mem_localBox w d' hdx
    · rw [Nat.cast_mul, mul_smul]; exact natCast_smul_mem_localBox w d hdx'

theorem tmul_one_mem_localBox_of_not_dvd (w : HeightOneSpectrum (𝓞 ℚ)) {z : ℍ[ℚ, a, b]} {n : ℕ}
    (hn : n ≠ 0) (hz : (n : ℚ) • z ∈ O) (hw : ¬ pgen w ∣ n) :
    z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox O w := by
  have e : z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) = ((n : ℚ) • z) ⊗ₜ[ℚ] (algebraMap ℚ (w.adicCompletion ℚ) ((n : ℚ)⁻¹)) := by
    rw [TensorProduct.smul_tmul, Algebra.smul_def, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn), map_one]
  rw [e]
  exact tmul_mem_localBox hz w (inv_natCast_mem_integers w hw)

end Boxes

section Split

variable {a b : ℚ}

theorem padic_norm_rat_eq_one {p : ℕ} [Fact p.Prime] {q : ℚ} (hq : q ≠ 0)
    (hden : ¬ p ∣ q.den) (hnum : ¬ p ∣ q.num.natAbs) : ‖(q : ℚ_[p])‖ = 1 := by
  have h1 : ‖(q : ℚ_[p])‖ ≤ 1 := Padic.norm_rat_le_one hden
  have hden' : ¬ p ∣ (q⁻¹).den := by rwa [Rat.den_inv_of_ne_zero hq]
  have h2 : ‖((q⁻¹ : ℚ) : ℚ_[p])‖ ≤ 1 := Padic.norm_rat_le_one hden'
  have hq' : (q : ℚ_[p]) ≠ 0 := by exact_mod_cast hq
  have hmul : ‖(q : ℚ_[p])‖ * ‖((q⁻¹ : ℚ) : ℚ_[p])‖ = 1 := by
    rw [← norm_mul, Rat.cast_inv, mul_inv_cancel₀ hq', norm_one]
  have hpos : 0 < ‖(q : ℚ_[p])‖ := norm_pos_iff.2 hq'
  nlinarith [norm_nonneg ((q⁻¹ : ℚ) : ℚ_[p])]

def excNat (a b : ℚ) : ℕ := 2 * a.den * b.den * a.num.natAbs * b.num.natAbs

theorem excNat_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : excNat a b ≠ 0 := by
  unfold excNat
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero a.den_ne_zero) b.den_ne_zero) ?_) ?_
  · exact Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 ha)
  · exact Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hb)

theorem exists_ne_zero_not_isUnit (ha : a ≠ 0) (hb : b ≠ 0) (w : HeightOneSpectrum (𝓞 ℚ))
    (hw : ¬ pgen w ∣ excNat a b) :
    ∃ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x := by
  classical

  haveI hpfact : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ)) :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator w⟩
  set p : ℕ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ) with hp
  have hpg : pgen w = p := rfl
  have hp2 : p ≠ 2 := by
    intro h2; apply hw; rw [hpg, h2]
    exact Dvd.intro (a.den * b.den * a.num.natAbs * b.num.natAbs) (by unfold excNat; ring)
  have hdiv : ∀ m : ℕ, m ∣ excNat a b → ¬ p ∣ m := fun m hm hpm => hw (hpg ▸ hpm.trans hm)
  have hna : ‖(a : ℚ_[p])‖ = 1 := padic_norm_rat_eq_one ha
    (hdiv _ ⟨2 * b.den * a.num.natAbs * b.num.natAbs, by unfold excNat; ring⟩)
    (hdiv _ ⟨2 * a.den * b.den * b.num.natAbs, by unfold excNat; ring⟩)
  have hnb : ‖(b : ℚ_[p])‖ = 1 := padic_norm_rat_eq_one hb
    (hdiv _ ⟨2 * a.den * a.num.natAbs * b.num.natAbs, by unfold excNat; ring⟩)
    (hdiv _ ⟨2 * a.den * b.den * a.num.natAbs, by unfold excNat; ring⟩)
  obtain ⟨z, x, y, hne, heq⟩ := Padic.exists_ternary_isotropic_of_norm_eq_one_of_ne_two p hp2 (a : ℚ_[p]) (b : ℚ_[p]) hna hnb

  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) w
  have hea : e.symm (a : ℚ_[p]) = cst w a := by
    rw [show (a : ℚ_[p]) = algebraMap ℚ ℚ_[p] a from (eq_ratCast _ a).symm, AlgEquivClass.commutes]
  have heb : e.symm (b : ℚ_[p]) = cst w b := by
    rw [show (b : ℚ_[p]) = algebraMap ℚ ℚ_[p] b from (eq_ratCast _ b).symm, AlgEquivClass.commutes]
  have heq' : (e.symm z) ^ 2 - cst w a * (e.symm x) ^ 2 - cst w b * (e.symm y) ^ 2 = 0 := by
    have := congrArg e.symm heq
    rw [map_zero, map_sub, map_sub, map_mul, map_mul, map_pow, map_pow, map_pow, hea, heb] at this
    exact this
  have hne' : ¬ (e.symm z = 0 ∧ e.symm x = 0 ∧ e.symm y = 0) := by
    rintro ⟨h1, h2, h3⟩
    apply hne
    refine ⟨?_, ?_, ?_⟩
    · simpa using congrArg e h1
    · simpa using congrArg e h2
    · simpa using congrArg e h3

  set q : ℍ[w.adicCompletion ℚ, cst w a, cst w b] := ⟨e.symm z, e.symm x, e.symm y, 0⟩ with hq
  have hq0 : q ≠ 0 := by
    intro h0
    apply hne'
    have h1 := congrArg QuaternionAlgebra.re h0
    have h2 := congrArg QuaternionAlgebra.imI h0
    have h3 := congrArg QuaternionAlgebra.imJ h0
    simp only [hq] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hnrd : QuaternionAlgebra.nrd q = 0 := by
    rw [hq, QuaternionAlgebra.nrd_mk]
    linear_combination heq'
  obtain ⟨φ, hφ⟩ := exists_isCoord a b w
  refine ⟨φ.symm q, fun h0 => hq0 (by simpa using congrArg φ h0), fun hu => ?_⟩
  have hu' : IsUnit q := by simpa using hu.map φ
  have hqq : q * star q = 0 := by
    rw [QuaternionAlgebra.mul_star_eq_coe_nrd, hnrd]; rfl
  have hstar : star q = 0 := (hu'.mul_right_eq_zero).1 hqq
  exact hq0 (by simpa using congrArg star hstar)

end Split

section Idele

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

def yv (y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (w : HeightOneSpectrum (𝓞 ℚ)) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ :=
  Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)

def yiv (y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (w : HeightOneSpectrum (𝓞 ℚ)) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ :=
  Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((y⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)

theorem yv_mul_yiv (y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (w : HeightOneSpectrum (𝓞 ℚ)) : yv y w * yiv y w = 1 := by
  rw [yv, yiv, ← map_mul, Units.mul_inv, map_one]

theorem yiv_mul_yv (y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (w : HeightOneSpectrum (𝓞 ℚ)) : yiv y w * yv y w = 1 := by
  rw [yv, yiv, ← map_mul, Units.inv_mul, map_one]

theorem evalAt_tmul_one (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (z ⊗ₜ[ℚ] (1 : 𝔸f)) = z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  rw [Submodule.finiteAdeleEvalAt_tmul]
  rfl

theorem tmul_one_mul_tmul_one (w : HeightOneSpectrum (𝓞 ℚ)) (z z' : ℍ[ℚ, a, b]) :
    (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) * (z' ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) = (z * z') ⊗ₜ[ℚ] 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

variable {w : HeightOneSpectrum (𝓞 ℚ)}
  {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
    ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}

theorem nrd_φ_tmul_one (hφ : IsCoord a b w φ) (z : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (φ (z ⊗ₜ[ℚ] 1)) = cst w (QuaternionAlgebra.nrd z) := by
  rw [hφ.tmul_one, nrd_hatQ]

theorem nrd_φ_yiv (y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (hyw : QuaternionAlgebra.nrd (φ (yv y w)) = 1) :
    QuaternionAlgebra.nrd (φ (yiv y w)) = 1 := by
  have h := congrArg (fun t => QuaternionAlgebra.nrd (φ t)) (yv_mul_yiv y w)
  simp only [RingEquiv.map_mul, nrd_mul', hyw, one_mul, RingEquiv.map_one, QuaternionAlgebra.nrd_one] at h
  exact h

theorem barT_yv (y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (hyw : QuaternionAlgebra.nrd (φ (yv y w)) = 1) :
    barT φ (yv y w) = yiv y w :=
  barT_eq_of_mul_eq_one hyw (yv_mul_yiv y w)

theorem barT_yiv (y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (hyw : QuaternionAlgebra.nrd (φ (yv y w)) = 1) :
    barT φ (yiv y w) = yv y w :=
  barT_eq_of_mul_eq_one (nrd_φ_yiv y hyw) (yiv_mul_yv y w)

def Good (O : Submodule ℤ ℍ[ℚ, a, b]) (y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (Γ : ℍ[ℚ, a, b])
    (w : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  yiv y w * (Γ ⊗ₜ[ℚ] 1) ∈ Submodule.localBox O w ∧
    ((star Γ) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) * yv y w ∈ Submodule.localBox O w

theorem barT_first (hφ : IsCoord a b w φ) (y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ)
    (hyw : QuaternionAlgebra.nrd (φ (yv y w)) = 1) (Γ : ℍ[ℚ, a, b]) :
    barT φ (yiv y w * (Γ ⊗ₜ[ℚ] 1)) = ((star Γ) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) * yv y w := by
  rw [barT_mul, barT_tmul hφ, barT_yiv y hyw]

theorem good_of_first {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O)
    (hφ : IsCoord a b w φ) (y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ)
    (hyw : QuaternionAlgebra.nrd (φ (yv y w)) = 1) (Γ : ℍ[ℚ, a, b])
    (h1 : yiv y w * (Γ ⊗ₜ[ℚ] 1) ∈ Submodule.localBox O w) : Good O y Γ w :=
  ⟨h1, by rw [← barT_first hφ y hyw Γ]; exact barT_mem_localBox hO hφ h1⟩

theorem good_mul {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O)
    (y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) {Γ β : ℍ[ℚ, a, b]} (hΓ : Good O y Γ w)
    (hβ : β ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox O w)
    (hβ' : (star β) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox O w) :
    Good O y (Γ * β) w := by
  constructor
  · rw [← tmul_one_mul_tmul_one, ← mul_assoc]
    exact mul_mem_localBox hO w hΓ.1 hβ
  · rw [star_mul, ← tmul_one_mul_tmul_one, mul_assoc]
    exact mul_mem_localBox hO w hβ' hΓ.2

end Idele

section Induction

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem star_natCast_smul (n : ℕ) (z : ℍ[ℚ, a, b]) : star ((n : ℚ) • z) = (n : ℚ) • star z := by
  obtain ⟨z₀, z₁, z₂, z₃⟩ := z
  ext <;> simp

def NormOneAway (a b : ℚ) (y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 ℚ),
    ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
      IsCoord a b w φ → QuaternionAlgebra.nrd (φ (yv y w)) = 1

def Dense (a b : ℚ) (O : Submodule ℤ ℍ[ℚ, a, b]) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 ℚ),
    (∃ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x) →
    ∀ s' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ,
      (∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ → QuaternionAlgebra.nrd (φ s') = 1) →
      ∀ M : ℕ, M ≠ 0 →
        ∃ β : ℍ[ℚ, a, b], QuaternionAlgebra.nrd β = 1 ∧
          (∀ w' : HeightOneSpectrum (𝓞 ℚ), w' ≠ w →
            ∃ z ∈ Submodule.localBox O w',
              β ⊗ₜ[ℚ] (1 : w'.adicCompletion ℚ) = 1 + (M : ℚ) • z) ∧
          (∃ z ∈ Submodule.localBox O w,
              β ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) = s' + (M : ℚ) • z)

theorem one_add_smul_mem {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O)
    (w : HeightOneSpectrum (𝓞 ℚ)) (M : ℕ) {z : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ}
    (hz : z ∈ Submodule.localBox O w) : 1 + (M : ℚ) • z ∈ Submodule.localBox O w :=
  AddSubgroup.add_mem _ (one_mem_localBox hO w) (natCast_smul_mem_localBox w M hz)

theorem induct {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O)
    (hdense : Dense a b O)
    (y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (hy : NormOneAway a b y)
    (φ : (w : HeightOneSpectrum (𝓞 ℚ)) → (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]))
    (hφ : ∀ w, IsCoord a b w (φ w))
    (F : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∀ Γ : ℍ[ℚ, a, b], QuaternionAlgebra.nrd Γ = 1 →
      (∀ w ∈ F, ∃ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x) →
      (∀ w, w ∉ F → Good O y Γ w) →
      ∃ Γ' : ℍ[ℚ, a, b], QuaternionAlgebra.nrd Γ' = 1 ∧ ∀ w, Good O y Γ' w := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro Γ hΓ _ hgood
    exact ⟨Γ, hΓ, fun w => hgood w (Finset.notMem_empty w)⟩
  | insert w₁ F hw₁F ih =>
    intro Γ hΓ hsplit hgood
    have hsplit₁ := hsplit w₁ (Finset.mem_insert_self w₁ F)

    set s' : ℍ[ℚ, a, b] ⊗[ℚ] w₁.adicCompletion ℚ := ((star Γ) ⊗ₜ[ℚ] (1 : w₁.adicCompletion ℚ)) * yv y w₁ with hs'
    have hs'1 : ∀ φ' : ℍ[ℚ, a, b] ⊗[ℚ] w₁.adicCompletion ℚ ≃+*
        ℍ[w₁.adicCompletion ℚ, algebraMap ℚ (w₁.adicCompletion ℚ) a, algebraMap ℚ (w₁.adicCompletion ℚ) b],
        IsCoord a b w₁ φ' → QuaternionAlgebra.nrd (φ' s') = 1 := by
      intro φ' hφ'
      rw [hs', RingEquiv.map_mul, nrd_mul', nrd_φ_tmul_one hφ', QuaternionAlgebra.nrd_star, hΓ,
        show cst w₁ (1 : ℚ) = 1 from map_one _, one_mul]
      exact hy w₁ φ' hφ'

    obtain ⟨d, hd0, hd⟩ := exists_natCast_smul_mem_localBox hO w₁ (barT (φ w₁) s')
    obtain ⟨β, hβ1, haway, ⟨z₁, hz₁, hz₁eq⟩⟩ := hdense w₁ hsplit₁ s' hs'1 d hd0

    have hβint : ∀ w', w' ≠ w₁ →
        β ⊗ₜ[ℚ] (1 : w'.adicCompletion ℚ) ∈ Submodule.localBox O w' ∧
        (star β) ⊗ₜ[ℚ] (1 : w'.adicCompletion ℚ) ∈ Submodule.localBox O w' := by
      intro w' hw'1
      obtain ⟨z, hz, hzeq⟩ := haway w' hw'1
      have h1 : β ⊗ₜ[ℚ] (1 : w'.adicCompletion ℚ) ∈ Submodule.localBox O w' := by
        rw [hzeq]; exact one_add_smul_mem hO w' d hz
      exact ⟨h1, by rw [← barT_tmul (hφ w')]; exact barT_mem_localBox hO (hφ w') h1⟩

    refine ih (Γ * β) (by rw [nrd_mul', hΓ, hβ1, one_mul])
      (fun w hw => hsplit w (Finset.mem_insert_of_mem hw)) ?_
    intro w hwF
    by_cases hww₁ : w = w₁
    · subst hww₁
      have hyw : QuaternionAlgebra.nrd ((φ w) (yv y w)) = 1 := hy w (φ w) (hφ w)
      apply good_of_first hO (hφ w) y hyw
      have hfirst : yiv y w * (Γ ⊗ₜ[ℚ] 1) = barT (φ w) s' := by
        rw [hs', barT_mul, barT_tmul (hφ w), star_star, barT_yv y hyw]
      have hs's : barT (φ w) s' * s' = 1 := barT_mul_of_nrd s' (hs'1 (φ w) (hφ w))
      rw [← tmul_one_mul_tmul_one, ← mul_assoc, hfirst, hz₁eq, mul_add, hs's, mul_smul_comm, ← smul_mul_assoc]
      exact AddSubgroup.add_mem _ (one_mem_localBox hO w) (mul_mem_localBox hO w hd hz₁)
    · have hg := hgood w (by simp [hww₁, hwF])
      obtain ⟨h1, h2⟩ := hβint w hww₁
      exact good_mul hO y hg h1 h2

end Induction

section Main

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem exists_mem_finiteIdeleStabilizer_of_local (R : Submodule ℤ ℍ[ℚ, a, b])
    (hR : QuaternionAlgebra.IsOrder R)
    (x x' : (v : HeightOneSpectrum (𝓞 ℚ)) → ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
    (hx : ∀ v, x v ∈ Submodule.localBox R v) (hx' : ∀ v, x' v ∈ Submodule.localBox R v)
    (h1 : ∀ v, x v * x' v = 1) (h2 : ∀ v, x' v * x v = 1) :
    ∃ u ∈ Submodule.finiteIdeleStabilizer R,
      ∀ v : HeightOneSpectrum (𝓞 ℚ),
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = x v ∧
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = x' v := by
  obtain ⟨t, ht⟩ := Submodule.exists_forall_finiteAdeleEvalAt_eq R hR.fg hR.spanTop x
    (Filter.Eventually.of_forall hx)
  obtain ⟨t', ht'⟩ := Submodule.exists_forall_finiteAdeleEvalAt_eq R hR.fg hR.spanTop x'
    (Filter.Eventually.of_forall hx')
  have htt' : t * t' = 1 := by
    refine Submodule.eq_of_forall_finiteAdeleEvalAt_eq _ _ fun v => ?_
    rw [map_mul, ht, ht', h1, map_one]
  have ht't : t' * t = 1 := by
    refine Submodule.eq_of_forall_finiteAdeleEvalAt_eq _ _ fun v => ?_
    rw [map_mul, ht, ht', h2, map_one]
  set u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ := ⟨t, t', htt', ht't⟩ with hu
  refine ⟨u, ?_, fun v => ⟨ht v, ht' v⟩⟩
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits R hR]
  intro v
  rw [Submodule.mem_localBoxUnits_iff]
  constructor
  · rw [Units.coe_map]
    change Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v t ∈ _
    rw [ht]; exact hx v
  · rw [Units.coe_map_inv]
    change Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v t' ∈ _
    rw [ht']; exact hx' v

theorem inv_unique' {R : Type*} [Monoid R] {t b c : R} (h1 : t * b = 1) (h2 : c * t = 1) : b = c := by
  calc b = (c * t) * b := by rw [h2, one_mul]
    _ = c := by rw [mul_assoc, h1, mul_one]

theorem main (ha : a ≠ 0) (hb : b ≠ 0)
    {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O)
    (hdense : Dense a b O)
    (y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (hy : NormOneAway a b y) :
    ∃ (β : (ℍ[ℚ, a, b])ˣ) (u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ),
      QuaternionAlgebra.nrd (β : ℍ[ℚ, a, b]) = 1 ∧
      u ∈ Submodule.finiteIdeleStabilizer O ∧
      y = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] β * u := by
  classical
  have ha0 : a ≠ 0 := ha
  have hb0 : b ≠ 0 := hb
  choose φ hφ using fun w => exists_isCoord a b w
  have hyw : ∀ w, QuaternionAlgebra.nrd ((φ w) (yv y w)) = 1 := fun w => hy w (φ w) (hφ w)

  have hfin_y : {w : HeightOneSpectrum (𝓞 ℚ) | ¬ (yv y w ∈ Submodule.localBox O w ∧ yiv y w ∈ Submodule.localBox O w)}.Finite := by
    have h1 := Submodule.eventually_finiteAdeleEvalAt_mem_localBox O hO.fg hO.spanTop (y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)
    have h2 := Submodule.eventually_finiteAdeleEvalAt_mem_localBox O hO.fg hO.spanTop
      ((y⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)
    have := (h1.and h2)
    rw [Filter.eventually_cofinite] at this
    exact this
  have hfin_exc : {w : HeightOneSpectrum (𝓞 ℚ) | pgen w ∣ excNat a b}.Finite := finite_setOf_dvd (excNat_ne_zero ha0 hb0)
  set S : Finset (HeightOneSpectrum (𝓞 ℚ)) := (hfin_y.union hfin_exc).toFinset with hS
  have hout : ∀ w, w ∉ S → (yv y w ∈ Submodule.localBox O w ∧ yiv y w ∈ Submodule.localBox O w) ∧
      ¬ pgen w ∣ excNat a b := by
    intro w hwS
    have : w ∉ (hfin_y.union hfin_exc).toFinset := hwS
    rw [Set.Finite.mem_toFinset, Set.mem_union, not_or] at this
    simpa using this

  choose d hd0 hd using fun w => exists_natCast_smul_mem_localBox hO w (yiv y w)
  set M₂ : ℕ := ∏ w ∈ S, d w with hM₂
  have hM₂0 : M₂ ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ => hd0 w

  obtain ⟨γ, hγ1, hγ⟩ :=
    QuaternionAlgebra.IsOrder.exists_nrd_eq_one_forall_tmul_eq_add_smul_of_finset ha0 hb0 hO S
      (fun w => yv y w) (fun w _ φ' hφ' => hy w φ' hφ') M₂ hM₂0
  have hgoodS : ∀ w ∈ S, Good O y γ w := by
    intro w hw
    obtain ⟨z, hz, hzeq⟩ := hγ w hw
    apply good_of_first hO (hφ w) y (hyw w)
    obtain ⟨m, hm⟩ : d w ∣ M₂ := Finset.dvd_prod_of_mem _ hw
    rw [hzeq, mul_add, yiv_mul_yv, mul_smul_comm, hm, Nat.cast_mul, mul_comm ((d w : ℕ) : ℚ), mul_smul,
      ← smul_mul_assoc]
    exact AddSubgroup.add_mem _ (one_mem_localBox hO w)
      (natCast_smul_mem_localBox w m (mul_mem_localBox hO w (hd w) hz))

  obtain ⟨nγ, hnγ0, hnγ⟩ := exists_natCast_smul_mem_order hO γ
  have hnγ' : (nγ : ℚ) • star γ ∈ O := by rw [← star_natCast_smul]; exact star_mem hO hnγ
  have hfin_γ : {w : HeightOneSpectrum (𝓞 ℚ) | pgen w ∣ nγ}.Finite := finite_setOf_dvd hnγ0
  set F : Finset (HeightOneSpectrum (𝓞 ℚ)) := hfin_γ.toFinset \ S with hF
  have hFsplit : ∀ w ∈ F, ∃ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x := by
    intro w hw
    obtain ⟨-, hwS⟩ := Finset.mem_sdiff.1 hw
    exact exists_ne_zero_not_isUnit ha0 hb0 w (hout w hwS).2
  have hgoodF : ∀ w, w ∉ F → Good O y γ w := by
    intro w hwF
    by_cases hwS : w ∈ S
    · exact hgoodS w hwS
    · have hnd : ¬ pgen w ∣ nγ := by
        intro hdvd
        apply hwF
        exact Finset.mem_sdiff.2 ⟨(Set.Finite.mem_toFinset _).2 hdvd, hwS⟩
      obtain ⟨⟨hy1, hy2⟩, -⟩ := hout w hwS
      exact ⟨mul_mem_localBox hO w hy2 (tmul_one_mem_localBox_of_not_dvd w hnγ0 hnγ hnd),
        mul_mem_localBox hO w (tmul_one_mem_localBox_of_not_dvd w hnγ0 hnγ' hnd) hy1⟩

  obtain ⟨Γ, hΓ1, hΓ⟩ := induct hO hdense y hy φ hφ F γ hγ1 hFsplit hgoodF

  set xl : (w : HeightOneSpectrum (𝓞 ℚ)) → ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ :=
    fun w => ((star Γ) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) * yv y w with hxl
  set xl' : (w : HeightOneSpectrum (𝓞 ℚ)) → ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ :=
    fun w => yiv y w * (Γ ⊗ₜ[ℚ] 1) with hxl'
  have hstarΓ : star Γ * Γ = 1 := by
    rw [QuaternionAlgebra.star_mul_eq_coe_nrd, hΓ1]; rfl
  have hΓstar : Γ * star Γ = 1 := by
    rw [QuaternionAlgebra.mul_star_eq_coe_nrd, hΓ1]; rfl
  have hxl_eq : ∀ w, xl w = ((star Γ) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) * yv y w := fun w => rfl
  have hxl'_eq : ∀ w, xl' w = yiv y w * (Γ ⊗ₜ[ℚ] 1) := fun w => rfl
  have hx1 : ∀ w, xl w * xl' w = 1 := by
    intro w
    rw [hxl_eq w, hxl'_eq w, mul_assoc, ← mul_assoc (yv y w), yv_mul_yiv, one_mul,
      tmul_one_mul_tmul_one, hstarΓ]
    rfl
  have hx2 : ∀ w, xl' w * xl w = 1 := by
    intro w
    rw [hxl_eq w, hxl'_eq w, mul_assoc, ← mul_assoc (Γ ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)),
      tmul_one_mul_tmul_one, hΓstar, show ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) = 1 from rfl,
      one_mul, yiv_mul_yv]
  have hxlmem : ∀ w, xl w ∈ Submodule.localBox O w := fun w => by rw [hxl_eq w]; exact (hΓ w).2
  have hxl'mem : ∀ w, xl' w ∈ Submodule.localBox O w := fun w => by rw [hxl'_eq w]; exact (hΓ w).1
  obtain ⟨U, hUstab, hU⟩ := exists_mem_finiteIdeleStabilizer_of_local O hO xl xl' hxlmem hxl'mem hx1 hx2

  set βu : (ℍ[ℚ, a, b])ˣ := ⟨Γ, star Γ, hΓstar, hstarΓ⟩ with hβu
  refine ⟨βu, U, hΓ1, hUstab, ?_⟩
  apply Units.ext
  rw [Units.val_mul]
  refine Submodule.eq_of_forall_finiteAdeleEvalAt_eq _ _ fun w => ?_
  rw [map_mul, Submodule.val_finiteIdeleDiagonal_apply, (hU w).1, hxl_eq w]
  rw [show ((βu : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = Γ from rfl, evalAt_tmul_one]
  change yv y w = Γ ⊗ₜ[ℚ] 1 * (star Γ ⊗ₜ[ℚ] 1 * yv y w)
  rw [← mul_assoc, tmul_one_mul_tmul_one, hΓstar]
  exact (one_mul _).symm

end Main

end KRCC

end

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem solution
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O)
    (hdense : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      (∃ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x) →
      ∀ s' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ,
        (∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
            ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
          (∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
            φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
              algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
              algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
                ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a,
                  algebraMap ℚ (w.adicCompletion ℚ) b])) →
          QuaternionAlgebra.nrd (φ s') = 1) →
        ∀ M : ℕ, M ≠ 0 →
          ∃ β : ℍ[ℚ, a, b], QuaternionAlgebra.nrd β = 1 ∧
            (∀ w' : HeightOneSpectrum (𝓞 ℚ), w' ≠ w →
              ∃ z ∈ Submodule.localBox O w',
                β ⊗ₜ[ℚ] (1 : w'.adicCompletion ℚ) = 1 + (M : ℚ) • z) ∧
            (∃ z ∈ Submodule.localBox O w,
                β ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) = s' + (M : ℚ) • z))
    (y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hy : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
          φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
            algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
              ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a,
                algebraMap ℚ (w.adicCompletion ℚ) b])) →
        QuaternionAlgebra.nrd
          (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
            (y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) = 1) :
    ∃ (β : (ℍ[ℚ, a, b])ˣ) (u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      QuaternionAlgebra.nrd (β : ℍ[ℚ, a, b]) = 1 ∧
      u ∈ Submodule.finiteIdeleStabilizer O ∧
      y = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] β * u :=
  KRCC.main ha hb hO hdense y hy

end S_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_of_forall_exists_nrd_eq_one_tmul_eq_add_smul
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_of_forall_exists_nrd_eq_one_tmul_eq_add_smul (solution)
