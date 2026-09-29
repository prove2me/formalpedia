-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.exists_ne_neg_one_forall_exists_nrd_eq_one_tmul_eq_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4dc3cae4-3a74-578d-9472-f620b6a37705

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_forall_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero
import Theorems.Thm_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero
import Theorems.Thm_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split
import Theorems.Thm_QuadraticForm_exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real
import Theorems.Thm_Padic_exists_ternary_isotropic_of_norm_eq_one_of_ne_two
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_forall_exists_units_smul_conj_mem_of_int_trd_nrd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_ne_neg_one_forall_exists_nrd_eq_one_tmul_eq_add_smul
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option linter.style.longFile 0
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField Filter Topology

noncomputable section

namespace KLCC

section Places

abbrev pgen (w : HeightOneSpectrum (𝓞 ℚ)) : ℕ := Rat.HeightOneSpectrum.natGenerator w

theorem pgen_prime (w : HeightOneSpectrum (𝓞 ℚ)) : (pgen w).Prime :=
  Rat.HeightOneSpectrum.prime_natGenerator w

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ pgen w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem intCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℤ) :
    (z : 𝓞 ℚ) ∈ w.asIdeal ↔ (pgen w : ℤ) ∣ z := by
  rw [Int.natCast_dvd, ← natCast_mem_asIdeal_iff]
  rcases Int.natAbs_eq z with h | h
  · conv_lhs => rw [h]
    simp
  · conv_lhs => rw [h]
    simp

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
  exact_mod_cast (pgen_prime w).ne_zero

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem pgen_injective : Function.Injective pgen := by
  intro w w' h
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext h

theorem valuation_natCast_eq_one_of_not_dvd (w : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : ¬ pgen w ∣ n) :
    w.valuation ℚ (n : ℚ) = 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  refine (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 ?_
  rwa [natCast_mem_asIdeal_iff]

theorem valuation_intCast_eq_one_of_not_dvd (w : HeightOneSpectrum (𝓞 ℚ)) {z : ℤ}
    (hz : ¬ (pgen w : ℤ) ∣ z) : w.valuation ℚ (z : ℚ) = 1 := by
  rw [show (z : ℚ) = algebraMap (𝓞 ℚ) ℚ z from (map_intCast _ _).symm]
  refine (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (z : 𝓞 ℚ))).2 ?_
  rwa [intCast_mem_asIdeal_iff]

theorem valuation_intCast_le_one (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℤ) : w.valuation ℚ (z : ℚ) ≤ 1 := by
  rw [show (z : ℚ) = algebraMap (𝓞 ℚ) ℚ z from (map_intCast _ _).symm]
  exact HeightOneSpectrum.valuation_le_one w _

theorem valuation_natCast_le_one (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : w.valuation ℚ (n : ℚ) ≤ 1 := by
  exact_mod_cast valuation_intCast_le_one w n

theorem mem_integers_iff (w : HeightOneSpectrum (𝓞 ℚ)) (x : w.adicCompletion ℚ) :
    x ∈ w.adicCompletionIntegers ℚ ↔ Valued.v x ≤ 1 := HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

theorem natCast_adicCompletion_ne_zero (w : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : n ≠ 0) :
    (n : w.adicCompletion ℚ) ≠ 0 := by
  rw [show (n : w.adicCompletion ℚ) = algebraMap ℚ (w.adicCompletion ℚ) (n : ℚ) from (map_natCast _ _).symm]
  exact (map_ne_zero_iff _ (algebraMap ℚ (w.adicCompletion ℚ)).injective).2 (Nat.cast_ne_zero.2 hn)

theorem inv_natCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : ¬ pgen w ∣ n) :
    (algebraMap ℚ (w.adicCompletion ℚ) ((n : ℚ)⁻¹)) ∈ w.adicCompletionIntegers ℚ := by
  rw [mem_integers_iff, valued_algebraMap, map_inv₀, valuation_natCast_eq_one_of_not_dvd w hn, inv_one]

theorem intCast_div_natCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℤ) {n : ℕ} (hn : ¬ pgen w ∣ n) :
    (algebraMap ℚ (w.adicCompletion ℚ) ((z : ℚ) / n)) ∈ w.adicCompletionIntegers ℚ := by
  rw [div_eq_mul_inv, map_mul]
  refine mul_mem ?_ (inv_natCast_mem_integers w hn)
  rw [mem_integers_iff, valued_algebraMap]
  exact valuation_intCast_le_one w z

end Places

section Coord

variable {a b : ℚ}

abbrev cst (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) : w.adicCompletion ℚ := algebraMap ℚ (w.adicCompletion ℚ) r

def hatQ (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) : ℍ[w.adicCompletion ℚ, cst w a, cst w b] :=
  ⟨cst w x.re, cst w x.imI, cst w x.imJ, cst w x.imK⟩

theorem nrd_hatQ (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (hatQ w x) = cst w (QuaternionAlgebra.nrd x) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp [hatQ, QuaternionAlgebra.nrd, map_add, map_sub, map_mul, map_pow]

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

theorem IsCoord.eq (hφ : IsCoord a b w φ)
    {φ' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}
    (hφ' : IsCoord a b w φ') (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : φ' x = φ x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul z r => rw [hφ.tmul, hφ'.tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Coord

section Boxes

variable {a b : ℚ} {O : Submodule ℤ ℍ[ℚ, a, b]}

theorem tmul_mem_localBox {z : ℍ[ℚ, a, b]} (hz : z ∈ O) (w : HeightOneSpectrum (𝓞 ℚ))
    {c : w.adicCompletion ℚ} (hc : c ∈ w.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox O w :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem smul_mem_localBox (w : HeightOneSpectrum (𝓞 ℚ)) {r : ℚ}
    (hr : cst w r ∈ w.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hx : x ∈ Submodule.localBox O w) :
    r • x ∈ Submodule.localBox O w := by
  induction hx using AddSubgroup.closure_induction with
  | mem x' hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.smul_def]
    exact tmul_mem_localBox hz w (mul_mem hr hc)
  | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
  | add u u' _ _ hu hu' => rw [smul_add]; exact AddSubgroup.add_mem _ hu hu'
  | neg u _ hu => rw [smul_neg]; exact AddSubgroup.neg_mem _ hu

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

theorem exists_basis_smul_mem (hO : QuaternionAlgebra.IsOrder O) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ e₀ e₁ e₂ e₃ : ℤ,
      (N : ℚ) • (⟨e₀, e₁, e₂, e₃⟩ : ℍ[ℚ, a, b]) ∈ O := by
  obtain ⟨n₀, h₀, m₀⟩ := exists_natCast_smul_mem_order hO ⟨1, 0, 0, 0⟩
  obtain ⟨n₁, h₁, m₁⟩ := exists_natCast_smul_mem_order hO ⟨0, 1, 0, 0⟩
  obtain ⟨n₂, h₂, m₂⟩ := exists_natCast_smul_mem_order hO ⟨0, 0, 1, 0⟩
  obtain ⟨n₃, h₃, m₃⟩ := exists_natCast_smul_mem_order hO ⟨0, 0, 0, 1⟩
  refine ⟨n₀ * n₁ * n₂ * n₃, by positivity, fun e₀ e₁ e₂ e₃ => ?_⟩
  have e : ((n₀ * n₁ * n₂ * n₃ : ℕ) : ℚ) • (⟨e₀, e₁, e₂, e₃⟩ : ℍ[ℚ, a, b])
      = (e₀ * (n₁ * n₂ * n₃ : ℕ) : ℤ) • ((n₀ : ℚ) • (⟨1, 0, 0, 0⟩ : ℍ[ℚ, a, b]))
        + (e₁ * (n₀ * n₂ * n₃ : ℕ) : ℤ) • ((n₁ : ℚ) • (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]))
        + (e₂ * (n₀ * n₁ * n₃ : ℕ) : ℤ) • ((n₂ : ℚ) • (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]))
        + (e₃ * (n₀ * n₁ * n₂ : ℕ) : ℤ) • ((n₃ : ℚ) • (⟨0, 0, 0, 1⟩ : ℍ[ℚ, a, b])) := by
    simp only [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    ext <;> simp <;> ring
  rw [e]
  exact O.add_mem (O.add_mem (O.add_mem (O.smul_mem _ m₀) (O.smul_mem _ m₁)) (O.smul_mem _ m₂))
    (O.smul_mem _ m₃)

theorem exists_den (hO : QuaternionAlgebra.IsOrder O) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ o ∈ O, ∃ z₀ z₁ z₂ z₃ : ℤ,
      (N : ℚ) * o.re = z₀ ∧ (N : ℚ) * o.imI = z₁ ∧ (N : ℚ) * o.imJ = z₂ ∧ (N : ℚ) * o.imK = z₃ := by
  classical
  obtain ⟨S, hS⟩ := hO.fg
  let dq : ℍ[ℚ, a, b] → ℕ := fun s => s.re.den * s.imI.den * s.imJ.den * s.imK.den
  refine ⟨∏ s ∈ S, dq s, Finset.prod_ne_zero_iff.2 fun s _ => by
    simp only [dq]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Rat.den_ne_zero _) (Rat.den_ne_zero _))
      (Rat.den_ne_zero _)) (Rat.den_ne_zero _), fun o ho => ?_⟩
  set N : ℕ := ∏ s ∈ S, dq s with hN
  rw [← hS] at ho
  induction ho using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨K, hK⟩ : dq s ∣ N := Finset.dvd_prod_of_mem dq hs
    have hden : ∀ r : ℚ, ∃ z : ℤ, (r.den : ℚ) * r = z := fun r => ⟨r.num, Rat.den_mul_eq_num r⟩
    obtain ⟨y₀, hy₀⟩ := hden s.re
    obtain ⟨y₁, hy₁⟩ := hden s.imI
    obtain ⟨y₂, hy₂⟩ := hden s.imJ
    obtain ⟨y₃, hy₃⟩ := hden s.imK
    refine ⟨y₀ * (s.imI.den * s.imJ.den * s.imK.den * K : ℕ), y₁ * (s.re.den * s.imJ.den * s.imK.den * K : ℕ),
      y₂ * (s.re.den * s.imI.den * s.imK.den * K : ℕ), y₃ * (s.re.den * s.imI.den * s.imJ.den * K : ℕ),
      ?_, ?_, ?_, ?_⟩
    · rw [hK]; simp only [dq]; push_cast; linear_combination ((s.imI.den : ℚ) * s.imJ.den * s.imK.den * K) * hy₀
    · rw [hK]; simp only [dq]; push_cast; linear_combination ((s.re.den : ℚ) * s.imJ.den * s.imK.den * K) * hy₁
    · rw [hK]; simp only [dq]; push_cast; linear_combination ((s.re.den : ℚ) * s.imI.den * s.imK.den * K) * hy₂
    · rw [hK]; simp only [dq]; push_cast; linear_combination ((s.re.den : ℚ) * s.imI.den * s.imJ.den * K) * hy₃
  | zero => exact ⟨0, 0, 0, 0, by simp, by simp, by simp, by simp⟩
  | add u u' _ _ hu hu' =>
    obtain ⟨z₀, z₁, z₂, z₃, h₀, h₁, h₂, h₃⟩ := hu
    obtain ⟨z₀', z₁', z₂', z₃', h₀', h₁', h₂', h₃'⟩ := hu'
    refine ⟨z₀ + z₀', z₁ + z₁', z₂ + z₂', z₃ + z₃', ?_, ?_, ?_, ?_⟩
    · simp only [QuaternionAlgebra.re_add, mul_add, h₀, h₀', Int.cast_add]
    · simp only [QuaternionAlgebra.imI_add, mul_add, h₁, h₁', Int.cast_add]
    · simp only [QuaternionAlgebra.imJ_add, mul_add, h₂, h₂', Int.cast_add]
    · simp only [QuaternionAlgebra.imK_add, mul_add, h₃, h₃', Int.cast_add]
  | smul k u _ hu =>
    obtain ⟨z₀, z₁, z₂, z₃, h₀, h₁, h₂, h₃⟩ := hu
    refine ⟨k * z₀, k * z₁, k * z₂, k * z₃, ?_, ?_, ?_, ?_⟩
    · rw [QuaternionAlgebra.re_smul, zsmul_eq_mul, mul_left_comm, h₀, Int.cast_mul]
    · rw [QuaternionAlgebra.imI_smul, zsmul_eq_mul, mul_left_comm, h₁, Int.cast_mul]
    · rw [QuaternionAlgebra.imJ_smul, zsmul_eq_mul, mul_left_comm, h₂, Int.cast_mul]
    · rw [QuaternionAlgebra.imK_smul, zsmul_eq_mul, mul_left_comm, h₃, Int.cast_mul]

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
  set qq : ℍ[w.adicCompletion ℚ, cst w a, cst w b] := ⟨e.symm z, e.symm x, e.symm y, 0⟩ with hqq
  have hq0 : qq ≠ 0 := by
    intro h0
    apply hne'
    have h1 := congrArg QuaternionAlgebra.re h0
    have h2 := congrArg QuaternionAlgebra.imI h0
    have h3 := congrArg QuaternionAlgebra.imJ h0
    simp only [hqq] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hnrd : QuaternionAlgebra.nrd qq = 0 := by
    rw [hqq, QuaternionAlgebra.nrd_mk]
    linear_combination heq'
  obtain ⟨φ, hφ⟩ := exists_isCoord a b w
  refine ⟨φ.symm qq, fun h0 => hq0 (by simpa using congrArg φ h0), fun hu => ?_⟩
  have hu' : IsUnit qq := by simpa using hu.map φ
  have hqq2 : qq * star qq = 0 := by
    rw [QuaternionAlgebra.mul_star_eq_coe_nrd, hnrd]; rfl
  have hstar : star qq = 0 := (hu'.mul_right_eq_zero).1 hqq2
  exact hq0 (by simpa using congrArg star hstar)

end Split

section Local

variable {a b : ℚ}

theorem not_isSquare_of_valuation_odd (w : HeightOneSpectrum (𝓞 ℚ)) (x : w.adicCompletion ℚ) (n : ℤ)
    (hn : Odd n) (hx : Valued.v x = WithZero.exp n) : ¬ IsSquare x := by
  rintro ⟨s, rfl⟩
  have hs0 : Valued.v s ≠ 0 := by
    intro h0
    rw [map_mul, h0, mul_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  have hs : WithZero.exp (WithZero.log (Valued.v s)) = Valued.v s := WithZero.exp_log hs0
  rw [map_mul, ← hs, ← WithZero.exp_add, WithZero.exp_inj] at hx
  obtain ⟨k, hk⟩ := hn
  omega

theorem not_nonempty_algEquiv_matrix_of_forall_isUnit (u : HeightOneSpectrum (𝓞 ℚ))
    (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] u.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ¬ Nonempty (ℍ[u.adicCompletion ℚ, algebraMap ℚ (u.adicCompletion ℚ) a, algebraMap ℚ (u.adicCompletion ℚ) b]
        ≃ₐ[u.adicCompletion ℚ] Matrix (Fin 2) (Fin 2) (u.adicCompletion ℚ)) := by
  rintro ⟨ψ⟩
  set K := u.adicCompletion ℚ
  obtain ⟨φ₀, -, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ K a) (d₂ := (0 : K)) (d₃ := algebraMap ℚ K b) rfl (map_zero _) rfl AlgEquiv.refl
  let E : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, 0]
  let F : Matrix (Fin 2) (Fin 2) K := !![0, 0; 0, 1]
  have hEF : E * F = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [E, F]
  have hF : F ≠ 0 := fun h => by simpa [F] using congrFun (congrFun h 1) 1
  have hE : E ≠ 0 := fun h => by simpa [E] using congrFun (congrFun h 0) 0
  have hEu : ¬ IsUnit E := fun hu => hF ((hu.mul_right_eq_zero).1 hEF)
  have hx0 : φ₀.symm (ψ.symm E) ≠ 0 := by
    intro h0
    apply hE
    have := congrArg ψ (congrArg φ₀ h0)
    simpa using this
  have hxu := hdiv _ hx0
  have : IsUnit E := by simpa using (hxu.map φ₀).map ψ
  exact hEu this

theorem exists_pureNrd_eq_of_not_forall_isUnit (ha : a ≠ 0) (hb : b ≠ 0) (u : HeightOneSpectrum (𝓞 ℚ))
    (hndiv : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] u.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ∀ c : u.adicCompletion ℚ, ∃ x y z : u.adicCompletion ℚ,
      -(algebraMap ℚ (u.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (u.adicCompletion ℚ) b) * y ^ 2
        + (algebraMap ℚ (u.adicCompletion ℚ) a) * (algebraMap ℚ (u.adicCompletion ℚ) b) * z ^ 2 = c := by
  set K := u.adicCompletion ℚ
  intro c
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  set A := algebraMap ℚ K a
  set B := algebraMap ℚ K b
  obtain ⟨φ₀, -, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := A) (d₂ := (0 : K)) (d₃ := B) rfl (map_zero _) rfl AlgEquiv.refl
  have hK : ¬ ∀ x : ℍ[K, A, B], x ≠ 0 → IsUnit x := by
    intro hall
    apply hndiv
    intro x hx
    have hx' : φ₀ x ≠ 0 := by
      intro h0; apply hx; simpa using congrArg φ₀.symm h0
    have hu := hall (φ₀ x) hx'
    simpa using hu.map φ₀.symm
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hAK : A ≠ 0 := by simpa [A] using (algebraMap ℚ K).injective.ne ha
  have hBK : B ≠ 0 := by simpa [B] using (algebraMap ℚ K).injective.ne hb
  have hiso : ∃ x₀ x₁ x₂ x₃ : K, ¬ (x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
      x₀ ^ 2 - A * x₁ ^ 2 - B * x₂ ^ 2 + A * B * x₃ ^ 2 = 0 := by
    by_contra hno
    apply hK
    refine (QuaternionAlgebra.forall_isUnit_iff_forall_normForm_eq_zero K A B).2 fun x₀ x₁ x₂ x₃ h0 => ?_
    by_contra hne
    exact hno ⟨x₀, x₁, x₂, x₃, hne, h0⟩
  obtain ⟨x₀, x₁, x₂, x₃, hx, h0⟩ := hiso
  obtain ⟨ψ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero K h2 A B hAK hBK x₀ x₁ x₂ x₃ hx h0

  let Nm : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]
  have hNm : Nm * Nm = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Nm]
  have hNm0 : Nm ≠ 0 := fun h => by simpa [Nm] using congrFun (congrFun h 0) 1
  obtain ⟨n₀, n₁, n₂, n₃, hn⟩ : ∃ n₀ n₁ n₂ n₃ : K, ψ.symm Nm = ⟨n₀, n₁, n₂, n₃⟩ :=
    ⟨(ψ.symm Nm).re, (ψ.symm Nm).imI, (ψ.symm Nm).imJ, (ψ.symm Nm).imK, by ext <;> rfl⟩
  have hnn : (⟨n₀, n₁, n₂, n₃⟩ : ℍ[K, A, B]) * ⟨n₀, n₁, n₂, n₃⟩ = 0 := by
    rw [← hn, ← map_mul, hNm, map_zero]
  have hn0 : (⟨n₀, n₁, n₂, n₃⟩ : ℍ[K, A, B]) ≠ 0 := by
    rw [← hn]
    intro h0
    apply hNm0
    simpa using congrArg ψ h0
  rw [QuaternionAlgebra.mk_mul_mk] at hnn
  have hre := congrArg QuaternionAlgebra.re hnn
  have hI := congrArg QuaternionAlgebra.imI hnn
  have hJ := congrArg QuaternionAlgebra.imJ hnn
  have hKk := congrArg QuaternionAlgebra.imK hnn
  change _ = (0 : K) at hre hI hJ hKk
  have hn₀ : n₀ = 0 := by
    by_contra h
    have h1 : n₁ = 0 := by
      have : (2 * n₀) * n₁ = 0 := by linear_combination hI
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (mul_ne_zero h2 h)
      · exact h'
    have h2' : n₂ = 0 := by
      have : (2 * n₀) * n₂ = 0 := by linear_combination hJ
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (mul_ne_zero h2 h)
      · exact h'
    have h3 : n₃ = 0 := by
      have : (2 * n₀) * n₃ = 0 := by linear_combination hKk
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (mul_ne_zero h2 h)
      · exact h'
    subst h1 h2' h3
    have : n₀ * n₀ = 0 := by linear_combination hre
    exact h (mul_self_eq_zero.1 this)
  subst hn₀
  have hiso3 : ∃ x y z : K, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ -A * x ^ 2 - B * y ^ 2 + A * B * z ^ 2 = 0 := by
    refine ⟨n₁, n₂, n₃, ?_, by linear_combination (-1 : K) * hre⟩
    rintro ⟨rfl, rfl, rfl⟩
    exact hn0 (by ext <;> rfl)
  exact QuadraticForm.forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero K A B hAK hBK hiso3 c

theorem exists_pureNrd_eq_of_valuation_odd (ha : a ≠ 0) (hb : b ≠ 0) (u : HeightOneSpectrum (𝓞 ℚ))
    (c : ℚ) (n : ℤ) (hn : Odd n) (hc : Valued.v (cst u c) = WithZero.exp n) :
    ∃ x y z : u.adicCompletion ℚ,
      -(algebraMap ℚ (u.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (u.adicCompletion ℚ) b) * y ^ 2
        + (algebraMap ℚ (u.adicCompletion ℚ) a) * (algebraMap ℚ (u.adicCompletion ℚ) b) * z ^ 2 = cst u c := by
  by_cases hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] u.adicCompletion ℚ, x ≠ 0 → IsUnit x
  · refine QuadraticForm.exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split a b ha hb u
      (not_nonempty_algEquiv_matrix_of_forall_isUnit u hdiv) _ ?_
    refine not_isSquare_of_valuation_odd u _ n hn ?_
    rw [Valuation.map_neg, hc]
  · exact exists_pureNrd_eq_of_not_forall_isUnit ha hb u hdiv _

end Local

section Arith

variable {a b : ℚ}

def P0 (a b : ℚ) (p q : ℕ) : Finset ℕ := ((excNat a b * q).primeFactors).erase p

def c0 (a b : ℚ) (p q : ℕ) : ℕ := ∏ ℓ ∈ P0 a b p q, ℓ

variable {p q : ℕ}

theorem prime_of_mem_P0 {ℓ : ℕ} (h : ℓ ∈ P0 a b p q) : ℓ.Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase h)

theorem ne_of_mem_P0 {ℓ : ℕ} (h : ℓ ∈ P0 a b p q) : ℓ ≠ p := Finset.ne_of_mem_erase h

theorem c0_ne_zero : c0 a b p q ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun ℓ h => (prime_of_mem_P0 h).ne_zero

theorem mem_P0_of_dvd (ha : a ≠ 0) (hb : b ≠ 0) (hq : q.Prime) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (h : ℓ ∣ excNat a b * q) : ℓ ∈ P0 a b p q :=
  Finset.mem_erase.2 ⟨hℓp, Nat.mem_primeFactors.2 ⟨hℓ, h, mul_ne_zero (excNat_ne_zero ha hb) hq.ne_zero⟩⟩

theorem q_mem_P0 (ha : a ≠ 0) (hb : b ≠ 0) (hq : q.Prime) (hqp : q ≠ p) : q ∈ P0 a b p q :=
  mem_P0_of_dvd ha hb hq hq hqp (dvd_mul_left q _)

theorem dvd_c0_of_mem {ℓ : ℕ} (h : ℓ ∈ P0 a b p q) : ℓ ∣ c0 a b p q := Finset.dvd_prod_of_mem _ h

theorem c0_eq_mul_of_mem {ℓ : ℕ} (h : ℓ ∈ P0 a b p q) : ∃ m : ℕ, c0 a b p q = ℓ * m ∧ ¬ ℓ ∣ m := by
  classical
  refine ⟨∏ ℓ' ∈ (P0 a b p q).erase ℓ, ℓ', (Finset.mul_prod_erase _ _ h).symm, ?_⟩
  intro hd
  obtain ⟨ℓ', hℓ', hd'⟩ := (Nat.Prime.prime (prime_of_mem_P0 h)).exists_mem_finset_dvd hd
  have h1 := (Nat.prime_dvd_prime_iff_eq (prime_of_mem_P0 h) (prime_of_mem_P0 (Finset.mem_of_mem_erase hℓ'))).1 hd'
  exact Finset.ne_of_mem_erase hℓ' h1.symm

end Arith

section Beta

variable {a b : ℚ}

theorem nrd_one_add (y : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (1 + y) = 1 + QuaternionAlgebra.trd y + QuaternionAlgebra.nrd y := by
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp [QuaternionAlgebra.nrd, QuaternionAlgebra.trd]
  ring

theorem trd_one_add (y : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.trd (1 + y) = 2 + QuaternionAlgebra.trd y := by
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp [QuaternionAlgebra.trd]
  ring

theorem trd_smul (r : ℚ) (y : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.trd (r • y) = r * QuaternionAlgebra.trd y := by
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp [QuaternionAlgebra.trd]
  ring

theorem nrd_smul (r : ℚ) (y : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (r • y) = r ^ 2 * QuaternionAlgebra.nrd y := by
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp [QuaternionAlgebra.nrd]
  ring

theorem trd_mul_comm (x y : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.trd (x * y) = QuaternionAlgebra.trd (y * x) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.trd_mk]
  ring

theorem nrd_mul (x y : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

theorem trd_units_conj (μ : (ℍ[ℚ, a, b])ˣ) (x : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.trd ((μ : ℍ[ℚ, a, b]) * x * ((μ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = QuaternionAlgebra.trd x := by
  rw [trd_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

theorem nrd_units_conj (μ : (ℍ[ℚ, a, b])ˣ) (x : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd ((μ : ℍ[ℚ, a, b]) * x * ((μ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = QuaternionAlgebra.nrd x := by
  have h1 : QuaternionAlgebra.nrd (μ : ℍ[ℚ, a, b]) * QuaternionAlgebra.nrd ((μ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 1 := by
    rw [← nrd_mul, Units.mul_inv, QuaternionAlgebra.nrd_one]
  rw [nrd_mul, nrd_mul]
  linear_combination QuaternionAlgebra.nrd x * h1

variable {O : Submodule ℤ ℍ[ℚ, a, b]}

theorem exists_beta (ha : a < 0) (hb : b < 0) (hO : QuaternionAlgebra.IsOrder O)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ∃ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x)
    (q : ℕ) (hq : q.Prime) (hqp : q ≠ pgen v)
    {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (hd : ∀ α : ℍ[ℚ, a, b], (∃ t n : ℤ, QuaternionAlgebra.trd α = t ∧ QuaternionAlgebra.nrd α = n) →
      ∃ μ : (ℍ[ℚ, a, b])ˣ, (d₀ : ℚ) • ((μ : ℍ[ℚ, a, b]) * α * ↑μ⁻¹) ∈ O)
    (M' : ℕ) (hM' : M' ≠ 0) :
    ∃ (β o : ℍ[ℚ, a, b]) (k G : ℕ), o ∈ O ∧ G ≠ 0 ∧ ¬ q ∣ G ∧
      β = 1 + ((2 * M' : ℚ) / (pgen v : ℚ) ^ k) • o ∧
      QuaternionAlgebra.nrd β = 1 ∧
      QuaternionAlgebra.trd β - 2 = -((4 * d₀ ^ 2 * c0 a b (pgen v) q : ℚ) * (M' : ℚ) ^ 2 / (pgen v : ℚ) ^ k) ∧
      QuaternionAlgebra.trd β + 2 = (4 * G : ℚ) / (pgen v : ℚ) ^ k := by
  have hp : (pgen v).Prime := pgen_prime v
  have ha0 : a ≠ 0 := ha.ne
  have hb0 : b ≠ 0 := hb.ne
  set p : ℕ := pgen v with hp_def
  set c₀ : ℕ := c0 a b p q with hc₀_def
  have hc₀ : c₀ ≠ 0 := c0_ne_zero
  set B : ℕ := d₀ ^ 2 * M' ^ 2 * c₀ with hB
  set k : ℕ := B with hk
  have hBlt : B < p ^ k := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hp.two_le _)
  set G : ℕ := p ^ k - B with hG
  have hGB : G + B = p ^ k := Nat.sub_add_cancel hBlt.le
  have hG0 : G ≠ 0 := Nat.sub_ne_zero_of_lt hBlt

  have hℓG : ∀ ℓ ∈ P0 a b p q, ¬ ℓ ∣ G := by
    intro ℓ hℓ hdvd
    have h1 : ℓ ∣ B := Dvd.dvd.mul_left (dvd_c0_of_mem hℓ) _
    have h2 : ℓ ∣ p ^ k := by rw [← hGB]; exact dvd_add hdvd h1
    have h3 : ℓ ∣ p := (prime_of_mem_P0 hℓ).dvd_of_dvd_pow h2
    exact ne_of_mem_P0 hℓ ((Nat.prime_dvd_prime_iff_eq (prime_of_mem_P0 hℓ) hp).1 h3)
  have hqG : ¬ q ∣ G := hℓG q (q_mem_P0 ha0 hb0 hq hqp)
  set c : ℕ := c₀ * G with hc
  have hcpos : 0 < c := Nat.pos_of_ne_zero (mul_ne_zero hc₀ hG0)
  have hcQ : ((c : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hcpos.ne'

  have hloc : ∀ u : HeightOneSpectrum (𝓞 ℚ), ∃ x y z : u.adicCompletion ℚ,
      -(algebraMap ℚ (u.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (u.adicCompletion ℚ) b) * y ^ 2
        + (algebraMap ℚ (u.adicCompletion ℚ) a) * (algebraMap ℚ (u.adicCompletion ℚ) b) * z ^ 2
        = algebraMap ℚ (u.adicCompletion ℚ) (c : ℚ) := by
    intro u
    by_cases huv : u = v
    · subst huv
      refine exists_pureNrd_eq_of_not_forall_isUnit ha0 hb0 u (fun hall => ?_) _
      obtain ⟨x, hx0, hxu⟩ := hv
      exact hxu (hall x hx0)
    · have hℓp : pgen u ≠ p := fun h => huv (pgen_injective h)
      by_cases hP : pgen u ∈ P0 a b p q
      · obtain ⟨m, hm, hℓm⟩ := c0_eq_mul_of_mem hP
        have hval : Valued.v (cst u (c : ℚ)) = WithZero.exp (-1 : ℤ) := by
          rw [valued_algebraMap]
          have e1 : ((c : ℕ) : ℚ) = ((pgen u : ℕ) : ℚ) * ((m * G : ℕ) : ℚ) := by
            rw [hc, hc₀_def, hm]; push_cast; ring
          rw [e1, map_mul, valuation_pgen, valuation_natCast_eq_one_of_not_dvd u ?_, mul_one]
          intro hdvd
          rcases (Nat.Prime.dvd_mul (pgen_prime u)).1 hdvd with h | h
          · exact hℓm h
          · exact hℓG _ hP h
        exact exists_pureNrd_eq_of_valuation_odd ha0 hb0 u c (-1) (by decide) hval
      · have hexc : ¬ pgen u ∣ excNat a b := fun h =>
          hP (mem_P0_of_dvd ha0 hb0 hq (pgen_prime u) hℓp (h.mul_right q))
        refine exists_pureNrd_eq_of_not_forall_isUnit ha0 hb0 u (fun hall => ?_) _
        obtain ⟨x, hx0, hxu⟩ := exists_ne_zero_not_isUnit ha0 hb0 u hexc
        exact hxu (hall x hx0)

  have hR : ∃ x y z : ℝ, -(algebraMap ℚ ℝ a) * x ^ 2 - (algebraMap ℚ ℝ b) * y ^ 2
      + (algebraMap ℚ ℝ a) * (algebraMap ℚ ℝ b) * z ^ 2 = algebraMap ℚ ℝ (c : ℚ) := by
    refine ⟨Real.sqrt ((c : ℝ) / (-(a : ℝ))), 0, 0, ?_⟩
    have ha' : (0 : ℝ) < -(a : ℝ) := by
      have : (a : ℝ) < 0 := by exact_mod_cast ha
      linarith
    have hc' : (0 : ℝ) ≤ (c : ℝ) / (-(a : ℝ)) := div_nonneg (by positivity) ha'.le
    simp only [eq_ratCast]
    rw [Real.sq_sqrt hc']
    push_cast
    field_simp
    ring
  obtain ⟨x, y, z, hxyz⟩ :=
    QuadraticForm.exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real a b ha0 hb0 (c : ℚ) hcQ hloc hR

  set α₁ : ℍ[ℚ, a, b] := ⟨-((d₀ * M' * c₀ : ℕ) : ℚ), x, y, z⟩ with hα₁
  set t₁ : ℤ := -((2 * d₀ * M' * c₀ : ℕ) : ℤ) with ht₁
  set n₁ : ℤ := ((c₀ * p ^ k : ℕ) : ℤ) with hn₁
  have hGBQ : (G : ℚ) + (d₀ : ℚ) ^ 2 * (M' : ℚ) ^ 2 * c₀ = (p : ℚ) ^ k := by
    have := hGB; rw [hB] at this; exact_mod_cast this
  have htrd₁ : QuaternionAlgebra.trd α₁ = (t₁ : ℚ) := by
    rw [hα₁, QuaternionAlgebra.trd_mk, ht₁]; push_cast; ring
  have hnrd₁ : QuaternionAlgebra.nrd α₁ = (n₁ : ℚ) := by
    rw [hα₁, QuaternionAlgebra.nrd_mk, hn₁]
    have hcq : ((c : ℕ) : ℚ) = (c₀ : ℚ) * G := by rw [hc]; push_cast; ring
    push_cast
    linear_combination hxyz + hcq + (c₀ : ℚ) * hGBQ
  obtain ⟨μ, hμ⟩ := hd α₁ ⟨t₁, n₁, htrd₁, hnrd₁⟩
  set o : ℍ[ℚ, a, b] := (d₀ : ℚ) • ((μ : ℍ[ℚ, a, b]) * α₁ * ↑μ⁻¹) with ho
  have htrdo : QuaternionAlgebra.trd o = d₀ * (t₁ : ℚ) := by rw [ho, trd_smul, trd_units_conj, htrd₁]
  have hnrdo : QuaternionAlgebra.nrd o = (d₀ : ℚ) ^ 2 * (n₁ : ℚ) := by rw [ho, nrd_smul, nrd_units_conj, hnrd₁]
  have hpk : ((p : ℚ)) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  set r : ℚ := (2 * M' : ℚ) / (p : ℚ) ^ k with hr
  refine ⟨1 + r • o, o, k, G, hμ, hG0, hqG, rfl, ?_, ?_, ?_⟩
  · rw [nrd_one_add, trd_smul, nrd_smul, htrdo, hnrdo, hr, ht₁, hn₁]
    push_cast
    field_simp
    ring
  · rw [trd_one_add, trd_smul, htrdo, hr, ht₁]
    push_cast
    field_simp
    ring
  · rw [trd_one_add, trd_smul, htrdo, hr, ht₁]
    have hGQ : (G : ℚ) = (p : ℚ) ^ k - (d₀ : ℚ) ^ 2 * (M' : ℚ) ^ 2 * c₀ := by linear_combination hGBQ
    rw [hGQ]
    push_cast
    field_simp
    ring

end Beta

section Padic

variable {a b : ℚ}

def coord (i : Fin 4) (x : ℍ[ℚ, a, b]) : ℚ := (![x.re, x.imI, x.imJ, x.imK] : Fin 4 → ℚ) i

def E (i : Fin 4) : ℍ[ℚ, a, b] :=
  (![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] : Fin 4 → ℍ[ℚ, a, b]) i

theorem coord_add (i : Fin 4) (x y : ℍ[ℚ, a, b]) : coord i (x + y) = coord i x + coord i y := by
  fin_cases i <;> simp [coord]

theorem coord_smul (i : Fin 4) (r : ℚ) (x : ℍ[ℚ, a, b]) : coord i (r • x) = r * coord i x := by
  fin_cases i <;> simp [coord]

theorem padicNorm_coord_one_le (q : ℕ) [Fact q.Prime] (i : Fin 4) :
    padicNorm q (coord i (1 : ℍ[ℚ, a, b])) ≤ 1 := by
  fin_cases i <;> simp [coord]

theorem padicNorm_coord_le (q : ℕ) [Fact q.Prime] {p : ℕ} (hp : p.Prime) (hqp : q ≠ p)
    {N₁ : ℕ} (hN₁ : N₁ ≠ 0) (o : ℍ[ℚ, a, b])
    (ho : ∃ z₀ z₁ z₂ z₃ : ℤ,
      (N₁ : ℚ) * o.re = z₀ ∧ (N₁ : ℚ) * o.imI = z₁ ∧ (N₁ : ℚ) * o.imJ = z₂ ∧ (N₁ : ℚ) * o.imK = z₃)
    (M' k : ℕ) (i : Fin 4) :
    padicNorm q (coord i ((1 : ℍ[ℚ, a, b]) + ((2 * M' : ℚ) / (p : ℚ) ^ k) • o)) ≤ (padicNorm q N₁)⁻¹ := by
  have hq : q.Prime := Fact.out
  obtain ⟨z₀, z₁, z₂, z₃, h₀, h₁, h₂, h₃⟩ := ho
  have hN₁Q : (N₁ : ℚ) ≠ 0 := by exact_mod_cast hN₁
  obtain ⟨z, hz⟩ : ∃ z : ℤ, coord i o = z / N₁ := by
    fin_cases i
    · exact ⟨z₀, by simp [coord]; field_simp; linear_combination h₀⟩
    · exact ⟨z₁, by simp [coord]; field_simp; linear_combination h₁⟩
    · exact ⟨z₂, by simp [coord]; field_simp; linear_combination h₂⟩
    · exact ⟨z₃, by simp [coord]; field_simp; linear_combination h₃⟩
  have hpn : padicNorm q ((p : ℚ) ^ k) = 1 := by
    have : ((p : ℚ)) ^ k = ((p ^ k : ℕ) : ℚ) := by push_cast; ring
    rw [this, padicNorm.nat_eq_one_iff]
    intro hd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hd))
  have hN₁n : 0 < padicNorm q N₁ :=
    lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero hN₁Q))
  have hN₁le : padicNorm q N₁ ≤ 1 := padicNorm.of_nat _
  have hRge : 1 ≤ (padicNorm q N₁)⁻¹ := one_le_inv_iff₀.2 ⟨hN₁n, hN₁le⟩
  rw [coord_add, coord_smul, hz]
  refine le_trans padicNorm.nonarchimedean (max_le (le_trans (padicNorm_coord_one_le q i) hRge) ?_)
  have e1 : (2 * M' : ℚ) / (p : ℚ) ^ k * (z / N₁) = ((2 * M' * z : ℤ) : ℚ) / ((p : ℚ) ^ k) / (N₁ : ℚ) := by
    push_cast; field_simp
  rw [e1, padicNorm.div, padicNorm.div, hpn, div_one, div_eq_mul_inv]
  exact mul_le_of_le_one_left (le_trans (by norm_num) hRge) (padicNorm.of_int _)

theorem padicNorm_mul_sq_div_pow (q : ℕ) [Fact q.Prime] {p : ℕ} (hp : p.Prime) (hqp : q ≠ p)
    (A : ℚ) {M' : ℕ} (hM' : ¬ q ∣ M') (k : ℕ) :
    padicNorm q (A * (M' : ℚ) ^ 2 / (p : ℚ) ^ k) = padicNorm q A := by
  have hq : q.Prime := Fact.out
  have hpn : padicNorm q ((p : ℚ) ^ k) = 1 := by
    have : ((p : ℚ)) ^ k = ((p ^ k : ℕ) : ℚ) := by push_cast; ring
    rw [this, padicNorm.nat_eq_one_iff]
    intro hd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hd))
  have hMn : padicNorm q ((M' : ℚ) ^ 2) = 1 := by
    have : ((M' : ℚ)) ^ 2 = ((M' ^ 2 : ℕ) : ℚ) := by push_cast; ring
    rw [this, padicNorm.nat_eq_one_iff]
    intro hd
    exact hM' (hq.dvd_of_dvd_pow hd)
  rw [padicNorm.div, padicNorm.mul, hpn, hMn, mul_one, div_one]

theorem padicNorm_mul_div_pow (q : ℕ) [Fact q.Prime] {p : ℕ} (hp : p.Prime) (hqp : q ≠ p)
    (A : ℚ) {G : ℕ} (hG : ¬ q ∣ G) (k : ℕ) :
    padicNorm q (A * (G : ℚ) / (p : ℚ) ^ k) = padicNorm q A := by
  have hq : q.Prime := Fact.out
  have hpn : padicNorm q ((p : ℚ) ^ k) = 1 := by
    have : ((p : ℚ)) ^ k = ((p ^ k : ℕ) : ℚ) := by push_cast; ring
    rw [this, padicNorm.nat_eq_one_iff]
    intro hd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hd))
  have hGn : padicNorm q (G : ℚ) = 1 := by rw [padicNorm.nat_eq_one_iff]; exact hG
  rw [padicNorm.div, padicNorm.mul, hpn, hGn, mul_one, div_one]

theorem padicEquiv_cst (w : HeightOneSpectrum (𝓞 ℚ))
    [Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ))] (r : ℚ) :
    Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) w (cst w r)
      = (r : ℚ_[(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ)]) := by
  rw [AlgEquivClass.commutes, eq_ratCast]

theorem mem_integers_iff_norm_le_one (w : HeightOneSpectrum (𝓞 ℚ))
    [Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ))] (u : w.adicCompletion ℚ) :
    u ∈ w.adicCompletionIntegers ℚ ↔
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) w u‖ ≤ 1 := by
  have hbij := Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn (R := 𝓞 ℚ) w
  set e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) w
  constructor
  · intro hu
    exact (PadicInt.mem_subring_iff _).1 (hbij.1 hu)
  · intro hu
    obtain ⟨u', hu', he⟩ := hbij.2.2 ((PadicInt.mem_subring_iff _).2 hu)
    exact (e.injective he) ▸ hu'

end Padic

section Main

variable {a b : ℚ} {O : Submodule ℤ ℍ[ℚ, a, b]}

def Mseq (q : ℕ) (n : ℕ) : ℕ := ordCompl[q] (n + 1).factorial

theorem Mseq_ne_zero (q n : ℕ) : Mseq q n ≠ 0 :=
  (Nat.ordCompl_pos q (Nat.factorial_ne_zero _)).ne'

theorem not_dvd_Mseq {q : ℕ} (hq : q.Prime) (n : ℕ) : ¬ q ∣ Mseq q n :=
  Nat.not_dvd_ordCompl hq (Nat.factorial_ne_zero _)

theorem dvd_Mseq {q : ℕ} (hq : q.Prime) {M₁ n : ℕ} (hM₁ : M₁ ≠ 0) (hqM₁ : ¬ q ∣ M₁) (hle : M₁ ≤ n + 1) :
    M₁ ∣ Mseq q n := by
  have h1 : M₁ ∣ (n + 1).factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hM₁) hle
  rw [← Nat.ordProj_mul_ordCompl_eq_self (n + 1).factorial q] at h1
  have hcop : Nat.Coprime M₁ (q ^ ((n + 1).factorial.factorization q)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hq).2 hqM₁))
  exact hcop.dvd_of_dvd_mul_left h1

theorem main (ha : a < 0) (hb : b < 0) (hO : QuaternionAlgebra.IsOrder O)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ∃ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v) :
    ∃ s : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, s ≠ 1 ∧ s ≠ -1 ∧
      (∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ → QuaternionAlgebra.nrd (φ s) = 1) ∧
      ∀ M : ℕ, M ≠ 0 →
        ∃ β : ℍ[ℚ, a, b], QuaternionAlgebra.nrd β = 1 ∧
          (∀ w' : HeightOneSpectrum (𝓞 ℚ), w' ≠ v → w' ≠ w →
            ∃ z ∈ Submodule.localBox O w',
              β ⊗ₜ[ℚ] (1 : w'.adicCompletion ℚ) = 1 + (M : ℚ) • z) ∧
          (∃ z ∈ Submodule.localBox O w,
              β ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) = s + (M : ℚ) • z) := by
  classical

  set p : ℕ := pgen v with hp_def
  have hp : p.Prime := pgen_prime v
  haveI hqF : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ)) :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator w⟩
  set q : ℕ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ) with hq_def
  have hqg : pgen w = q := rfl
  have hq : q.Prime := hqF.out
  have hqp : q ≠ p := fun h => hw (pgen_injective (hqg.trans h))
  set K := w.adicCompletion ℚ

  obtain ⟨d₀, hd₀, hd⟩ :=
    QuaternionAlgebra.IsOrder.exists_forall_exists_units_smul_conj_mem_of_int_trd_nrd ha hb hO
  obtain ⟨N₁, hN₁, hden⟩ := exists_den hO
  obtain ⟨N₂, hN₂, hbasis⟩ := exists_basis_smul_mem hO
  set c₀ : ℕ := c0 a b p q with hc₀_def
  have hc₀ : c₀ ≠ 0 := c0_ne_zero

  have hex := fun n : ℕ => exists_beta ha hb hO v hv q hq hqp hd₀ hd (Mseq q n) (Mseq_ne_zero q n)
  choose β o k G ho hG0 hqG hβ hnrd htrm htrp using hex

  let y : ℕ → (Fin 4 → ℚ_[q]) := fun n i => ((coord i (β n) : ℚ) : ℚ_[q])
  have hy : ∀ n i, y n i = ((coord i (β n) : ℚ) : ℚ_[q]) := fun n i => rfl

  set R : ℝ := (((padicNorm q N₁)⁻¹ : ℚ) : ℝ) with hR
  have hR0 : 0 ≤ R := by
    rw [hR]; exact_mod_cast inv_nonneg.2 (padicNorm.nonneg _)
  have hyR : ∀ n, y n ∈ Metric.closedBall (0 : Fin 4 → ℚ_[q]) R := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR0]
    intro i
    rw [hy, Padic.eq_padicNorm, hR]
    have := padicNorm_coord_le q hp hqp hN₁ (o n) (hden _ (ho n)) (Mseq q n) (k n) i
    rw [← hβ n] at this
    exact_mod_cast this
  obtain ⟨alim, -, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hyR

  set e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) w with he_def
  have he : ∀ r : ℚ, e (cst w r) = (r : ℚ_[q]) := fun r => padicEquiv_cst w r
  have hes : ∀ r : ℚ, e.symm (r : ℚ_[q]) = cst w r := fun r => by
    rw [← he, e.symm_apply_apply]
  obtain ⟨φ, hφ⟩ := exists_isCoord a b w
  set xlim : ℍ[K, cst w a, cst w b] := ⟨e.symm (alim 0), e.symm (alim 1), e.symm (alim 2), e.symm (alim 3)⟩
    with hxlim
  set s : ℍ[ℚ, a, b] ⊗[ℚ] K := φ.symm xlim with hs_def
  have hφs : φ s = xlim := by rw [hs_def, RingEquiv.apply_symm_apply]

  have hFc : Continuous fun t : Fin 4 → ℚ_[q] =>
      t 0 ^ 2 - (a : ℚ_[q]) * t 1 ^ 2 - (b : ℚ_[q]) * t 2 ^ 2 + (a : ℚ_[q]) * (b : ℚ_[q]) * t 3 ^ 2 := by
    fun_prop
  have hF := (hFc.tendsto alim).comp hlim
  have hF1 : ∀ n, (fun t : Fin 4 → ℚ_[q] =>
      t 0 ^ 2 - (a : ℚ_[q]) * t 1 ^ 2 - (b : ℚ_[q]) * t 2 ^ 2 + (a : ℚ_[q]) * (b : ℚ_[q]) * t 3 ^ 2) (y (ψ n)) = 1 := by
    intro n
    have h := congrArg (fun t : ℚ => (t : ℚ_[q])) (hnrd (ψ n))
    simp only [QuaternionAlgebra.nrd, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_one] at h
    simp only [hy, coord]
    exact h
  have hnrdlim : alim 0 ^ 2 - (a : ℚ_[q]) * alim 1 ^ 2 - (b : ℚ_[q]) * alim 2 ^ 2
      + (a : ℚ_[q]) * (b : ℚ_[q]) * alim 3 ^ 2 = 1 := by
    refine tendsto_nhds_unique hF ?_
    have : ((fun t : Fin 4 → ℚ_[q] =>
        t 0 ^ 2 - (a : ℚ_[q]) * t 1 ^ 2 - (b : ℚ_[q]) * t 2 ^ 2 + (a : ℚ_[q]) * (b : ℚ_[q]) * t 3 ^ 2) ∘ (y ∘ ψ))
        = fun _ => 1 := by
      funext n; exact hF1 n
    rw [this]
    exact tendsto_const_nhds
  have hnrdx : QuaternionAlgebra.nrd xlim = 1 := by
    apply e.injective
    rw [map_one, hxlim, QuaternionAlgebra.nrd_mk]
    simp only [map_add, map_sub, map_mul, map_pow, he, hes, e.apply_symm_apply] at hnrdlim ⊢
    convert hnrdlim using 2 <;> simp [he]
  have hsnrd : ∀ φ' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
      IsCoord a b w φ' → QuaternionAlgebra.nrd (φ' s) = 1 := by
    intro φ' hφ'
    rw [hφ.eq hφ' s, hφs, hnrdx]

  set ρ₁ : ℚ := padicNorm q ((4 * d₀ ^ 2 * c₀ : ℕ) : ℚ) with hρ₁
  set ρ₂ : ℚ := padicNorm q (4 : ℚ) with hρ₂
  have hρ₁0 : ρ₁ ≠ 0 := padicNorm.nonzero (by positivity)
  have hρ₂0 : ρ₂ ≠ 0 := padicNorm.nonzero (by norm_num)
  have htr1 : ∀ n, ‖2 * y n 0 - 2‖ = (ρ₁ : ℝ) := by
    intro n
    have e1 : (2 : ℚ_[q]) * y n 0 - 2 = ((QuaternionAlgebra.trd (β n) - 2 : ℚ) : ℚ_[q]) := by
      simp only [hy, coord, QuaternionAlgebra.trd]
      push_cast
      simp
    rw [e1, Padic.eq_padicNorm, htrm n, padicNorm.neg,
      padicNorm_mul_sq_div_pow q hp hqp _ (not_dvd_Mseq hq n) (k n), hρ₁, hc₀_def, hp_def]
    push_cast
    ring_nf
  have htr2 : ∀ n, ‖2 * y n 0 + 2‖ = (ρ₂ : ℝ) := by
    intro n
    have e1 : (2 : ℚ_[q]) * y n 0 + 2 = ((QuaternionAlgebra.trd (β n) + 2 : ℚ) : ℚ_[q]) := by
      simp only [hy, coord, QuaternionAlgebra.trd]
      push_cast
      simp
    rw [e1, Padic.eq_padicNorm, htrp n, padicNorm_mul_div_pow q hp hqp _ (hqG n) (k n), hρ₂]
  have hlim1 : ‖2 * alim 0 - 2‖ = (ρ₁ : ℝ) := by
    have hc : Continuous fun t : Fin 4 → ℚ_[q] => ‖2 * t 0 - 2‖ := by fun_prop
    have h1 := (hc.tendsto alim).comp hlim
    have h2 : ((fun t : Fin 4 → ℚ_[q] => ‖2 * t 0 - 2‖) ∘ (y ∘ ψ)) = fun _ => (ρ₁ : ℝ) := by
      funext n; exact htr1 (ψ n)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hlim2 : ‖2 * alim 0 + 2‖ = (ρ₂ : ℝ) := by
    have hc : Continuous fun t : Fin 4 → ℚ_[q] => ‖2 * t 0 + 2‖ := by fun_prop
    have h1 := (hc.tendsto alim).comp hlim
    have h2 : ((fun t : Fin 4 → ℚ_[q] => ‖2 * t 0 + 2‖) ∘ (y ∘ ψ)) = fun _ => (ρ₂ : ℝ) := by
      funext n; exact htr2 (ψ n)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have ha0ne1 : alim 0 ≠ 1 := by
    intro h
    rw [h, mul_one, sub_self, norm_zero] at hlim1
    exact hρ₁0 (by exact_mod_cast hlim1.symm)
  have ha0ne2 : alim 0 ≠ -1 := by
    intro h
    rw [h, mul_neg, mul_one, neg_add_cancel, norm_zero] at hlim2
    exact hρ₂0 (by exact_mod_cast hlim2.symm)
  have hs1 : s ≠ 1 := by
    intro h
    have h1 : xlim = 1 := by rw [← hφs, h, map_one]
    have h2 : e.symm (alim 0) = 1 := by
      have := congrArg QuaternionAlgebra.re h1
      simpa [hxlim] using this
    exact ha0ne1 (by simpa using congrArg e h2)
  have hs2 : s ≠ -1 := by
    intro h
    have h1 : xlim = -1 := by rw [← hφs, h, map_neg, map_one]
    have h2 : e.symm (alim 0) = -1 := by
      have := congrArg QuaternionAlgebra.re h1
      simpa [hxlim] using this
    exact ha0ne2 (by simpa using congrArg e h2)
  refine ⟨s, hs1, hs2, hsnrd, fun M hM => ?_⟩

  set j : ℕ := M.factorization q with hj
  set M₁ : ℕ := ordCompl[q] M with hM₁
  have hMM : q ^ j * M₁ = M := Nat.ordProj_mul_ordCompl_eq_self M q
  have hM₁0 : M₁ ≠ 0 := (Nat.ordCompl_pos q hM).ne'
  have hqM₁ : ¬ q ∣ M₁ := Nat.not_dvd_ordCompl hq hM
  set ε : ℝ := ‖(((M * N₂ : ℕ) : ℚ) : ℚ_[q])‖ with hε
  have hMN₂ : ((M * N₂ : ℕ) : ℚ) ≠ 0 := by exact_mod_cast mul_ne_zero hM hN₂
  have hMN₂' : (((M * N₂ : ℕ) : ℚ) : ℚ_[q]) ≠ 0 := by exact_mod_cast hMN₂
  have hε0 : 0 < ε := norm_pos_iff.2 hMN₂'
  obtain ⟨n₀, hn₀⟩ := (Metric.tendsto_atTop.1 hlim) ε hε0
  set n : ℕ := max n₀ M₁ with hn
  set m : ℕ := ψ n with hm
  have hdist : dist (y m) alim < ε := hn₀ n (le_max_left _ _)
  have hM₁dvd : M₁ ∣ Mseq q m := by
    refine dvd_Mseq hq hM₁0 hqM₁ ?_
    calc M₁ ≤ n := le_max_right _ _
      _ ≤ ψ n := hψ.le_apply
      _ ≤ ψ n + 1 := Nat.le_succ _
  have hpk : ((p : ℚ)) ^ (k m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  refine ⟨β m, hnrd m, fun w' hw'v hw'w => ?_, ?_⟩
  ·
    obtain ⟨L, hL⟩ := hM₁dvd
    have hw'p : pgen w' ≠ p := fun h => hw'v (pgen_injective h)
    have hw'q : pgen w' ≠ q := fun h => hw'w (pgen_injective (h.trans hqg.symm))
    have hndvd : ¬ pgen w' ∣ p ^ (k m) * q ^ j := by
      intro hd
      rcases (Nat.Prime.dvd_mul (pgen_prime w')).1 hd with h | h
      · exact hw'p ((Nat.prime_dvd_prime_iff_eq (pgen_prime w') hp).1 ((pgen_prime w').dvd_of_dvd_pow h))
      · exact hw'q ((Nat.prime_dvd_prime_iff_eq (pgen_prime w') hq).1 ((pgen_prime w').dvd_of_dvd_pow h))
    set t : ℚ := ((2 * L : ℤ) : ℚ) / ((p ^ (k m) * q ^ j : ℕ) : ℚ) with ht
    have htint : cst w' t ∈ w'.adicCompletionIntegers ℚ := intCast_div_natCast_mem_integers w' _ hndvd
    have hrt : (2 * (Mseq q m : ℕ) : ℚ) / (p : ℚ) ^ (k m) = (M : ℚ) * t := by
      rw [ht, hL, ← hMM]
      have hq0 : ((q : ℚ)) ^ j ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne_zero)
      push_cast
      field_simp
    refine ⟨(o m) ⊗ₜ[ℚ] cst w' t, tmul_mem_localBox (ho m) w' htint, ?_⟩
    rw [hβ m, TensorProduct.add_tmul, hrt, mul_smul, ← Algebra.TensorProduct.one_def,
      ← TensorProduct.smul_tmul', TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  ·
    let δ : Fin 4 → K := fun i => cst w (coord i (β m)) - e.symm (alim i)
    let u : Fin 4 → K := fun i => cst w (((M * N₂ : ℕ) : ℚ)⁻¹) * δ i
    have hu : ∀ i, u i ∈ w.adicCompletionIntegers ℚ := by
      intro i
      rw [mem_integers_iff_norm_le_one]
      have e1 : e (u i) = ((((M * N₂ : ℕ) : ℚ) : ℚ_[q]))⁻¹ * (y m i - alim i) := by
        simp only [u, δ, map_mul, map_sub, he, hy, e.apply_symm_apply, Rat.cast_inv]
      rw [← he_def, e1, norm_mul, norm_inv, ← hε]
      have h2 : ‖y m i - alim i‖ ≤ dist (y m) alim := by
        rw [← dist_eq_norm]; exact dist_le_pi_dist _ _ i
      have h3 : ε⁻¹ * ‖y m i - alim i‖ ≤ ε⁻¹ * ε :=
        mul_le_mul_of_nonneg_left (le_trans h2 hdist.le) (inv_nonneg.2 hε0.le)
      rw [inv_mul_cancel₀ hε0.ne'] at h3
      exact h3
    have hδ : ∀ i, δ i = cst w ((M * N₂ : ℕ) : ℚ) * u i := by
      intro i
      simp only [u]
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hMN₂, map_one, one_mul]
    set z : ℍ[ℚ, a, b] ⊗[ℚ] K := ∑ i : Fin 4, ((N₂ : ℚ) • E i) ⊗ₜ[ℚ] u i with hz
    have hEO : ∀ i : Fin 4, (N₂ : ℚ) • (E i : ℍ[ℚ, a, b]) ∈ O := by
      intro i
      fin_cases i
      · simpa [E] using hbasis 1 0 0 0
      · simpa [E] using hbasis 0 1 0 0
      · simpa [E] using hbasis 0 0 1 0
      · simpa [E] using hbasis 0 0 0 1
    have hzmem : z ∈ Submodule.localBox O w :=
      AddSubgroup.sum_mem _ fun i _ => tmul_mem_localBox (hEO i) w (hu i)
    refine ⟨z, hzmem, ?_⟩

    have hMz : (M : ℚ) • z = ∑ i : Fin 4, (E i : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] δ i := by
      rw [hz, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.smul_tmul', smul_smul, TensorProduct.smul_tmul, Algebra.smul_def, hδ i]
      congr 2
      push_cast; ring

    have hφdiff : φ (β m ⊗ₜ[ℚ] (1 : K) - s) = φ (∑ i : Fin 4, (E i : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] δ i) := by
      rw [map_sub, hφ.tmul_one, hφs, map_sum]
      simp only [hφ.tmul]
      rw [Fin.sum_univ_four]
      ext <;> simp [hatQ, hxlim, δ, E, coord]
    have hdiff : β m ⊗ₜ[ℚ] (1 : K) - s = (M : ℚ) • z := by
      rw [hMz]; exact φ.injective hφdiff
    rw [← hdiff]
    abel

end Main

end KLCC

end

open scoped TensorProduct Quaternion in
open IsDedekindDomain NumberField in
theorem solution
    {a b : ℚ} (ha : a < 0) (hb : b < 0)
    {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ∃ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v) :
    ∃ s : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, s ≠ 1 ∧ s ≠ -1 ∧
      (∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
          φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
            algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
              ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a,
                algebraMap ℚ (w.adicCompletion ℚ) b])) →
        QuaternionAlgebra.nrd (φ s) = 1) ∧
      ∀ M : ℕ, M ≠ 0 →
        ∃ β : ℍ[ℚ, a, b], QuaternionAlgebra.nrd β = 1 ∧
          (∀ w' : HeightOneSpectrum (𝓞 ℚ), w' ≠ v → w' ≠ w →
            ∃ z ∈ Submodule.localBox O w',
              β ⊗ₜ[ℚ] (1 : w'.adicCompletion ℚ) = 1 + (M : ℚ) • z) ∧
          (∃ z ∈ Submodule.localBox O w,
              β ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) = s + (M : ℚ) • z) :=
  KLCC.main ha hb hO v hv w hw

end S_QuaternionAlgebra_IsOrder_exists_ne_neg_one_forall_exists_nrd_eq_one_tmul_eq_add_smul
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_exists_ne_neg_one_forall_exists_nrd_eq_one_tmul_eq_add_smul (solution)
