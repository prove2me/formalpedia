-- Prove2me | solution 1 for ValuationSubring.isCompact_ratClosure_inter_closedBall_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/2413cb65-4c5c-5bd2-9825-1205f294b48a

import Mathlib
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_isCompact_ratClosure_inter_closedBall_of_liesOverPrime

set_option autoImplicit false

p2m_open "ValuationSubring P2MW.S_ValuationSubring_isCompact_ratClosure_inter_closedBall_of_liesOverPrime.ValuationSubring"

namespace ValuationSubring
p2m_export "ValuationSubring" "valuation_surjective ext mem_nonunits_iff ValueGroup valuation_le_one_iff valuation ratClosure isClosed_ratClosure LiesOverPrime mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one"
namespace F0kit
p2m_open "ValuationSubring"

theorem exists_nat_sub_mul_den_eq {r : ℕ} (hr : 0 < r) (q : ℚ) (hcop : (q.den).Coprime r) (N : ℕ) :
    ∃ a : ℕ, a < r ^ N ∧ ∃ w : ℤ, ((q - a) * q.den : ℚ) = (r : ℚ) ^ N * w := by
  have hcopN : (q.den).Coprime (r ^ N) := Nat.Coprime.pow_right N hcop
  obtain ⟨y, hy⟩ := Int.mod_coprime hcopN

  have hRpos : (0 : ℤ) < (r : ℤ) ^ N := by positivity
  set a : ℤ := (q.num * y) % ((r : ℤ) ^ N) with ha
  have ha0 : 0 ≤ a := Int.emod_nonneg _ hRpos.ne'
  have haR : a < (r : ℤ) ^ N := Int.emod_lt_of_pos _ hRpos
  have hdvd : ((r : ℤ) ^ N) ∣ q.num - a * q.den := by

    have h1 : a ≡ q.num * y [ZMOD (r : ℤ) ^ N] := Int.mod_modEq _ _
    have h2 : (q.den : ℤ) * y ≡ 1 [ZMOD (r : ℤ) ^ N] := by exact_mod_cast hy
    have h3 : a * q.den ≡ q.num [ZMOD (r : ℤ) ^ N] := by
      calc a * q.den ≡ q.num * y * q.den [ZMOD (r : ℤ) ^ N] := h1.mul_right _
        _ = q.num * (q.den * y) := by ring
        _ ≡ q.num * 1 [ZMOD (r : ℤ) ^ N] := h2.mul_left _
        _ = q.num := by ring
    exact (Int.modEq_iff_dvd.mp h3)
  obtain ⟨w, hw⟩ := hdvd
  refine ⟨a.toNat, ?_, w, ?_⟩
  · have : (a.toNat : ℤ) < (r : ℤ) ^ N := by rw [Int.toNat_of_nonneg ha0]; exact haR
    exact_mod_cast this
  · have hq : (q : ℚ) = q.num / q.den := (Rat.num_div_den q).symm
    have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    have haa : ((a.toNat : ℕ) : ℚ) = (a : ℚ) := by exact_mod_cast Int.toNat_of_nonneg ha0
    have hw' : ((q.num - a * q.den : ℤ) : ℚ) = (((r : ℤ) ^ N * w : ℤ) : ℚ) := by exact_mod_cast hw
    push_cast at hw'
    rw [haa, ← hw', sub_mul, Rat.mul_den_eq_num]

section B

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ}

theorem v_coe (x : AlgebraicClosure ℚ) : Valued.v (x : A.valuation.Completion) = A.valuation x := by
  rw [show (x : A.valuation.Completion) =
      (((WithVal.equiv A.valuation).symm x : WithVal A.valuation) : A.valuation.Completion) from rfl,
    Valued.valuedCompletion_apply]
  rfl

noncomputable def coeHom : AlgebraicClosure ℚ →+* A.valuation.Completion :=
  (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* A.valuation.Completion).comp
    (WithVal.equiv A.valuation).symm.toRingHom

theorem coeHom_apply (x : AlgebraicClosure ℚ) : coeHom A x = (x : A.valuation.Completion) := rfl

theorem coe_ratCast' (q : ℚ) : ((q : AlgebraicClosure ℚ) : A.valuation.Completion) = (q : A.valuation.Completion) := by
  rw [← coeHom_apply, map_ratCast]

theorem v_ratCast (q : ℚ) : Valued.v (q : A.valuation.Completion) = A.valuation (q : AlgebraicClosure ℚ) := by
  rw [← coe_ratCast', v_coe]

theorem v_natCast (n : ℕ) : Valued.v (n : A.valuation.Completion) = A.valuation (n : AlgebraicClosure ℚ) := by
  rw [← Rat.cast_natCast, v_ratCast, Rat.cast_natCast]

theorem vA_natCast_le_one (n : ℕ) : A.valuation (n : AlgebraicClosure ℚ) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (natCast_mem A n)

theorem vA_intCast_le_one (n : ℤ) : A.valuation (n : AlgebraicClosure ℚ) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (intCast_mem A n)

theorem vA_natCast_eq_one_of_coprime (hA : A.LiesOverPrime r) {d : ℕ} (hd : d.Coprime r) :
    A.valuation (d : AlgebraicClosure ℚ) = 1 := by
  refine le_antisymm (vA_natCast_le_one A d) (not_lt.mp fun hlt => ?_)
  have hAr : A.valuation (r : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA
  obtain ⟨u, t, hut⟩ := Nat.isCoprime_iff_coprime.mpr hd

  have h1 : (u : AlgebraicClosure ℚ) * d + t * r = 1 := by exact_mod_cast hut
  have hv : A.valuation ((u : AlgebraicClosure ℚ) * d + t * r) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (vA_intCast_le_one A u) zero_le' hlt
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (vA_intCast_le_one A t) zero_le' hAr
  rw [h1, map_one] at hv
  exact lt_irrefl _ hv

theorem den_coprime_of_vA_le_one (hr : r.Prime) (hA : A.LiesOverPrime r) {q : ℚ}
    (hq : A.valuation (q : AlgebraicClosure ℚ) ≤ 1) : (q.den).Coprime r := by
  rw [Nat.Coprime, Nat.gcd_comm, ← Nat.Coprime, hr.coprime_iff_not_dvd]
  intro hdvd
  have hAr : A.valuation (r : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA
  obtain ⟨k, hk⟩ := hdvd
  have hden : A.valuation (q.den : AlgebraicClosure ℚ) < 1 := by
    rw [hk, Nat.cast_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le' hAr (vA_natCast_le_one A k)

  have hnum : (q.num.natAbs).Coprime r :=
    Nat.Coprime.coprime_dvd_right ⟨k, hk⟩ q.reduced
  have hvnum : A.valuation (q.num : AlgebraicClosure ℚ) = 1 := by
    have h := vA_natCast_eq_one_of_coprime A hA hnum
    have hcast : ((q.num.natAbs : ℕ) : AlgebraicClosure ℚ) = ((q.num.natAbs : ℤ) : AlgebraicClosure ℚ) := (Int.cast_natCast _).symm
    rcases Int.natAbs_eq q.num with hn | hn
    · rw [hn, ← hcast]; exact h
    · rw [hn, Int.cast_neg, Valuation.map_neg, ← hcast]; exact h
  have hden0 : A.valuation (q.den : AlgebraicClosure ℚ) ≠ 0 :=
    (map_ne_zero _).mpr (by exact_mod_cast q.den_nz)
  have hq' : A.valuation (q : AlgebraicClosure ℚ) = (A.valuation (q.den : AlgebraicClosure ℚ))⁻¹ := by
    rw [Rat.cast_def, map_div₀, hvnum, one_div]
  rw [hq'] at hq
  have : 1 ≤ A.valuation (q.den : AlgebraicClosure ℚ) := by
    rwa [inv_le_one₀ (zero_lt_iff.mpr hden0)] at hq
  exact absurd hden (not_lt.mpr this)

end B

section N

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ}

theorem vA_ratCast_mul (x y : ℚ) :
    A.valuation ((x * y : ℚ) : AlgebraicClosure ℚ) = A.valuation (x : AlgebraicClosure ℚ) * A.valuation (y : AlgebraicClosure ℚ) := by
  rw [Rat.cast_mul, map_mul]

theorem net (hr : r.Prime) (hA : A.LiesOverPrime r) (m n : ℕ) (q : ℚ)
    (hq : A.valuation (q : AlgebraicClosure ℚ) ≤ ((A.valuation (r : AlgebraicClosure ℚ))⁻¹) ^ m) :
    ∃ a : ℕ, a < r ^ (n + m) ∧
      A.valuation (((q - (a : ℚ) / (r : ℚ) ^ m : ℚ)) : AlgebraicClosure ℚ) ≤ A.valuation (r : AlgebraicClosure ℚ) ^ n := by
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hvr0 : A.valuation (r : AlgebraicClosure ℚ) ≠ 0 := (map_ne_zero _).mpr (by exact_mod_cast hr.ne_zero)

  set q' : ℚ := q * (r : ℚ) ^ m with hq'def
  have hq' : A.valuation (q' : AlgebraicClosure ℚ) ≤ 1 := by
    rw [hq'def, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, map_mul, map_pow]
    calc A.valuation (q : AlgebraicClosure ℚ) * A.valuation (r : AlgebraicClosure ℚ) ^ m
        ≤ ((A.valuation (r : AlgebraicClosure ℚ))⁻¹) ^ m * A.valuation (r : AlgebraicClosure ℚ) ^ m :=
          mul_le_mul_left hq _
      _ = 1 := by rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hvr0)]
  have hcop : (q'.den).Coprime r := den_coprime_of_vA_le_one A hr hA hq'
  obtain ⟨a, ha, w, hw⟩ := exists_nat_sub_mul_den_eq hr.pos q' hcop (n + m)
  refine ⟨a, ha, ?_⟩

  have hden : (q'.den : ℚ) ≠ 0 := by exact_mod_cast q'.den_nz
  have key : (q - (a : ℚ) / (r : ℚ) ^ m : ℚ) = (r : ℚ) ^ n * w / q'.den := by
    have h1 : (q - (a : ℚ) / (r : ℚ) ^ m : ℚ) = (q' - a) / (r : ℚ) ^ m := by
      rw [hq'def]; field_simp
    have h2 : (q' - a : ℚ) = (r : ℚ) ^ (n + m) * w / q'.den := by
      rw [eq_div_iff hden]; exact hw
    rw [h1, h2, pow_add]
    field_simp
  rw [key, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_intCast, Rat.cast_natCast,
    map_div₀, map_mul, map_pow, vA_natCast_eq_one_of_coprime A hA hcop, div_one]
  exact mul_le_of_le_one_right zero_le' (vA_intCast_le_one A w)

end N

end ValuationSubring.F0kit

open ValuationSubring.F0kit in

theorem solution
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∀ ρ : A.ValueGroup, IsCompact {x : A.valuation.Completion |
      x ∈ Set.range (algebraMap (↥(ratClosure A)) A.valuation.Completion) ∧ Valued.v x ≤ ρ} := by
  classical
  have hrp : r.Prime := Fact.out
  intro ρ

  let C := A.valuation.Completion
  have hrange : ∀ x : A.valuation.Completion,
      x ∈ Set.range (algebraMap (↥(ratClosure A)) A.valuation.Completion) ↔ x ∈ ratClosure A :=
    fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

  have hball_closed : ∀ k : A.valuation.Completion, IsClosed {x : A.valuation.Completion | Valued.v x ≤ Valued.v k} := by
    intro k
    have : {x : A.valuation.Completion | Valued.v x ≤ Valued.v k} =
        {x | Valued.v.restrict x ≤ Valued.v.restrict k} := by
      ext x; simp only [Set.mem_setOf_eq, Valuation.restrict_le_iff]
    rw [this]; exact Valued.isClosed_closedBall _ _
  have hball_open : ∀ k : A.valuation.Completion, k ≠ 0 → IsOpen {x : A.valuation.Completion | Valued.v x ≤ Valued.v k} := by
    intro k hk
    have : {x : A.valuation.Completion | Valued.v x ≤ Valued.v k} =
        {x | Valued.v.restrict x ≤ Valued.v.restrict k} := by
      ext x; simp only [Set.mem_setOf_eq, Valuation.restrict_le_iff]
    rw [this]
    exact (Valued.isClopen_closedBall _ ((map_ne_zero _).mpr hk)).isOpen

  rcases eq_or_ne ρ 0 with rfl | hρ
  · apply Set.Finite.isCompact
    refine (Set.finite_singleton (0 : A.valuation.Completion)).subset ?_
    rintro x ⟨-, hx⟩
    exact (map_eq_zero _).mp (le_antisymm hx zero_le')

  have hAr : A.valuation (r : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA
  have hvr : Valued.v ((r : A.valuation.Completion)) = A.valuation (r : AlgebraicClosure ℚ) := v_natCast A r
  have hvr0 : Valued.v ((r : A.valuation.Completion)) ≠ 0 := by
    rw [hvr]; exact (map_ne_zero _).mpr (by exact_mod_cast hrp.ne_zero)
  have hrC0 : (r : A.valuation.Completion) ≠ 0 := fun h => hvr0 (by rw [h, map_zero])
  have hvr1 : Valued.v ((r : A.valuation.Completion)) < 1 := by rw [hvr]; exact hAr
  have hvrpos : 0 < Valued.v ((r : A.valuation.Completion)) := zero_lt_iff.mpr hvr0

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by convert AlgebraicClosure.isAlgebraic ℚ; rfl; rfl
  haveI : MulArchimedean A.ValueGroup :=
    ValuationSubring.mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one A hrp hAr
  have hrank : ∀ γ : A.ValueGroup, γ ≠ 0 → ∃ n : ℕ, Valued.v ((r : A.valuation.Completion)) ^ n ≤ γ := by
    intro γ hγ
    obtain ⟨n, hn⟩ := MulArchimedean.arch γ⁻¹ ((one_lt_inv₀ hvrpos).mpr hvr1)
    refine ⟨n, ?_⟩
    rw [inv_pow] at hn
    exact (inv_le_inv₀ (zero_lt_iff.mpr hγ) (pow_pos hvrpos n)).mp hn

  obtain ⟨m, hm⟩ := MulArchimedean.arch ρ ((one_lt_inv₀ hvrpos).mpr hvr1)
  let c : A.valuation.Completion := ((r : A.valuation.Completion)⁻¹) ^ m
  have hvc : Valued.v c = ((Valued.v ((r : A.valuation.Completion)))⁻¹) ^ m := by
    simp only [c, map_pow, map_inv₀]
  have hc0 : c ≠ 0 := pow_ne_zero _ (inv_ne_zero hrC0)

  let S : Set A.valuation.Completion := ratClosure A
  let Bc : Set A.valuation.Completion := {x | Valued.v x ≤ Valued.v c}
  have hK : IsCompact (S ∩ Bc) := by
    rw [isCompact_iff_totallyBounded_isComplete]
    refine ⟨?_, ((isClosed_ratClosure A).inter (hball_closed c)).isComplete⟩

    let T : Set A.valuation.Completion := Set.range (Rat.cast : ℚ → A.valuation.Completion)
    have hbotT : ((⊥ : Subfield A.valuation.Completion) : Set A.valuation.Completion) ⊆ T := by
      intro x hx
      have : (⊥ : Subfield A.valuation.Completion) ≤ (Rat.castHom A.valuation.Completion).fieldRange := bot_le
      obtain ⟨q, hq⟩ := RingHom.mem_fieldRange.mp (this hx)
      exact ⟨q, by rw [← hq]; rfl⟩
    have hsub : S ∩ Bc ⊆ closure (Bc ∩ T) := by
      intro x ⟨hxS, hxB⟩
      have hx' : x ∈ Bc ∩ closure ((⊥ : Subfield A.valuation.Completion) : Set A.valuation.Completion) := ⟨hxB, hxS⟩
      exact closure_mono (Set.inter_subset_inter_right _ hbotT) ((hball_open c hc0).inter_closure hx')
    refine (TotallyBounded.closure ?_).subset hsub

    rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
    intro U hU
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU

    obtain ⟨d₁, d₂, hd₁, hd₂, hdγ⟩ := Valuation.exists_div_eq_of_unit (Valued.v (R := A.valuation.Completion)) γ
    have hd₂0 : d₂ ≠ 0 := fun h => by rw [h, map_zero] at hd₂; exact lt_irrefl _ hd₂
    have hd₁0 : d₁ ≠ 0 := fun h => by rw [h, map_zero] at hd₁; exact lt_irrefl _ hd₁
    let d : A.valuation.Completion := d₁ / d₂
    have hd0 : Valued.v d ≠ 0 := (map_ne_zero _).mpr (div_ne_zero hd₁0 hd₂0)
    obtain ⟨n, hn⟩ := hrank (Valued.v d) hd0

    have hU' : ∀ z : A.valuation.Completion, Valued.v z ≤ Valued.v ((r : A.valuation.Completion)) ^ (n + 1) → z ∈ U := by
      intro z hz
      apply hγ
      rw [Set.mem_setOf_eq, ← hdγ, ← map_div₀]
      have hlt : Valued.v z < Valued.v d := by
        refine lt_of_le_of_lt hz (lt_of_lt_of_le ?_ hn)
        rw [pow_succ]
        exact mul_lt_of_lt_one_right (pow_pos hvrpos n) hvr1
      exact lt_of_not_ge fun h => (not_le.mpr hlt) ((Valuation.restrict_le_iff _).mp h)

    refine ⟨((Finset.range (r ^ (n + 1 + m))).image
        (fun a : ℕ => (((a : ℚ) / (r : ℚ) ^ m : ℚ) : A.valuation.Completion)) : Set A.valuation.Completion),
      Finset.finite_toSet _, ?_⟩
    rintro z ⟨hzB, ⟨q, rfl⟩⟩
    have hq : A.valuation (q : AlgebraicClosure ℚ) ≤ ((A.valuation (r : AlgebraicClosure ℚ))⁻¹) ^ m := by
      rw [← v_ratCast, ← hvr, ← hvc]; exact hzB
    obtain ⟨a, ha, hva⟩ := net A hrp hA m (n + 1) q hq
    refine Set.mem_iUnion₂.mpr ⟨(((a : ℚ) / (r : ℚ) ^ m : ℚ) : A.valuation.Completion), ?_, ?_⟩
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr ha, rfl⟩)
    · rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
      apply hU'
      rw [← Rat.cast_sub, v_ratCast, hvr]
      exact hva

  obtain ⟨k₀, hk₀⟩ := A.valuation_surjective ρ
  have hρk : ρ = Valued.v ((k₀ : A.valuation.Completion)) := by rw [v_coe, hk₀]
  refine hK.of_isClosed_subset ?_ ?_
  · have : {x : A.valuation.Completion | x ∈ Set.range (algebraMap (↥(ratClosure A)) A.valuation.Completion) ∧ Valued.v x ≤ ρ}
        = S ∩ {x | Valued.v x ≤ Valued.v ((k₀ : A.valuation.Completion))} := by
      ext x; rw [Set.mem_setOf_eq, hrange, ← hρk]; rfl
    rw [this]
    exact (isClosed_ratClosure A).inter (hball_closed _)
  · rintro x ⟨hx, hxρ⟩
    exact ⟨(hrange x).mp hx, le_trans hxρ (by rw [hvc]; exact hm)⟩

end S_ValuationSubring_isCompact_ratClosure_inter_closedBall_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_isCompact_ratClosure_inter_closedBall_of_liesOverPrime (solution)
