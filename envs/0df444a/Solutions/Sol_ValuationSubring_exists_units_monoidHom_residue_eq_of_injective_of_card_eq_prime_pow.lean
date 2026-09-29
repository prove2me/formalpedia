-- Prove2me | solution 1 for ValuationSubring.exists_units_monoidHom_residue_eq_of_injective_of_card_eq_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/6231f915-9128-5ccc-9c18-d2e31031eac0

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime
import Theorems.Thm_ValuationSubring_apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_units_monoidHom_residue_eq_of_injective_of_card_eq_prime_pow

set_option autoImplicit false

namespace TeichE72

open Polynomial

theorem eq_one_of_pow_eq_one_of_map_eq_one {S k : Type*} [CommRing S] [IsDomain S] [CommRing k]
    (f : S →+* k) {N : ℕ} (hN : (N : k) ≠ 0) {η : S} (hη : η ^ N = 1) (h1 : f η = 1) : η = 1 := by
  by_contra hne
  have hgeom : (η - 1) * ∑ i ∈ Finset.range N, η ^ i = 0 := by
    rw [mul_geom_sum, hη, sub_self]
  have hsum : ∑ i ∈ Finset.range N, η ^ i = 0 :=
    (mul_eq_zero.mp hgeom).resolve_left (sub_ne_zero.mpr hne)
  have := congrArg f hsum
  rw [map_sum, map_zero] at this
  simp only [map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
  exact hN this

variable {p : ℕ} [hp : Fact p.Prime]
  (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)

include hP in
theorem charP_residueField : CharP (IsLocalRing.ResidueField ↥P) p := by
  have hmem : ((p : ↥P)) ∈ IsLocalRing.maximalIdeal ↥P := by
    rw [ValuationSubring.valuation_lt_one_iff]
    have := (ValuationSubring.mem_nonunits_iff (A := P)).mp hP
    simpa using this
  have h0 : ((p : IsLocalRing.ResidueField ↥P)) = 0 := by
    rw [← map_natCast (IsLocalRing.residue ↥P), IsLocalRing.residue_eq_zero_iff]
    exact hmem
  have hdvd : ringChar (IsLocalRing.ResidueField ↥P) ∣ p := (ringChar.spec _ p).mp h0
  have hne : ringChar (IsLocalRing.ResidueField ↥P) ≠ 1 := CharP.ringChar_ne_one
  exact ringChar.of_eq (((Nat.dvd_prime hp.out).mp hdvd).resolve_left hne)

theorem mem_of_pow_eq_one {ζ : AlgebraicClosure ℚ} {N : ℕ} (hN : N ≠ 0) (hζ : ζ ^ N = 1) : ζ ∈ P := by
  rw [← ValuationSubring.valuation_le_one_iff]
  by_contra h
  push Not at h
  have : 1 < P.valuation (ζ ^ N) := by rw [map_pow]; exact one_lt_pow' h hN
  rw [hζ, map_one] at this
  exact lt_irrefl _ this

end TeichE72

namespace TeichE72

section Construct

variable {p : ℕ} [hp : Fact p.Prime]
  (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
  {O : Type*} [CommRing O] (i : O →+* ↥P) (hinj : Function.Injective i)
  (hO : ∀ y : AlgebraicClosure ℚ, y ∈ P → (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ y = y) →
    ∃ x : O, ((i x : ↥P) : AlgebraicClosure ℚ) = y)

include hP hinj hO in

theorem existsUnique_lift {N : ℕ} (hN : ¬ p ∣ N) (hN0 : N ≠ 0)
    (x : IsLocalRing.ResidueField ↥P) (hx : x ^ N = 1) :
    ∃! ζ : O, ζ ^ N = 1 ∧ IsLocalRing.residue ↥P (i ζ) = x := by
  classical
  haveI := charP_residueField P hP
  haveI : IsDomain O := hinj.isDomain i
  have hNk : ((N : IsLocalRing.ResidueField ↥P)) ≠ 0 := fun h =>
    hN ((CharP.cast_eq_zero_iff _ p N).mp h)
  set ρ : O →+* IsLocalRing.ResidueField ↥P := (IsLocalRing.residue ↥P).comp i with hρ
  have hN1 : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN0)

  have huniq : ∀ ζ ζ' : O, ζ ^ N = 1 → ζ' ^ N = 1 → ρ ζ = ρ ζ' → ζ = ζ' := by
    intro ζ ζ' hζ hζ' h
    set η := ζ * ζ' ^ (N - 1) with hηdef
    have hinv : ζ' ^ (N - 1) * ζ' = 1 := by rw [← pow_succ, hN1, hζ']
    have hη : η ^ N = 1 := by
      rw [hηdef, mul_pow, ← pow_mul, mul_comm (N - 1) N, pow_mul, hζ', one_pow, hζ, one_mul]
    have h1 : ρ η = 1 := by
      rw [hηdef, map_mul, h, ← map_mul, mul_comm, hinv, map_one]
    have hη1 : η = 1 := eq_one_of_pow_eq_one_of_map_eq_one ρ hNk hη h1
    have h2 := congrArg (fun t => t * ζ') hη1
    simp only [hηdef, mul_assoc, hinv, mul_one, one_mul] at h2
    exact h2

  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) N
  obtain ⟨z₀, hz₀⟩ := hO ζ₀ (mem_of_pow_eq_one P hN0 hζ₀.pow_eq_one)
    (fun σ hσ => ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn hp.out P hP hσ hN hζ₀.pow_eq_one)
  have hci : Function.Injective (fun t : O => ((i t : ↥P) : AlgebraicClosure ℚ)) :=
    Subtype.val_injective.comp hinj
  have hprim : IsPrimitiveRoot z₀ N := by
    refine IsPrimitiveRoot.of_map_of_injective (f := (P.subtype.comp i)) ?_ ?_
    · show IsPrimitiveRoot ((i z₀ : ↥P) : AlgebraicClosure ℚ) N
      rw [hz₀]; exact hζ₀
    · exact hci
  set TO := Polynomial.nthRootsFinset N (1 : O) with hTO
  set Tk := Polynomial.nthRootsFinset N (1 : IsLocalRing.ResidueField ↥P) with hTk
  have hcardO : TO.card = N := hprim.card_nthRootsFinset
  have hcardk : Tk.card ≤ N := by
    rw [hTk, Polynomial.nthRootsFinset]
    exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_nthRoots N 1)
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  have hmaps : ∀ ζ ∈ TO, ρ ζ ∈ Tk := by
    intro ζ hζ
    rw [hTO, Polynomial.mem_nthRootsFinset hNpos] at hζ
    rw [hTk, Polynomial.mem_nthRootsFinset hNpos, ← map_pow, hζ, map_one]
  have hinj : Set.InjOn ρ TO := by
    intro ζ hζ ζ' hζ' h
    rw [Finset.mem_coe, hTO, Polynomial.mem_nthRootsFinset hNpos] at hζ hζ'
    exact huniq ζ ζ' hζ hζ' h
  have himage : TO.image ρ = Tk := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.mp hy
      exact hmaps ζ hζ
    · rw [Finset.card_image_of_injOn hinj, hcardO]
      exact hcardk
  have hxT : x ∈ Tk := by rw [hTk, Polynomial.mem_nthRootsFinset hNpos]; exact hx
  rw [← himage] at hxT
  obtain ⟨ζ, hζ, hζx⟩ := Finset.mem_image.mp hxT
  rw [hTO, Polynomial.mem_nthRootsFinset hNpos] at hζ
  exact ⟨ζ, ⟨hζ, hζx⟩, fun ζ' ⟨hζ', hζ'x⟩ => huniq ζ' ζ hζ' hζ (hζ'x.trans hζx.symm)⟩

include hP hinj hO in
theorem main (F : Type*) [Field F] [Fintype F] (s : ℕ) (hF : Fintype.card F = p ^ s) :
    ∃ (χ : Fˣ →* Oˣ) (ι₀ : F →+* IsLocalRing.ResidueField ↥P),
      ∀ l : Fˣ, IsLocalRing.residue ↥P (i ((χ l : Oˣ) : O)) = ι₀ l := by
  classical
  haveI : IsDomain O := hinj.isDomain i
  set k := IsLocalRing.ResidueField ↥P
  haveI : CharP k p := charP_residueField P hP
  obtain ⟨e⟩ := P.nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime hP
  haveI : IsAlgClosed k := IsAlgClosed.of_ringEquiv _ _ e.symm

  have hs : s ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hF
    have : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  haveI : CharP F p := by
    have h0 : ((p : F)) ^ s = 0 := by
      have := FiniteField.cast_card_eq_zero F
      rw [hF] at this
      exact_mod_cast this
    have hp0 : (p : F) = 0 := (pow_eq_zero_iff hs).mp h0
    have hdvd : ringChar F ∣ p := (ringChar.spec F p).mp hp0
    have hne : ringChar F ≠ 1 := CharP.ringChar_ne_one
    exact ringChar.of_eq (((Nat.dvd_prime hp.out).mp hdvd).resolve_left hne)
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  haveI : Module.Finite (ZMod p) F := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (ZMod p) F := Algebra.IsAlgebraic.of_finite (ZMod p) F
  let ι₁ : F →ₐ[ZMod p] k := IsAlgClosed.lift
  let ι₀ : F →+* k := ι₁.toRingHom

  set N := p ^ s - 1 with hNdef
  have hpow : 2 ≤ p ^ s := le_trans hp.out.two_le (Nat.le_self_pow hs p)
  have hN0 : N ≠ 0 := by omega
  have hpN : ¬ p ∣ N := by
    intro h
    have h1 : p ∣ p ^ s := dvd_pow_self p hs
    have : p ∣ p ^ s - (p ^ s - 1) := Nat.dvd_sub h1 h
    rw [Nat.sub_sub_self (by omega : 1 ≤ p ^ s)] at this
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)

  have hlN : ∀ l : Fˣ, (ι₀ (l : F)) ^ N = 1 := by
    intro l
    rw [← map_pow, hNdef, ← hF, FiniteField.pow_card_sub_one_eq_one (l : F) l.ne_zero, map_one]

  have hN1 : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN0)
  let ζ : Fˣ → O := fun l => (existsUnique_lift P hP i hinj hO hpN hN0 (ι₀ l) (hlN l)).choose
  have hζ : ∀ l : Fˣ, (ζ l) ^ N = 1 ∧ IsLocalRing.residue ↥P (i (ζ l)) = ι₀ l := fun l =>
    (existsUnique_lift P hP i hinj hO hpN hN0 (ι₀ l) (hlN l)).choose_spec.1
  have hζu : ∀ (l : Fˣ) (z : O), z ^ N = 1 → IsLocalRing.residue ↥P (i z) = ι₀ l → z = ζ l :=
    fun l z hz hzx => (existsUnique_lift P hP i hinj hO hpN hN0 (ι₀ l) (hlN l)).choose_spec.2 z ⟨hz, hzx⟩
  let toU : Fˣ → Oˣ := fun l =>
    Units.mkOfMulEqOne (ζ l) ((ζ l) ^ (N - 1)) (by rw [← pow_succ', hN1, (hζ l).1])
  refine ⟨{ toFun := toU, map_one' := ?_, map_mul' := ?_ }, ι₀, fun l => ?_⟩
  · apply Units.ext
    show ζ 1 = 1
    symm
    exact hζu 1 1 (one_pow N) (by simp)
  · intro a b
    apply Units.ext
    show ζ (a * b) = ζ a * ζ b
    symm
    refine hζu (a * b) _ ?_ ?_
    · rw [mul_pow, (hζ a).1, (hζ b).1, one_mul]
    · rw [map_mul, map_mul, (hζ a).2, (hζ b).2, Units.val_mul, map_mul]
  · exact (hζ l).2

end Construct

end TeichE72

theorem solution
    (p : ℕ) [Fact p.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    {O : Type*} [CommRing O] (i : O →+* ↥P) (hinj : Function.Injective i)
    (hO : ∀ y : AlgebraicClosure ℚ, y ∈ P → (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ y = y) →
      ∃ x : O, ((i x : ↥P) : AlgebraicClosure ℚ) = y)
    (F : Type*) [Field F] [Fintype F] (s : ℕ) (hF : Fintype.card F = p ^ s) :
    ∃ (χ : Fˣ →* Oˣ) (ι₀ : F →+* IsLocalRing.ResidueField ↥P),
      ∀ l : Fˣ, IsLocalRing.residue ↥P (i ((χ l : Oˣ) : O)) = ι₀ l :=
  TeichE72.main P hP i hinj hO F s hF

end S_ValuationSubring_exists_units_monoidHom_residue_eq_of_injective_of_card_eq_prime_pow
end P2MW
export P2MW.S_ValuationSubring_exists_units_monoidHom_residue_eq_of_injective_of_card_eq_prime_pow (solution)
