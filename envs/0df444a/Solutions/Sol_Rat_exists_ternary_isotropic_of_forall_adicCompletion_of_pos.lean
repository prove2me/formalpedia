-- Prove2me | solution 1 for Rat.exists_ternary_isotropic_of_forall_adicCompletion_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/07064587-ab42-5439-a015-96be888268ee

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rat_exists_ternary_isotropic_of_forall_adicCompletion_of_pos

open IsDedekindDomain NumberField

namespace W7tHasseMink3

section FieldGeneric

variable {F : Type*} [Field F]

def TernIso (F : Type*) [Field F] (a b : F) : Prop :=
  ∃ z x y : F, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0

theorem ternIso_symm {a b : F} : TernIso F a b → TernIso F b a := by
  rintro ⟨z, x, y, hnt, heq⟩
  exact ⟨z, y, x, fun ⟨h1, h2, h3⟩ ↦ hnt ⟨h1, h3, h2⟩, by linear_combination heq⟩

theorem ternIso_comm {a b : F} : TernIso F a b ↔ TernIso F b a :=
  ⟨ternIso_symm, ternIso_symm⟩

theorem ternIso_mul_sq_right {a b s : F} (hs : s ≠ 0) :
    TernIso F a (b * s ^ 2) ↔ TernIso F a b := by
  constructor
  · rintro ⟨z, x, y, hnt, heq⟩
    refine ⟨z, x, y * s, ?_, by linear_combination heq⟩
    rintro ⟨hz, hx, hy⟩
    exact hnt ⟨hz, hx, (mul_eq_zero.mp hy).resolve_right hs⟩
  · rintro ⟨z, x, y, hnt, heq⟩
    refine ⟨z * s, x * s, y, ?_, by linear_combination s ^ 2 * heq⟩
    rintro ⟨hz, hx, hy⟩
    exact hnt ⟨(mul_eq_zero.mp hz).resolve_right hs, (mul_eq_zero.mp hx).resolve_right hs, hy⟩

theorem ternIso_mul_sq_left {a b s : F} (hs : s ≠ 0) :
    TernIso F (a * s ^ 2) b ↔ TernIso F a b := by
  rw [ternIso_comm, ternIso_mul_sq_right hs, ternIso_comm]

theorem ternIso_of_eq_sq {a b r : F} (h : a = r ^ 2) : TernIso F a b :=
  ⟨r, 1, 0, fun ⟨_, h1, _⟩ ↦ one_ne_zero h1, by rw [h]; ring⟩

theorem ternIso_normTransfer {a b b' t : F} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hbb' : b * b' = t ^ 2 - a) : TernIso F a b ↔ TernIso F a b' := by
  have key : ∀ {B B' : F}, B ≠ 0 → B * B' = t ^ 2 - a → TernIso F a B → TernIso F a B' := by
    intro B B' hB hBB' h
    obtain ⟨z, x, y, hnt, heq⟩ := h
    by_cases hy : y = 0
    · subst hy
      have hx : x ≠ 0 := by
        intro hx0
        subst hx0
        apply hnt
        refine ⟨?_, rfl, rfl⟩
        have : z ^ 2 = 0 := by linear_combination heq
        exact pow_eq_zero_iff two_ne_zero |>.mp this
      refine ⟨z / x, 1, 0, fun ⟨_, h1, _⟩ ↦ one_ne_zero h1, ?_⟩
      field_simp
      linear_combination heq
    · refine ⟨(z * t + a * x) / B, (z + t * x) / B, y, fun ⟨_, _, hy0⟩ ↦ hy hy0, ?_⟩
      have h1 : z ^ 2 - a * x ^ 2 = B * y ^ 2 := by linear_combination heq
      have brahm : (z * t + a * x) ^ 2 - a * (z + t * x) ^ 2 = B ^ 2 * (B' * y ^ 2) := by
        linear_combination (t ^ 2 - a) * h1 - B * y ^ 2 * hBB'
      field_simp
      linear_combination brahm
  exact ⟨key hb hbb', key hb' (by linear_combination hbb')⟩

theorem ternIso_map {K Φ : Type*} [Field K] [FunLike Φ F K] [RingHomClass Φ F K] (φ : Φ)
    (hφ : Function.Injective φ) {a b : F} (h : TernIso F a b) : TernIso K (φ a) (φ b) := by
  obtain ⟨z, x, y, hnt, heq⟩ := h
  refine ⟨φ z, φ x, φ y, ?_, ?_⟩
  · rintro ⟨hz, hx, hy⟩
    exact hnt ⟨hφ (by rw [hz, map_zero]), hφ (by rw [hx, map_zero]), hφ (by rw [hy, map_zero])⟩
  · have := congrArg φ heq
    simpa [map_sub, map_mul, map_pow, map_zero] using this

end FieldGeneric

section LocIso

def LocIso (a b : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  TernIso (v.adicCompletion ℚ) (algebraMap ℚ (v.adicCompletion ℚ) a)
    (algebraMap ℚ (v.adicCompletion ℚ) b)

theorem algebraMap_adicCompletion_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) {s : ℚ} (hs : s ≠ 0) :
    algebraMap ℚ (v.adicCompletion ℚ) s ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap ℚ (v.adicCompletion ℚ)).injective).mpr hs

theorem locIso_comm {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ)) : LocIso a b v ↔ LocIso b a v :=
  ternIso_comm

theorem locIso_mul_sq_left {a b s : ℚ} (hs : s ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    LocIso (a * s ^ 2) b v ↔ LocIso a b v := by
  unfold LocIso
  rw [map_mul, map_pow]
  exact ternIso_mul_sq_left (algebraMap_adicCompletion_ne_zero v hs)

theorem locIso_mul_sq_right {a b s : ℚ} (hs : s ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    LocIso a (b * s ^ 2) v ↔ LocIso a b v := by
  unfold LocIso
  rw [map_mul, map_pow]
  exact ternIso_mul_sq_right (algebraMap_adicCompletion_ne_zero v hs)

theorem locIso_normTransfer {a b b' t : ℚ} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hbb' : b * b' = t ^ 2 - a) (v : HeightOneSpectrum (𝓞 ℚ)) :
    LocIso a b v ↔ LocIso a b' v := by
  unfold LocIso
  refine ternIso_normTransfer (t := algebraMap ℚ _ t) (algebraMap_adicCompletion_ne_zero v hb)
    (algebraMap_adicCompletion_ne_zero v hb') ?_
  rw [← map_mul, hbb', map_sub, map_pow]

end LocIso

section PadicLocal

variable {p : ℕ} [hp : Fact p.Prime]

theorem padic_valuation_neg (x : ℚ_[p]) : (-x).valuation = x.valuation := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := norm_neg x
  rw [Padic.norm_eq_zpow_neg_valuation (neg_ne_zero.mpr hx),
    Padic.norm_eq_zpow_neg_valuation hx] at h
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp_ne_one : (p : ℝ) ≠ 1 := by exact_mod_cast hp.out.ne_one
  have := (zpow_right_inj₀ hp_pos hp_ne_one).mp h
  linarith

theorem isSquare_zmod_of_padic_ternIso {a c : ℤ} (hpa : ¬ (p : ℤ) ∣ a) (hpc : ¬ (p : ℤ) ∣ c)
    (h : TernIso ℚ_[p] (a : ℚ_[p]) (((p : ℤ) * c : ℤ) : ℚ_[p])) :
    IsSquare ((a : ZMod p)) := by
  set A : ℚ_[p] := (a : ℚ_[p]) with hA_def
  set B : ℚ_[p] := (((p : ℤ) * c : ℤ) : ℚ_[p]) with hB_def
  have ha0 : a ≠ 0 := fun h0 ↦ hpa (h0 ▸ dvd_zero _)
  have hc0 : c ≠ 0 := fun h0 ↦ hpc (h0 ▸ dvd_zero _)
  have hA0 : A ≠ 0 := Int.cast_ne_zero.mpr ha0
  have hcQ0 : (c : ℚ_[p]) ≠ 0 := Int.cast_ne_zero.mpr hc0
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hB : B = (p : ℚ_[p]) * (c : ℚ_[p]) := by rw [hB_def]; push_cast; ring
  have hB0 : B ≠ 0 := hB ▸ mul_ne_zero hp0 hcQ0
  have vA : A.valuation = 0 := by
    rw [hA_def, Padic.valuation_intCast, padicValInt.eq_zero_of_not_dvd hpa]; rfl
  have vc : (c : ℚ_[p]).valuation = 0 := by
    rw [Padic.valuation_intCast, padicValInt.eq_zero_of_not_dvd hpc]; rfl
  have vB : B.valuation = 1 := by
    rw [hB, Padic.valuation_mul hp0 hcQ0, Padic.valuation_p, vc, add_zero]
  obtain ⟨z, x, y, hnt, heq⟩ := h
  by_cases hx : x = 0
  ·
    subst hx
    exfalso
    have hy : y ≠ 0 := by
      intro hy; subst hy
      apply hnt
      refine ⟨?_, rfl, rfl⟩
      have : z ^ 2 = 0 := by linear_combination heq
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    have hz : z ≠ 0 := by
      intro hz; subst hz
      have : B * y ^ 2 = 0 := by linear_combination -heq
      exact (mul_ne_zero hB0 (pow_ne_zero 2 hy)) this
    have hval := congrArg Padic.valuation (show z ^ 2 = B * y ^ 2 by linear_combination heq)
    rw [Padic.valuation_pow, Padic.valuation_mul hB0 (pow_ne_zero 2 hy), Padic.valuation_pow,
      vB] at hval
    push_cast at hval
    omega
  ·
    set w : ℚ_[p] := z / x with hw_def
    set u : ℚ_[p] := y / x with hu_def
    have hwu : w ^ 2 = A + B * u ^ 2 := by
      rw [hw_def, hu_def]
      field_simp
      linear_combination heq

    have hu_int : ‖u‖ ≤ 1 := by
      rcases eq_or_ne u 0 with hu0 | hu0
      · simp [hu0]
      rw [Padic.norm_le_one_iff_val_nonneg]
      by_contra hneg
      have hneg' : u.valuation < 0 := lt_of_not_ge hneg
      have hT0 : B * u ^ 2 ≠ 0 := mul_ne_zero hB0 (pow_ne_zero 2 hu0)
      have vT : (B * u ^ 2).valuation = 1 + 2 * u.valuation := by
        rw [Padic.valuation_mul hB0 (pow_ne_zero 2 hu0), Padic.valuation_pow, vB]; push_cast; ring
      rcases eq_or_ne w 0 with hw0 | hw0
      · have hT : B * u ^ 2 = -A := by
          have : w ^ 2 = 0 := by rw [hw0]; ring
          linear_combination hwu.symm.trans this
        have := congrArg Padic.valuation hT
        rw [vT, padic_valuation_neg, vA] at this
        omega
      · have h1 : min A.valuation (B * u ^ 2).valuation ≤ (A + B * u ^ 2).valuation :=
          Padic.le_valuation_add (by rw [← hwu]; exact pow_ne_zero 2 hw0)
        have h2 : min (w ^ 2).valuation (-A).valuation ≤ (w ^ 2 + -A).valuation :=
          Padic.le_valuation_add (by
            rw [show w ^ 2 + -A = B * u ^ 2 by linear_combination hwu]; exact hT0)
        rw [← hwu, Padic.valuation_pow, vA, vT] at h1
        rw [show w ^ 2 + -A = B * u ^ 2 by linear_combination hwu, Padic.valuation_pow,
          padic_valuation_neg, vA, vT] at h2
        push_cast at h1 h2
        rw [min_le_iff] at h1 h2
        omega

    have hw_int : ‖w‖ ≤ 1 := by
      rcases eq_or_ne w 0 with hw0 | hw0
      · simp [hw0]
      rw [Padic.norm_le_one_iff_val_nonneg]
      rcases eq_or_ne u 0 with hu0 | hu0
      · have hwA : w ^ 2 = A := by rw [hwu, hu0]; ring
        have := congrArg Padic.valuation hwA
        rw [Padic.valuation_pow, vA] at this
        push_cast at this
        omega
      · have hu_val : 0 ≤ u.valuation := (Padic.norm_le_one_iff_val_nonneg u).mp hu_int
        have vT : (B * u ^ 2).valuation = 1 + 2 * u.valuation := by
          rw [Padic.valuation_mul hB0 (pow_ne_zero 2 hu0), Padic.valuation_pow, vB]
          push_cast; ring
        have h1 : min A.valuation (B * u ^ 2).valuation ≤ (A + B * u ^ 2).valuation :=
          Padic.le_valuation_add (by rw [← hwu]; exact pow_ne_zero 2 hw0)
        rw [← hwu, Padic.valuation_pow, vA, vT] at h1
        push_cast at h1
        rw [min_le_iff] at h1
        omega

    set w' : ℤ_[p] := ⟨w, hw_int⟩ with hw'_def
    set u' : ℤ_[p] := ⟨u, hu_int⟩ with hu'_def
    have hInt : w' ^ 2 = (a : ℤ_[p]) + (((p : ℤ) * c : ℤ) : ℤ_[p]) * u' ^ 2 := by
      apply PadicInt.ext
      rw [PadicInt.coe_pow, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow,
        PadicInt.coe_intCast, PadicInt.coe_intCast]
      exact hwu
    have hres := congrArg (PadicInt.toZMod (p := p)) hInt
    rw [map_pow, map_add, map_mul, map_intCast, map_intCast] at hres
    have hpc0 : ((((p : ℤ) * c : ℤ)) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact dvd_mul_right _ _
    rw [hpc0, zero_mul, add_zero] at hres
    exact ⟨PadicInt.toZMod w', by rw [← sq]; exact hres.symm⟩

end PadicLocal

section SqrtMod

local instance instFactPrimesW7T (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

theorem isSquare_zmod_prime_of_locIso {a b : ℤ} {p : ℕ} (hpp : p.Prime) (hpb : (p : ℤ) ∣ b)
    (hsf : Squarefree b) (hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), LocIso (a : ℚ) (b : ℚ) v) :
    IsSquare ((a : ZMod p)) := by
  by_cases hpa : (p : ℤ) ∣ a
  · exact ⟨0, by rw [(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr hpa, mul_zero]⟩
  obtain ⟨c, rfl⟩ := hpb
  have hpc : ¬ (p : ℤ) ∣ c := by
    rintro ⟨d, rfl⟩
    have hunit : IsUnit (p : ℤ) := hsf p ⟨d, by ring⟩
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hunit
    exact hpp.ne_one hunit

  let q : Nat.Primes := ⟨p, hpp⟩
  haveI : Fact p.Prime := ⟨hpp⟩
  let v : HeightOneSpectrum (𝓞 ℚ) := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q
  let e := (Padic.adicCompletionEquiv (𝓞 ℚ) q).symm
  have hloc : TernIso ℚ_[p] (e (algebraMap ℚ _ (a : ℚ)))
      (e (algebraMap ℚ _ (((p : ℤ) * c : ℤ) : ℚ))) :=
    ternIso_map e (EquivLike.injective e) (hv v)
  have hcast : ∀ n : ℤ, e (algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ)) = (n : ℚ_[p]) := by
    intro n
    rw [AlgEquivClass.commutes]
    simp
  rw [hcast, hcast] at hloc
  exact isSquare_zmod_of_padic_ternIso hpa hpc hloc

theorem isSquare_prod_mk {R S : Type*} [Mul R] [Mul S] {x : R} {y : S}
    (hx : IsSquare x) (hy : IsSquare y) : IsSquare ((x, y) : R × S) := by
  obtain ⟨r, hr⟩ := hx
  obtain ⟨s, hs⟩ := hy
  exact ⟨(r, s), by rw [hr, hs]; rfl⟩

theorem isSquare_zmod_of_forall_prime {a : ℤ} :
    ∀ n : ℕ, n ≠ 0 → Squarefree n →
      (∀ p : ℕ, p.Prime → p ∣ n → IsSquare ((a : ZMod p))) → IsSquare ((a : ZMod n)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro hn hsf hprime
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have hn1 : n = 1 := by omega
    subst hn1
    exact ⟨(a : ZMod 1), Subsingleton.elim _ _⟩
  obtain ⟨p, hpp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  obtain ⟨m, rfl⟩ := hpn
  have hm0 : m ≠ 0 := fun h ↦ hn (by rw [h, mul_zero])
  have hpm : ¬ p ∣ m := by
    rintro ⟨d, rfl⟩
    have hunit : IsUnit p := hsf p ⟨d, by ring⟩
    exact hpp.ne_one (Nat.isUnit_iff.mp hunit)
  have hcop : p.Coprime m := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hpm
  have hmlt : m < p * m := by
    have := hpp.two_le
    nlinarith [Nat.pos_of_ne_zero hm0]
  have hmSq : IsSquare ((a : ZMod m)) :=
    IH m hmlt hm0 (hsf.squarefree_of_dvd (dvd_mul_left m p))
      (fun r hr hrm ↦ hprime r hr (dvd_mul_of_dvd_right hrm p))
  have hpSq : IsSquare ((a : ZMod p)) := hprime p hpp (dvd_mul_right p m)

  let e := ZMod.chineseRemainder hcop
  have himg : IsSquare (e (a : ZMod (p * m))) := by
    rw [map_intCast]
    have : ((a : ℤ) : ZMod p × ZMod m) = ((a : ZMod p), (a : ZMod m)) := by
      ext <;> simp
    rw [this]
    exact isSquare_prod_mk hpSq hmSq
  obtain ⟨r, hr⟩ := himg
  refine ⟨e.symm r, ?_⟩
  apply e.injective
  rw [map_mul, hr, RingEquiv.apply_symm_apply]

theorem exists_sqrtMod_of_locIso {a b : ℤ} (hb : b ≠ 0) (hsf : Squarefree b)
    (hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), LocIso (a : ℚ) (b : ℚ) v) :
    ∃ s : ℤ, b ∣ s ^ 2 - a := by
  set n : ℕ := b.natAbs with hn_def
  have hn0 : n ≠ 0 := Int.natAbs_ne_zero.mpr hb
  haveI : NeZero n := ⟨hn0⟩
  have hnsf : Squarefree n := Int.squarefree_natAbs.mpr hsf
  have hsq : IsSquare ((a : ZMod n)) := by
    refine isSquare_zmod_of_forall_prime n hn0 hnsf (fun p hpp hpn ↦ ?_)
    have hpb : (p : ℤ) ∣ b := Int.natCast_dvd.mpr hpn
    exact isSquare_zmod_prime_of_locIso hpp hpb hsf hv
  obtain ⟨r, hr⟩ := hsq
  refine ⟨(r.val : ℤ), ?_⟩
  rw [← Int.natAbs_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, hr, sq, sub_self]

end SqrtMod

section Descent

theorem exists_small_sqrtMod {a b : ℤ} (hb : b ≠ 0)
    (h : ∃ s, b ∣ s ^ 2 - a) : ∃ t : ℤ, b ∣ t ^ 2 - a ∧ 2 * t.natAbs ≤ b.natAbs := by
  obtain ⟨s, hs⟩ := h
  have hn : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  set t := Int.bmod s b.natAbs with ht_def
  refine ⟨t, ?_, ?_⟩
  · have hts : b ∣ t - s :=
      (Int.natAbs_dvd.mp (Int.dvd_bmod_sub_self (x := s) (m := b.natAbs)))
    have hfact : t ^ 2 - a = (t - s) * (t + s) + (s ^ 2 - a) := by ring
    rw [hfact]
    exact dvd_add (Dvd.dvd.mul_right hts _) hs
  · have h1 : -((b.natAbs : ℤ) / 2) ≤ t := Int.le_bmod hn
    have h2 : t < ((b.natAbs : ℤ) + 1) / 2 := Int.bmod_lt hn
    omega

theorem descent_bound {a b t : ℤ} (hb : b ≠ 0) (hdvd : b ∣ t ^ 2 - a)
    (ht : 2 * t.natAbs ≤ b.natAbs) (hab : a.natAbs ≤ b.natAbs)
    (hb2 : 2 ≤ b.natAbs) :
    ((t ^ 2 - a) / b).natAbs < b.natAbs := by
  set b' := (t ^ 2 - a) / b with hb'_def
  have hbb' : b * b' = t ^ 2 - a := by rw [hb'_def]; exact Int.mul_ediv_cancel' hdvd
  have hmul : b.natAbs * b'.natAbs = (t ^ 2 - a).natAbs := by
    rw [← Int.natAbs_mul, hbb']
  have hsub : (t ^ 2 - a).natAbs ≤ t.natAbs ^ 2 + a.natAbs := by
    calc (t ^ 2 - a).natAbs ≤ (t ^ 2).natAbs + a.natAbs := Int.natAbs_sub_le _ _
      _ = t.natAbs ^ 2 + a.natAbs := by rw [Int.natAbs_pow]
  have hsq : 4 * t.natAbs ^ 2 ≤ b.natAbs ^ 2 := by
    calc 4 * t.natAbs ^ 2 = (2 * t.natAbs) ^ 2 := by ring
      _ ≤ b.natAbs ^ 2 := Nat.pow_le_pow_left ht 2
  have hn : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have h4 : 4 * b'.natAbs ≤ b.natAbs + 4 := by
    refine Nat.le_of_mul_le_mul_left ?_ hn
    calc b.natAbs * (4 * b'.natAbs) = 4 * (b.natAbs * b'.natAbs) := by ring
      _ = 4 * (t ^ 2 - a).natAbs := by rw [hmul]
      _ ≤ 4 * (t.natAbs ^ 2 + a.natAbs) := by omega
      _ ≤ b.natAbs ^ 2 + 4 * b.natAbs := by omega
      _ = b.natAbs * (b.natAbs + 4) := by ring
  omega

theorem int_sq_mul_squarefree {n : ℤ} (hn : n ≠ 0) :
    ∃ m u : ℤ, m * u ^ 2 = n ∧ Squarefree m ∧ u ≠ 0 ∧ m ≠ 0 ∧
      m.natAbs ≤ n.natAbs ∧ (0 < n → 0 < m) := by
  obtain ⟨m₀, u₀, heq, hsqf⟩ := Nat.sq_mul_squarefree n.natAbs
  have hn1 : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn
  have hu₀ : 0 < u₀ := by
    rcases Nat.eq_zero_or_pos u₀ with h | h
    · subst h; simp at heq; omega
    · exact h
  have hdvd : (u₀ : ℤ) ^ 2 ∣ n := Int.natAbs_dvd_natAbs.mp <| by
    simp only [Int.natAbs_pow, Int.natAbs_natCast]
    exact ⟨m₀, by linarith [heq]⟩
  set m : ℤ := n / (u₀ : ℤ) ^ 2 with hm_def
  have hmul : m * (u₀ : ℤ) ^ 2 = n := Int.ediv_mul_cancel hdvd
  have hm0 : m ≠ 0 := fun h ↦ hn (by rw [← hmul, h, zero_mul])
  have habs : m.natAbs * u₀ ^ 2 = n.natAbs := by
    have h := congrArg Int.natAbs hmul
    simpa [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using h
  have hu2 : 0 < u₀ ^ 2 := by positivity
  have hmabs : m.natAbs = m₀ :=
    Nat.eq_of_mul_eq_mul_right hu2 (habs.trans (by linarith [heq]))
  refine ⟨m, (u₀ : ℤ), hmul, ?_, by exact_mod_cast hu₀.ne', hm0, ?_, ?_⟩
  · rw [← Int.squarefree_natAbs, hmabs]; exact hsqf
  · calc m.natAbs = m₀ := hmabs
      _ ≤ u₀ ^ 2 * m₀ := Nat.le_mul_of_pos_left _ hu2
      _ = n.natAbs := heq
  · intro hpos
    have hu2Z : (0 : ℤ) < (u₀ : ℤ) ^ 2 := by positivity
    by_contra hle
    have hmle : m ≤ 0 := not_lt.mp hle
    have : m * (u₀ : ℤ) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hmle hu2Z.le
    linarith [hmul]

theorem legendre_descent :
    ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → Squarefree a → Squarefree b →
      ¬ (a < 0 ∧ b < 0) →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), LocIso (a : ℚ) (b : ℚ) v) →
      TernIso ℚ (a : ℚ) (b : ℚ) := by
  suffices key : ∀ n : ℕ, ∀ a b : ℤ, a.natAbs + b.natAbs = n →
      a ≠ 0 → b ≠ 0 → Squarefree a → Squarefree b → ¬ (a < 0 ∧ b < 0) →
      (∀ v, LocIso (a : ℚ) (b : ℚ) v) → TernIso ℚ (a : ℚ) (b : ℚ) from
    fun a b ↦ key _ a b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro a b hn ha hb hasf hbsf hsgn hv
  have step : ∀ a' b' : ℤ, a'.natAbs + b'.natAbs = n →
      a' ≠ 0 → b' ≠ 0 → Squarefree a' → Squarefree b' → ¬ (a' < 0 ∧ b' < 0) →
      (∀ v, LocIso (a' : ℚ) (b' : ℚ) v) → a'.natAbs ≤ b'.natAbs →
      TernIso ℚ (a' : ℚ) (b' : ℚ) := by
    clear hn ha hb hasf hbsf hsgn hv a b
    intro a b hsum ha hb hasf hbsf hsgn hv hab

    rcases Nat.lt_or_ge b.natAbs 2 with hblt | hb2
    · have hbeq : b.natAbs = 1 := by have := Int.natAbs_pos.mpr ha; omega
      have haeq : a.natAbs = 1 := le_antisymm (hab.trans_eq hbeq) (Int.natAbs_pos.mpr ha)
      rcases Int.natAbs_eq_iff.mp haeq with rfl | rfl
      · exact ternIso_of_eq_sq (r := 1) (by simp)
      · rcases Int.natAbs_eq_iff.mp hbeq with rfl | rfl
        · exact ternIso_symm (ternIso_of_eq_sq (r := 1) (by simp))
        · exact absurd ⟨by simp, by simp⟩ hsgn

    obtain ⟨t, hdvd, hsmall⟩ :=
      exists_small_sqrtMod hb (exists_sqrtMod_of_locIso hb hbsf hv)
    set b₁ : ℤ := (t ^ 2 - a) / b with hb₁_def
    have hbb₁ : b * b₁ = t ^ 2 - a := Int.mul_ediv_cancel' hdvd
    rcases eq_or_ne b₁ 0 with hb₁0 | hb₁0
    · have hat : a = t ^ 2 := by have h := hbb₁; rw [hb₁0, mul_zero] at h; linarith
      exact ternIso_of_eq_sq (r := (t : ℚ)) (by rw [hat]; push_cast; ring)
    have hb₁lt : b₁.natAbs < b.natAbs :=
      hb₁_def ▸ descent_bound hb hdvd hsmall hab hb2
    obtain ⟨b₂, u, humul, hb₂sf, hu0, hb₂0, hb₂le, hb₂pos⟩ := int_sq_mul_squarefree hb₁0
    have huQ : (u : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hu0
    have hbQ : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
    have hb₁Q : (b₁ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb₁0
    have hbb₁Q : (b : ℚ) * (b₁ : ℚ) = (t : ℚ) ^ 2 - (a : ℚ) := by exact_mod_cast hbb₁
    have hcast : (b₁ : ℚ) = (b₂ : ℚ) * (u : ℚ) ^ 2 := by exact_mod_cast humul.symm

    have hv₂ : ∀ v, LocIso (a : ℚ) (b₂ : ℚ) v := by
      intro v
      have h1 : LocIso (a : ℚ) (b₁ : ℚ) v := (locIso_normTransfer hbQ hb₁Q hbb₁Q v).mp (hv v)
      rw [hcast] at h1
      exact (locIso_mul_sq_right huQ v).mp h1

    have hsgn₂ : ¬ (a < 0 ∧ b₂ < 0) := by
      rintro ⟨haneg, hb₂neg⟩
      have hbpos : 0 < b := (lt_or_gt_of_ne hb).resolve_left (fun h ↦ hsgn ⟨haneg, h⟩)
      have hb₁pos : 0 < b₁ := by
        have hprod : 0 < b * b₁ := by rw [hbb₁]; nlinarith [sq_nonneg t]
        exact (mul_pos_iff_of_pos_left hbpos).mp hprod
      exact absurd (hb₂pos hb₁pos) (not_lt_of_gt hb₂neg)

    have hsolv₂ : TernIso ℚ (a : ℚ) (b₂ : ℚ) :=
      IH (a.natAbs + b₂.natAbs) (by omega) a b₂ rfl ha hb₂0 hasf hb₂sf hsgn₂ hv₂

    have hsolv₁ : TernIso ℚ (a : ℚ) (b₁ : ℚ) := by
      rw [hcast]; exact (ternIso_mul_sq_right huQ).mpr hsolv₂
    exact (ternIso_normTransfer hbQ hb₁Q hbb₁Q).mpr hsolv₁
  rcases le_total a.natAbs b.natAbs with hab | hab
  · exact step a b hn ha hb hasf hbsf hsgn hv hab
  · exact ternIso_symm <|
      step b a (by omega) hb ha hbsf hasf (fun ⟨h1, h2⟩ ↦ hsgn ⟨h2, h1⟩)
        (fun v ↦ (locIso_comm v).mp (hv v)) hab

end Descent

section Rational

theorem rat_mul_den_sq (q : ℚ) : q * (q.den : ℚ) ^ 2 = ((q.num * q.den : ℤ) : ℚ) := by
  have h := Rat.mul_den_eq_num q
  push_cast
  rw [sq, ← mul_assoc, h]

theorem numDen_ne_zero {q : ℚ} (hq : q ≠ 0) : q.num * q.den ≠ 0 :=
  mul_ne_zero (Rat.num_ne_zero.mpr hq) (Int.natCast_ne_zero.mpr q.den_nz)

theorem ternIso_rat_of_forall_locIso {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), LocIso a b v) (hR : 0 < a ∨ 0 < b) :
    TernIso ℚ a b := by
  set A : ℤ := a.num * a.den with hA_def
  set B : ℤ := b.num * b.den with hB_def
  have hA0 : A ≠ 0 := numDen_ne_zero ha
  have hB0 : B ≠ 0 := numDen_ne_zero hb
  have hdA : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_nz
  have hdB : (b.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr b.den_nz
  have haA : a * (a.den : ℚ) ^ 2 = (A : ℚ) := rat_mul_den_sq a
  have hbB : b * (b.den : ℚ) ^ 2 = (B : ℚ) := rat_mul_den_sq b
  obtain ⟨A₀, uA, huAmul, hA₀sf, huA0, hA₀0, -, hA₀pos⟩ := int_sq_mul_squarefree hA0
  obtain ⟨B₀, uB, huBmul, hB₀sf, huB0, hB₀0, -, hB₀pos⟩ := int_sq_mul_squarefree hB0
  have huAQ : (uA : ℚ) ≠ 0 := Int.cast_ne_zero.mpr huA0
  have huBQ : (uB : ℚ) ≠ 0 := Int.cast_ne_zero.mpr huB0
  have hAcast : (A : ℚ) = (A₀ : ℚ) * (uA : ℚ) ^ 2 := by exact_mod_cast huAmul.symm
  have hBcast : (B : ℚ) = (B₀ : ℚ) * (uB : ℚ) ^ 2 := by exact_mod_cast huBmul.symm

  have hv₀ : ∀ v, LocIso (A₀ : ℚ) (B₀ : ℚ) v := by
    intro v
    have h1 : LocIso (A : ℚ) (B : ℚ) v := by
      rw [← haA, ← hbB]
      exact (locIso_mul_sq_left hdA v).mpr ((locIso_mul_sq_right hdB v).mpr (hv v))
    rw [hAcast, hBcast] at h1
    exact (locIso_mul_sq_left huAQ v).mp ((locIso_mul_sq_right huBQ v).mp h1)

  have hposA : 0 < a → 0 < A := fun h ↦
    mul_pos (Rat.num_pos.mpr h) (Int.natCast_pos.mpr a.den_pos)
  have hposB : 0 < b → 0 < B := fun h ↦
    mul_pos (Rat.num_pos.mpr h) (Int.natCast_pos.mpr b.den_pos)
  have hsgn₀ : ¬ (A₀ < 0 ∧ B₀ < 0) := by
    rintro ⟨hAneg, hBneg⟩
    rcases hR with h | h
    · exact absurd (hA₀pos (hposA h)) (not_lt_of_gt hAneg)
    · exact absurd (hB₀pos (hposB h)) (not_lt_of_gt hBneg)

  have h₀ := legendre_descent A₀ B₀ hA₀0 hB₀0 hA₀sf hB₀sf hsgn₀ hv₀
  have h₁ : TernIso ℚ (A : ℚ) (B : ℚ) := by
    rw [hAcast, hBcast]
    exact (ternIso_mul_sq_left huAQ).mpr ((ternIso_mul_sq_right huBQ).mpr h₀)
  rw [← haA, ← hbB] at h₁
  exact (ternIso_mul_sq_left hdA).mp ((ternIso_mul_sq_right hdB).mp h₁)

end Rational

end W7tHasseMink3

open W7tHasseMink3 in
theorem solution
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2
          - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2 = 0)
    (hR : 0 < a ∨ 0 < b) :
    ∃ z x y : ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 :=
  ternIso_rat_of_forall_locIso ha hb hv hR

end S_Rat_exists_ternary_isotropic_of_forall_adicCompletion_of_pos
end P2MW
export P2MW.S_Rat_exists_ternary_isotropic_of_forall_adicCompletion_of_pos (solution)
