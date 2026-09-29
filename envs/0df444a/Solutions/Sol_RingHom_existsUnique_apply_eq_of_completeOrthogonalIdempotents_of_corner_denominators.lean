-- Prove2me | solution 1 for RingHom.existsUnique_apply_eq_of_completeOrthogonalIdempotents_of_corner_denominators
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/7cb4ecd8-9bff-5f84-819e-935b1916a52b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_existsUnique_apply_eq_of_completeOrthogonalIdempotents_of_corner_denominators

namespace P2mCornerHom

noncomputable section

variable {K : Type} [CommRing K] {ι : Type} [Fintype ι] [DecidableEq ι]
variable {e : ι → K} (he : CompleteOrthogonalIdempotents e)
variable {χ : ι → (K →+* ℚ)} (hχe : ∀ a b : ι, χ b (e a) = if b = a then 1 else 0)
variable (hsep : ∀ k k' : K, (∀ a, χ a k = χ a k') → k = k')
variable {d : ι → ℕ} (hd : ∀ a, 0 < d a)
variable (hval : ∀ (a : ι) (k : K), ∃ (n : ℕ) (m : ℤ), χ a k = m / (d a : ℚ) ^ n)
variable (hinv : ∀ a : ι, ∃ y : K, χ a y = (d a : ℚ)⁻¹)

include hχe hsep in

theorem e_mul_eq_zero {a : ι} {k : K} (hk : χ a k = 0) : e a * k = 0 := by
  apply hsep
  intro b
  rw [map_mul, hχe, map_zero]
  by_cases h : b = a
  · subst h; rw [if_pos rfl, hk, mul_zero]
  · rw [if_neg h, zero_mul]

abbrev B (χ : ι → (K →+* ℚ)) (a : ι) : Subring ℚ := (χ a).range

abbrev ρ (χ : ι → (K →+* ℚ)) (a : ι) : K →+* B χ a := (χ a).rangeRestrict

theorem ρ_surjective (a : ι) : Function.Surjective (ρ χ a) := (χ a).rangeRestrict_surjective

theorem coe_ρ (a : ι) (k : K) : (ρ χ a k : ℚ) = χ a k := rfl

theorem ker_ρ (a : ι) : RingHom.ker (ρ χ a) = RingHom.ker (χ a) := by
  ext k
  rw [RingHom.mem_ker, RingHom.mem_ker, ← Subtype.coe_inj]
  rfl

include hval hinv hd in

theorem isLocalization_B (a : ι) : IsLocalization.Away ((d a : ℤ)) (B χ a) := by
  have hd0 : ((d a : ℚ)) ≠ 0 := by exact_mod_cast (hd a).ne'
  obtain ⟨y, hy⟩ := hinv a
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · rintro ⟨x, n, rfl⟩

    refine IsUnit.of_mul_eq_one (b := ρ χ a (y ^ n)) (Subtype.ext ?_)
    change ((algebraMap ℤ (B χ a) ((d a : ℤ) ^ n) : B χ a) : ℚ) * χ a (y ^ n) = 1
    rw [map_pow (χ a), hy, map_pow]
    change (((d a : ℤ) : B χ a) : ℚ) ^ n * _ = 1
    push_cast
    rw [← mul_pow, mul_inv_cancel₀ hd0, one_pow]
  · rintro ⟨z, k, rfl⟩
    obtain ⟨n, m, hm⟩ := hval a k
    refine ⟨(m, ⟨(d a : ℤ) ^ n, n, rfl⟩), Subtype.ext ?_⟩
    change χ a k * (((d a : ℤ) ^ n : ℤ) : ℚ) = (m : ℚ)
    rw [hm]
    push_cast
    field_simp
  · intro x x' hxx'
    refine ⟨1, ?_⟩
    have : ((x : ℚ)) = x' := by
      have := congrArg (fun z : B χ a => (z : ℚ)) hxx'
      simpa using this
    simp only [OneMemClass.coe_one, one_mul]
    exact_mod_cast this

variable {T : Type} [CommRing T] {b : ι → T} (hb : CompleteOrthogonalIdempotents b)
variable (hbd : ∀ a : ι, ∃ v : T, v * ((d a : T) * b a) = b a)

def I (b : ι → T) (a : ι) : Ideal T := Ideal.span {1 - b a}

theorem one_sub_mem_I (a : ι) : 1 - b a ∈ I b a := Ideal.subset_span rfl

include hb in
theorem b_mem_I {a a' : ι} (h : a' ≠ a) : b a' ∈ I b a := by
  have : b a' = b a' * (1 - b a) := by
    rw [mul_sub, mul_one, hb.ortho h, sub_zero]
  rw [this]
  exact Ideal.mul_mem_left _ _ (one_sub_mem_I a)

include hb in
theorem mk_b (a a' : ι) : Ideal.Quotient.mk (I b a) (b a') = if a = a' then 1 else 0 := by
  by_cases h : a = a'
  · subst h
    rw [if_pos rfl, eq_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk (I b a)), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (one_sub_mem_I a)
  · rw [if_neg h]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (b_mem_I hb (Ne.symm h))

include hb in
theorem isCoprime_I : Pairwise (Function.onFun IsCoprime (I b)) := by
  intro a a' h
  rw [Function.onFun, Ideal.isCoprime_iff_exists]
  exact ⟨1 - b a, one_sub_mem_I a, b a, b_mem_I hb h, by ring⟩

include hb in
theorem iInf_I : ⨅ a, I b a = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  have hxb : ∀ a, x * b a = 0 := by
    intro a
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_iInf.mp hx a)
    rw [← ht, mul_assoc, sub_mul, one_mul, hb.idem a, sub_self, mul_zero]
  calc x = x * ∑ a, b a := by rw [hb.complete, mul_one]
    _ = 0 := by rw [Finset.mul_sum]; exact Finset.sum_eq_zero fun a _ => hxb a

def πT (b : ι → T) : T →+* ∀ a, T ⧸ I b a := RingHom.pi fun a => Ideal.Quotient.mk (I b a)

@[scoped simp] theorem πT_apply (t : T) (a : ι) : πT b t a = Ideal.Quotient.mk (I b a) t := rfl

include hb in
theorem πT_injective : Function.Injective (πT b) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  have : t ∈ ⨅ a, I b a := by
    refine Ideal.mem_iInf.mpr fun a => Ideal.Quotient.eq_zero_iff_mem.mp ?_
    exact congrFun ht a
  rwa [iInf_I hb, Ideal.mem_bot] at this

include hb in
theorem πT_surjective : Function.Surjective (πT b) := by
  intro y
  obtain ⟨xbar, hx⟩ := Ideal.quotientInfToPiQuotient_surj (isCoprime_I hb) y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
  refine ⟨x, ?_⟩
  rw [← hx]
  funext a
  rw [πT_apply, Ideal.quotientInfToPiQuotient_mk']

include hbd hb in

theorem isUnit_d (a : ι) : IsUnit ((Int.castRingHom (T ⧸ I b a)) (d a : ℤ)) := by
  obtain ⟨v, hv⟩ := hbd a
  refine IsUnit.of_mul_eq_one_right (a := Ideal.Quotient.mk (I b a) v) ?_
  have h1 : Ideal.Quotient.mk (I b a) (b a) = 1 := by rw [mk_b hb, if_pos rfl]
  have := congrArg (Ideal.Quotient.mk (I b a)) hv
  rw [map_mul, map_mul, h1, mul_one, map_natCast] at this
  simpa using this

def f (hd : ∀ a, 0 < d a)
    (hval : ∀ (a : ι) (k : K), ∃ (n : ℕ) (m : ℤ), χ a k = m / (d a : ℚ) ^ n)
    (hinv : ∀ a : ι, ∃ y : K, χ a y = (d a : ℚ)⁻¹)
    (hb : CompleteOrthogonalIdempotents b)
    (hbd : ∀ a : ι, ∃ v : T, v * ((d a : T) * b a) = b a) (a : ι) : K →+* T ⧸ I b a :=
  haveI := isLocalization_B hd hval hinv a
  (IsLocalization.Away.lift ((d a : ℤ)) (isUnit_d hb hbd a)).comp (ρ χ a)

theorem f_apply_of_eq_intCast (a : ι) (k : K) (m : ℤ) (hk : χ a k = m) :
    f hd hval hinv hb hbd a k = m := by
  haveI := isLocalization_B hd hval hinv a
  have hρ : ρ χ a k = algebraMap ℤ (B χ a) m := Subtype.ext (by rw [coe_ρ, hk]; rfl)
  change IsLocalization.Away.lift ((d a : ℤ)) (isUnit_d hb hbd a) (ρ χ a k) = _
  rw [hρ, IsLocalization.Away.lift_eq]
  simp

include hχe in
theorem f_e (a c : ι) : f hd hval hinv hb hbd a (e c) = if a = c then 1 else 0 := by
  by_cases h : a = c
  · rw [if_pos h, f_apply_of_eq_intCast (hd := hd) (hval := hval) (hinv := hinv) (hb := hb)
      (hbd := hbd) (m := 1) a (e c) (by rw [hχe, if_pos h]; simp)]; simp
  · rw [if_neg h, f_apply_of_eq_intCast (hd := hd) (hval := hval) (hinv := hinv) (hb := hb)
      (hbd := hbd) (m := 0) a (e c) (by rw [hχe, if_neg h]; simp)]; simp

def φ (hd : ∀ a, 0 < d a)
    (hval : ∀ (a : ι) (k : K), ∃ (n : ℕ) (m : ℤ), χ a k = m / (d a : ℚ) ^ n)
    (hinv : ∀ a : ι, ∃ y : K, χ a y = (d a : ℚ)⁻¹)
    (hb : CompleteOrthogonalIdempotents b)
    (hbd : ∀ a : ι, ∃ v : T, v * ((d a : T) * b a) = b a) : K →+* T :=
  ((RingEquiv.ofBijective (πT b) ⟨πT_injective hb, πT_surjective hb⟩).symm : (∀ a, T ⧸ I b a) →+* T).comp
    (RingHom.pi fun a => f hd hval hinv hb hbd a)

theorem πT_φ (k : K) : πT b (φ hd hval hinv hb hbd k) = fun a => f hd hval hinv hb hbd a k := by
  set E := RingEquiv.ofBijective (πT b) ⟨πT_injective hb, πT_surjective hb⟩ with hE
  have hEapp : ∀ t, πT b t = E t := fun t => rfl
  change πT b (E.symm ((RingHom.pi fun a => f hd hval hinv hb hbd a) k)) = _
  rw [hEapp, RingEquiv.apply_symm_apply]
  rfl

include hχe in
theorem φ_e (c : ι) : φ hd hval hinv hb hbd (e c) = b c := by
  apply πT_injective hb
  rw [πT_φ]
  funext a
  rw [f_e hχe, πT_apply, mk_b hb]

include hχe hsep hb he in

theorem ker_le_of_apply_e {φ' : K →+* T} (hφ' : ∀ a, φ' (e a) = b a) (a : ι) :
    RingHom.ker (ρ χ a) ≤ RingHom.ker ((Ideal.Quotient.mk (I b a)).comp φ') := by
  intro k hk
  rw [ker_ρ, RingHom.mem_ker] at hk
  rw [RingHom.mem_ker, RingHom.comp_apply]
  have hek : e a * k = 0 := e_mul_eq_zero hχe hsep hk
  have hk' : k = ∑ c, e c * k := by rw [← Finset.sum_mul, he.complete, one_mul]
  rw [hk', map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hc : c = a
  · subst hc; rw [hek, map_zero, map_zero]
  · rw [map_mul, map_mul, hφ', mk_b hb, if_neg (Ne.symm hc), zero_mul]

include hχe hsep hb he hd hval hinv in
theorem mk_comp_eq {φ₁ φ₂ : K →+* T} (h₁ : ∀ a, φ₁ (e a) = b a) (h₂ : ∀ a, φ₂ (e a) = b a)
    (a : ι) : (Ideal.Quotient.mk (I b a)).comp φ₁ = (Ideal.Quotient.mk (I b a)).comp φ₂ := by
  haveI := isLocalization_B hd hval hinv a
  set L := (ρ χ a).liftOfSurjective (C := T ⧸ I b a) (ρ_surjective a) with hL
  set g₁ := L ⟨(Ideal.Quotient.mk (I b a)).comp φ₁, ker_le_of_apply_e he hχe hsep hb h₁ a⟩
  set g₂ := L ⟨(Ideal.Quotient.mk (I b a)).comp φ₂, ker_le_of_apply_e he hχe hsep hb h₂ a⟩
  have hg₁ : g₁.comp (ρ χ a) = (Ideal.Quotient.mk (I b a)).comp φ₁ :=
    (ρ χ a).liftOfSurjective_comp (ρ_surjective a) _
  have hg₂ : g₂.comp (ρ χ a) = (Ideal.Quotient.mk (I b a)).comp φ₂ :=
    (ρ χ a).liftOfSurjective_comp (ρ_surjective a) _
  have hg : g₁ = g₂ :=
    IsLocalization.ringHom_ext (Submonoid.powers ((d a : ℤ))) (RingHom.ext_int _ _)
  rw [← hg₁, ← hg₂, hg]

include hχe hsep hb he hd hval hinv in
theorem eq_of_apply_e {φ₁ φ₂ : K →+* T} (h₁ : ∀ a, φ₁ (e a) = b a) (h₂ : ∀ a, φ₂ (e a) = b a) :
    φ₁ = φ₂ := by
  refine RingHom.ext fun k => πT_injective hb (funext fun a => ?_)
  rw [πT_apply, πT_apply]
  exact congrArg (fun g : K →+* T ⧸ I b a => g k)
    (mk_comp_eq he hχe hsep hd hval hinv hb h₁ h₂ a)

end

end P2mCornerHom
p2m_reactivate "P2MW.S_RingHom_existsUnique_apply_eq_of_completeOrthogonalIdempotents_of_corner_denominators.P2mCornerHom"

open P2mCornerHom in
theorem solution
    (K : Type) [CommRing K] (ι : Type) [Fintype ι] [DecidableEq ι]
    (e : ι → K) (he : CompleteOrthogonalIdempotents e)
    (χ : ι → (K →+* ℚ)) (hχe : ∀ a b : ι, χ b (e a) = if b = a then 1 else 0)
    (hsep : ∀ k k' : K, (∀ a, χ a k = χ a k') → k = k')
    (d : ι → ℕ) (hd : ∀ a, 0 < d a)
    (hval : ∀ (a : ι) (k : K), ∃ (n : ℕ) (m : ℤ), χ a k = m / (d a : ℚ) ^ n)
    (hinv : ∀ a : ι, ∃ y : K, χ a y = (d a : ℚ)⁻¹)
    (T : Type) [CommRing T] (b : ι → T) (hb : CompleteOrthogonalIdempotents b)
    (hbd : ∀ a : ι, ∃ v : T, v * ((d a : T) * b a) = b a) :
    ∃! φ : K →+* T, ∀ a, φ (e a) = b a :=
  ⟨φ hd hval hinv hb hbd, fun c => φ_e hχe hd hval hinv hb hbd c,
    fun φ' hφ' => eq_of_apply_e he hχe hsep hd hval hinv hb hφ'
      (fun c => φ_e hχe hd hval hinv hb hbd c)⟩

end S_RingHom_existsUnique_apply_eq_of_completeOrthogonalIdempotents_of_corner_denominators
end P2MW
export P2MW.S_RingHom_existsUnique_apply_eq_of_completeOrthogonalIdempotents_of_corner_denominators (solution)
