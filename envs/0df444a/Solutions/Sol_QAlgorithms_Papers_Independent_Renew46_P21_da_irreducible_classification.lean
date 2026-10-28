-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P21.da_irreducible_classification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T22:00:50.741201+00:00
-- url     : https://prove2.me/submissions/b463a32c-91b5-4fd7-aea7-deb4dfc6fde5

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P21

namespace QAlgorithms.Papers.Independent.Renew46.P21

universe u v w

section X4DA

variable {S : Type v} [Semigroup S]

theorem X4DA_mem_self (s : S) : s ∈ principalIdeal s := ⟨1, 1, by simp⟩

theorem X4DA_trans {x y z : S} (hxy : x ∈ principalIdeal y) (hyz : y ∈ principalIdeal z) :
    x ∈ principalIdeal z := by
  obtain ⟨a, b, hab⟩ := hxy
  obtain ⟨c, d, hcd⟩ := hyz
  refine ⟨a * c, d * b, ?_⟩
  rw [hab, hcd]
  simp only [mul_assoc]

theorem X4DA_pi_eq {a b : S} (h1 : a ∈ principalIdeal b) (h2 : b ∈ principalIdeal a) :
    principalIdeal a = principalIdeal b := by
  ext x
  exact ⟨fun hx => X4DA_trans hx h1, fun hx => X4DA_trans hx h2⟩

theorem X4DA_mem_right (a x : S) : a * x ∈ principalIdeal a := ⟨1, (x : WithOne S), by simp⟩

theorem X4DA_mem_left (x a : S) : x * a ∈ principalIdeal a := ⟨(x : WithOne S), 1, by simp⟩

theorem X4DA_ex_l (Y : WithOne S) (a : S) : ∃ c : S, (c : WithOne S) = (a : WithOne S) * Y := by
  cases Y with
  | one => exact ⟨a, by simp⟩
  | coe y => exact ⟨a * y, by simp⟩

theorem X4DA_ex_r (X : WithOne S) (a : S) : ∃ c : S, (c : WithOne S) = X * (a : WithOne S) := by
  cases X with
  | one => exact ⟨a, by simp⟩
  | coe y => exact ⟨y * a, by simp⟩

/-- The local monoid `eSe`. -/
abbrev X4DA_Loc (e : S) := {x : S // e * x = x ∧ x * e = x}

def X4DA_locMonoid (e : S) (he : e * e = e) : Monoid (X4DA_Loc e) where
  mul x y := ⟨x.1 * y.1, by rw [← mul_assoc, x.2.1], by rw [mul_assoc, y.2.2]⟩
  one := ⟨e, he, he⟩
  mul_assoc x y z := Subtype.ext (mul_assoc x.1 y.1 z.1)
  one_mul x := Subtype.ext x.2.1
  mul_one x := Subtype.ext x.2.2

theorem X4DA_fin_comm {N : Type*} [Monoid N] [Finite N] {a b : N} (h : a * b = 1) :
    b * a = 1 := by
  have hinj : Function.Injective (fun z : N => b * z) := by
    intro z z' hz
    simp only at hz
    have := congrArg (a * ·) hz
    simpa [← mul_assoc, h] using this
  obtain ⟨c, hc⟩ := (Finite.injective_iff_surjective.mp hinj) 1
  simp only at hc
  have hac : a = c := by
    calc a = a * (b * c) := by rw [hc, mul_one]
      _ = c := by rw [← mul_assoc, h, one_mul]
  rw [hac]; exact hc

theorem X4DA_idem_pow {N : Type*} [Monoid N] [Finite N] (c : N) :
    ∃ n : ℕ, 1 ≤ n ∧ c ^ n * c ^ n = c ^ n := by
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => c ^ (n + 1))
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm h.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  set p := j - i with hp
  have hp1 : 1 ≤ p := by omega
  have hj : j + 1 = i + 1 + p := by omega
  have hbase : ∀ k : ℕ, c ^ (i + 1 + k * p) = c ^ (i + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc c ^ (i + 1 + (k + 1) * p) = c ^ (i + 1 + p) * c ^ (k * p) := by
            rw [← pow_add]; congr 1; ring
        _ = c ^ (i + 1) * c ^ (k * p) := by rw [← hj, ← h]
        _ = c ^ (i + 1) := by rw [← pow_add, ih]
  have hgen : ∀ m k : ℕ, i + 1 ≤ m → c ^ (m + k * p) = c ^ m := by
    intro m k hm
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
    calc c ^ (i + 1 + r + k * p) = c ^ (i + 1 + k * p) * c ^ r := by
          rw [← pow_add]; congr 1; ring
      _ = c ^ (i + 1 + r) := by rw [hbase, ← pow_add]
  refine ⟨(i + 1) * p, by nlinarith, ?_⟩
  rw [← pow_add]
  exact hgen _ _ (by nlinarith)

variable [Finite S]

/-- Aperiodicity: an element of `eSe` that is `J`-above `e` equals `e`. -/
theorem X4DA_k1 (hT : OnlyTrivialSubgroups S) (e : S) (he : e * e = e) (u : S)
    (h1 : e * u = u) (h2 : u * e = u) (hmem : e ∈ principalIdeal u) : u = e := by
  letI := X4DA_locMonoid e he
  obtain ⟨X, Y, hXY⟩ := hmem
  have hee : ∀ r : WithOne S, (e : WithOne S) * (e * r) = e * r := by
    intro r; rw [← mul_assoc, ← WithOne.coe_mul, he]
  have hu1 : ∀ r : WithOne S, (e : WithOne S) * (u * r) = u * r := by
    intro r; rw [← mul_assoc, ← WithOne.coe_mul, h1]
  have hu2 : ∀ r : WithOne S, (u : WithOne S) * (e * r) = u * r := by
    intro r; rw [← mul_assoc, ← WithOne.coe_mul, h2]
  obtain ⟨x0, hx0⟩ := X4DA_ex_r X e
  obtain ⟨x, hx⟩ := X4DA_ex_l (x0 : WithOne S) e
  obtain ⟨y0, hy0⟩ := X4DA_ex_l Y e
  obtain ⟨y, hy⟩ := X4DA_ex_r (y0 : WithOne S) e
  have hxv : (x : WithOne S) = e * X * e := by rw [hx, hx0, mul_assoc]
  have hyv : (y : WithOne S) = e * Y * e := by rw [hy, hy0, mul_assoc]
  have hxl : e * x = x ∧ x * e = x := by
    constructor <;> apply WithOne.coe_injective <;> rw [WithOne.coe_mul, hxv]
    · simp only [mul_assoc, hee]
    · simp only [mul_assoc]; rw [← WithOne.coe_mul e e, he]
  have hyl : e * y = y ∧ y * e = y := by
    constructor <;> apply WithOne.coe_injective <;> rw [WithOne.coe_mul, hyv]
    · simp only [mul_assoc, hee]
    · simp only [mul_assoc]; rw [← WithOne.coe_mul e e, he]
  let xl : X4DA_Loc e := ⟨x, hxl⟩
  let yl : X4DA_Loc e := ⟨y, hyl⟩
  let ul : X4DA_Loc e := ⟨u, h1, h2⟩
  have hprod : xl * (ul * yl) = 1 := by
    apply Subtype.ext
    show x * (u * y) = e
    apply WithOne.coe_injective
    simp only [WithOne.coe_mul]
    rw [hxv, hyv]
    calc (e : WithOne S) * X * e * (u * (e * Y * e)) = e * (X * u * Y) * e := by
          simp only [mul_assoc, hu1, hu2]
      _ = e := by rw [← hXY, mul_assoc, ← WithOne.coe_mul, he, ← WithOne.coe_mul, he]
  have h3 : ul * (yl * xl) = 1 := by
    rw [← mul_assoc]; exact X4DA_fin_comm hprod
  have h4 : (yl * xl) * ul = 1 := X4DA_fin_comm h3
  have hU : IsUnit ul := isUnit_iff_exists.mpr ⟨yl * xl, h3, h4⟩
  let f : (X4DA_Loc e)ˣ →ₙ* S :=
    { toFun := fun g => g.val.val
      map_mul' := fun a b => rfl }
  have hinj : Function.Injective f := fun a b h => Units.ext (Subtype.ext h)
  have hsub := hT (X4DA_Loc e)ˣ f hinj
  obtain ⟨w, hw⟩ := hU
  have hw1 : w = 1 := Subsingleton.elim _ _
  have : ul = 1 := by rw [← hw, hw1]; rfl
  exact congrArg Subtype.val this

variable (hT : OnlyTrivialSubgroups S)
  (hreg : ∀ J : JClass S, RegularClass J → ∀ s ∈ J.val, ∀ t ∈ J.val, s * t ∈ J.val)
include hT hreg

theorem X4DA_cl {e : S} (he : e * e = e) (a b : S) (ha : principalIdeal a = principalIdeal e)
    (hb : principalIdeal b = principalIdeal e) : principalIdeal (a * b) = principalIdeal e :=
  hreg ⟨greenClass e, e, rfl⟩ ⟨e, (rfl : principalIdeal e = principalIdeal e), he⟩ a ha b hb

/-- In `DA`, for an idempotent `e`, `e ≤_J s` iff `e s e = e`. -/
theorem X4DA_mem_iff {e : S} (he : e * e = e) (s : S) :
    e ∈ principalIdeal s ↔ e * s * e = e := by
  constructor
  · rintro ⟨X, Y, hXY⟩
    obtain ⟨q0, hq0⟩ := X4DA_ex_l Y s
    obtain ⟨q, hq⟩ := X4DA_ex_l (e : WithOne S) q0
    have hqv : (q : WithOne S) = s * Y * e := by rw [hq, hq0]
    have hqe : q * e = q := by
      apply WithOne.coe_injective
      rw [WithOne.coe_mul, hqv, mul_assoc, ← WithOne.coe_mul e e, he]
    have hqPI : principalIdeal q = principalIdeal e := by
      apply X4DA_pi_eq
      · exact ⟨(s : WithOne S) * Y, 1, by rw [hqv, mul_one]⟩
      · refine ⟨X, 1, ?_⟩
        rw [mul_one, hqv]
        calc (e : WithOne S) = e * e := by rw [← WithOne.coe_mul, he]
          _ = X * (s * Y * e) := by rw [hXY]; simp only [mul_assoc]
    have heq : e * q = e := by
      have hc := X4DA_cl hT hreg he e q rfl hqPI
      refine X4DA_k1 hT e (by exact he) (e * q) (by rw [← mul_assoc, he])
        (by rw [mul_assoc, hqe]) (by rw [hc]; exact X4DA_mem_self e)
    have hesPI : principalIdeal (e * s) = principalIdeal e := by
      apply X4DA_pi_eq (X4DA_mem_right e s)
      refine ⟨1, Y * e, ?_⟩
      rw [one_mul]
      calc (e : WithOne S) = ((e * q : S) : WithOne S) := by rw [heq]
        _ = (e * s : S) * (Y * e) := by rw [WithOne.coe_mul, hqv]; simp only [WithOne.coe_mul, mul_assoc]
    have hese := X4DA_cl hT hreg he (e * s) e hesPI rfl
    exact X4DA_k1 hT e he (e * s * e) (by rw [← mul_assoc, ← mul_assoc, he])
      (by rw [mul_assoc, he]) (by rw [hese]; exact X4DA_mem_self e)
  · intro h
    exact ⟨(e : WithOne S), (e : WithOne S), by rw [← WithOne.coe_mul, ← WithOne.coe_mul, h]⟩

theorem X4DA_mul {e : S} (he : e * e = e) (s t : S) (hse : e * s * e = e)
    (hte : e * t * e = e) : e * (s * t) * e = e := by
  have hes : principalIdeal (e * s) = principalIdeal e := by
    apply X4DA_pi_eq (X4DA_mem_right e s)
    exact ⟨1, (e : WithOne S), by rw [one_mul, ← WithOne.coe_mul, hse]⟩
  have hte' : principalIdeal (t * e) = principalIdeal e := by
    apply X4DA_pi_eq (X4DA_mem_left t e)
    exact ⟨(e : WithOne S), 1, by rw [mul_one, ← WithOne.coe_mul, ← mul_assoc, hte]⟩
  have hp := X4DA_cl hT hreg he _ _ hes hte'
  have hk := X4DA_k1 hT e he (e * s * (t * e)) (by simp only [← mul_assoc, he])
    (by rw [mul_assoc, mul_assoc t, he]) (by rw [hp]; exact X4DA_mem_self e)
  calc e * (s * t) * e = e * s * (t * e) := by simp only [mul_assoc]
    _ = e := hk

theorem X4DA_mul_left {e : S} (he : e * e = e) (s t : S)
    (h : e * (s * t) * e = e) : e * s * e = e := by
  rw [← X4DA_mem_iff hT hreg he]
  exact ⟨(e : WithOne S), ((t * e : S) : WithOne S), by
    rw [← WithOne.coe_mul, ← WithOne.coe_mul]; congr 1; simpa only [mul_assoc] using h.symm⟩

theorem X4DA_mul_right {e : S} (he : e * e = e) (s t : S)
    (h : e * (s * t) * e = e) : e * t * e = e := by
  rw [← X4DA_mem_iff hT hreg he]
  exact ⟨((e * s : S) : WithOne S), (e : WithOne S), by
    rw [← WithOne.coe_mul, ← WithOne.coe_mul]; congr 1; simpa only [mul_assoc] using h.symm⟩

theorem X4DA_mem_classIdeal (J : JClass S) (g : S) (hgi : g * g = g)
    (hg : J.val = greenClass g) (s : S) : s ∈ classIdeal J ↔ g * s * g ≠ g := by
  rw [ne_eq, ← X4DA_mem_iff hT hreg hgi]
  simp only [classIdeal, Set.mem_ofPred_eq, hg]
  constructor
  · intro h hg'
    apply h
    intro t ht
    have : t ∈ principalIdeal g := by
      have ht' : principalIdeal t = principalIdeal g := ht
      rw [← ht']; exact X4DA_mem_self t
    exact X4DA_trans this hg'
  · intro h hsub
    exact h (hsub (show principalIdeal g = principalIdeal g from rfl))

theorem X4DA_sc_one {K : Type u} [CommRing K] (J : JClass S) (g : S) (hgi : g * g = g)
    (hg : J.val = greenClass g) (s : S) (h : g * s * g = g) : scalarCharacter K J s = 1 := by
  have : s ∉ classIdeal J := by rw [X4DA_mem_classIdeal hT hreg J g hgi hg]; simpa using h
  simp [scalarCharacter, this]

theorem X4DA_sc_zero {K : Type u} [CommRing K] (J : JClass S) (g : S) (hgi : g * g = g)
    (hg : J.val = greenClass g) (s : S) (h : g * s * g ≠ g) : scalarCharacter K J s = 0 := by
  have : s ∈ classIdeal J := by rw [X4DA_mem_classIdeal hT hreg J g hgi hg]; exact h
  simp [scalarCharacter, this]

omit hT hreg in
theorem X4DA_reg_rep (J : JClass S) (h : RegularClass J) :
    ∃ g : S, g * g = g ∧ J.val = greenClass g := by
  obtain ⟨g, hgJ, hgi⟩ := h
  obtain ⟨s0, hs0⟩ := J.property
  refine ⟨g, hgi, ?_⟩
  rw [hs0] at hgJ ⊢
  have hgJ' : principalIdeal g = principalIdeal s0 := hgJ
  ext t
  show principalIdeal t = principalIdeal s0 ↔ principalIdeal t = principalIdeal g
  rw [hgJ']

end X4DA

end QAlgorithms.Papers.Independent.Renew46.P21


universe u v w

open QAlgorithms.Papers.Independent.Renew46.P21 in
theorem solution {K : Type u} {S : Type v}
    [Field K] [Semigroup S] [Finite S]
    (hgroups : OnlyTrivialSubgroups S)
    (hregular : ∀ J : JClass S, RegularClass J →
      ∀ s ∈ J.val, ∀ t ∈ J.val, s * t ∈ J.val) :
    (∀ J : JClass S, RegularClass J → ∃ rho : RightSemigroupAction K S K,
      (∀ (s : S) (k : K), rho.act s k = scalarCharacter K J s * k) ∧
      SemigroupSimple rho ∧ HasApex rho J) ∧
    (∀ (M : Type w) [AddCommGroup M] [Module K M]
      (rho : RightSemigroupAction K S M), SemigroupSimple rho →
      FiniteDimensional K M ∧ Module.finrank K M = 1 ∧
        ∃! J : JClass S, HasApex rho J ∧ ScalarModel rho J) := by
  have hT := hgroups
  have hreg := hregular
  constructor
  · -- existence of the scalar models
    intro J hJreg
    obtain ⟨g, hgi, hg⟩ := X4DA_reg_rep J hJreg
    have hmul : ∀ s t : S, scalarCharacter K J (s * t) =
        scalarCharacter K J t * scalarCharacter K J s := by
      intro s t
      by_cases hs : g * s * g = g
      · by_cases ht : g * t * g = g
        · rw [X4DA_sc_one hT hreg J g hgi hg _ (X4DA_mul hT hreg hgi s t hs ht),
            X4DA_sc_one hT hreg J g hgi hg _ hs, X4DA_sc_one hT hreg J g hgi hg _ ht, one_mul]
        · rw [X4DA_sc_zero hT hreg J g hgi hg _ (fun h => ht (X4DA_mul_right hT hreg hgi s t h)),
            X4DA_sc_zero hT hreg J g hgi hg _ ht, zero_mul]
      · rw [X4DA_sc_zero hT hreg J g hgi hg _ (fun h => hs (X4DA_mul_left hT hreg hgi s t h)),
          X4DA_sc_zero hT hreg J g hgi hg _ hs, mul_zero]
    let rho : RightSemigroupAction K S K :=
      { act := fun s => scalarCharacter K J s • LinearMap.id
        mul_apply := by
          intro s t m
          simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
          rw [hmul]; ring }
    have hact : ∀ (s : S) (k : K), rho.act s k = scalarCharacter K J s * k := by
      intro s k; simp [rho]
    have hgg : g * g * g = g := by rw [hgi, hgi]
    refine ⟨rho, hact, ⟨⟨g, 1, ?_⟩, fun U _ => Ideal.eq_bot_or_top U⟩, ?_, ?_⟩
    · rw [hact, X4DA_sc_one hT hreg J g hgi hg _ hgg]; simp
    · exact ⟨g, by rw [hg]; exact (rfl : principalIdeal g = principalIdeal g), hgi⟩
    · ext s
      simp only [semigroupAnnihilator, Set.mem_ofPred_eq]
      simp only [hact]
      rw [X4DA_mem_classIdeal hT hreg J g hgi hg]
      constructor
      · intro h hs
        have := h 1
        rw [X4DA_sc_one hT hreg J g hgi hg _ hs] at this
        simp at this
      · intro hs m
        rw [X4DA_sc_zero hT hreg J g hgi hg _ hs, zero_mul]
  · intro M _ _ rho hsimple
    obtain ⟨⟨s0, m0, hs0⟩, hirr⟩ := hsimple
    set A := rho.act with hA
    have hmulA : ∀ (s t : S) (m : M), A (s * t) m = A t (A s m) := rho.mul_apply
    -- choose a non-annihilating element with minimal principal ideal
    have hex : ∃ n : ℕ, ∃ s : S, A s ≠ 0 ∧ (principalIdeal s).ncard = n :=
      ⟨_, s0, fun h => hs0 (by rw [h]; rfl), rfl⟩
    classical
    obtain ⟨s, hs0', hsn⟩ := Nat.find_spec hex
    have hmin : ∀ t : S, A t ≠ 0 → Nat.find hex ≤ (principalIdeal t).ncard :=
      fun t ht => Nat.find_min' hex ⟨t, ht, rfl⟩
    have hminPI : ∀ t : S, t ∈ principalIdeal s → A t ≠ 0 →
        principalIdeal t = principalIdeal s := by
      intro t hts ht
      have hsub : principalIdeal t ⊆ principalIdeal s := fun x hx => X4DA_trans hx hts
      exact Set.eq_of_subset_of_ncard_le hsub (by rw [hsn]; exact hmin _ ht)
    -- the submodule killed by every `x s`
    let U0 : Submodule K M := LinearMap.ker (A s) ⊓ ⨅ t : S, LinearMap.ker (A s ∘ₗ A t)
    have hmemU0 : ∀ m, m ∈ U0 ↔ A s m = 0 ∧ ∀ t, A s (A t m) = 0 := by
      intro m
      simp [U0, Submodule.mem_iInf]
    have hU0inv : SemigroupInvariant rho U0 := by
      intro r m hm
      rw [hmemU0] at hm ⊢
      refine ⟨hm.2 r, fun t => ?_⟩
      rw [← hmulA r t]; exact hm.2 _
    have hU0 : U0 = ⊥ := by
      rcases hirr U0 hU0inv with h | h
      · exact h
      · exfalso
        apply hs0'
        apply LinearMap.ext
        intro m
        have : m ∈ U0 := by rw [h]; trivial
        exact ((hmemU0 m).mp this).1
    obtain ⟨m1, hm1⟩ : ∃ m, A s m ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hs0' (LinearMap.ext h)
    have hvU : ¬ (A s m1 ∈ U0) := by
      rw [hU0, Submodule.mem_bot]; exact hm1
    -- find `b = x s` with `A (s b) ≠ 0`
    obtain ⟨b, ⟨xb, hxb⟩, hAsb⟩ : ∃ b : S, (∃ x : WithOne S, (b : WithOne S) = x * s) ∧
        A (s * b) ≠ 0 := by
      rw [hmemU0] at hvU
      by_cases h : A s (A s m1) = 0
      · have : ∃ t, A s (A t (A s m1)) ≠ 0 := by
          by_contra h'
          push_neg at h'
          exact hvU ⟨h, h'⟩
        obtain ⟨t, ht⟩ := this
        refine ⟨t * s, ⟨(t : WithOne S), by simp⟩, fun h0 => ht ?_⟩
        have := congrArg (fun L => L m1) h0
        simp only [LinearMap.zero_apply] at this
        rw [← this, hmulA, hmulA]
      · refine ⟨s, ⟨1, by simp⟩, fun h0 => h ?_⟩
        have := congrArg (fun L => L m1) h0
        simp only [LinearMap.zero_apply] at this
        rw [← this, hmulA]
    have hsb : principalIdeal (s * b) = principalIdeal s :=
      hminPI (s * b) (X4DA_mem_right s b) hAsb
    have hsmem : s ∈ principalIdeal (s * b) := by rw [hsb]; exact X4DA_mem_self s
    obtain ⟨X, Y, hXY⟩ := hsmem
    obtain ⟨c, hc⟩ := X4DA_ex_l Y b
    have hXc : (s : WithOne S) = X * s * c := by
      rw [hc]
      calc (s : WithOne S) = X * ↑(s * b) * Y := hXY
        _ = X * s * (b * Y) := by rw [WithOne.coe_mul]; simp only [mul_assoc]
    have hpow : ∀ n : ℕ, (s : WithOne S) = X ^ n * s * (c : WithOne S) ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc (s : WithOne S) = X ^ n * s * (c : WithOne S) ^ n := ih
          _ = X ^ n * (X * s * c) * (c : WithOne S) ^ n := by rw [← hXc]
          _ = X ^ (n + 1) * s * (c : WithOne S) ^ (n + 1) := by
            rw [pow_succ X n, pow_succ' (c : WithOne S) n]; simp only [mul_assoc]
    haveI : Finite (WithOne S) := inferInstanceAs (Finite (Option S))
    obtain ⟨n, hn1, hnid⟩ := X4DA_idem_pow (c : WithOne S)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hfex : ∀ k : ℕ, ∃ f : S, (f : WithOne S) = (c : WithOne S) ^ (k + 1) := by
      intro k
      induction k with
      | zero => exact ⟨c, by simp⟩
      | succ k ih =>
        obtain ⟨f, hf⟩ := ih
        exact ⟨f * c, by rw [pow_succ, ← hf, WithOne.coe_mul]⟩
    obtain ⟨e, hev⟩ := hfex k
    have he : e * e = e := by
      apply WithOne.coe_injective
      rw [WithOne.coe_mul, hev, hnid]
    have hse : s * e = s := by
      apply WithOne.coe_injective
      rw [WithOne.coe_mul, hev]
      calc (s : WithOne S) * (c : WithOne S) ^ (k + 1)
          = X ^ (k + 1) * s * ((c : WithOne S) ^ (k + 1) * (c : WithOne S) ^ (k + 1)) := by
            conv_lhs => rw [hpow (k + 1)]
            simp only [mul_assoc]
        _ = s := by rw [hnid, ← hpow]
    have he0 : A e ≠ 0 := by
      intro h0
      apply hs0'
      apply LinearMap.ext
      intro m
      rw [← hse, hmulA, h0]; rfl
    have hemem : e ∈ principalIdeal s := by
      refine ⟨xb, Y * (c : WithOne S) ^ k, ?_⟩
      rw [hev, pow_succ', hc, hxb]
      simp only [mul_assoc]
    have hePI : principalIdeal e = principalIdeal s := hminPI e hemem he0
    have hen : (principalIdeal e).ncard = Nat.find hex := by rw [hePI, hsn]
    -- dichotomy
    have hdich : ∀ s : S, A (e * s * e) = 0 ∨ e * s * e = e := by
      intro s
      by_cases h : A (e * s * e) = 0
      · exact Or.inl h
      · right
        have hsub : principalIdeal (e * s * e) ⊆ principalIdeal e := by
          intro x hx
          exact X4DA_trans hx ⟨1, ((s * e : S) : WithOne S), by
            rw [one_mul, ← WithOne.coe_mul, mul_assoc]⟩
        have heq : principalIdeal (e * s * e) = principalIdeal e :=
          Set.eq_of_subset_of_ncard_le hsub (by rw [hen]; exact hmin _ h)
        have hmem : e ∈ principalIdeal (e * s * e) := by rw [heq]; exact X4DA_mem_self e
        exact X4DA_k1 hT e he (e * s * e) (by rw [← mul_assoc, ← mul_assoc, he])
          (by rw [mul_assoc, he]) hmem
    obtain ⟨m2, hm2⟩ : ∃ m, A e m ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact he0 (LinearMap.ext h)
    set v := A e m2 with hvdef
    have hv0 : v ≠ 0 := hm2
    have hve : A e v = v := by rw [hvdef, ← hmulA, he]
    have hleft : ∀ x : S, A x v = A (e * x) v := by
      intro x; rw [hmulA, hve]
    set J : JClass S := ⟨greenClass e, e, rfl⟩ with hJ
    have hJg : J.val = greenClass e := rfl
    -- the submodule U
    let U : Submodule K M := LinearMap.ker (A e) ⊓ ⨅ t : S, LinearMap.ker (A e ∘ₗ A t)
    have hmemU : ∀ m, m ∈ U ↔ A e m = 0 ∧ ∀ t, A e (A t m) = 0 := by
      intro m
      simp [U, Submodule.mem_iInf]
    have hUinv : SemigroupInvariant rho U := by
      intro s m hm
      rw [hmemU] at hm ⊢
      refine ⟨hm.2 s, fun t => ?_⟩
      rw [← hmulA s t]; exact hm.2 _
    have hU : U = ⊥ := by
      rcases hirr U hUinv with h | h
      · exact h
      · exfalso
        have : v ∈ U := by rw [h]; trivial
        rw [hmemU] at this
        exact hv0 (by rw [← hve]; exact this.1)
    have hAe : ∀ x : S, A e (A x v) = A (e * x * e) v := by
      intro x
      rw [← hmulA x e, hleft (x * e)]; simp only [mul_assoc]
    -- Claim A
    have hclaim : ∀ s : S, A s v = scalarCharacter K J s • v := by
      intro s
      have hw : A s v - scalarCharacter K J s • v ∈ U := by
        rw [hmemU]
        by_cases hs : e * s * e = e
        · rw [X4DA_sc_one hT hreg J e he hJg _ hs, one_smul]
          refine ⟨?_, fun t => ?_⟩
          · rw [map_sub, hAe s, hs, hve, sub_self]
          · rw [map_sub, map_sub, ← hmulA s t, hAe (s * t), hAe t]
            by_cases hst : e * (s * t) * e = e
            · rw [hst, X4DA_mul_right hT hreg he s t hst, sub_self]
            · have hte : e * t * e ≠ e := fun h => hst (X4DA_mul hT hreg he s t hs h)
              rcases hdich (s * t) with h1 | h1
              · rcases hdich t with h2 | h2
                · rw [h1, h2]; simp
                · exact absurd h2 hte
              · exact absurd h1 hst
        · rw [X4DA_sc_zero hT hreg J e he hJg _ hs, zero_smul, sub_zero]
          refine ⟨?_, fun t => ?_⟩
          · rw [hAe s]
            rcases hdich s with h1 | h1
            · rw [h1]; rfl
            · exact absurd h1 hs
          · rw [← hmulA s t, hAe (s * t)]
            rcases hdich (s * t) with h1 | h1
            · rw [h1]; rfl
            · exact absurd (X4DA_mul_left hT hreg he s t h1) hs
      rw [hU, Submodule.mem_bot, sub_eq_zero] at hw
      exact hw
    -- span
    have hspan : Submodule.span K {v} = ⊤ := by
      rcases hirr (Submodule.span K {v}) (by
        intro s m hm
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
        rw [map_smul, hclaim, smul_smul]
        exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩) with h | h
      · exfalso
        have : v ∈ Submodule.span K {v} := Submodule.mem_span_singleton_self v
        rw [h, Submodule.mem_bot] at this
        exact hv0 this
      · exact h
    have hall : ∀ (s : S) (m : M), A s m = scalarCharacter K J s • m := by
      intro s m
      have hm : m ∈ Submodule.span K {v} := by rw [hspan]; trivial
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
      rw [map_smul, hclaim, smul_smul, smul_smul, mul_comm]
    have hrank : Module.finrank K M = 1 := by
      rw [← finrank_top K M, ← hspan, finrank_span_singleton hv0]
    have hfin : FiniteDimensional K M := Module.finite_of_finrank_eq_succ hrank
    have hann : semigroupAnnihilator rho = classIdeal J := by
      ext s
      simp only [semigroupAnnihilator, Set.mem_ofPred_eq]
      rw [X4DA_mem_classIdeal hT hreg J e he hJg]
      constructor
      · intro h hs
        have := h v
        rw [← hA, hall, X4DA_sc_one hT hreg J e he hJg _ hs, one_smul] at this
        exact hv0 this
      · intro hs m
        rw [← hA, hall, X4DA_sc_zero hT hreg J e he hJg _ hs, zero_smul]
    have hapex : HasApex rho J := ⟨⟨e, (rfl : principalIdeal e = principalIdeal e), he⟩, hann⟩
    refine ⟨hfin, hrank, J, ⟨hapex, ?_⟩, ?_⟩
    · let g : K ≃ₗ[K] M := (LinearEquiv.toSpanNonzeroSingleton K M v hv0).trans
        (LinearEquiv.ofTop _ hspan)
      have hg : ∀ c : K, g c = c • v := fun c => rfl
      refine ⟨g.symm, fun s m => ?_⟩
      conv_lhs => rw [← g.apply_symm_apply m, hg]
      rw [← hA, hall, smul_smul, ← hg, LinearEquiv.symm_apply_apply]
    · rintro J' ⟨⟨hJ'reg, hJ'⟩, _⟩
      obtain ⟨g', hgi', hg'⟩ := X4DA_reg_rep J' hJ'reg
      have hiff : ∀ s : S, g' * s * g' ≠ g' ↔ e * s * e ≠ e := by
        intro s
        rw [← X4DA_mem_classIdeal hT hreg J' g' hgi' hg', ← X4DA_mem_classIdeal hT hreg J e he hJg,
          ← hJ', hann]
      have h1 : e * g' * e = e := by
        by_contra h
        exact ((hiff g').mpr h) (by rw [hgi', hgi'])
      have h2 : g' * e * g' = g' := by
        by_contra h
        exact ((hiff e).mp h) (by rw [he, he])
      rw [← X4DA_mem_iff hT hreg he] at h1
      rw [← X4DA_mem_iff hT hreg hgi'] at h2
      apply Subtype.ext
      rw [hg', hJg]
      have hPI : principalIdeal g' = principalIdeal e := by
        ext x; exact ⟨fun hx => X4DA_trans hx h2, fun hx => X4DA_trans hx h1⟩
      simp only [greenClass, hPI]
