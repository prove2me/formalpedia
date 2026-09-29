-- Prove2me | solution 1 for UniqueFactorizationMonoid.exists_forall_mul_eq_of_cocycle_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/4eda8235-1a9e-5049-be17-1a8fb2ed4d08

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UniqueFactorizationMonoid_exists_forall_mul_eq_of_cocycle_of_injective

set_option autoImplicit false

open UniqueFactorizationMonoid

namespace P1ACocycle

variable {B : Type*} [CommRing B] [IsDomain B] [NormalizationMonoid B] [UniqueFactorizationMonoid B]
variable [DecidableEq B]

noncomputable def ν (p x : B) : ℤ := ((normalizedFactors x).count p : ℤ)

lemma ν_mul (p : B) {x y : B} (hx : x ≠ 0) (hy : y ≠ 0) :
    ν p (x * y) = ν p x + ν p y := by
  simp [ν, normalizedFactors_mul hx hy, Multiset.count_add]

lemma ν_pow (p : B) (x : B) (n : ℕ) : ν p (x ^ n) = n * ν p x := by
  simp [ν, normalizedFactors_pow, Multiset.count_nsmul]

lemma ν_eq_zero_of_not_mem {p x : B} (h : p ∉ normalizedFactors x) : ν p x = 0 := by
  simp [ν, Multiset.count_eq_zero.mpr h]

lemma ν_eq_zero_of_dvd_pow {p x c : B} {M : ℕ} (hx : x ≠ 0) (hc : c ≠ 0)
    (hdvd : x ∣ c ^ M) (hp : p ∉ normalizedFactors c) : ν p x = 0 := by
  have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hx (pow_ne_zero M hc)).mp hdvd
  have := Multiset.le_iff_count.mp hle p
  rw [normalizedFactors_pow, Multiset.count_nsmul, Multiset.count_eq_zero.mpr hp, mul_zero] at this
  simp [ν, Nat.le_zero.mp this]

lemma normalizedFactors_finset_prod (S : Finset B) (g : B → B) (hg : ∀ p ∈ S, g p ≠ 0) :
    normalizedFactors (∏ p ∈ S, g p) = ∑ p ∈ S, normalizedFactors (g p) := by
  induction S using Finset.induction_on with
  | empty => simp [normalizedFactors_one]
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      normalizedFactors_mul (hg a (Finset.mem_insert_self a S))
        (Finset.prod_ne_zero_iff.mpr fun p hp => hg p (Finset.mem_insert_of_mem hp)),
      ih fun p hp => hg p (Finset.mem_insert_of_mem hp)]

lemma ν_prod_pow (s : B) (k : B → ℕ) (q : B) :
    ν q (∏ p ∈ (normalizedFactors s).toFinset, p ^ k p) =
      if q ∈ (normalizedFactors s).toFinset then (k q : ℤ) else 0 := by
  have hne : ∀ p ∈ (normalizedFactors s).toFinset, p ^ k p ≠ 0 := fun p hp =>
    pow_ne_zero _ (irreducible_of_normalized_factor p (Multiset.mem_toFinset.mp hp)).ne_zero
  have hterm : ∀ p ∈ (normalizedFactors s).toFinset,
      Multiset.count q (normalizedFactors (p ^ k p)) = if q = p then k p else 0 := by
    intro p hp
    have hp' := Multiset.mem_toFinset.mp hp
    rw [normalizedFactors_pow, Multiset.count_nsmul,
      normalizedFactors_irreducible (irreducible_of_normalized_factor p hp'),
      normalize_normalized_factor p hp', Multiset.count_singleton]
    split_ifs <;> simp
  unfold ν
  rw [normalizedFactors_finset_prod _ _ hne, Multiset.count_sum', Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq]
  split_ifs <;> simp

lemma exists_mul_pow_eq {K : Type*} [Field K] (φ : B →+* K) (hφ : Function.Injective φ)
    {X Y c : B} (hX : X ≠ 0) (hY : Y ≠ 0) (hc : c ≠ 0)
    (H : ∀ p, p ∉ normalizedFactors c → ν p Y ≤ ν p X) :
    ∃ (n : ℕ) (W : B), φ X / φ Y * φ c ^ n = φ W := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = Multiset.card (normalizedFactors Y) := ⟨_, rfl⟩
  have hdvd : Y ∣ X * c ^ n := by
    rw [dvd_iff_normalizedFactors_le_normalizedFactors hY (mul_ne_zero hX (pow_ne_zero n hc)),
      normalizedFactors_mul hX (pow_ne_zero n hc), normalizedFactors_pow, Multiset.le_iff_count]
    intro p
    rw [Multiset.count_add, Multiset.count_nsmul]
    by_cases hp : p ∈ normalizedFactors c
    · calc Multiset.count p (normalizedFactors Y) ≤ n := hn ▸ Multiset.count_le_card p _
        _ ≤ n * Multiset.count p (normalizedFactors c) :=
            Nat.le_mul_of_pos_right n (Multiset.count_pos.mpr hp)
        _ ≤ _ := Nat.le_add_left _ _
    · have := H p hp
      simp only [ν, Nat.cast_le] at this
      exact this.trans (Nat.le_add_right _ _)
  obtain ⟨W, hW⟩ := hdvd
  refine ⟨n, W, ?_⟩
  have hY' : φ Y ≠ 0 := (map_ne_zero_iff φ hφ).mpr hY
  rw [div_mul_eq_mul_div, ← map_pow, ← map_mul, hW, map_mul, mul_div_cancel_left₀ _ hY']

end P1ACocycle

open P1ACocycle in
theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
    {K : Type*} [Field K] (φ : B →+* K) (hφ : Function.Injective φ)
    {ι : Type*} (b : ι → B) (u : ι → ι → K)
    (hreg : ∀ i j, b i ≠ 0 → b j ≠ 0 → ∃ (n : ℕ) (x : B), u i j * φ (b i * b j) ^ n = φ x)
    (hrefl : ∀ i, b i ≠ 0 → u i i = 1)
    (hcocycle : ∀ i j k, b i ≠ 0 → b j ≠ 0 → b k ≠ 0 → u i j * u j k = u i k) :
    ∃ h : ι → K, (∀ i, b i ≠ 0 →
        h i ≠ 0 ∧ (∃ (n : ℕ) (x : B), h i * φ (b i) ^ n = φ x) ∧
          (∃ (n : ℕ) (y : B), (h i)⁻¹ * φ (b i) ^ n = φ y)) ∧
      ∀ i j, b i ≠ 0 → b j ≠ 0 → u i j * h j = h i := by
  classical
  by_cases hJ : ∃ i₀, b i₀ ≠ 0
  swap
  · exact ⟨fun _ => 1, fun i hi => absurd hi (not_exists.mp hJ i),
      fun i j hi _ => absurd hi (not_exists.mp hJ i)⟩
  obtain ⟨i₀, hs⟩ := hJ
  letI : NormalizationMonoid B := UniqueFactorizationMonoid.strongNormalizationMonoid.toNormalizationMonoid
  have hφ0 : ∀ {x : B}, x ≠ 0 → φ x ≠ 0 := fun hx => (map_ne_zero_iff φ hφ).mpr hx

  have hunit : ∀ i j, b i ≠ 0 → b j ≠ 0 → u i j * u j i = 1 := fun i j hi hj => by
    rw [hcocycle i j i hi hj hi, hrefl i hi]
  have hu0 : ∀ i j, b i ≠ 0 → b j ≠ 0 → u i j ≠ 0 := fun i j hi hj h0 => by
    have := hunit i j hi hj
    rw [h0, zero_mul] at this
    exact zero_ne_one this

  have rep : ∀ j, ∃ (n : ℕ) (x : B), b j ≠ 0 → u j i₀ * φ (b j * b i₀) ^ n = φ x := by
    intro j
    by_cases hj : b j ≠ 0
    · obtain ⟨n, x, h⟩ := hreg j i₀ hj hs
      exact ⟨n, x, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose N X hNX using rep

  have hXdvd : ∀ j, b j ≠ 0 → X j ≠ 0 ∧ ∃ M : ℕ, X j ∣ (b j * b i₀) ^ M := by
    intro j hj
    obtain ⟨n', x', h'⟩ := hreg i₀ j hs hj
    have key : X j * x' = (b j * b i₀) ^ (N j + n') := by
      apply hφ
      rw [map_mul, ← hNX j hj, ← h']
      simp only [map_pow, map_mul]
      linear_combination ((φ (b j) * φ (b i₀)) ^ (N j + n')) * hunit j i₀ hj hs
    refine ⟨fun h0 => ?_, N j + n', ⟨x', key.symm⟩⟩
    rw [h0, zero_mul] at key
    exact pow_ne_zero _ (mul_ne_zero hj hs) key.symm

  obtain ⟨c, hc_def⟩ : ∃ c : ι → B → ℤ, ∀ j p, c j p = ν p (X j) - N j * ν p (b j * b i₀) :=
    ⟨fun j p => ν p (X j) - N j * ν p (b j * b i₀), fun _ _ => rfl⟩

  have hc : ∀ j j' p, b j ≠ 0 → b j' ≠ 0 → p ∉ normalizedFactors (b j) →
      p ∉ normalizedFactors (b j') → c j p = c j' p := by
    intro j j' p hj hj' hpj hpj'
    obtain ⟨m, w, hw⟩ := hreg j j' hj hj'
    obtain ⟨m', w', hw'⟩ := hreg j' j hj' hj
    have hww' : w * w' = (b j * b j') ^ (m + m') := by
      apply hφ
      rw [map_mul, ← hw, ← hw']
      simp only [map_pow, map_mul]
      linear_combination ((φ (b j) * φ (b j')) ^ (m + m')) * hunit j j' hj hj'
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hww'
      exact pow_ne_zero _ (mul_ne_zero hj hj') hww'.symm
    have hνw : ν p w = 0 := by
      refine ν_eq_zero_of_dvd_pow hw0 (mul_ne_zero hj hj') ⟨w', hww'.symm⟩ ?_
      rw [normalizedFactors_mul hj hj', Multiset.mem_add]
      exact fun h => h.elim hpj hpj'
    have hX0 := (hXdvd j hj).1
    have hX0' := (hXdvd j' hj').1
    have key : w * X j' * (b j * b i₀) ^ N j = X j * (b j * b j') ^ m * (b j' * b i₀) ^ N j' := by
      apply hφ
      simp only [map_pow, map_mul]
      rw [← hw, ← hNX j' hj', ← hNX j hj, ← hcocycle j j' i₀ hj hj' hs]
      simp only [map_pow, map_mul]
      ring
    have hν := congrArg (ν p) key
    simp only [ν_mul p (mul_ne_zero hw0 hX0') (pow_ne_zero _ (mul_ne_zero hj hs)), ν_mul p hw0 hX0',
      ν_mul p (mul_ne_zero hX0 (pow_ne_zero _ (mul_ne_zero hj hj'))) (pow_ne_zero _ (mul_ne_zero hj' hs)),
      ν_mul p hX0 (pow_ne_zero _ (mul_ne_zero hj hj')), ν_pow,
      ν_mul p hj hs, ν_mul p hj hj', ν_mul p hj' hs, hνw,
      ν_eq_zero_of_not_mem hpj, ν_eq_zero_of_not_mem hpj'] at hν
    rw [hc_def, hc_def, ν_mul p hj hs, ν_mul p hj' hs, ν_eq_zero_of_not_mem hpj,
      ν_eq_zero_of_not_mem hpj']
    linarith

  obtain ⟨e, he_def⟩ : ∃ e : B → ℤ, ∀ p, e p =
      if h : ∃ j, b j ≠ 0 ∧ p ∉ normalizedFactors (b j) then c (Classical.choose h) p else 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨F₁, hF₁_def⟩ : ∃ F₁ : B,
      F₁ = ∏ p ∈ (normalizedFactors (b i₀)).toFinset, p ^ (-e p).toNat := ⟨_, rfl⟩
  obtain ⟨F₂, hF₂_def⟩ : ∃ F₂ : B,
      F₂ = ∏ p ∈ (normalizedFactors (b i₀)).toFinset, p ^ (e p).toNat := ⟨_, rfl⟩
  have hF₁0 : F₁ ≠ 0 := hF₁_def ▸ Finset.prod_ne_zero_iff.mpr fun p hp =>
    pow_ne_zero _ (irreducible_of_normalized_factor p (Multiset.mem_toFinset.mp hp)).ne_zero
  have hF₂0 : F₂ ≠ 0 := hF₂_def ▸ Finset.prod_ne_zero_iff.mpr fun p hp =>
    pow_ne_zero _ (irreducible_of_normalized_factor p (Multiset.mem_toFinset.mp hp)).ne_zero
  have hνF₁ : ∀ q, ν q F₁ =
      if q ∈ (normalizedFactors (b i₀)).toFinset then (((-e q).toNat : ℕ) : ℤ) else 0 :=
    fun q => by rw [hF₁_def]; exact ν_prod_pow (b i₀) (fun p => (-e p).toNat) q
  have hνF₂ : ∀ q, ν q F₂ =
      if q ∈ (normalizedFactors (b i₀)).toFinset then (((e q).toNat : ℕ) : ℤ) else 0 :=
    fun q => by rw [hF₂_def]; exact ν_prod_pow (b i₀) (fun p => (e p).toNat) q

  have hmain : ∀ j, b j ≠ 0 → ∀ p, p ∉ normalizedFactors (b j) →
      ν p (X j * F₁) = ν p ((b j * b i₀) ^ N j * F₂) := by
    intro j hj p hpj
    obtain ⟨hX0, M, hM⟩ := hXdvd j hj
    rw [ν_mul p hX0 hF₁0, ν_mul p (pow_ne_zero _ (mul_ne_zero hj hs)) hF₂0, ν_pow, hνF₁, hνF₂]
    by_cases hps : p ∈ normalizedFactors (b i₀)
    · have hpP : p ∈ (normalizedFactors (b i₀)).toFinset := Multiset.mem_toFinset.mpr hps
      rw [if_pos hpP, if_pos hpP]
      have hex : ∃ j, b j ≠ 0 ∧ p ∉ normalizedFactors (b j) := ⟨j, hj, hpj⟩
      have he : e p = c j p := by
        rw [he_def, dif_pos hex]
        exact hc _ _ p (Classical.choose_spec hex).1 hj (Classical.choose_spec hex).2 hpj
      have ht := (e p).toNat_sub_toNat_neg
      rw [hc_def] at he
      linarith
    · have hpP : p ∉ (normalizedFactors (b i₀)).toFinset :=
        fun h => hps (Multiset.mem_toFinset.mp h)
      rw [if_neg hpP, if_neg hpP, ν_mul p hj hs, ν_eq_zero_of_not_mem hpj,
        ν_eq_zero_of_not_mem hps]
      have hX : ν p (X j) = 0 :=
        ν_eq_zero_of_dvd_pow hX0 (mul_ne_zero hj hs) hM (by
          rw [normalizedFactors_mul hj hs, Multiset.mem_add]
          exact fun h => h.elim hpj hps)
      rw [hX]
      ring

  refine ⟨fun j => u j i₀ * (φ F₁ / φ F₂), fun j hj => ?_, fun i j hi hj => ?_⟩
  · dsimp only
    obtain ⟨hX0, -⟩ := hXdvd j hj
    have hY0 : (b j * b i₀) ^ N j * F₂ ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (mul_ne_zero hj hs)) hF₂0
    have hrepr : u j i₀ * (φ F₁ / φ F₂) = φ (X j * F₁) / φ ((b j * b i₀) ^ N j * F₂) := by
      have hu : u j i₀ = φ (X j) / φ ((b j * b i₀) ^ N j) := by
        rw [eq_div_iff (hφ0 (pow_ne_zero _ (mul_ne_zero hj hs))), ← hNX j hj, map_pow]
      rw [hu, map_mul, map_mul, div_mul_div_comm]
    refine ⟨mul_ne_zero (hu0 j i₀ hj hs) (div_ne_zero (hφ0 hF₁0) (hφ0 hF₂0)), ?_, ?_⟩
    · rw [hrepr]
      exact exists_mul_pow_eq φ hφ (mul_ne_zero hX0 hF₁0) hY0 hj
        fun p hp => (hmain j hj p hp).ge
    · rw [hrepr, inv_div]
      exact exists_mul_pow_eq φ hφ hY0 (mul_ne_zero hX0 hF₁0) hj
        fun p hp => (hmain j hj p hp).le
  · rw [← mul_assoc, hcocycle i j i₀ hi hj hs]

end S_UniqueFactorizationMonoid_exists_forall_mul_eq_of_cocycle_of_injective
end P2MW
export P2MW.S_UniqueFactorizationMonoid_exists_forall_mul_eq_of_cocycle_of_injective (solution)
