-- Prove2me | solution 1 for PrivPCP.lemma_5_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:09:08.139028+00:00
-- url     : https://prove2.me/submissions/3c77e5e2-9e5d-4b7a-b11b-36823f3bb382
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_PrivPCP_primes_Ioc_three
import Theorems.Thm_PrivPCP_linnik_xylouris


namespace PrivPCP.L54

/-- Hall selection: if every set has at least `k` elements, pick distinct representatives -/
lemma hall_select (k : ℕ) (I : Fin k → Finset ℕ) (hI : ∀ i, k ≤ (I i).card) :
    ∃ f : Fin k → ℕ, Function.Injective f ∧ ∀ i, f i ∈ I i := by
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective I).1
  intro s
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp
  · calc s.card ≤ k := by simpa using Finset.card_le_univ s
      _ ≤ (I i).card := hI i
      _ ≤ (s.biUnion I).card := Finset.card_le_card (Finset.subset_biUnion_of_mem I hi)

lemma coprime_of_distinct {k : ℕ} (b h : Fin k → ℕ) (hb : ∀ i, (b i).Prime) (hh : ∀ i, (h i).Prime)
    (hbi : Function.Injective b) (hhi : Function.Injective h) (hbh : ∀ i j, b i ≠ h j) :
    ∀ i j, i ≠ j → Nat.Coprime (b i * h i) (b j * h j) := by
  intro i j hij
  have cp : ∀ p r : ℕ, p.Prime → r.Prime → p ≠ r → Nat.Coprime p r :=
    fun p r hp hr hpr => (Nat.coprime_primes hp hr).2 hpr
  apply Nat.Coprime.mul
  · apply Nat.Coprime.mul_right
    · exact cp _ _ (hb i) (hb j) (fun e => hij (hbi e))
    · exact cp _ _ (hb i) (hh j) (hbh i j)
  · apply Nat.Coprime.mul_right
    · exact cp _ _ (hh i) (hb j) (fun e => hbh j i e.symm)
    · exact cp _ _ (hh i) (hh j) (fun e => hij (hhi e))

lemma card_zpowers_pow {G : Type} [Group G] (g : G) (m d : ℕ) (hg : orderOf g = m) (hd : d ∣ m)
    (hm : 0 < m) : Nat.card (Subgroup.zpowers (g ^ (m / d))) = d := by
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hm
  have hmd : m / d ∣ orderOf g := by rw [hg]; exact Nat.div_dvd_of_dvd hd
  have hmd0 : m / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hm hd) hd0).ne'
  rw [Nat.card_zpowers, orderOf_pow_of_dvd hmd0 hmd, hg, Nat.div_div_self hd hm.ne']

/-- subgroups of the multiplicative group of `𝔽_q` -/
theorem group_part (q : ℕ) [Fact q.Prime] (k : ℕ) (s h : Fin k → ℕ) (hdiv : ∀ i, h i ∣ s i)
    (hsq : ∀ i, s i ∣ q - 1) (hlt : ∀ i, s i < q - 1) :
    ∃ (S Γ : Fin k → Subgroup (ZMod q)ˣ) (ζ : Fin k → (ZMod q)ˣ),
      (∀ i, Nat.card (S i) = s i ∧ Nat.card (Γ i) = h i ∧ Γ i ≤ S i) ∧
      (∀ i, ∀ γ ∈ Γ i, ζ i * γ ∉ S i) ∧
      (∀ i, ∀ γ ∈ Γ i, ∀ x : (ZMod q)ˣ,
        ((∃ γ' ∈ Γ i, x = ζ i * γ') → ∃ γ' ∈ Γ i, γ * x = ζ i * γ') ∧ (x ∈ S i → γ * x ∈ S i)) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
  have hcard : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hog : orderOf g = q - 1 := by rw [← hcard]; exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hq1 : 0 < q - 1 := by have := (Fact.out : q.Prime).two_le; omega
  have hhq : ∀ i, h i ∣ q - 1 := fun i => (hdiv i).trans (hsq i)
  have hdm : ∀ i, (q - 1) / h i = (q - 1) / s i * (s i / h i) := by
    intro i
    obtain ⟨a, ha⟩ := hsq i
    obtain ⟨c, hc⟩ := hdiv i
    have hh0 : 0 < h i := by
      rcases Nat.eq_zero_or_pos (h i) with h0 | h0
      · rw [h0, zero_mul] at hc; rw [hc, zero_mul] at ha; omega
      · exact h0
    have hs0 : 0 < s i := by rw [hc]; exact Nat.mul_pos hh0 (by
      rcases Nat.eq_zero_or_pos c with c0 | c0
      · rw [c0, mul_zero] at hc; rw [hc, zero_mul] at ha; omega
      · exact c0)
    rw [ha, hc, Nat.mul_div_cancel_left _ (Nat.mul_pos hh0 (Nat.pos_of_ne_zero (by
      rintro rfl; simp at hs0 hc; omega))), Nat.mul_div_cancel_left _ hh0, mul_assoc,
      Nat.mul_div_cancel_left _ hh0, mul_comm]
  have hle : ∀ i, Subgroup.zpowers (g ^ ((q - 1) / h i)) ≤ Subgroup.zpowers (g ^ ((q - 1) / s i)) := by
    intro i
    rw [Subgroup.zpowers_le, hdm i, pow_mul]
    exact Subgroup.npow_mem_zpowers _ _
  refine ⟨fun i => Subgroup.zpowers (g ^ ((q - 1) / s i)),
    fun i => Subgroup.zpowers (g ^ ((q - 1) / h i)), fun _ => g, ?_, ?_, ?_⟩
  · intro i
    exact ⟨card_zpowers_pow g _ _ hog (hsq i) hq1, card_zpowers_pow g _ _ hog (hhq i) hq1, hle i⟩
  · intro i γ hγ hmem
    have hγS := hle i hγ
    have hgS : g ∈ Subgroup.zpowers (g ^ ((q - 1) / s i)) :=
      (Subgroup.mul_mem_cancel_right _ hγS).1 hmem
    have hle' : Subgroup.zpowers g ≤ Subgroup.zpowers (g ^ ((q - 1) / s i)) :=
      (Subgroup.zpowers_le).2 hgS
    have := Subgroup.card_le_of_le hle'
    rw [Nat.card_zpowers, hog, card_zpowers_pow g _ _ hog (hsq i) hq1] at this
    have := hlt i
    omega
  · intro i γ hγ x
    refine ⟨fun ⟨γ', hγ', hx⟩ => ⟨γ * γ', Subgroup.mul_mem _ hγ hγ', by rw [hx, mul_left_comm]⟩,
      fun hx => Subgroup.mul_mem _ (hle i hγ) hx⟩

end PrivPCP.L54


namespace PrivPCP.L54

open Real

/-- degree margins -/
lemma margins (b h : ℕ) (hb : 129 ≤ b) (hh : 1 ≤ h) :
    (1 / 128 : ℝ) * ((b * h : ℕ) : ℝ) ≤ ((h + ⌈((b * h : ℕ) : ℝ) / 128⌉₊ : ℕ) : ℝ) - h ∧
    ((7 * (h + ⌈((b * h : ℕ) : ℝ) / 128⌉₊) + 2 * h - 2 + 1 : ℕ) : ℝ) ≤ ((b * h : ℕ) : ℝ) / 4 := by
  set s : ℝ := ((b * h : ℕ) : ℝ) with hs
  set c := ⌈s / 128⌉₊ with hc
  have hc1 : s / 128 ≤ c := Nat.le_ceil _
  have hs0 : 0 ≤ s := by positivity
  have hc2 : (c : ℝ) < s / 128 + 1 := Nat.ceil_lt_add_one (by positivity)
  refine ⟨?_, ?_⟩
  · push_cast; linarith
  · have e : 7 * (h + c) + 2 * h - 2 + 1 = 9 * h + 7 * c - 1 := by omega
    rw [e]
    have : 1 ≤ 9 * h + 7 * c := by omega
    rw [Nat.cast_sub this]
    push_cast
    have hbr : (129 : ℝ) ≤ b := by exact_mod_cast hb
    have hhr : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hsbh : s = (b : ℝ) * h := by rw [hs]; push_cast; ring
    have : (129 : ℝ) * h ≤ s := by rw [hsbh]; nlinarith
    nlinarith

end PrivPCP.L54


namespace PrivPCP.L54

open Real

lemma prod_ge_pow {k : ℕ} (f : Fin k → ℝ) (a : ℝ) (ha : 0 ≤ a) (hf : ∀ i, a ≤ f i) :
    a ^ k ≤ ∏ i, f i := by
  have := Finset.prod_le_prod (s := Finset.univ) (fun i _ => ha) (fun i _ => hf i)
  simpa using this

lemma prod_le_pow {k : ℕ} (f : Fin k → ℝ) (a : ℝ) (hf0 : ∀ i, 0 ≤ f i) (hf : ∀ i, f i ≤ a) :
    ∏ i, f i ≤ a ^ k := by
  have := Finset.prod_le_prod (s := Finset.univ) (fun i _ => hf0 i) (fun i _ => hf i)
  simpa using this

/-- the size bound for `N` -/
lemma size_bound (A1 A2 lam x B L : ℝ) (k : ℕ) (hA1 : 0 < A1) (hA2 : 0 < A2) (hlam : 1 ≤ lam)
    (hA1l : 1 ≤ A1 * lam) (hx : 0 ≤ x)
    (hB0 : 0 ≤ B) (hB : B ≤ A1 * lam + 1) (hL0 : 0 ≤ L) (hL : L ≤ max (A2 * x + 1) (4 * B)) :
    (12 * B * L) ^ k ≤ (48 * A1 * A2 + 432 * A1 ^ 2) ^ k *
      max (x ^ k * lam ^ k) (lam ^ (2 * k)) := by
  have hB2 : B ≤ 2 * A1 * lam := by linarith
  have hC0 : 0 ≤ 48 * A1 * A2 := by positivity
  have hC1 : 0 ≤ 432 * A1 ^ 2 := by positivity
  rcases le_total (A2 * x + 1) (4 * B) with hcase | hcase
  · -- `L ≤ 4B + ...`
    have hL' : L ≤ 4 * B := hL.trans (max_le hcase le_rfl)
    have : 12 * B * L ≤ 432 * A1 ^ 2 * lam ^ 2 := by
      have := mul_le_mul hB2 (hL'.trans (by linarith : 4 * B ≤ 8 * A1 * lam)) hL0 (by positivity)
      nlinarith
    calc (12 * B * L) ^ k ≤ (432 * A1 ^ 2 * lam ^ 2) ^ k := pow_le_pow_left₀ (by positivity) this k
      _ = (432 * A1 ^ 2) ^ k * lam ^ (2 * k) := by rw [mul_pow, ← pow_mul, mul_comm 2 k]
      _ ≤ (48 * A1 * A2 + 432 * A1 ^ 2) ^ k * lam ^ (2 * k) := by
          gcongr; linarith
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · have hL' : L ≤ A2 * x + 1 := hL.trans (max_le le_rfl hcase)
    -- `A2 x + 1 ≤ A2 x + 4B` is not available; use `1 ≤ A1 lam ≤ B`-free bound
    have h4 : 4 * B ≤ A2 * x + 1 := hcase
    have hB1 : 0 ≤ A2 * x := by positivity
    -- `12 B L ≤ 12 B (A2 x + 1)` and `B ≤ (A2 x + 1)/4`
    by_cases hx1 : 1 ≤ A2 * x
    · have : 12 * B * L ≤ 48 * A1 * A2 * lam * x := by
        have := mul_le_mul hB2 (hL'.trans (by linarith : A2 * x + 1 ≤ 2 * (A2 * x))) hL0 (by positivity)
        nlinarith
      calc (12 * B * L) ^ k ≤ (48 * A1 * A2 * lam * x) ^ k := pow_le_pow_left₀ (by positivity) this k
        _ = (48 * A1 * A2) ^ k * (x ^ k * lam ^ k) := by ring
        _ ≤ (48 * A1 * A2 + 432 * A1 ^ 2) ^ k * (x ^ k * lam ^ k) := by gcongr; linarith
        _ ≤ _ := by gcongr; exact le_max_left _ _
    · push Not at hx1
      have hL2 : L ≤ 2 := by linarith
      have hB3 : B ≤ 1 / 2 := by linarith
      have : 12 * B * L ≤ 432 * A1 ^ 2 * lam ^ 2 := by
        have h1 : 12 * B * L ≤ 12 := by nlinarith
        have h2 : (1 : ℝ) ≤ (A1 * lam) ^ 2 := by nlinarith
        nlinarith
      calc (12 * B * L) ^ k ≤ (432 * A1 ^ 2 * lam ^ 2) ^ k := pow_le_pow_left₀ (by positivity) this k
        _ = (432 * A1 ^ 2) ^ k * lam ^ (2 * k) := by rw [mul_pow, ← pow_mul, mul_comm 2 k]
        _ ≤ (48 * A1 * A2 + 432 * A1 ^ 2) ^ k * lam ^ (2 * k) := by gcongr; linarith
        _ ≤ _ := by gcongr; exact le_max_right _ _

end PrivPCP.L54


namespace PrivPCP.L54

open Real

theorem main_of (HA : ∃ A0 : ℝ, 0 < A0 ∧ ∀ t : ℕ, 1 ≤ t → ∀ m : ℕ, A0 * t * Real.log (t + 1) ≤ m →
      t ≤ ((Finset.Ioc m (3 * m)).filter Nat.Prime).card)
    (HB : ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → ∃ q : ℕ, q.Prime ∧ M ∣ q - 1 ∧ q ≤ M ^ 6) :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 1 ≤ C ∧
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 2 ≤ k →
    ∃ (q : ℕ) (h s : Fin k → ℕ) (S Γ : Fin k → Subgroup (ZMod q)ˣ) (ζ : Fin k → (ZMod q)ˣ),
      q.Prime ∧
      (∀ i, Nat.card (S i) = s i ∧ Nat.card (Γ i) = h i ∧ Γ i ≤ S i) ∧
      (∀ i, (1 / 128 : ℝ) * s i ≤ ((h i + ⌈(s i : ℝ) / 128⌉₊ : ℕ) : ℝ) - h i ∧
        ((7 * (h i + ⌈(s i : ℝ) / 128⌉₊) + 2 * h i - 2 + 1 : ℕ) : ℝ) ≤ (s i : ℝ) / 4) ∧
      n < ∏ i, h i ∧ ∏ i, h i < ∏ i, s i ∧
      ((∏ i, s i : ℕ) : ℝ) ≤ C ^ k * max ((n : ℝ) * Real.log (n + 1) * ((k : ℝ) * Real.log (k + 1)) ^ k)
        (((k : ℝ) * Real.log (k + 1)) ^ (2 * k)) ∧
      (∀ i j, (1 / 4 : ℝ) ≤ (s i : ℝ) / s j ∧ (s i : ℝ) / s j ≤ 4) ∧
      c * n * Real.log (n + 1) ≤ (2 : ℝ) ^ (∑ i, Nat.log 2 (h i)) ∧
      (∀ i, (h i).Prime) ∧ Function.Injective h ∧ (∀ i j, i ≠ j → Nat.Coprime (s i) (s j)) ∧
      (∏ i, s i) ∣ q - 1 ∧ ∏ i, s i < q ∧ q ≤ (∏ i, s i) ^ 6 ∧
      (∀ i, ∀ γ ∈ Γ i, ζ i * γ ∉ S i) ∧
      (∀ i, ∀ γ ∈ Γ i, ∀ x : (ZMod q)ˣ,
        ((∃ γ' ∈ Γ i, x = ζ i * γ') → ∃ γ' ∈ Γ i, γ * x = ζ i * γ') ∧ (x ∈ S i → γ * x ∈ S i)) := by
  intro c hc
  obtain ⟨A0, hA0, hA⟩ := HA
  obtain ⟨M0, hM⟩ := HB
  set A1 : ℝ := A0 + 129 + M0 with hA1def
  set A2 : ℝ := 2 * max c 1 with hA2def
  have hM0r : (0 : ℝ) ≤ M0 := by positivity
  have hA1 : 129 ≤ A1 := by linarith
  have hA2 : 2 ≤ A2 := by have := le_max_right c 1; linarith
  refine ⟨48 * A1 * A2 + 432 * A1 ^ 2, by nlinarith, ?_⟩
  intro n hn k hk
  set lam : ℝ := (k : ℝ) * Real.log (k + 1) with hlamdef
  have hlog2 := Real.log_two_gt_d9
  have hlogk : Real.log 2 ≤ Real.log (k + 1) := by
    apply Real.log_le_log (by norm_num)
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlam : 1 ≤ lam := by rw [hlamdef]; nlinarith
  have hA1l : 1 ≤ A1 * lam := by nlinarith
  set B : ℕ := ⌈A1 * lam⌉₊ with hBdef
  have hB1 : A1 * lam ≤ B := Nat.le_ceil _
  have hB2 : (B : ℝ) < A1 * lam + 1 := Nat.ceil_lt_add_one (by positivity)
  have hB129 : 129 ≤ B := by
    have : (129 : ℝ) ≤ B := by nlinarith
    exact_mod_cast this
  have hBM : M0 ≤ B := by
    have : (M0 : ℝ) ≤ B := by
      have : (M0 : ℝ) ≤ A1 := by have : (0 : ℝ) ≤ A0 := hA0.le; linarith
      nlinarith
    exact_mod_cast this
  have hBA : ∀ m : ℕ, B ≤ m → A0 * (k : ℝ) * Real.log ((k : ℝ) + 1) ≤ m := by
    intro m hm
    have : (B : ℝ) ≤ m := by exact_mod_cast hm
    have : A0 * lam ≤ A1 * lam := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      have : (0 : ℝ) ≤ M0 := by positivity
      linarith
    rw [hlamdef] at this
    linarith [show A0 * (k : ℝ) * Real.log ((k : ℝ) + 1) = A0 * ((k : ℝ) * Real.log ((k : ℝ) + 1)) by ring]
  clear_value B
  -- the primes `b i`
  obtain ⟨b, hbinj, hbmem⟩ := hall_select k (fun _ => (Finset.Ioc B (3 * B)).filter Nat.Prime)
    (fun _ => hA k (by omega) B (hBA B le_rfl))
  have hb : ∀ i, B < b i ∧ b i ≤ 3 * B ∧ (b i).Prime := by
    intro i
    have := hbmem i
    simp only [Finset.mem_filter, Finset.mem_Ioc] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  -- sizes
  set y : ℝ := (n : ℝ) * Real.log (n + 1) with hydef
  have hn0r : (0 : ℝ) ≤ n := by positivity
  have hy0 : 0 ≤ y := by
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg this
    positivity
  set x : ℝ := y ^ ((k : ℝ)⁻¹) with hxdef
  have hx0 : 0 ≤ x := Real.rpow_nonneg hy0 _
  have hxk : x ^ k = y := Real.rpow_inv_natCast_pow hy0 (by omega)
  clear_value x
  set L : ℕ := max ⌈A2 * x⌉₊ (4 * B) with hLdef
  have hL4B : 4 * B ≤ L := le_max_right _ _
  have hLx : A2 * x ≤ L := by
    have : (⌈A2 * x⌉₊ : ℝ) ≤ L := by exact_mod_cast le_max_left _ _
    exact (Nat.le_ceil _).trans this
  have hLle : (L : ℝ) ≤ max (A2 * x + 1) (4 * B) := by
    rw [hLdef, Nat.cast_max]
    push_cast
    exact max_le_max (Nat.ceil_lt_add_one (by positivity)).le le_rfl
  clear_value L
  set T : ℕ := 3 * B * L with hTdef
  have hB0 : 0 < B := by omega
  have hTL : T / (3 * B) = L := by rw [hTdef]; exact Nat.mul_div_cancel_left L (by omega)
  have hT12 : 12 * B * B ≤ T := by rw [hTdef]; nlinarith
  have hBT : B ≤ T := by rw [hTdef]; nlinarith
  have hT1 : 1 ≤ T := by omega
  have hTr : ((4 * T : ℕ) : ℝ) = 12 * (B : ℝ) * L := by rw [hTdef]; push_cast; ring
  clear_value T
  have hmL : ∀ i, L ≤ T / b i := by
    intro i
    rw [← hTL]
    exact Nat.div_le_div_left (hb i).2.1 (by have := (hb i).1; omega)
  -- the primes `h i`
  obtain ⟨h, hhinj, hhmem⟩ := hall_select k
    (fun i => (Finset.Ioc (T / b i + 1) (3 * (T / b i + 1))).filter Nat.Prime)
    (fun i => hA k (by omega) _ (hBA _ (by have := hmL i; omega)))
  have hh : ∀ i, T / b i + 1 < h i ∧ h i ≤ 3 * (T / b i + 1) ∧ (h i).Prime := by
    intro i
    have := hhmem i
    simp only [Finset.mem_filter, Finset.mem_Ioc] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hbh : ∀ i j, b i ≠ h j := by
    intro i j e
    have := (hb i).2.1; have := hmL j; have := (hh j).1
    omega
  set s : Fin k → ℕ := fun i => b i * h i with hsdef
  have hsT : ∀ i, T < s i := by
    intro i
    have hbpos : 0 < b i := by have := (hb i).1; omega
    have h1 : T < b i * (T / b i + 1) := Nat.lt_mul_div_succ T hbpos
    have h2 : b i * (T / b i + 1) ≤ b i * h i := Nat.mul_le_mul_left _ (hh i).1.le
    exact lt_of_lt_of_le h1 h2
  have hs4T : ∀ i, s i < 4 * T := by
    intro i
    have h1 : b i * (T / b i) ≤ T := Nat.mul_div_le T (b i)
    have h2 : s i ≤ b i * (3 * (T / b i + 1)) := Nat.mul_le_mul_left _ (hh i).2.1
    have h3 : 12 * B * B ≤ T := hT12
    have h4 := (hb i).2.1
    have h5 : b i * (3 * (T / b i + 1)) = 3 * (b i * (T / b i)) + 3 * b i := by ring
    nlinarith
  -- the product `N`
  have hs1 : ∀ i, 1 ≤ s i := fun i => by have := hsT i; omega
  have hsleN : ∀ i, s i ≤ ∏ j, s j := fun i =>
    Finset.single_le_prod' (fun j _ => hs1 j) (Finset.mem_univ i)
  have hNM : M0 ≤ ∏ j, s j := by
    have := hsleN ⟨0, by omega⟩
    have := hsT ⟨0, by omega⟩
    omega
  obtain ⟨q, hq, hNq, hq6⟩ := hM _ hNM
  haveI := Fact.mk hq
  have hq2 := hq.two_le
  have hNq1 : ∏ j, s j ≤ q - 1 := Nat.le_of_dvd (by omega) hNq
  have hslt : ∀ i, s i < q - 1 := by
    intro i
    obtain ⟨j, hj⟩ : ∃ j : Fin k, j ≠ i := by
      by_cases h0 : i.val = 0
      · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h0; simp at h0⟩
      · exact ⟨⟨0, by omega⟩, fun e => h0 (by rw [← e])⟩
    have hpair : s i * s j ≤ ∏ l, s l := by
      have := Finset.prod_le_prod_of_subset_of_one_le' (f := s) (Finset.subset_univ {i, j})
        (fun l _ _ => hs1 l)
      rwa [Finset.prod_pair (Ne.symm hj)] at this
    have : 2 ≤ s j := by have := hsT j; omega
    have : s i < s i * s j := by nlinarith [hs1 i]
    omega
  obtain ⟨S, Γ, ζ, hSΓ, hζ, hinv⟩ := group_part q k s h (fun i => dvd_mul_left _ _)
    (fun i => (Finset.dvd_prod_of_mem s (Finset.mem_univ i)).trans hNq) hslt
  have hhL : ∀ i, (L : ℝ) < h i := by
    intro i; have := hmL i; have := (hh i).1
    exact_mod_cast (show L < h i by omega)
  refine ⟨q, h, s, S, Γ, ζ, hq, hSΓ, ?_, ?_, ?_, ?_, ?_, ?_, fun i => (hh i).2.2, hhinj, ?_, hNq,
    by omega, hq6, hζ, hinv⟩
  · intro i
    exact margins (b i) (h i) (by have := (hb i).1; omega) (hh i).2.2.one_lt.le
  · -- `n < ∏ h`
    have hprod : (A2 * x) ^ k ≤ ∏ i, (h i : ℝ) :=
      prod_ge_pow _ _ (by positivity) (fun i => (hLx.trans (hhL i).le))
    have hA2k : (4 : ℝ) ≤ A2 ^ k := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
        _ ≤ A2 ^ k := pow_le_pow_left₀ (by norm_num) hA2 k
    have hyn : (n : ℝ) * 0.69 ≤ y := by
      rw [hydef]
      have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hl : Real.log 2 ≤ Real.log ((n : ℝ) + 1) :=
        Real.log_le_log (by norm_num) (by linarith only [hn1'])
      have h69 : (0.69 : ℝ) ≤ Real.log ((n : ℝ) + 1) := by linarith only [hl, hlog2]
      exact mul_le_mul_of_nonneg_left h69 hn0r
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (n : ℝ) < ∏ i, (h i : ℝ) := by
      rw [mul_pow, hxk] at hprod
      have hmul := mul_le_mul_of_nonneg_right hA2k hy0
      linarith only [hprod, hmul, hyn, hn1]
    exact_mod_cast this
  · exact Finset.prod_lt_prod_of_nonempty (fun i _ => (hh i).2.2.pos)
      (fun i _ => by
        show h i < b i * h i
        have h1 : 1 < b i := by have := (hb i).1; omega
        exact lt_mul_of_one_lt_left (hh i).2.2.pos h1) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  · -- size of `N`
    have h1 : ((∏ i, s i : ℕ) : ℝ) ≤ ((4 * T : ℕ) : ℝ) ^ k := by
      push_cast
      exact prod_le_pow _ _ (fun i => by positivity) (fun i => by exact_mod_cast (hs4T i).le)
    rw [hTr] at h1
    have h3 := size_bound A1 A2 lam x B L k (by linarith only [hA1]) (by linarith only [hA2]) hlam hA1l hx0
      (by positivity) hB2.le (by positivity) hLle
    rw [hxk] at h3
    exact h1.trans h3
  · intro i j
    have hi := hsT i; have hj := hs4T j; have hi' := hs4T i; have hj' := hsT j
    have hT0 : (0 : ℝ) < T := by
      exact_mod_cast (show 0 < T by omega)
    have ri : (T : ℝ) < s i := by exact_mod_cast hi
    have rj : (s j : ℝ) < 4 * T := by exact_mod_cast hj
    have ri' : (s i : ℝ) < 4 * T := by exact_mod_cast hi'
    have rj' : (T : ℝ) < s j := by exact_mod_cast hj'
    have hsj : (0 : ℝ) < s j := by linarith only [rj', hT0]
    constructor
    · rw [le_div_iff₀ hsj]; linarith only [ri, rj]
    · rw [div_le_iff₀ hsj]; linarith only [ri', rj']
  · -- the hypercube condition
    rw [← Finset.prod_pow_eq_pow_sum]
    have hper : ∀ i, A2 * x / 2 ≤ (2 : ℝ) ^ Nat.log 2 (h i) := by
      intro i
      have h1 : h i < 2 ^ (Nat.log 2 (h i) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have h1' : (h i : ℝ) < 2 * 2 ^ Nat.log 2 (h i) := by
        have : ((h i : ℕ) : ℝ) < ((2 ^ (Nat.log 2 (h i) + 1) : ℕ) : ℝ) := by exact_mod_cast h1
        rw [pow_succ] at this; push_cast at this; linarith only [this]
      have h2 := hhL i
      linarith only [h1', h2, hLx]
    have hprod := prod_ge_pow _ _ (by positivity) hper
    have e : (A2 * x / 2) ^ k = (A2 / 2) ^ k * y := by rw [← hxk]; ring
    rw [e] at hprod
    have hA2c : c ≤ (A2 / 2) ^ k := by
      have : A2 / 2 = max c 1 := by rw [hA2def]; ring
      rw [this]
      calc c ≤ max c 1 := le_max_left _ _
        _ ≤ (max c 1) ^ k := le_self_pow₀ (le_max_right _ _) (by omega)
    have : c * y ≤ (A2 / 2) ^ k * y := mul_le_mul_of_nonneg_right hA2c hy0
    calc c * n * Real.log (n + 1) = c * y := by rw [hydef]; ring
      _ ≤ _ := this.trans hprod
  · exact coprime_of_distinct b h (fun i => (hb i).2.2) (fun i => (hh i).2.2) hbinj hhinj hbh

end PrivPCP.L54


theorem solution : ∀ c : ℝ, 0 < c → ∃ C : ℝ, 1 ≤ C ∧
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 2 ≤ k →
    ∃ (q : ℕ) (h s : Fin k → ℕ) (S Γ : Fin k → Subgroup (ZMod q)ˣ) (ζ : Fin k → (ZMod q)ˣ),
      q.Prime ∧
      (∀ i, Nat.card (S i) = s i ∧ Nat.card (Γ i) = h i ∧ Γ i ≤ S i) ∧
      -- 1. degree margins
      (∀ i, (1 / 128 : ℝ) * s i ≤ ((h i + ⌈(s i : ℝ) / 128⌉₊ : ℕ) : ℝ) - h i ∧
        ((7 * (h i + ⌈(s i : ℝ) / 128⌉₊) + 2 * h i - 2 + 1 : ℕ) : ℝ) ≤ (s i : ℝ) / 4) ∧
      -- 2. domain sizes
      n < ∏ i, h i ∧ ∏ i, h i < ∏ i, s i ∧
      ((∏ i, s i : ℕ) : ℝ) ≤ C ^ k * max ((n : ℝ) * Real.log (n + 1) * ((k : ℝ) * Real.log (k + 1)) ^ k)
        (((k : ℝ) * Real.log (k + 1)) ^ (2 * k)) ∧
      (∀ i j, (1 / 4 : ℝ) ≤ (s i : ℝ) / s j ∧ (s i : ℝ) / s j ≤ 4) ∧
      c * n * Real.log (n + 1) ≤ (2 : ℝ) ^ (∑ i, Nat.log 2 (h i)) ∧
      -- 3. field and subgroup choices
      (∀ i, (h i).Prime) ∧ Function.Injective h ∧ (∀ i j, i ≠ j → Nat.Coprime (s i) (s j)) ∧
      (∏ i, s i) ∣ q - 1 ∧ ∏ i, s i < q ∧ q ≤ (∏ i, s i) ^ 6 ∧
      (∀ i, ∀ γ ∈ Γ i, ζ i * γ ∉ S i) ∧
      (∀ i, ∀ γ ∈ Γ i, ∀ x : (ZMod q)ˣ,
        ((∃ γ' ∈ Γ i, x = ζ i * γ') → ∃ γ' ∈ Γ i, γ * x = ζ i * γ') ∧ (x ∈ S i → γ * x ∈ S i)) :=
  PrivPCP.L54.main_of PrivPCP.primes_Ioc_three PrivPCP.linnik_xylouris


