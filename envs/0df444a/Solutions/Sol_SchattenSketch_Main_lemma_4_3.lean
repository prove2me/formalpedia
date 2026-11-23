-- Prove2me | solution 1 for SchattenSketch.Main.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T06:03:38.000809+00:00
-- url     : https://prove2.me/submissions/d2166489-9db0-4991-8e14-d092328ad9bf

import Mathlib

lemma stz_reduce {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A : Finset ι) (v : ι → E) (s : ℝ) :
    ∀ n : ℕ, ∀ l : ι → ℝ, (A.filter (fun i => 0 < l i ∧ l i < 1)).card = n →
      (∀ i ∈ A, 0 ≤ l i ∧ l i ≤ 1) → ∑ i ∈ A, l i • v i = 0 → ∑ i ∈ A, l i = s →
      ∃ μ : ι → ℝ, (A.filter (fun i => 0 < μ i ∧ μ i < 1)).card ≤ Module.finrank ℝ E + 1 ∧
        (∀ i ∈ A, 0 ≤ μ i ∧ μ i ≤ 1) ∧ ∑ i ∈ A, μ i • v i = 0 ∧ ∑ i ∈ A, μ i = s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hn hl h0 hs
  by_cases hle : n ≤ Module.finrank ℝ E + 1
  · exact ⟨l, hn ▸ hle, hl, h0, hs⟩
  push Not at hle
  set F := A.filter (fun i => 0 < l i ∧ l i < 1) with hF
  have hFA : F ⊆ A := Finset.filter_subset _ _
  have hnli : ¬ LinearIndependent ℝ (fun i : F => ((v i, (1:ℝ)) : E × ℝ)) := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_coe, Module.finrank_prod, Module.finrank_self] at this
    omega
  obtain ⟨g, hg, i1, hi1⟩ := Fintype.not_linearIndependent_iff.1 hnli
  set δ : ι → ℝ := fun i => if h : i ∈ F then g ⟨i, h⟩ else 0 with hδ
  have key : ∑ i ∈ A, δ i • v i = ∑ i : F, g i • v i := by
    rw [← Finset.sum_subset hFA (fun i _ hi => by simp [hδ, hi])]
    rw [← Finset.sum_coe_sort F (fun i => δ i • v i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [hδ]
  have key1 : ∑ i ∈ A, δ i = ∑ i : F, g i := by
    rw [← Finset.sum_subset hFA (fun i _ hi => by simp [hδ, hi])]
    rw [← Finset.sum_coe_sort F (fun i => δ i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [hδ]
  have hδv : ∑ i ∈ A, δ i • v i = 0 := by
    rw [key]
    have := congrArg Prod.fst hg
    simpa [Prod.fst_sum] using this
  have hδ1 : ∑ i ∈ A, δ i = 0 := by
    rw [key1]
    have := congrArg Prod.snd hg
    simpa [Prod.snd_sum] using this
  have hδF : ∀ i, i ∉ F → δ i = 0 := fun i hi => by simp [hδ, hi]
  have hex : ∃ i ∈ F, δ i ≠ 0 := ⟨i1, i1.2, by simpa [hδ] using hi1⟩
  set F' := F.filter (fun i => δ i ≠ 0) with hF'
  have hF'ne : F'.Nonempty := by
    obtain ⟨i, hi, hne⟩ := hex
    exact ⟨i, Finset.mem_filter.2 ⟨hi, hne⟩⟩
  set r : ι → ℝ := fun i => if 0 < δ i then (1 - l i) / δ i else l i / (-δ i) with hr
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image F' r hF'ne
  have hFmem : ∀ i ∈ F, 0 < l i ∧ l i < 1 := fun i hi => (Finset.mem_filter.1 hi).2
  have hrpos : ∀ i ∈ F', 0 < r i := by
    intro i hi
    obtain ⟨hiF, hne⟩ := Finset.mem_filter.1 hi
    obtain ⟨h1, h2⟩ := hFmem i hiF
    simp only [hr]
    split_ifs with hp
    · exact div_pos (by linarith) hp
    · have : δ i < 0 := lt_of_le_of_ne (not_lt.1 hp) hne
      exact div_pos h1 (by linarith)
  set t := r i0 with ht
  have htpos : 0 < t := hrpos i0 hi0
  have hupper : ∀ i ∈ F, 0 < δ i → t * δ i ≤ 1 - l i := by
    intro i hi hp
    have hmem : i ∈ F' := Finset.mem_filter.2 ⟨hi, hp.ne'⟩
    have := hmin i hmem
    simp only [hr, if_pos hp] at this
    rw [le_div_iff₀ hp] at this
    exact this
  have hlower : ∀ i ∈ F, δ i < 0 → t * (-δ i) ≤ l i := by
    intro i hi hp
    have hmem : i ∈ F' := Finset.mem_filter.2 ⟨hi, hp.ne⟩
    have := hmin i hmem
    simp only [hr, if_neg (not_lt.2 hp.le)] at this
    rw [le_div_iff₀ (by linarith)] at this
    exact this
  set μ : ι → ℝ := fun i => l i + t * δ i with hμ
  have hμb : ∀ i ∈ A, 0 ≤ μ i ∧ μ i ≤ 1 := by
    intro i hi
    by_cases hiF : i ∈ F
    · obtain ⟨h1, h2⟩ := hFmem i hiF
      simp only [hμ]
      rcases lt_trichotomy (δ i) 0 with hneg | hz | hpos
      · have := hlower i hiF hneg
        constructor <;> nlinarith
      · rw [hz]; constructor <;> linarith
      · have := hupper i hiF hpos
        constructor <;> nlinarith
    · simp only [hμ, hδF i hiF]; simpa using hl i hi
  have hμ0 : μ i0 = 0 ∨ μ i0 = 1 := by
    obtain ⟨hiF, hne⟩ := Finset.mem_filter.1 hi0
    simp only [hμ]
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · left
      have : t = l i0 / (-δ i0) := by simp only [ht, hr, if_neg (not_lt.2 hneg.le)]
      rw [this]; field_simp; ring
    · right
      have : t = (1 - l i0) / δ i0 := by simp only [ht, hr, if_pos hpos]
      rw [this]; field_simp; ring
  have hsub : A.filter (fun i => 0 < μ i ∧ μ i < 1) ⊆ F.erase i0 := by
    intro i hi
    obtain ⟨hiA, hm⟩ := Finset.mem_filter.1 hi
    rw [Finset.mem_erase]
    constructor
    · rintro rfl
      rcases hμ0 with h | h <;> linarith [hm.1, hm.2]
    · by_contra hiF
      have hF2 : i ∉ F := hiF
      have : μ i = l i := by simp only [hμ, hδF i hF2]; ring
      rw [this] at hm
      exact hiF (Finset.mem_filter.2 ⟨hiA, hm⟩)
  have hcard : (A.filter (fun i => 0 < μ i ∧ μ i < 1)).card < n := by
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_filter.1 hi0).1] at this
    have hpos : 0 < F.card := Finset.card_pos.2 ⟨i0, (Finset.mem_filter.1 hi0).1⟩
    omega
  refine ih _ hcard μ rfl hμb ?_ ?_
  · have : ∑ i ∈ A, μ i • v i = ∑ i ∈ A, l i • v i + t • ∑ i ∈ A, δ i • v i := by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hμ, add_smul, mul_smul]
    rw [this, h0, hδv]; simp
  · have : ∑ i ∈ A, μ i = ∑ i ∈ A, l i + t * ∑ i ∈ A, δ i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [this, hs, hδ1]; simp

lemma stz_step {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A : Finset ι) (v : ι → E) (d : ℕ)
    (hd : Module.finrank ℝ E = d) (hA : d < A.card) (l : ι → ℝ)
    (hl : ∀ i ∈ A, 0 ≤ l i ∧ l i ≤ 1) (h0 : ∑ i ∈ A, l i • v i = 0)
    (hs : ∑ i ∈ A, l i = (A.card : ℝ) - d) :
    ∃ i ∈ A, ∃ μ : ι → ℝ, (∀ j ∈ A.erase i, 0 ≤ μ j ∧ μ j ≤ 1) ∧
      ∑ j ∈ A.erase i, μ j • v j = 0 ∧ ∑ j ∈ A.erase i, μ j = ((A.erase i).card : ℝ) - d := by
  have hAd : (d : ℝ) + 1 ≤ A.card := by exact_mod_cast hA
  have hpos : (0:ℝ) < (A.card : ℝ) - d := by linarith
  set c : ℝ := ((A.card : ℝ) - 1 - d) / ((A.card : ℝ) - d) with hc
  have hc0 : 0 ≤ c := div_nonneg (by linarith) hpos.le
  have hc1 : c ≤ 1 := by rw [hc, div_le_one hpos]; linarith
  obtain ⟨μ, hcardμ, hμb, hμ0, hμs⟩ := stz_reduce A v ((A.card : ℝ) - 1 - d) _ (fun i => c * l i) rfl
    (fun i hi => ⟨mul_nonneg hc0 (hl i hi).1, by nlinarith [(hl i hi).1, (hl i hi).2]⟩)
    (by
      have : ∑ i ∈ A, (c * l i) • v i = c • ∑ i ∈ A, l i • v i := by
        rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun i _ => by rw [mul_smul])
      rw [this, h0]; simp)
    (by
      rw [← Finset.mul_sum, hs, hc]; field_simp)
  have hz : ∃ i ∈ A, μ i = 0 := by
    by_contra hnz
    push Not at hnz
    set F := A.filter (fun i => 0 < μ i ∧ μ i < 1) with hF
    set O := A.filter (fun i => ¬ (0 < μ i ∧ μ i < 1)) with hO
    have hFO := Finset.sum_filter_add_sum_filter_not A (fun i => 0 < μ i ∧ μ i < 1) μ
    have hcardFO := Finset.card_filter_add_card_filter_not (s := A)
      (fun i => 0 < μ i ∧ μ i < 1)
    have hOone : ∑ i ∈ O, μ i = O.card := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      obtain ⟨hiA, hn⟩ := Finset.mem_filter.1 hi
      obtain ⟨h1, h2⟩ := hμb i hiA
      have : 0 < μ i := lt_of_le_of_ne h1 (Ne.symm (hnz i hiA))
      have : μ i = 1 := by
        by_contra hne
        exact hn ⟨this, lt_of_le_of_ne h2 hne⟩
      simp [this]
    have hFnn : 0 ≤ ∑ i ∈ F, μ i :=
      Finset.sum_nonneg (fun i hi => (hμb i (Finset.mem_filter.1 hi).1).1)
    have hcardF : (F.card : ℝ) ≤ d + 1 := by
      have : F.card ≤ d + 1 := hd ▸ hcardμ
      exact_mod_cast this
    have hcardFO' : (F.card : ℝ) + O.card = A.card := by exact_mod_cast hcardFO
    have hsum : ∑ i ∈ F, μ i = (F.card : ℝ) - 1 - d := by linarith
    by_cases hFe : F = ∅
    · rw [hFe] at hsum
      simp at hsum
      linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
    · have hne : F.Nonempty := Finset.nonempty_iff_ne_empty.2 hFe
      have : 0 < ∑ i ∈ F, μ i := Finset.sum_pos (fun i hi => (Finset.mem_filter.1 hi).2.1) hne
      linarith
  obtain ⟨i, hi, hmi⟩ := hz
  refine ⟨i, hi, μ, fun j hj => hμb j (Finset.mem_of_mem_erase hj), ?_, ?_⟩
  · rw [Finset.sum_erase _ (by simp [hmi])]; exact hμ0
  · rw [Finset.sum_erase _ hmi, hμs, Finset.card_erase_of_mem hi, Nat.cast_sub (by omega)]
    simp

lemma stz_enum {ι : Type*} [DecidableEq ι] [Nonempty ι] (A : Finset ι) :
    ∃ f : ℕ → ι, Set.InjOn f (Finset.range A.card) ∧ A = (Finset.range A.card).image f := by
  induction A using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.arbitrary ι, by simp, by simp⟩
  | insert a s has ih =>
    obtain ⟨f, hinj, himg⟩ := ih
    rw [Finset.card_insert_of_notMem has]
    refine ⟨fun j => if j = s.card then a else f j, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_range, Set.mem_Iio] at hx hy
      simp only at hxy
      by_cases hx' : x = s.card <;> by_cases hy' : y = s.card
      · omega
      · rw [if_pos hx', if_neg hy'] at hxy
        exfalso; apply has; rw [himg, hxy]
        exact Finset.mem_image.2 ⟨y, Finset.mem_range.2 (by omega), rfl⟩
      · rw [if_neg hx', if_pos hy'] at hxy
        exfalso; apply has; rw [himg, ← hxy]
        exact Finset.mem_image.2 ⟨x, Finset.mem_range.2 (by omega), rfl⟩
      · rw [if_neg hx', if_neg hy'] at hxy
        exact hinj (by simp; omega) (by simp; omega) hxy
    · ext x
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro (rfl | hx)
        · exact ⟨s.card, by omega, by simp⟩
        · have := himg ▸ hx
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 this
          rw [Finset.mem_range] at hj
          exact ⟨j, by omega, by simp [show j ≠ s.card by omega]⟩
      · rintro ⟨j, hj, rfl⟩
        by_cases h : j = s.card
        · left; simp [h]
        · right
          have hm : f j ∈ s := by
            have := Finset.mem_image_of_mem f (Finset.mem_range.2 (show j < s.card by omega))
            rwa [← himg] at this
          simpa [h] using hm

lemma stz_chain {ι E : Type*} [DecidableEq ι] [Nonempty ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (v : ι → E) (hv : ∀ i, ‖v i‖ ≤ 1) (d : ℕ)
    (hd : Module.finrank ℝ E = d) :
    ∀ n : ℕ, ∀ A : Finset ι, A.card = n →
      (d < A.card → ∃ l : ι → ℝ, (∀ i ∈ A, 0 ≤ l i ∧ l i ≤ 1) ∧ ∑ i ∈ A, l i • v i = 0 ∧
        ∑ i ∈ A, l i = (A.card : ℝ) - d) →
      ∃ f : ℕ → ι, Set.InjOn f (Finset.range n) ∧ A = (Finset.range n).image f ∧
        ∀ k ≤ n, ‖∑ j ∈ Finset.range k, v (f j)‖ ≤ d := by
  intro n
  induction n with
  | zero =>
    intro A hA _
    refine ⟨fun _ => Classical.arbitrary ι, by simp, ?_, by intro k hk; simp [Nat.le_zero.1 hk]⟩
    simpa [Finset.card_eq_zero] using hA
  | succ n ih =>
    intro A hA hfeas
    by_cases hn : n + 1 ≤ d
    · obtain ⟨f, hinj, himg⟩ := stz_enum A
      rw [hA] at hinj himg
      refine ⟨f, hinj, himg, fun k hk => ?_⟩
      calc ‖∑ j ∈ Finset.range k, v (f j)‖ ≤ ∑ j ∈ Finset.range k, ‖v (f j)‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ Finset.range k, (1:ℝ) := Finset.sum_le_sum (fun j _ => hv _)
        _ = k := by simp
        _ ≤ d := by exact_mod_cast hk.trans hn
    · push Not at hn
      obtain ⟨l, hl, h0, hs⟩ := hfeas (by omega)
      obtain ⟨i, hi, μ, hμb, hμ0, hμs⟩ := stz_step A v d hd (by omega) l hl h0 hs
      have hcard : (A.erase i).card = n := by rw [Finset.card_erase_of_mem hi]; omega
      obtain ⟨f, hinj, himg, hbd⟩ := ih (A.erase i) hcard (fun _ => ⟨μ, hμb, hμ0, by
        rw [hμs]⟩)
      have hnotin : ∀ j < n, f j ≠ i := by
        intro j hj hfj
        have : f j ∈ A.erase i := by
          rw [himg]; exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩
        rw [hfj] at this; simp at this
      refine ⟨fun j => if j = n then i else f j, ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        simp only [Finset.coe_range, Set.mem_Iio] at hx hy
        simp only at hxy
        by_cases hx' : x = n <;> by_cases hy' : y = n
        · omega
        · rw [if_pos hx', if_neg hy'] at hxy
          exact absurd hxy.symm (hnotin y (by omega))
        · rw [if_neg hx', if_pos hy'] at hxy
          exact absurd hxy (hnotin x (by omega))
        · rw [if_neg hx', if_neg hy'] at hxy
          exact hinj (by simp; omega) (by simp; omega) hxy
      · ext x
        simp only [Finset.mem_image, Finset.mem_range]
        constructor
        · intro hx
          by_cases hxi : x = i
          · exact ⟨n, by omega, by simp [hxi]⟩
          · have hx' : x ∈ A.erase i := Finset.mem_erase.2 ⟨hxi, hx⟩
            rw [himg] at hx'
            obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx'
            rw [Finset.mem_range] at hj
            exact ⟨j, by omega, by simp [show j ≠ n by omega]⟩
        · rintro ⟨j, hj, rfl⟩
          by_cases h : j = n
          · simp [h, hi]
          · simp only [h, if_false]
            have : f j ∈ A.erase i := by
              rw [himg]; exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩
            exact Finset.mem_of_mem_erase this
      · intro k hk
        by_cases hkn : k ≤ n
        · rw [Finset.sum_congr rfl (g := fun j => v (f j))
            (fun j hj => by
              have := Finset.mem_range.1 hj
              simp [show j ≠ n by omega])]
          exact hbd k hkn
        · have hk' : k = n + 1 := by omega
          subst hk'
          rw [Finset.sum_range_succ]
          have h1 : ∑ j ∈ Finset.range n, v (if j = n then i else f j) =
              ∑ j ∈ Finset.range n, v (f j) :=
            Finset.sum_congr rfl (fun j hj => by
              simp [show j ≠ n by have := Finset.mem_range.1 hj; omega])
          have h4 : (fun j => if j = n then i else f j) n = i := by simp
          rw [h1, h4]
          have h2 : ∑ j ∈ Finset.range n, v (f j) = ∑ x ∈ A.erase i, v x := by
            rw [himg, Finset.sum_image hinj]
          rw [h2, add_comm, Finset.add_sum_erase _ _ hi]
          have h3 : ∑ x ∈ A, v x = ∑ x ∈ A, (1 - l x) • v x := by
            have : ∑ x ∈ A, (1 - l x) • v x = ∑ x ∈ A, v x - ∑ x ∈ A, l x • v x := by
              rw [← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl (fun x _ => by rw [sub_smul, one_smul])
            rw [this, h0, sub_zero]
          rw [h3]
          calc ‖∑ x ∈ A, (1 - l x) • v x‖ ≤ ∑ x ∈ A, ‖(1 - l x) • v x‖ := norm_sum_le _ _
            _ ≤ ∑ x ∈ A, (1 - l x) := Finset.sum_le_sum (fun x hx => by
                rw [norm_smul, Real.norm_of_nonneg (by linarith [(hl x hx).2])]
                calc (1 - l x) * ‖v x‖ ≤ (1 - l x) * 1 :=
                      mul_le_mul_of_nonneg_left (hv x) (by linarith [(hl x hx).2])
                  _ = 1 - l x := mul_one _)
            _ = d := by
                rw [Finset.sum_sub_distrib, hs]; simp [hA]

theorem solution (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (d N : ℕ) (hd : 1 ≤ d) (hE : Module.finrank ℝ E = d) (hN : 1 ≤ N)
    (v : Fin N → E) (hv : ∀ i, ‖v i‖ ≤ 1) (hsum : ∑ i, v i = 0) :
    ∃ π : Equiv.Perm (Fin N), ∀ m : ℕ, 1 ≤ m → m ≤ N →
      ‖∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < m), v (π i)‖ ≤ d := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨f, hinj, himg, hbd⟩ := stz_chain v hv d hE N Finset.univ (by simp) (by
    intro hdN
    have hNd : (d : ℝ) < N := by simpa using hdN
    refine ⟨fun _ => ((N : ℝ) - d) / N, fun i _ => ⟨?_, ?_⟩, ?_, ?_⟩
    · exact div_nonneg (by linarith) (by positivity)
    · have : (0:ℝ) < N := by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
      rw [div_le_one this]; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
    · rw [← Finset.smul_sum, hsum]; simp
    · have : (0:ℝ) < N := by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp)
  have hinj' : Function.Injective (fun i : Fin N => f i.val) := by
    intro a b hab
    exact Fin.ext (hinj (by simp) (by simp) hab)
  have hbij : Function.Bijective (fun i : Fin N => f i.val) :=
    ⟨hinj', Finite.injective_iff_surjective.1 hinj'⟩
  refine ⟨Equiv.ofBijective _ hbij, fun m hm1 hmN => ?_⟩
  have : ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < m), v (Equiv.ofBijective _ hbij i) =
      ∑ j ∈ Finset.range m, v (f j) := by
    refine Finset.sum_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_ ?_
    · intro i hi; simpa using hi
    · intro a _ b _ hab; exact Fin.ext hab
    · intro j hj
      have := Finset.mem_range.1 hj
      exact ⟨⟨j, by omega⟩, by simpa using this, rfl⟩
    · intro i _; rfl
  rw [this]
  exact hbd m hmN
