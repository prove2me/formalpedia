-- Prove2me | solution 1 for RecoveringBandits.claim_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:02:59.39326+00:00
-- url     : https://prove2.me/submissions/aec3c242-3dd1-441a-9416-12c296f336a7

import Mathlib
import Definitions.Def_RecoveringBandits_Admissible
import Definitions.Def_RecoveringBandits_F
import Definitions.Def_RecoveringBandits_supp

namespace RecoveringBandits.Aux_RB

open RecoveringBandits Filter Topology

theorem slope_eq (r : ℕ → ℝ) (h0 : r 0 = 0) (d : ℕ) : chordSlope r 0 d = r d / d := by
  unfold chordSlope
  rw [h0]
  simp

theorem exists_max_slope (r : ℕ → ℝ) (Rmax : ℝ) (hr : ArmAdmissible r Rmax) :
    ∃ d, 0 < d ∧ ∀ d', 0 < d' → chordSlope r 0 d' ≤ chordSlope r 0 d := by
  obtain ⟨h0, hnn, _, hle⟩ := hr
  by_cases hall : ∀ d, r d = 0
  · refine ⟨1, one_pos, fun d' _ => ?_⟩
    rw [slope_eq r h0, slope_eq r h0, hall, hall]
    simp
  push_neg at hall
  obtain ⟨d0, hd0⟩ := hall
  have hd0pos : 0 < d0 := by
    rcases Nat.eq_zero_or_pos d0 with h | h
    · subst h; exact absurd h0 hd0
    · exact h
  have hrd0 : 0 < r d0 := lt_of_le_of_ne (hnn d0) (Ne.symm hd0)
  have hd0R : (0 : ℝ) < d0 := by exact_mod_cast hd0pos
  set c := r d0 / d0 with hc
  have hcpos : 0 < c := div_pos hrd0 hd0R
  set N := ⌈Rmax / c⌉₊ + d0 with hN
  obtain ⟨dm, hdm, hmax⟩ := Finset.exists_max_image (Finset.Icc 1 N) (fun d : ℕ => r d / d)
    ⟨d0, Finset.mem_Icc.mpr ⟨hd0pos, by omega⟩⟩
  have hdm1 : 1 ≤ dm := (Finset.mem_Icc.mp hdm).1
  refine ⟨dm, hdm1, fun d' hd' => ?_⟩
  rw [slope_eq r h0, slope_eq r h0]
  by_cases hd'N : d' ≤ N
  · exact hmax d' (Finset.mem_Icc.mpr ⟨hd', hd'N⟩)
  · push_neg at hd'N
    have hc0 : c ≤ r dm / dm := hmax d0 (Finset.mem_Icc.mpr ⟨hd0pos, by omega⟩)
    have hd'R : (0 : ℝ) < d' := by exact_mod_cast hd'
    have hRc : Rmax / c ≤ (N : ℝ) := by
      have := Nat.le_ceil (Rmax / c)
      have : ((⌈Rmax / c⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : ⌈Rmax / c⌉₊ ≤ N)
      linarith
    have hNd : (N : ℝ) < d' := by exact_mod_cast hd'N
    have h1 : r d' / d' ≤ Rmax / d' := div_le_div_of_nonneg_right (hle d') hd'R.le
    have h2 : Rmax / d' < c := by
      rw [div_lt_iff₀ hd'R]
      rw [div_le_iff₀ hcpos] at hRc
      nlinarith
    linarith

theorem supp_one_spec (r : ℕ → ℝ) (Rmax : ℝ) (hr : ArmAdmissible r Rmax) :
    0 < supp r 1 ∧ ∀ d, 0 < d → r d / d ≤ r (supp r 1) / (supp r 1 : ℝ) := by
  classical
  have hex := exists_max_slope r Rmax hr
  have hs : supp r 1 = Nat.find hex := by
    show nextSupp r (supp r 0) = Nat.find hex
    simp only [supp]
    unfold nextSupp
    rw [dif_pos hex]
  have hspec := Nat.find_spec hex
  rw [hs]
  refine ⟨hspec.1, fun d hd => ?_⟩
  have := hspec.2 d hd
  rwa [slope_eq r hr.1, slope_eq r hr.1] at this

theorem prev_lt (S : Finset ℕ) (s : ℕ) (hs : 1 ≤ s) : prevPull S s < s := by
  unfold prevPull
  rcases (S.filter (· < s)).eq_empty_or_nonempty with h | h
  · rw [h]; simp; omega
  · obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (S.filter (· < s)) id h
    have : (S.filter (· < s)).sup id = a := by
      apply le_antisymm
      · exact Finset.sup_le fun b hb => hmax b hb
      · exact Finset.le_sup (f := id) ha
    rw [this]
    exact (Finset.mem_filter.mp ha).2

theorem le_prev (S : Finset ℕ) (s s' : ℕ) (hs : s ∈ S) (hlt : s < s') : s ≤ prevPull S s' := by
  unfold prevPull
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hs, hlt⟩)

theorem gap_sum_le (S : Finset ℕ) (T : ℕ) (hS : S ⊆ Finset.Icc 1 T) :
    ∑ s ∈ S, (s - prevPull S s) ≤ T := by
  classical
  have hdisj : (S : Set ℕ).PairwiseDisjoint fun s => Finset.Ioc (prevPull S s) s := by
    intro s hs s' hs' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha ha'
    rw [Finset.mem_Ioc] at ha ha'
    rcases lt_or_gt_of_ne hne with h | h
    · have := le_prev S s s' hs h
      omega
    · have := le_prev S s' s hs' h
      omega
  have hcard : ∑ s ∈ S, (s - prevPull S s) = (S.biUnion fun s => Finset.Ioc (prevPull S s) s).card := by
    rw [Finset.card_biUnion hdisj]
    apply Finset.sum_congr rfl
    intro s _
    rw [Nat.card_Ioc]
  rw [hcard]
  calc (S.biUnion fun s => Finset.Ioc (prevPull S s) s).card ≤ (Finset.Icc 1 T).card := by
        apply Finset.card_le_card
        intro a ha
        rw [Finset.mem_biUnion] at ha
        obtain ⟨s, hs, ha⟩ := ha
        rw [Finset.mem_Ioc] at ha
        have := Finset.mem_Icc.mp (hS hs)
        rw [Finset.mem_Icc]
        omega
    _ = T := by simp

end RecoveringBandits.Aux_RB

open RecoveringBandits RecoveringBandits.Aux_RB Filter Topology in
theorem solution (r : ℕ → ℝ) (Rmax : ℝ) (hr : ArmAdmissible r Rmax) (x : ℝ)
    (hx : 1 / (supp r 1 : ℝ) ≤ x) :
    (∀ T : ℕ, 1 ≤ T → FT r T x ≤ r (supp r 1) / (supp r 1 : ℝ)) ∧
    F r x = r (supp r 1) / (supp r 1 : ℝ) := by
  classical
  obtain ⟨hd1pos, hslope⟩ := supp_one_spec r Rmax hr
  set d1 := supp r 1 with hd1
  set sstar := r d1 / (d1 : ℝ) with hsstar
  have hd1R : (0 : ℝ) < d1 := by exact_mod_cast hd1pos
  have hrd1 : 0 ≤ r d1 := hr.2.1 d1
  have hs0 : 0 ≤ sstar := div_nonneg hrd1 hd1R.le
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hx
  -- reward bound
  have hreward : ∀ T (S : Finset ℕ), S ⊆ Finset.Icc 1 T → schedReward r S ≤ sstar * T := by
    intro T S hS
    unfold schedReward
    have h1 : ∀ s ∈ S, r (s - prevPull S s) ≤ sstar * ((s - prevPull S s : ℕ) : ℝ) := by
      intro s hs
      have hs1 : 1 ≤ s := (Finset.mem_Icc.mp (hS hs)).1
      have hlt := prev_lt S s hs1
      have hg : 0 < s - prevPull S s := by omega
      have hgR : (0 : ℝ) < ((s - prevPull S s : ℕ) : ℝ) := by exact_mod_cast hg
      have := hslope _ hg
      rw [div_le_iff₀ hgR] at this
      linarith
    calc ∑ s ∈ S, r (s - prevPull S s) ≤ ∑ s ∈ S, sstar * ((s - prevPull S s : ℕ) : ℝ) :=
          Finset.sum_le_sum h1
      _ = sstar * ((∑ s ∈ S, (s - prevPull S s) : ℕ) : ℝ) := by
          rw [← Finset.mul_sum]; push_cast; rfl
      _ ≤ sstar * T := by
          apply mul_le_mul_of_nonneg_left _ hs0
          exact_mod_cast gap_sum_le S T hS
  have hupper : ∀ T : ℕ, 1 ≤ T → FT r T x ≤ sstar := by
    intro T hT
    have hTR : (0 : ℝ) < T := by exact_mod_cast hT
    unfold FT
    apply csSup_le
    · exact ⟨_, ⟨∅, ⟨Finset.empty_subset _, by simp; positivity⟩, rfl⟩⟩
    · rintro _ ⟨S, ⟨hS, _⟩, rfl⟩
      rw [div_le_iff₀ hTR]
      exact hreward T S hS
  have hbdd : ∀ T : ℕ, 1 ≤ T → BddAbove ((fun S : Finset ℕ => schedReward r S / T) ''
      {S | S ⊆ Finset.Icc 1 T ∧ (S.card : ℝ) ≤ x * T}) := by
    intro T hT
    have hTR : (0 : ℝ) < T := by exact_mod_cast hT
    refine ⟨sstar, ?_⟩
    rintro _ ⟨S, ⟨hS, _⟩, rfl⟩
    rw [div_le_iff₀ hTR]
    exact hreward T S hS
  -- periodic schedule
  have hlower : ∀ T : ℕ, 1 ≤ T → ((T / d1 : ℕ) : ℝ) * r d1 / T ≤ FT r T x := by
    intro T hT
    have hTR : (0 : ℝ) < T := by exact_mod_cast hT
    set K := T / d1 with hK
    set S : Finset ℕ := (Finset.range K).image fun j => (j + 1) * d1 with hSdef
    have hinj : Function.Injective fun j : ℕ => (j + 1) * d1 := by
      intro a b h
      simp only at h
      have := Nat.eq_of_mul_eq_mul_right hd1pos h
      omega
    have hKd : K * d1 ≤ T := Nat.div_mul_le_self T d1
    have hSsub : S ⊆ Finset.Icc 1 T := by
      intro s hs
      rw [hSdef, Finset.mem_image] at hs
      obtain ⟨j, hj, rfl⟩ := hs
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Icc]
      constructor
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      · calc (j + 1) * d1 ≤ K * d1 := Nat.mul_le_mul_right _ (by omega)
          _ ≤ T := hKd
    have hcardS : S.card = K := by
      rw [hSdef, Finset.card_image_of_injective _ hinj, Finset.card_range]
    have hcardle : (S.card : ℝ) ≤ x * T := by
      rw [hcardS]
      have h1 : (K : ℝ) ≤ (T : ℝ) / d1 := Nat.cast_div_le
      have h2 : (T : ℝ) / d1 = T * (1 / d1) := by ring
      have h3 : (T : ℝ) * (1 / d1) ≤ T * x := mul_le_mul_of_nonneg_left hx hTR.le
      linarith
    have hprev : ∀ j < K, prevPull S ((j + 1) * d1) = j * d1 := by
      intro j hj
      unfold prevPull
      have hfilter : S.filter (· < (j + 1) * d1) = (Finset.range j).image fun i => (i + 1) * d1 := by
        ext s
        simp only [hSdef, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨⟨i, hi, rfl⟩, hlt⟩
          refine ⟨i, ?_, rfl⟩
          by_contra hge
          push_neg at hge
          have : (j + 1) * d1 ≤ (i + 1) * d1 := Nat.mul_le_mul_right _ (by omega)
          omega
        · rintro ⟨i, hi, rfl⟩
          refine ⟨⟨i, by omega, rfl⟩, ?_⟩
          exact Nat.mul_lt_mul_of_pos_right (by omega) hd1pos
      rw [hfilter]
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0; simp
      · apply le_antisymm
        · apply Finset.sup_le
          intro s hs
          rw [Finset.mem_image] at hs
          obtain ⟨i, hi, rfl⟩ := hs
          rw [Finset.mem_range] at hi
          exact Nat.mul_le_mul_right _ (by omega)
        · have hmem : j * d1 ∈ (Finset.range j).image fun i => (i + 1) * d1 := by
            rw [Finset.mem_image]
            exact ⟨j - 1, Finset.mem_range.mpr (by omega), by
              rw [show j - 1 + 1 = j by omega]⟩
          exact Finset.le_sup (f := id) hmem
    have hrewardS : schedReward r S = K * r d1 := by
      unfold schedReward
      rw [hSdef, Finset.sum_image (fun a _ b _ h => hinj h)]
      rw [← hSdef]
      have : ∀ j ∈ Finset.range K, r ((j + 1) * d1 - prevPull S ((j + 1) * d1)) = r d1 := by
        intro j hj
        rw [hprev j (Finset.mem_range.mp hj)]
        congr 1
        rw [Nat.add_mul, one_mul, Nat.add_sub_cancel_left]
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hmemset : schedReward r S / T ∈ ((fun S : Finset ℕ => schedReward r S / T) ''
        {S | S ⊆ Finset.Icc 1 T ∧ (S.card : ℝ) ≤ x * T}) := ⟨S, ⟨hSsub, hcardle⟩, rfl⟩
    have := le_csSup (hbdd T hT) hmemset
    unfold FT
    rw [hrewardS] at this
    exact this
  refine ⟨hupper, ?_⟩
  -- limit
  have htend : Tendsto (fun T : ℕ => FT r (T + 1) x) atTop (𝓝 sstar) := by
    have hL : Tendsto (fun T : ℕ => sstar - r d1 * (1 / ((T : ℝ) + 1))) atTop (𝓝 sstar) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (r d1)
      have := this.const_sub sstar
      simpa using this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hL tendsto_const_nhds
    · intro T
      have hT1 : 1 ≤ T + 1 := by omega
      have hl := hlower (T + 1) hT1
      have hTR : (0 : ℝ) < ((T + 1 : ℕ) : ℝ) := by positivity
      have hkey : ((T + 1 : ℕ) : ℝ) < (d1 : ℝ) * (((T + 1) / d1 : ℕ) + 1 : ℝ) := by
        have := Nat.lt_mul_div_succ (T + 1) hd1pos
        exact_mod_cast this
      simp only
      refine le_trans ?_ hl
      have hK : ((T + 1 : ℕ) : ℝ) / d1 - 1 ≤ (((T + 1) / d1 : ℕ) : ℝ) := by
        rw [div_sub_one hd1R.ne', div_le_iff₀ hd1R]
        linarith
      rw [hsstar]
      push_cast at hK hTR ⊢
      rw [le_div_iff₀ hTR]
      have : (r d1 / d1 - r d1 * (1 / ((T : ℝ) + 1))) * ((T : ℝ) + 1) =
          ((T + 1 : ℝ) / d1 - 1) * r d1 := by
        field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right hK hrd1
    · intro T
      exact hupper (T + 1) (by omega)
  unfold F
  exact htend.limsup_eq
