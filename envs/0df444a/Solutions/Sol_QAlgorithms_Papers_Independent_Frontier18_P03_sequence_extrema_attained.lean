-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P03.sequence_extrema_attained
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T14:52:19.614188+00:00
-- url     : https://prove2.me/submissions/8905a55f-fa16-4897-a7ca-6aac1d7332ba

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P03

open Filter

namespace X6F03G

/-- revisit every requirement infinitely often at witness times -/
theorem diagF (W : ℕ → Set ℕ) (hW : ∀ j, ∃ᶠ n in atTop, n ∈ W j) :
    ∃ J : ℕ → ℕ, ∀ j, ∃ᶠ n in atTop, J n = j ∧ n ∈ W j := by
  classical
  set σ : ℕ → ℕ := fun k => (Nat.unpair k).1
  have hnext : ∀ k N, ∃ n ≥ N, n ∈ W (σ k) := fun k N => frequently_atTop.1 (hW (σ k)) N
  choose nx hnx1 hnx2 using hnext
  let t : ℕ → ℕ := fun k => Nat.rec (nx 0 0) (fun k tk => nx (k + 1) (tk + 1)) k
  have ht0 : t 0 = nx 0 0 := rfl
  have hts : ∀ k, t (k + 1) = nx (k + 1) (t k + 1) := fun k => rfl
  have hmono : StrictMono t := by
    apply strictMono_nat_of_lt_succ
    intro k
    rw [hts]
    exact Nat.lt_of_succ_le (hnx1 _ _)
  have hW' : ∀ k, t k ∈ W (σ k) := by
    intro k
    cases k with
    | zero => rw [ht0]; exact hnx2 0 0
    | succ k => rw [hts]; exact hnx2 _ _
  refine ⟨fun n : ℕ => @dite _ (∃ k, t k = n) (Classical.propDecidable _)
    (fun h => σ (Classical.choose h)) (fun _ => 0), fun j => ?_⟩
  rw [frequently_atTop]
  intro N
  refine ⟨t (Nat.pair j N), ?_, ?_, ?_⟩
  · exact (Nat.right_le_pair j N).trans (hmono.id_le _)
  · have h : ∃ k, t k = t (Nat.pair j N) := ⟨_, rfl⟩
    dsimp only
    rw [dif_pos h]
    have := hmono.injective (Classical.choose_spec h)
    rw [this]
    simp [σ]
  · have := hW' (Nat.pair j N)
    simpa [σ] using this

/-- eventually-type diagonal argument with monotone requirements -/
theorem diagE (u : ℕ → ℕ → ℕ → ℝ) (x : ℝ)
    (hmono : ∀ j n i i', i ≤ i' → u j n i ≤ u j n i')
    (h : ∀ j, ∀ ε > 0, ∀ᶠ n in atTop, u j n j ≤ x + ε) :
    ∃ J : ℕ → ℕ, ∀ i, ∀ ε > 0, ∀ᶠ n in atTop, u (J n) n i ≤ x + ε := by
  classical
  have hN : ∀ j, ∃ N, ∀ n ≥ N, u j n j ≤ x + 1 / ((j : ℝ) + 1) := by
    intro j
    exact eventually_atTop.1 (h j _ (by positivity))
  choose N hN using hN
  set M : ℕ → ℕ := fun j => (∑ i ∈ Finset.range (j + 1), N i) + j
  have hMN : ∀ j, N j ≤ M j := by
    intro j
    have : N j ≤ ∑ i ∈ Finset.range (j + 1), N i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ j)
    simp only [M]; omega
  have hMj : ∀ j, j ≤ M j := fun j => by simp only [M]; omega
  set J : ℕ → ℕ := fun n => Nat.findGreatest (fun j => M j ≤ n) n
  have hJ1 : ∀ j n, M j ≤ n → j ≤ J n := fun j n hjn =>
    Nat.le_findGreatest ((hMj j).trans hjn) hjn
  have hJ2 : ∀ n, M 0 ≤ n → M (J n) ≤ n := fun n hn =>
    Nat.findGreatest_spec (P := fun j => M j ≤ n) (Nat.zero_le n) hn
  refine ⟨J, fun i ε hε => ?_⟩
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
  rw [eventually_atTop]
  refine ⟨M (max i K) + M 0, fun n hn => ?_⟩
  have h1 : max i K ≤ J n := hJ1 _ _ (by omega)
  have h2 : M (J n) ≤ n := hJ2 n (by omega)
  have h3 := hN (J n) n ((hMN _).trans h2)
  have h4 : u (J n) n i ≤ u (J n) n (J n) := hmono _ _ _ _ ((le_max_left _ _).trans h1)
  have h5 : 1 / ((J n : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (K : ℝ) ≤ J n := by exact_mod_cast (le_max_right _ _).trans h1
    linarith
  linarith


theorem approx_below (s : EReal) (hs : s ≠ ⊥) : ∃ a : ℕ → ℝ, Monotone a ∧
    (∀ j, (a j : EReal) < s) ∧ ∀ m : EReal, (∀ j, (a j : EReal) ≤ m) → s ≤ m := by
  induction s using EReal.rec with
  | bot => exact absurd rfl hs
  | coe r =>
    refine ⟨fun j => r - 1 / ((j : ℝ) + 1), fun i j hij => ?_, fun j => ?_, fun m hm => ?_⟩
    · have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (i : ℝ) ≤ j := by exact_mod_cast hij
        linarith
      simp only; linarith
    · exact EReal.coe_lt_coe_iff.2 (by simp only; linarith [show (0:ℝ) < 1 / ((j:ℝ)+1) by positivity])
    · induction m using EReal.rec with
      | bot => exact absurd (hm 0) (by rw [le_bot_iff]; exact EReal.coe_ne_bot _)
      | top => exact le_top
      | coe t =>
        rw [EReal.coe_le_coe_iff]
        by_contra h
        push Not at h
        obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 h)
        have := EReal.coe_le_coe_iff.1 (hm j)
        linarith
  | top =>
    refine ⟨fun j => (j : ℝ), fun i j hij => by show ((i : ℕ) : ℝ) ≤ (j : ℝ); exact_mod_cast hij, fun j => EReal.coe_lt_top _,
      fun m hm => ?_⟩
    induction m using EReal.rec with
    | bot => exact absurd (hm 0) (by rw [le_bot_iff]; exact EReal.coe_ne_bot _)
    | top => exact le_rfl
    | coe t =>
      obtain ⟨j, hj⟩ := exists_nat_gt t
      have := EReal.coe_le_coe_iff.1 (hm j)
      linarith

theorem approx_above (s : EReal) (hs : s ≠ ⊤) : ∃ a : ℕ → ℝ, Antitone a ∧
    (∀ j, s < (a j : EReal)) ∧ ∀ m : EReal, (∀ j, m ≤ (a j : EReal)) → m ≤ s := by
  obtain ⟨a, ha1, ha2, ha3⟩ := approx_below (-s) (by simpa using hs)
  refine ⟨fun j => -a j, fun i j hij => neg_le_neg (ha1 hij), fun j => ?_, fun m hm => ?_⟩
  · have := ha2 j
    rw [EReal.coe_neg]
    exact EReal.lt_neg_comm.1 this
  · have := ha3 (-m) fun j => by
      have := hm j
      rw [EReal.coe_neg] at this
      exact EReal.le_neg.1 this
    exact EReal.neg_le_neg_iff.1 this


open QAlgorithms.Papers.Independent.Frontier18.P03

section parts
variable (F : ℕ → Set (ℝ → ℝ)) (hne : ∀ n, (F n).Nonempty)
  (hmono : ∀ n, ∀ f ∈ F n, Monotone f) (x : ℝ)

include hmono in
theorem limsup_mono (g : FunctionChoices F) {a b : ℝ} (hab : a ≤ b) :
    limsup (fun n => ((g.val n a : ℝ) : EReal)) atTop ≤
      limsup (fun n => ((g.val n b : ℝ) : EReal)) atTop :=
  limsup_le_limsup (Eventually.of_forall fun n =>
    EReal.coe_le_coe_iff.2 (hmono n _ (g.prop n) hab))

include hmono in
theorem liminf_mono (g : FunctionChoices F) {a b : ℝ} (hab : a ≤ b) :
    liminf (fun n => ((g.val n a : ℝ) : EReal)) atTop ≤
      liminf (fun n => ((g.val n b : ℝ) : EReal)) atTop :=
  liminf_le_liminf (Eventually.of_forall fun n =>
    EReal.coe_le_coe_iff.2 (hmono n _ (g.prop n) hab))

include hne in
theorem choice0 : Nonempty (FunctionChoices F) :=
  ⟨⟨fun n => (hne n).some, fun n => (hne n).some_mem⟩⟩

include hne hmono in
theorem part1 : ∃ f : FunctionChoices F,
    IsGreatest (Set.range fun g : FunctionChoices F => minusCutoff g.val x)
      (minusCutoff f.val x) := by
  suffices h : ∃ f : FunctionChoices F, ∀ g : FunctionChoices F,
      minusCutoff g.val x ≤ minusCutoff f.val x by
    obtain ⟨f, hf⟩ := h
    exact ⟨f, ⟨f, rfl⟩, by rintro _ ⟨g, rfl⟩; exact hf g⟩
  set s := ⨆ g : FunctionChoices F, minusCutoff g.val x
  by_cases hs : s = ⊥
  · obtain ⟨f0⟩ := choice0 F hne
    refine ⟨f0, fun g => ?_⟩
    have := le_iSup (fun g : FunctionChoices F => minusCutoff g.val x) g
    rw [show (⨆ g : FunctionChoices F, minusCutoff g.val x) = ⊥ from hs] at this
    exact this.trans bot_le
  obtain ⟨a, ha_mono, ha_lt, ha_sup⟩ := approx_below s hs
  have hreq : ∀ j, ∃ g : FunctionChoices F,
      limsup (fun n => ((g.val n (a j) : ℝ) : EReal)) atTop ≤ x := by
    intro j
    obtain ⟨g, hg⟩ := lt_iSup_iff.1 (ha_lt j)
    obtain ⟨r, ⟨b, rfl, hb⟩, hab⟩ := lt_sSup_iff.1 hg
    exact ⟨g, (limsup_mono F hmono g (EReal.coe_lt_coe_iff.1 hab).le).trans hb⟩
  choose g hg using hreq
  set u : ℕ → ℕ → ℕ → ℝ := fun j n i => (g j).val n (a i)
  have hu : ∀ j n i i', i ≤ i' → u j n i ≤ u j n i' := fun j n i i' h =>
    hmono n _ ((g j).prop n) (ha_mono h)
  have hev : ∀ j, ∀ ε > 0, ∀ᶠ n in atTop, u j n j ≤ x + ε := by
    intro j ε hε
    have hlt : limsup (fun n => (((g j).val n (a j) : ℝ) : EReal)) atTop < ((x + ε : ℝ) : EReal) :=
      (hg j).trans_lt (EReal.coe_lt_coe_iff.2 (by linarith))
    filter_upwards [eventually_lt_of_limsup_lt hlt] with n hn
    exact (EReal.coe_lt_coe_iff.1 hn).le
  obtain ⟨J, hJ⟩ := diagE u x hu hev
  let f : FunctionChoices F := ⟨fun n => (g (J n)).val n, fun n => (g (J n)).prop n⟩
  refine ⟨f, fun g' => (le_iSup (fun g : FunctionChoices F => minusCutoff g.val x) g').trans
    (ha_sup _ fun j => ?_)⟩
  apply le_sSup
  refine ⟨a j, rfl, ?_⟩
  apply EReal.le_of_forall_lt_iff_le.1
  intro z hz
  have hz' : x < z := EReal.coe_lt_coe_iff.1 hz
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hJ j (z - x) (by linarith)] with n hn
  have : (f.val n (a j)) ≤ z := by
    have : u (J n) n j = f.val n (a j) := rfl
    linarith
  exact_mod_cast this

include hne hmono in
theorem part2 : ∃ f : FunctionChoices F,
    IsGreatest (Set.range fun g : FunctionChoices F => plusCutoff g.val x)
      (plusCutoff f.val x) := by
  suffices h : ∃ f : FunctionChoices F, ∀ g : FunctionChoices F,
      plusCutoff g.val x ≤ plusCutoff f.val x by
    obtain ⟨f, hf⟩ := h
    exact ⟨f, ⟨f, rfl⟩, by rintro _ ⟨g, rfl⟩; exact hf g⟩
  set s := ⨆ g : FunctionChoices F, plusCutoff g.val x
  by_cases hs : s = ⊥
  · obtain ⟨f0⟩ := choice0 F hne
    refine ⟨f0, fun g => ?_⟩
    have := le_iSup (fun g : FunctionChoices F => plusCutoff g.val x) g
    rw [show (⨆ g : FunctionChoices F, plusCutoff g.val x) = ⊥ from hs] at this
    exact this.trans bot_le
  obtain ⟨a, -, ha_lt, ha_sup⟩ := approx_below s hs
  have hreq : ∀ j, ∃ g : FunctionChoices F, ∃ y : ℝ, y < x ∧
      ∃ᶠ n in atTop, g.val n (a j) < y := by
    intro j
    obtain ⟨g, hg⟩ := lt_iSup_iff.1 (ha_lt j)
    have hnot : liminf (fun n => ((g.val n (a j) : ℝ) : EReal)) atTop < (x : EReal) := by
      by_contra h
      push Not at h
      have : plusCutoff g.val x ≤ (a j : EReal) := sInf_le ⟨a j, rfl, h⟩
      exact absurd hg (not_lt.2 this)
    obtain ⟨y, hy1, hy2⟩ := EReal.lt_iff_exists_real_btwn.1 hnot
    refine ⟨g, y, EReal.coe_lt_coe_iff.1 hy2, ?_⟩
    exact (frequently_lt_of_liminf_lt (by isBoundedDefault) hy1).mono fun n hn =>
      EReal.coe_lt_coe_iff.1 hn
  choose g y hy hfreq using hreq
  obtain ⟨J, hJ⟩ := diagF (fun j => {n | (g j).val n (a j) < y j}) hfreq
  let f : FunctionChoices F := ⟨fun n => (g (J n)).val n, fun n => (g (J n)).prop n⟩
  refine ⟨f, fun g' => (le_iSup (fun g : FunctionChoices F => plusCutoff g.val x) g').trans
    (ha_sup _ fun j => ?_)⟩
  apply le_sInf
  rintro r ⟨b, rfl, hb⟩
  by_contra hlt
  push Not at hlt
  have hba : b ≤ a j := (EReal.coe_lt_coe_iff.1 hlt).le
  have h1 : liminf (fun n => ((f.val n (a j) : ℝ) : EReal)) atTop ≤ (y j : EReal) := by
    apply liminf_le_of_frequently_le'
    refine (hJ j).mono fun n hn => ?_
    obtain ⟨hJn, hn⟩ := hn
    have : f.val n (a j) = (g j).val n (a j) := by
      show (g (J n)).val n (a j) = _
      rw [hJn]
    rw [this]
    exact EReal.coe_le_coe_iff.2 (le_of_lt hn)
  have h2 := (liminf_mono F hmono f hba).trans h1
  have h3 : (y j : EReal) < x := EReal.coe_lt_coe_iff.2 (hy j)
  exact absurd (hb.trans h2) (not_le.2 h3)

include hne hmono in
theorem part3 : ∃ f : FunctionChoices F,
    IsLeast (Set.range fun g : FunctionChoices F => minusCutoff g.val x)
      (minusCutoff f.val x) := by
  suffices h : ∃ f : FunctionChoices F, ∀ g : FunctionChoices F,
      minusCutoff f.val x ≤ minusCutoff g.val x by
    obtain ⟨f, hf⟩ := h
    exact ⟨f, ⟨f, rfl⟩, by rintro _ ⟨g, rfl⟩; exact hf g⟩
  set s := ⨅ g : FunctionChoices F, minusCutoff g.val x
  by_cases hs : s = ⊤
  · obtain ⟨f0⟩ := choice0 F hne
    refine ⟨f0, fun g => ?_⟩
    have := iInf_le (fun g : FunctionChoices F => minusCutoff g.val x) g
    rw [show (⨅ g : FunctionChoices F, minusCutoff g.val x) = ⊤ from hs] at this
    exact le_top.trans this
  obtain ⟨a, -, ha_lt, ha_inf⟩ := approx_above s hs
  have hreq : ∀ j, ∃ g : FunctionChoices F, ∃ y : ℝ, x < y ∧
      ∃ᶠ n in atTop, y < g.val n (a j) := by
    intro j
    obtain ⟨g, hg⟩ := iInf_lt_iff.1 (ha_lt j)
    have hnot : (x : EReal) < limsup (fun n => ((g.val n (a j) : ℝ) : EReal)) atTop := by
      by_contra h
      push Not at h
      have : (a j : EReal) ≤ minusCutoff g.val x := le_sSup ⟨a j, rfl, h⟩
      exact absurd hg (not_lt.2 this)
    obtain ⟨y, hy1, hy2⟩ := EReal.lt_iff_exists_real_btwn.1 hnot
    refine ⟨g, y, EReal.coe_lt_coe_iff.1 hy1, ?_⟩
    exact (frequently_lt_of_lt_limsup (by isBoundedDefault) hy2).mono fun n hn =>
      EReal.coe_lt_coe_iff.1 hn
  choose g y hy hfreq using hreq
  obtain ⟨J, hJ⟩ := diagF (fun j => {n | y j < (g j).val n (a j)}) hfreq
  let f : FunctionChoices F := ⟨fun n => (g (J n)).val n, fun n => (g (J n)).prop n⟩
  refine ⟨f, fun g' => (ha_inf _ fun j => ?_).trans
    (iInf_le (fun g : FunctionChoices F => minusCutoff g.val x) g')⟩
  apply sSup_le
  rintro r ⟨b, rfl, hb⟩
  by_contra hlt
  push Not at hlt
  have hab : a j ≤ b := (EReal.coe_lt_coe_iff.1 hlt).le
  have h1 : (y j : EReal) ≤ limsup (fun n => ((f.val n (a j) : ℝ) : EReal)) atTop := by
    apply le_limsup_of_frequently_le'
    refine (hJ j).mono fun n hn => ?_
    obtain ⟨hJn, hn⟩ := hn
    have : f.val n (a j) = (g j).val n (a j) := by
      show (g (J n)).val n (a j) = _
      rw [hJn]
    rw [this]
    exact EReal.coe_le_coe_iff.2 (le_of_lt hn)
  have h2 := h1.trans ((limsup_mono F hmono f hab).trans hb)
  have h3 : (x : EReal) < y j := EReal.coe_lt_coe_iff.2 (hy j)
  exact absurd h2 (not_le.2 h3)

include hne hmono in
theorem part4 : ∃ f : FunctionChoices F,
    IsLeast (Set.range fun g : FunctionChoices F => plusCutoff g.val x)
      (plusCutoff f.val x) := by
  suffices h : ∃ f : FunctionChoices F, ∀ g : FunctionChoices F,
      plusCutoff f.val x ≤ plusCutoff g.val x by
    obtain ⟨f, hf⟩ := h
    exact ⟨f, ⟨f, rfl⟩, by rintro _ ⟨g, rfl⟩; exact hf g⟩
  set s := ⨅ g : FunctionChoices F, plusCutoff g.val x
  by_cases hs : s = ⊤
  · obtain ⟨f0⟩ := choice0 F hne
    refine ⟨f0, fun g => ?_⟩
    have := iInf_le (fun g : FunctionChoices F => plusCutoff g.val x) g
    rw [show (⨅ g : FunctionChoices F, plusCutoff g.val x) = ⊤ from hs] at this
    exact le_top.trans this
  obtain ⟨a, ha_anti, ha_lt, ha_inf⟩ := approx_above s hs
  have hreq : ∀ j, ∃ g : FunctionChoices F,
      (x : EReal) ≤ liminf (fun n => ((g.val n (a j) : ℝ) : EReal)) atTop := by
    intro j
    obtain ⟨g, hg⟩ := iInf_lt_iff.1 (ha_lt j)
    obtain ⟨r, ⟨b, rfl, hb⟩, hba⟩ := sInf_lt_iff.1 hg
    exact ⟨g, hb.trans (liminf_mono F hmono g (EReal.coe_lt_coe_iff.1 hba).le)⟩
  choose g hg using hreq
  set u : ℕ → ℕ → ℕ → ℝ := fun j n i => -(g j).val n (a i)
  have hu : ∀ j n i i', i ≤ i' → u j n i ≤ u j n i' := fun j n i i' h =>
    neg_le_neg (hmono n _ ((g j).prop n) (ha_anti h))
  have hev : ∀ j, ∀ ε > 0, ∀ᶠ n in atTop, u j n j ≤ -x + ε := by
    intro j ε hε
    have hlt : ((x - ε : ℝ) : EReal) < liminf (fun n => (((g j).val n (a j) : ℝ) : EReal)) atTop :=
      (EReal.coe_lt_coe_iff.2 (by linarith)).trans_le (hg j)
    filter_upwards [eventually_lt_of_lt_liminf hlt] with n hn
    have := (EReal.coe_lt_coe_iff.1 hn).le
    simp only [u]; linarith
  obtain ⟨J, hJ⟩ := diagE u (-x) hu hev
  let f : FunctionChoices F := ⟨fun n => (g (J n)).val n, fun n => (g (J n)).prop n⟩
  refine ⟨f, fun g' => (ha_inf _ fun j => ?_).trans
    (iInf_le (fun g : FunctionChoices F => plusCutoff g.val x) g')⟩
  apply sInf_le
  refine ⟨a j, rfl, ?_⟩
  apply EReal.ge_of_forall_gt_iff_ge.1
  intro z hz
  have hz' : z < x := EReal.coe_lt_coe_iff.1 hz
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hJ j (x - z) (by linarith)] with n hn
  have : z ≤ f.val n (a j) := by
    have : u (J n) n j = -f.val n (a j) := rfl
    linarith
  exact_mod_cast this

end parts

end X6F03G

open X6F03G QAlgorithms.Papers.Independent.Frontier18.P03 in
theorem solution
    (F : ℕ → Set (ℝ → ℝ))
    (hne : ∀ n, (F n).Nonempty)
    (hmono : ∀ n, ∀ f ∈ F n, Monotone f) (x : ℝ) :
    (∃ f : FunctionChoices F,
      IsGreatest (Set.range fun g : FunctionChoices F => minusCutoff g.val x)
        (minusCutoff f.val x)) ∧
    (∃ f : FunctionChoices F,
      IsGreatest (Set.range fun g : FunctionChoices F => plusCutoff g.val x)
        (plusCutoff f.val x)) ∧
    (∃ f : FunctionChoices F,
      IsLeast (Set.range fun g : FunctionChoices F => minusCutoff g.val x)
        (minusCutoff f.val x)) ∧
    (∃ f : FunctionChoices F,
      IsLeast (Set.range fun g : FunctionChoices F => plusCutoff g.val x)
        (plusCutoff f.val x)) :=
  ⟨part1 F hne hmono x, part2 F hne hmono x, part3 F hne hmono x, part4 F hne hmono x⟩
