-- Prove2me | solution 1 for RubinsteinBargaining.PEP.proposition_4
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T18:53:14.796616+00:00
-- url     : https://prove2.me/submissions/8101673b-1d52-49c0-955a-be61fd9899e1

import Definitions.Def_RubinsteinBargaining_PEP_EquilibriumSets
import Definitions.Def_RubinsteinBargaining_PEP_Delta

open scoped Classical
open RubinsteinBargaining.PEP

namespace DisproveRubinsteinProp4

noncomputable def w1 (x : ℝ) : ℝ :=
  4 * x + if (1 / 2 : ℝ) ≤ x then 1 else 0

noncomputable def w2 (x : ℝ) : ℝ :=
  4 * (1 - x)

noncomputable def u1 (s : Partition) (t : ℕ) : ℝ :=
  w1 s.val - (t : ℝ)

noncomputable def u2 (s : Partition) (t : ℕ) : ℝ :=
  w2 s.val - (t : ℝ)

def relFromUtil (u : Partition → ℕ → ℝ) : Outcome → Outcome → Prop
  | _, none => True
  | none, some _ => False
  | some (r, t1), some (s, t2) => u s t2 ≤ u r t1

def prefFromUtil (u : Partition → ℕ → ℝ) : Preference where
  weak := relFromUtil u
  complete a b := by
    cases a <;> cases b <;> simp [relFromUtil]
    exact le_total _ _
  reflexive a := by
    cases a <;> simp [relFromUtil]
  transitive a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> simp [relFromUtil] at hab hbc ⊢
    exact le_trans hbc hab

noncomputable def p0 : Preferences where
  one := prefFromUtil u1
  two := prefFromUtil u2

@[simp] lemma weak_one_agreement (r s : Partition) (t1 t2 : ℕ) :
    weak p0 .one (agreement r t1) (agreement s t2) ↔ u1 s t2 ≤ u1 r t1 := Iff.rfl

@[simp] lemma weak_two_agreement (r s : Partition) (t1 t2 : ℕ) :
    weak p0 .two (agreement r t1) (agreement s t2) ↔ u2 s t2 ≤ u2 r t1 := Iff.rfl

@[simp] lemma weak_none_right (i : Player) (a : Outcome) :
    weak p0 i a none := by
  cases i <;> cases a <;> simp [weak, preference, p0, prefFromUtil, relFromUtil]

@[simp] lemma weak_none_left_agreement (i : Player) (s : Partition) (t : ℕ) :
    ¬ weak p0 i none (agreement s t) := by
  cases i <;> simp [weak, preference, p0, prefFromUtil, relFromUtil, agreement]

lemma strict_one_agreement (r s : Partition) (t1 t2 : ℕ) :
    strict p0 .one (agreement r t1) (agreement s t2) ↔ u1 s t2 < u1 r t1 := by
  dsimp [strict]
  rw [weak_one_agreement, weak_one_agreement, not_le]
  exact ⟨fun h => h.2, fun h => ⟨le_of_lt h, h⟩⟩

lemma strict_two_agreement (r s : Partition) (t1 t2 : ℕ) :
    strict p0 .two (agreement r t1) (agreement s t2) ↔ u2 s t2 < u2 r t1 := by
  dsimp [strict]
  rw [weak_two_agreement, weak_two_agreement, not_le]
  exact ⟨fun h => h.2, fun h => ⟨le_of_lt h, h⟩⟩

lemma w1_strictMono : StrictMono w1 := by
  intro x y hxy
  dsimp [w1]
  split_ifs with hx hy hy
  · linarith
  · exfalso; linarith
  · linarith
  · linarith

lemma p0_A1 : A1 p0 := by
  intro i r s t hrs
  cases i
  · rw [strict_one_agreement]
    dsimp [u1]
    have hrs' : s.val < r.val := hrs
    have := w1_strictMono hrs'
    linarith
  · rw [strict_two_agreement]
    dsimp [u2, w2]
    dsimp [share] at hrs
    linarith

lemma p0_A2 : A2 p0 := by
  intro i s t1 t2 _ ht
  have htR : (t1 : ℝ) < (t2 : ℝ) := Nat.cast_lt.mpr ht
  cases i
  · constructor
    · rw [strict_one_agreement]; dsimp [u1]; linarith
    · exact ⟨weak_none_right .one (agreement s t2), weak_none_left_agreement .one s t2⟩
  · constructor
    · rw [strict_two_agreement]; dsimp [u2]; linarith
    · exact ⟨weak_none_right .two (agreement s t2), weak_none_left_agreement .two s t2⟩

lemma p0_A3 : A3 p0 := by
  intro i r s t1 t2
  cases i
  · simp only [weak_one_agreement, u1, Nat.cast_add, Nat.cast_one]
    constructor <;> intro h <;> linarith
  · simp only [weak_two_agreement, u2, Nat.cast_add, Nat.cast_one]
    constructor <;> intro h <;> linarith

lemma p0_A4 : A4 p0 := by
  intro i r r0 s t1 t2 hlim
  refine ⟨?_, fun _ => weak_none_right i _⟩
  intro hn
  cases i
  · rw [weak_one_agreement]
    change u1 s t2 ≤ w1 (r0 : ℝ) - (t1 : ℝ)
    have h4 : Filter.Tendsto (fun n => 4 * (r n : ℝ) - (t1 : ℝ)) Filter.atTop
        (nhds (4 * (r0 : ℝ) - (t1 : ℝ))) := by
      exact ((continuous_const.mul continuous_id).sub continuous_const).continuousAt.tendsto.comp hlim
    by_cases hr0 : (1 / 2 : ℝ) ≤ (r0 : ℝ)
    · have hle : ∀ n, u1 s t2 - 1 ≤ 4 * (r n : ℝ) - (t1 : ℝ) := by
        intro n
        have h_n : u1 s t2 ≤ w1 (r n : ℝ) - (t1 : ℝ) := (weak_one_agreement (r n) s t1 t2).mp (hn n)
        dsimp [w1] at h_n
        split_ifs at h_n <;> linarith
      have hlim_le := ge_of_tendsto h4 (Filter.Eventually.of_forall hle)
      dsimp [w1]
      rw [if_pos hr0]
      linarith
    · have hr0_lt : (r0 : ℝ) < 1 / 2 := lt_of_not_ge hr0
      have hev : ∀ᶠ n in Filter.atTop, (r n : ℝ) < 1 / 2 :=
        hlim.eventually (Iio_mem_nhds hr0_lt)
      have hev_le : ∀ᶠ n in Filter.atTop, u1 s t2 ≤ 4 * (r n : ℝ) - (t1 : ℝ) := by
        filter_upwards [hev] with n hn_lt
        have h_n : u1 s t2 ≤ w1 (r n : ℝ) - (t1 : ℝ) := (weak_one_agreement (r n) s t1 t2).mp (hn n)
        dsimp [w1] at h_n
        rw [if_neg (not_le.mpr hn_lt)] at h_n
        linarith
      have hlim_le := ge_of_tendsto h4 hev_le
      dsimp [w1]
      rw [if_neg hr0]
      linarith
  · rw [weak_two_agreement]
    change u2 s t2 ≤ 4 * (1 - (r0 : ℝ)) - (t1 : ℝ)
    have h4 : Filter.Tendsto (fun n => 4 * (1 - (r n : ℝ)) - (t1 : ℝ)) Filter.atTop
        (nhds (4 * (1 - (r0 : ℝ)) - (t1 : ℝ))) := by
      exact ((continuous_const.mul (continuous_const.sub continuous_id)).sub
        continuous_const).continuousAt.tendsto.comp hlim
    have hle : ∀ n, u2 s t2 ≤ 4 * (1 - (r n : ℝ)) - (t1 : ℝ) := by
      intro n
      exact (weak_two_agreement (r n) s t1 t2).mp (hn n)
    exact ge_of_tendsto h4 (Filter.Eventually.of_forall hle)

lemma indiff_one_diff (r s : Partition)
    (h : indifferent p0 .one (agreement r 1) (agreement s 0)) :
    r.val - s.val = 1 / 4 := by
  rcases h with ⟨h1, h2⟩
  rw [weak_one_agreement] at h1 h2
  have heq : u1 r 1 = u1 s 0 := le_antisymm h2 h1
  dsimp [u1, w1] at heq
  push_cast at heq
  have hr0 : 0 ≤ r.val := r.2.1
  have hr1 : r.val ≤ 1 := r.2.2
  have hs0 : 0 ≤ s.val := s.2.1
  have hs1 : s.val ≤ 1 := s.2.2
  split_ifs at heq with h_r h_s h_s
  · linarith
  · exfalso; linarith
  · exfalso; linarith
  · linarith

lemma indiff_two_diff (r s : Partition)
    (h : indifferent p0 .two (agreement r 1) (agreement s 0)) :
    share .two r - share .two s = 1 / 4 := by
  rcases h with ⟨h1, h2⟩
  rw [weak_two_agreement] at h1 h2
  have heq : u2 r 1 = u2 s 0 := le_antisymm h2 h1
  dsimp [u2, w2, share] at heq ⊢
  push_cast at heq
  linarith

lemma p0_A5 : A5 p0 := by
  intro i r s r' s' h h' _
  cases i
  · have hd1 := indiff_one_diff r s h
    have hd2 := indiff_one_diff r' s' h'
    dsimp [share]
    linarith
  · have hd1 := indiff_two_diff r s h
    have hd2 := indiff_two_diff r' s' h'
    linarith

lemma p0_FullAxioms : FullAxioms p0 :=
  ⟨p0_A1, p0_A2, p0_A3, p0_A4, p0_A5⟩

def mkPart (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Partition :=
  ⟨x, ⟨hx0, hx1⟩⟩

noncomputable def pZero : Partition := mkPart 0 (by norm_num) (by norm_num)
noncomputable def pQuarter : Partition := mkPart (1 / 4) (by norm_num) (by norm_num)
noncomputable def pHalf : Partition := mkPart (1 / 2) (by norm_num) (by norm_num)
noncomputable def pFiveEighths : Partition := mkPart (5 / 8) (by norm_num) (by norm_num)
noncomputable def pThreeQuarters : Partition := mkPart (3 / 4) (by norm_num) (by norm_num)
noncomputable def pOne : Partition := mkPart 1 (by norm_num) (by norm_num)

lemma fiveEighths_not_mem_Delta1 : (5 / 8 : ℝ) ∉ Delta1 p0 := by
  rintro ⟨yval, ⟨x, y, hq, hyLeast, hxGreatest⟩⟩
  have hx : x = pFiveEighths := by
    ext
    exact Prod.ext_iff.mp hq |>.1.symm
  subst hx
  have hy_mem : pHalf ∈ {y' : Partition | weak p0 .one (agreement y' 0) (agreement pFiveEighths 1)} := by
    change u1 pFiveEighths 1 ≤ u1 pHalf 0
    norm_num [u1, w1, pFiveEighths, pHalf, mkPart]
  have hy_le_half : y.val ≤ 1 / 2 := hyLeast.2 hy_mem
  have hhalf_le_y : 1 / 2 ≤ y.val := by
    by_contra hlt
    have hlt' : y.val < 1 / 2 := lt_of_not_ge hlt
    have hy1 : u1 pFiveEighths 1 ≤ u1 y 0 := hyLeast.1
    dsimp [u1, w1, pFiveEighths, mkPart] at hy1
    rw [if_neg hlt] at hy1
    norm_num at hy1
    linarith
  have hy_val : y.val = 1 / 2 := le_antisymm hy_le_half hhalf_le_y
  have h34_mem : pThreeQuarters ∈ {x' : Partition | weak p0 .two (agreement x' 0) (agreement y 1)} := by
    change u2 y 1 ≤ u2 pThreeQuarters 0
    dsimp [u2, w2, pThreeQuarters, mkPart]
    push_cast
    linarith
  have h34_le : (3 / 4 : ℝ) ≤ (5 / 8 : ℝ) := hxGreatest.2 h34_mem
  norm_num at h34_le

/-! ### Stationary and trigger strategies -/

noncomputable def fH : Strategy where
  offer := fun _ => pOne
  answer := fun h => match h.getLast? with
    | some s => decide ((3 / 4 : ℝ) ≤ s.val)
    | none => true

noncomputable def gH : Strategy where
  offer := fun _ => pThreeQuarters
  answer := fun _ => true

noncomputable def fL : Strategy where
  offer := fun _ => pQuarter
  answer := fun _ => true

noncomputable def gL : Strategy where
  offer := fun _ => pZero
  answer := fun h => match h.getLast? with
    | some s => decide (s.val ≤ (1 / 4 : ℝ))
    | none => false

noncomputable def fStar : Strategy where
  offer := fun h => match h with
    | [] => pFiveEighths
    | a :: _ => if a.val ≤ (5 / 8 : ℝ) then pOne else pQuarter
  answer := fun h => match h with
    | [] => true
    | a :: _ => if a.val ≤ (5 / 8 : ℝ) then fH.answer h else fL.answer h

noncomputable def gStar : Strategy where
  offer := fun h => match h with
    | [] => pThreeQuarters
    | a :: _ => if a.val ≤ (5 / 8 : ℝ) then pThreeQuarters else pZero
  answer := fun h => match h with
    | [] => true
    | a :: _ => if a.val ≤ (5 / 8 : ℝ) then gH.answer h else gL.answer h

lemma offers_length (s1 s2 : Strategy) (n : ℕ) : (offers s1 s2 n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [offers, ih]

lemma offers_succ_ne_nil (s1 s2 : Strategy) (n : ℕ) : offers s1 s2 (n + 1) ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  rw [offers_length] at hlen
  simp at hlen

lemma offers_succ_getLast? (s1 s2 : Strategy) (n : ℕ) :
    (offers s1 s2 (n + 1)).getLast? = some (nextOffer s1 s2 (offers s1 s2 n)) := by
  simp [offers]

lemma play_congr {f1 f2 g1 g2 : Strategy}
    (hof : f1.offer = f2.offer) (hog : g1.offer = g2.offer)
    (haf : ∀ l, l ≠ [] → f1.answer l = f2.answer l)
    (hag : ∀ l, l ≠ [] → g1.answer l = g2.answer l) :
    play f1 g1 = play f2 g2 := by
  have hoff : ∀ n, offers f1 g1 n = offers f2 g2 n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp [offers, nextOffer, ih, hof, hog]
  have hacc : ∀ n, acceptedAt f1 g1 n ↔ acceptedAt f2 g2 n := by
    intro n
    dsimp [acceptedAt]
    rw [hoff (n + 1)]
    have hne : offers f2 g2 (n + 1) ≠ [] := offers_succ_ne_nil f2 g2 n
    split_ifs
    · rw [hag _ hne]
    · rw [haf _ hne]
  have hfirst : firstAcceptance f1 g1 = firstAcceptance f2 g2 := by
    classical
    dsimp [firstAcceptance]
    by_cases h1 : ∃ n, acceptedAt f1 g1 n
    · have h2 : ∃ n, acceptedAt f2 g2 n := by
        rcases h1 with ⟨n, hn⟩
        exact ⟨n, (hacc n).mp hn⟩
      rw [dif_pos h1, dif_pos h2]
      congr 1
      exact le_antisymm (Nat.find_mono (fun n hn => (hacc n).mpr hn))
        (Nat.find_mono (fun n hn => (hacc n).mp hn))
    · have h2 : ¬ ∃ n, acceptedAt f2 g2 n := by
        rintro ⟨n, hn⟩
        exact h1 ⟨n, (hacc n).mpr hn⟩
      rw [dif_neg h1, dif_neg h2]
  dsimp [play]
  rw [hfirst]
  cases firstAcceptance f2 g2 with
  | none => rfl
  | some n =>
    simp [nextOffer, hoff n, hof, hog]

lemma play_of_acceptedAt_zero {s1 s2 : Strategy} (h0 : acceptedAt s1 s2 0) :
    play s1 s2 = agreement (s1.offer []) 1 := by
  classical
  have hex : ∃ n, acceptedAt s1 s2 n := ⟨0, h0⟩
  have hfind : Nat.find hex = 0 := Nat.le_zero.mp (Nat.find_min' hex h0)
  dsimp [play, firstAcceptance]
  rw [dif_pos hex, hfind]
  simp [offers, nextOffer]

lemma restrict_fStar_high (a : Partition) (tl : List Partition) (ha : a.val ≤ 5 / 8) :
    (restrictStrategy fStar (a :: tl)).offer = fH.offer ∧
    ∀ l, l ≠ [] → (restrictStrategy fStar (a :: tl)).answer l = fH.answer l := by
  refine ⟨?_, ?_⟩
  · ext future
    simp [restrictStrategy, fStar, fH, ha]
  · intro l hl
    have hlast : (a :: (tl ++ l)).getLast? = l.getLast? :=
      List.getLast?_append_of_ne_nil (a :: tl) hl
    dsimp [restrictStrategy, fStar, fH]
    rw [if_pos ha, hlast]

lemma restrict_fStar_low (a : Partition) (tl : List Partition) (ha : ¬ a.val ≤ 5 / 8) :
    (restrictStrategy fStar (a :: tl)).offer = fL.offer ∧
    ∀ l, l ≠ [] → (restrictStrategy fStar (a :: tl)).answer l = fL.answer l := by
  refine ⟨?_, ?_⟩
  · ext future
    simp [restrictStrategy, fStar, fL, ha]
  · intro l _
    simp [restrictStrategy, fStar, fL, ha]

lemma restrict_gStar_high (a : Partition) (tl : List Partition) (ha : a.val ≤ 5 / 8) :
    (restrictStrategy gStar (a :: tl)).offer = gH.offer ∧
    ∀ l, l ≠ [] → (restrictStrategy gStar (a :: tl)).answer l = gH.answer l := by
  refine ⟨?_, ?_⟩
  · ext future
    simp [restrictStrategy, gStar, gH, ha]
  · intro l _
    simp [restrictStrategy, gStar, gH, ha]

lemma restrict_gStar_low (a : Partition) (tl : List Partition) (ha : ¬ a.val ≤ 5 / 8) :
    (restrictStrategy gStar (a :: tl)).offer = gL.offer ∧
    ∀ l, l ≠ [] → (restrictStrategy gStar (a :: tl)).answer l = gL.answer l := by
  refine ⟨?_, ?_⟩
  · ext future
    simp [restrictStrategy, gStar, gL, ha]
  · intro l hl
    have hlast : (a :: (tl ++ l)).getLast? = l.getLast? :=
      List.getLast?_append_of_ne_nil (a :: tl) hl
    dsimp [restrictStrategy, gStar, gL]
    rw [if_neg ha, hlast]

/-! ### Stationary plays and deviation bounds -/

lemma play_fH_gH : play fH gH = agreement pOne 1 := by
  apply play_of_acceptedAt_zero
  simp [acceptedAt, gH]

lemma play_gH_fH : play gH fH = agreement pThreeQuarters 1 := by
  apply play_of_acceptedAt_zero
  simp [acceptedAt, offers, nextOffer, gH, fH, pThreeQuarters, mkPart]

lemma play_fL_gL : play fL gL = agreement pQuarter 1 := by
  apply play_of_acceptedAt_zero
  simp [acceptedAt, offers, nextOffer, fL, gL, pQuarter, mkPart]

lemma play_gL_fL : play gL fL = agreement pZero 1 := by
  apply play_of_acceptedAt_zero
  simp [acceptedAt, fL]

lemma play_fStar_gStar : play fStar gStar = agreement pFiveEighths 1 := by
  apply play_of_acceptedAt_zero
  simp [acceptedAt, offers, nextOffer, fStar, gStar, gH, pFiveEighths, mkPart]

lemma w1_le_five (r : Partition) : w1 r.val ≤ 5 := by
  have hr1 : r.val ≤ 1 := r.2.2
  dsimp [w1]
  split_ifs <;> linarith

lemma w1_nonneg (r : Partition) : 0 ≤ w1 r.val := by
  have hr0 : 0 ≤ r.val := r.2.1
  dsimp [w1]
  split_ifs <;> linarith

lemma w2_le_four (r : Partition) : w2 r.val ≤ 4 := by
  have hr0 : 0 ≤ r.val := r.2.1
  dsimp [w2]
  linarith

lemma w2_nonneg (r : Partition) : 0 ≤ w2 r.val := by
  have hr1 : r.val ≤ 1 := r.2.2
  dsimp [w2]
  linarith

lemma bound_play_d_gH (d : Strategy) (s : Partition) (t : ℕ) (hs : 4 ≤ u1 s t) :
    ¬ strict p0 .one (play d gH) (agreement s t) := by
  dsimp [play]
  cases firstAcceptance d gH with
  | none =>
    simp [strict]
  | some n =>
    rw [strict_one_agreement, not_lt]
    have hw := w1_le_five (nextOffer d gH (offers d gH n))
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have : u1 (nextOffer d gH (offers d gH n)) (n + 1) ≤ 4 := by
      dsimp [u1]
      linarith
    linarith

lemma bound_play_d_fL (d : Strategy) (s : Partition) (t : ℕ) (hs : 3 ≤ u2 s t) :
    ¬ strict p0 .two (play d fL) (agreement s t) := by
  dsimp [play]
  cases firstAcceptance d fL with
  | none =>
    simp [strict]
  | some n =>
    rw [strict_two_agreement, not_lt]
    have hw := w2_le_four (nextOffer d fL (offers d fL n))
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have : u2 (nextOffer d fL (offers d fL n)) (n + 1) ≤ 3 := by
      dsimp [u2]
      linarith
    linarith

lemma fH_answer_offers (d : Strategy) (n : ℕ) :
    fH.answer (offers d fH (n + 1)) = decide ((3 / 4 : ℝ) ≤ (nextOffer d fH (offers d fH n)).val) := by
  change (match (offers d fH (n + 1)).getLast? with
    | some s => decide ((3 / 4 : ℝ) ≤ s.val)
    | none => true) = _
  rw [offers_succ_getLast?]

lemma gL_answer_offers (d : Strategy) (n : ℕ) :
    gL.answer (offers d gL (n + 1)) = decide ((nextOffer d gL (offers d gL n)).val ≤ (1 / 4 : ℝ)) := by
  change (match (offers d gL (n + 1)).getLast? with
    | some s => decide (s.val ≤ (1 / 4 : ℝ))
    | none => false) = _
  rw [offers_succ_getLast?]

lemma bound_play_d_fH (d : Strategy) (s : Partition) (t : ℕ) (hs : 0 ≤ u2 s t) :
    ¬ strict p0 .two (play d fH) (agreement s t) := by
  classical
  dsimp [play, firstAcceptance]
  split_ifs with hex
  · rw [strict_two_agreement, not_lt]
    have hacc : acceptedAt d fH (Nat.find hex) := Nat.find_spec hex
    generalize Nat.find hex = n at hacc ⊢
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    by_cases hev : Even n
    · have hacc' : fH.answer (offers d fH (n + 1)) = true := by
        dsimp [acceptedAt] at hacc
        rwa [if_pos hev] at hacc
      rw [fH_answer_offers, decide_eq_true_eq] at hacc'
      have hu : u2 (nextOffer d fH (offers d fH n)) (n + 1) ≤ 0 := by
        dsimp [u2, w2]
        linarith
      linarith
    · have hlen : ¬ Even (offers d fH n).length := by
        rw [offers_length]
        exact hev
      have hr : nextOffer d fH (offers d fH n) = pOne := by
        unfold nextOffer
        rw [if_neg hlen]
        rfl
      rw [hr]
      have hu : u2 pOne (n + 1) ≤ 0 := by
        dsimp [u2, w2, pOne, mkPart]
        linarith
      linarith
  · simp [strict]

lemma bound_play_d_gL (d : Strategy) (s : Partition) (t : ℕ) (hs : 0 ≤ u1 s t) :
    ¬ strict p0 .one (play d gL) (agreement s t) := by
  classical
  dsimp [play, firstAcceptance]
  split_ifs with hex
  · rw [strict_one_agreement, not_lt]
    have hacc : acceptedAt d gL (Nat.find hex) := Nat.find_spec hex
    generalize Nat.find hex = n at hacc ⊢
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    by_cases hev : Even n
    · have hacc' : gL.answer (offers d gL (n + 1)) = true := by
        dsimp [acceptedAt] at hacc
        rwa [if_pos hev] at hacc
      rw [gL_answer_offers, decide_eq_true_eq] at hacc'
      have hr_lt : ¬ (1 / 2 : ℝ) ≤ (nextOffer d gL (offers d gL n)).val := by linarith
      have hu : u1 (nextOffer d gL (offers d gL n)) (n + 1) ≤ 0 := by
        dsimp [u1, w1]
        rw [if_neg hr_lt]
        linarith
      linarith
    · have hlen : ¬ Even (offers d gL n).length := by
        rw [offers_length]
        exact hev
      have hr : nextOffer d gL (offers d gL n) = pZero := by
        unfold nextOffer
        rw [if_neg hlen]
        rfl
      rw [hr]
      have hu : u1 pZero (n + 1) ≤ 0 := by
        norm_num [u1, w1, pZero, mkPart]
        linarith
      linarith
  · simp [strict]

lemma bound_play_d_gStar_root (d : Strategy) :
    ¬ strict p0 .one (play d gStar) (agreement pFiveEighths 1) := by
  classical
  have h58 : u1 pFiveEighths 1 = 5 / 2 := by
    norm_num [u1, w1, pFiveEighths, mkPart]
  by_cases ha : (d.offer []).val ≤ 5 / 8
  · have hacc0 : acceptedAt d gStar 0 := by
      simp [acceptedAt, offers, nextOffer, gStar, gH, ha]
    rw [play_of_acceptedAt_zero hacc0, strict_one_agreement, not_lt, h58]
    dsimp [u1, w1]
    split_ifs <;> linarith
  · have hnot0 : ¬ acceptedAt d gStar 0 := by
      change ¬ gStar.answer [d.offer []] = true
      dsimp [gStar, gL]
      rw [if_neg ha]
      simp only [decide_eq_true_eq]
      intro hle
      linarith
    dsimp [play, firstAcceptance]
    split_ifs with hex
    · rw [strict_one_agreement, not_lt, h58]
      have hspec : acceptedAt d gStar (Nat.find hex) := Nat.find_spec hex
      generalize Nat.find hex = n at hspec ⊢
      have hn0 : n ≠ 0 := by
        intro h0
        apply hnot0
        simpa [h0] using hspec
      by_cases hn1 : n = 1
      · subst hn1
        have hr : nextOffer d gStar (offers d gStar 1) = pZero := by
          dsimp [offers, nextOffer, gStar]
          rw [if_neg ha]
        rw [hr]
        norm_num [u1, w1, pZero, mkPart]
      · have hn2 : 2 ≤ n := by omega
        have hnR : (3 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ n + 1)
        have hw := w1_le_five (nextOffer d gStar (offers d gStar n))
        dsimp [u1]
        linarith
    · simp [strict]

lemma actingPlayer_even (h : List Partition) (hev : Even h.length) :
    actingPlayer .one h = .one := by
  unfold actingPlayer; rw [if_pos hev]

lemma actingPlayer_odd (h : List Partition) (hodd : ¬ Even h.length) :
    actingPlayer .one h = .two := by
  unfold actingPlayer; rw [if_neg hodd]; rfl

lemma plannedAnswer_even (f g : Strategy) (h : List Partition) (hev : Even h.length) :
    plannedAnswer f g h = f.answer h := by
  unfold plannedAnswer; rw [if_pos hev]

lemma plannedAnswer_odd (f g : Strategy) (h : List Partition) (hodd : ¬ Even h.length) :
    plannedAnswer f g h = g.answer h := by
  unfold plannedAnswer; rw [if_neg hodd]

lemma continuation_even (f g : Strategy) (h : List Partition) (hev : Even h.length) :
    continuation f g h = play (restrictStrategy f h) (restrictStrategy g h) := by
  unfold continuation; rw [if_pos hev]

lemma continuation_odd (f g : Strategy) (h : List Partition) (hodd : ¬ Even h.length) :
    continuation f g h = play (restrictStrategy g h) (restrictStrategy f h) := by
  unfold continuation; rw [if_neg hodd]

lemma deviation_even (f g : Strategy) (h : List Partition) (d : Strategy) (hev : Even h.length) :
    deviation f g h d = play d (restrictStrategy g h) := by
  unfold deviation; rw [if_pos hev]

lemma deviation_odd (f g : Strategy) (h : List Partition) (d : Strategy) (hodd : ¬ Even h.length) :
    deviation f g h d = play d (restrictStrategy f h) := by
  unfold deviation; rw [if_neg hodd]

lemma isPE_fStar_gStar : IsPE .one p0 fStar gStar := by
  intro h
  cases h with
  | nil =>
    have hev : Even ([] : List Partition).length := by decide
    refine ⟨?_, ?_⟩
    · intro d
      rw [actingPlayer_even _ hev, deviation_even _ _ _ _ hev, continuation_even _ _ _ hev]
      have hrest : restrictStrategy gStar [] = gStar := by
        cases gStar; rfl
      have hrest_f : restrictStrategy fStar [] = fStar := by
        cases fStar; rfl
      rw [hrest, hrest_f, play_fStar_gStar]
      exact bound_play_d_gStar_root d
    · intro s hs
      simp at hs
  | cons a tl =>
    by_cases ha : a.val ≤ 5 / 8
    · obtain ⟨hof_f, haf_f⟩ := restrict_fStar_high a tl ha
      obtain ⟨hof_g, haf_g⟩ := restrict_gStar_high a tl ha
      by_cases hev : Even (a :: tl).length
      · refine ⟨?_, ?_⟩
        · intro d
          rw [actingPlayer_even _ hev, deviation_even _ _ _ _ hev, continuation_even _ _ _ hev]
          rw [play_congr rfl hof_g (fun _ _ => rfl) haf_g]
          rw [play_congr hof_f hof_g haf_f haf_g, play_fH_gH]
          apply bound_play_d_gH
          norm_num [u1, w1, pOne, mkPart]
        · intro s hs
          rw [actingPlayer_even _ hev, plannedAnswer_even _ _ _ hev, continuation_even _ _ _ hev]
          have h_ans : fStar.answer (a :: tl) = decide ((3 / 4 : ℝ) ≤ s.val) := by
            change (if a.val ≤ 5 / 8 then fH.answer (a :: tl) else fL.answer (a :: tl)) = _
            rw [if_pos ha]
            unfold fH
            dsimp only
            rw [hs]
          rw [h_ans]
          by_cases hs34 : (3 / 4 : ℝ) ≤ s.val
          · rw [if_pos (decide_eq_true hs34)]
            intro d
            rw [deviation_even _ _ _ _ hev, play_congr rfl hof_g (fun _ _ => rfl) haf_g]
            apply bound_play_d_gH
            have hs12 : (1 / 2 : ℝ) ≤ s.val := by linarith
            dsimp [u1, w1]
            rw [if_pos hs12]
            push_cast
            linarith
          · rw [if_neg (by simp only [decide_eq_true_eq]; exact hs34)]
            rw [play_congr hof_f hof_g haf_f haf_g, play_fH_gH, weak_one_agreement]
            dsimp [u1, w1, pOne, mkPart]
            push_cast
            split_ifs <;> linarith
      · refine ⟨?_, ?_⟩
        · intro d
          rw [actingPlayer_odd _ hev, deviation_odd _ _ _ _ hev, continuation_odd _ _ _ hev]
          rw [play_congr rfl hof_f (fun _ _ => rfl) haf_f]
          rw [play_congr hof_g hof_f haf_g haf_f, play_gH_fH]
          apply bound_play_d_fH
          norm_num [u2, w2, pThreeQuarters, mkPart]
        · intro s _hs
          rw [actingPlayer_odd _ hev, plannedAnswer_odd _ _ _ hev]
          have h_ans : gStar.answer (a :: tl) = true := by
            change (if a.val ≤ 5 / 8 then gH.answer (a :: tl) else gL.answer (a :: tl)) = true
            rw [if_pos ha]
            rfl
          rw [h_ans, if_pos rfl]
          intro d
          rw [deviation_odd _ _ _ _ hev, play_congr rfl hof_f (fun _ _ => rfl) haf_f]
          apply bound_play_d_fH
          dsimp [u2]
          have := w2_nonneg s
          push_cast
          linarith
    · obtain ⟨hof_f, haf_f⟩ := restrict_fStar_low a tl ha
      obtain ⟨hof_g, haf_g⟩ := restrict_gStar_low a tl ha
      by_cases hev : Even (a :: tl).length
      · refine ⟨?_, ?_⟩
        · intro d
          rw [actingPlayer_even _ hev, deviation_even _ _ _ _ hev, continuation_even _ _ _ hev]
          rw [play_congr rfl hof_g (fun _ _ => rfl) haf_g]
          rw [play_congr hof_f hof_g haf_f haf_g, play_fL_gL]
          apply bound_play_d_gL
          norm_num [u1, w1, pQuarter, mkPart]
        · intro s _hs
          rw [actingPlayer_even _ hev, plannedAnswer_even _ _ _ hev]
          have h_ans : fStar.answer (a :: tl) = true := by
            change (if a.val ≤ 5 / 8 then fH.answer (a :: tl) else fL.answer (a :: tl)) = true
            rw [if_neg ha]
            rfl
          rw [h_ans, if_pos rfl]
          intro d
          rw [deviation_even _ _ _ _ hev, play_congr rfl hof_g (fun _ _ => rfl) haf_g]
          apply bound_play_d_gL
          dsimp [u1]
          have := w1_nonneg s
          push_cast
          linarith
      · refine ⟨?_, ?_⟩
        · intro d
          rw [actingPlayer_odd _ hev, deviation_odd _ _ _ _ hev, continuation_odd _ _ _ hev]
          rw [play_congr rfl hof_f (fun _ _ => rfl) haf_f]
          rw [play_congr hof_g hof_f haf_g haf_f, play_gL_fL]
          apply bound_play_d_fL
          norm_num [u2, w2, pZero, mkPart]
        · intro s hs
          rw [actingPlayer_odd _ hev, plannedAnswer_odd _ _ _ hev, continuation_odd _ _ _ hev]
          have h_ans : gStar.answer (a :: tl) = decide (s.val ≤ (1 / 4 : ℝ)) := by
            change (if a.val ≤ 5 / 8 then gH.answer (a :: tl) else gL.answer (a :: tl)) = _
            rw [if_neg ha]
            unfold gL
            dsimp only
            rw [hs]
          rw [h_ans]
          by_cases hs14 : s.val ≤ (1 / 4 : ℝ)
          · rw [if_pos (decide_eq_true hs14)]
            intro d
            rw [deviation_odd _ _ _ _ hev, play_congr rfl hof_f (fun _ _ => rfl) haf_f]
            apply bound_play_d_fL
            dsimp [u2, w2]
            push_cast
            linarith
          · rw [if_neg (by simp only [decide_eq_true_eq]; exact hs14)]
            rw [play_congr hof_g hof_f haf_g haf_f, play_gL_fL, weak_two_agreement]
            dsimp [u2, w2, pZero, mkPart]
            push_cast
            linarith

lemma fiveEighths_mem_A : (5 / 8 : ℝ) ∈ A p0 := by
  exact ⟨pFiveEighths, fStar, gStar, 1, rfl, isPE_fStar_gStar, play_fStar_gStar⟩

end DisproveRubinsteinProp4

theorem solution : ¬ (∀ (p : Preferences), FullAxioms p → A p ⊆ Delta1 p ∧ B p ⊆ Delta2 p) := by
  intro hall
  have hsub := (hall DisproveRubinsteinProp4.p0 DisproveRubinsteinProp4.p0_FullAxioms).1
  exact DisproveRubinsteinProp4.fiveEighths_not_mem_Delta1
    (hsub DisproveRubinsteinProp4.fiveEighths_mem_A)
