-- Prove2me | solution 2 for QEC.Locality.BKRecursivePartition.remainder_recurrence_le_bkSumPreservingRecurrenceTwice
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:30:01.671367+00:00
-- url     : https://prove2.me/submissions/3aef5130-1790-4175-a836-c31d9f47c5a5

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QLAux.minSize_le_card (G : ConnectivityGraph ι) (W : Finset ι) :
    minimumTwoThirdsBalancedVertexSeparatorSize G W ≤ W.card := by
  unfold minimumTwoThirdsBalancedVertexSeparatorSize
  apply Finset.min'_le
  refine Finset.mem_image.2 ⟨W, ?_, rfl⟩
  rw [mem_twoThirdsBalancedSeparatorCandidates_iff]
  exact ⟨subset_rfl, self_isTwoThirdsBalancedVertexSeparator G W⟩

theorem QLAux.profile_mono (G : ConnectivityGraph ι) {a b : Nat} (hab : a ≤ b) :
    twoThirdsSeparationProfile G a ≤ twoThirdsSeparationProfile G b := by
  unfold twoThirdsSeparationProfile
  apply Finset.max'_le
  intro y hy
  obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hy
  have := (mem_inducedVertexSetsAtMost_iff a W).1 hW
  apply Finset.le_max'
  exact Finset.mem_image.2 ⟨W, (mem_inducedVertexSetsAtMost_iff b W).2 ⟨this.1, this.2.trans hab⟩, rfl⟩

theorem QLAux.profile_le (G : ConnectivityGraph ι) (s : Nat) :
    twoThirdsSeparationProfile G s ≤ s := by
  unfold twoThirdsSeparationProfile
  apply Finset.max'_le
  intro y hy
  obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hy
  have := (mem_inducedVertexSetsAtMost_iff s W).1 hW
  exact le_trans (QLAux.minSize_le_card G W) this.2

theorem QLAux.depth_term {d s : Nat} (h : bkScaleTerminal d s) : bkTwoThirdsDepth d s = 0 := by
  conv_lhs => rw [bkTwoThirdsDepth]
  rw [if_pos h]

theorem QLAux.depth_nonterm {d s : Nat} (h : ¬ bkScaleTerminal d s) :
    bkTwoThirdsDepth d s = 1 + bkTwoThirdsDepth d (bkTwoThirdsChildScale s) := by
  conv_lhs => rw [bkTwoThirdsDepth]
  rw [if_neg h]

theorem QLAux.R_term (G : ConnectivityGraph ι) {d s : Nat} (h : bkScaleTerminal d s) :
    bkSumPreservingRecurrence G d s = 0 := by
  conv_lhs => rw [bkSumPreservingRecurrence]
  rw [if_pos h]

theorem QLAux.R_nonterm (G : ConnectivityGraph ι) {d s : Nat} (h : ¬ bkScaleTerminal d s) :
    bkSumPreservingRecurrence G d s =
        twoThirdsSeparationProfile G s +
        (bkAdmissibleChildPairs s).sup (fun children =>
          if _hchildren : children ∈ bkAdmissibleChildPairs s then
            bkSumPreservingRecurrence G d children.1 +
              bkSumPreservingRecurrence G d children.2
          else 0) := by
  conv_lhs => rw [bkSumPreservingRecurrence]
  rw [if_neg h]

theorem QLAux.nonterm_pos {d s : Nat} (h : ¬ bkScaleTerminal d s) : 0 < s := by
  unfold bkScaleTerminal at h
  omega

theorem QLAux.depth_mono (d : Nat) : ∀ (b a : Nat), a ≤ b →
    bkTwoThirdsDepth d a ≤ bkTwoThirdsDepth d b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a hab
    by_cases hb : bkScaleTerminal d b
    · have ha : bkScaleTerminal d a := by
        unfold bkScaleTerminal at hb ⊢; omega
      rw [QLAux.depth_term ha, QLAux.depth_term hb]
    · by_cases ha : bkScaleTerminal d a
      · rw [QLAux.depth_term ha]; exact Nat.zero_le _
      · rw [QLAux.depth_nonterm ha, QLAux.depth_nonterm hb]
        have hbpos := QLAux.nonterm_pos hb
        have hlt : bkTwoThirdsChildScale b < b := bkTwoThirdsChildScale_lt b hbpos
        have hle : bkTwoThirdsChildScale a ≤ bkTwoThirdsChildScale b := by
          unfold bkTwoThirdsChildScale
          exact Nat.div_le_div_right (by omega)
        have := ih _ hlt _ hle
        omega

theorem QLAux.R_le_mul_depth (G : ConnectivityGraph ι) (d : Nat) : ∀ s : Nat,
    bkSumPreservingRecurrence G d s ≤ s * bkTwoThirdsDepth d s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    by_cases hs : bkScaleTerminal d s
    · rw [QLAux.R_term G hs]; exact Nat.zero_le _
    · rw [QLAux.R_nonterm G hs, QLAux.depth_nonterm hs]
      have hsup : (bkAdmissibleChildPairs s).sup (fun children =>
          if _hchildren : children ∈ bkAdmissibleChildPairs s then
            bkSumPreservingRecurrence G d children.1 +
              bkSumPreservingRecurrence G d children.2
          else 0) ≤ s * bkTwoThirdsDepth d (bkTwoThirdsChildScale s) := by
        apply Finset.sup_le
        intro c hc
        simp only [dif_pos hc]
        obtain ⟨h1, h2, h3, h4, h5⟩ := (mem_bkAdmissibleChildPairs_iff).1 hc
        have e1 := ih c.1 h1
        have e2 := ih c.2 h2
        have d1 : bkTwoThirdsDepth d c.1 ≤ bkTwoThirdsDepth d (bkTwoThirdsChildScale s) :=
          QLAux.depth_mono d _ _ (by unfold bkTwoThirdsChildScale; exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega))
        have d2 : bkTwoThirdsDepth d c.2 ≤ bkTwoThirdsDepth d (bkTwoThirdsChildScale s) :=
          QLAux.depth_mono d _ _ (by unfold bkTwoThirdsChildScale; exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega))
        have m1 := Nat.mul_le_mul_left c.1 d1
        have m2 := Nat.mul_le_mul_left c.2 d2
        have m3 : (c.1 + c.2) * bkTwoThirdsDepth d (bkTwoThirdsChildScale s) ≤
            s * bkTwoThirdsDepth d (bkTwoThirdsChildScale s) := Nat.mul_le_mul_right _ h3
        have : (c.1 + c.2) * bkTwoThirdsDepth d (bkTwoThirdsChildScale s) =
            c.1 * bkTwoThirdsDepth d (bkTwoThirdsChildScale s) +
              c.2 * bkTwoThirdsDepth d (bkTwoThirdsChildScale s) := by ring
        omega
      have hp := QLAux.profile_le G s
      have : s * (1 + bkTwoThirdsDepth d (bkTwoThirdsChildScale s)) =
          s + s * bkTwoThirdsDepth d (bkTwoThirdsChildScale s) := by ring
      omega

theorem QLAux.R_mono (G : ConnectivityGraph ι) (d : Nat) {a b : Nat} (hab : a ≤ b) :
    bkSumPreservingRecurrence G d a ≤ bkSumPreservingRecurrence G d b := by
  by_cases hb : bkScaleTerminal d b
  · have ha : bkScaleTerminal d a := by
      unfold bkScaleTerminal at hb ⊢; omega
    rw [QLAux.R_term G ha, QLAux.R_term G hb]
  · by_cases ha : bkScaleTerminal d a
    · rw [QLAux.R_term G ha]; exact Nat.zero_le _
    · rw [QLAux.R_nonterm G ha, QLAux.R_nonterm G hb]
      apply Nat.add_le_add (QLAux.profile_mono G hab)
      apply Finset.sup_le
      intro c hc
      simp only [dif_pos hc]
      have hc' : c ∈ bkAdmissibleChildPairs b := by
        obtain ⟨h1, h2, h3, h4, h5⟩ := (mem_bkAdmissibleChildPairs_iff).1 hc
        exact (mem_bkAdmissibleChildPairs_iff).2 ⟨by omega, by omega, by omega, by omega, by omega⟩
      refine le_trans ?_ (Finset.le_sup (f := fun children =>
          if _hchildren : children ∈ bkAdmissibleChildPairs b then
            bkSumPreservingRecurrence G d children.1 +
              bkSumPreservingRecurrence G d children.2
          else 0) hc')
      simp only [dif_pos hc']
      exact le_rfl

theorem QLAux.S_le_R (G : ConnectivityGraph ι) (d : Nat) : ∀ n : Nat, ∀ V : Finset ι, V.card = n →
    bkSeparatorRecurrence G d V ≤ bkSumPreservingRecurrence G d V.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V hV
    by_cases hs : bkSeparatorTerminal d V
    · rw [bkSeparatorRecurrence, if_pos hs]; exact Nat.zero_le _
    · have hs' : ¬ bkScaleTerminal d V.card := by
        intro h
        apply hs
        unfold bkSeparatorTerminal
        unfold bkScaleTerminal at h
        rcases h with h | h
        · left; exact Finset.card_eq_zero.1 h
        · right; exact h
      have hne : V.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h; apply hs; exact Or.inl h
      rw [bkSeparatorRecurrence, if_neg hs, QLAux.R_nonterm G hs']
      have hspec := measuredTwoThirdsSplit_spec G V
      obtain ⟨hsub, hunion, hdisj, hbl, hbr, -⟩ := hspec
      have hl := measuredTwoThirdsLeft_card_lt G V hne
      have hr := measuredTwoThirdsRight_card_lt G V hne
      have ihl := ih _ (by omega) (measuredTwoThirdsLeft G V) rfl
      have ihr := ih _ (by omega) (measuredTwoThirdsRight G V) rfl
      have hsum : (measuredTwoThirdsLeft G V).card + (measuredTwoThirdsRight G V).card ≤ V.card := by
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
        exact Finset.card_le_card Finset.sdiff_subset
      have hmem : ((measuredTwoThirdsLeft G V).card, (measuredTwoThirdsRight G V).card) ∈
          bkAdmissibleChildPairs V.card :=
        (mem_bkAdmissibleChildPairs_iff).2 ⟨hl, hr, hsum, hbl, hbr⟩
      have hle := Finset.le_sup (f := fun children =>
          if _hchildren : children ∈ bkAdmissibleChildPairs V.card then
            bkSumPreservingRecurrence G d children.1 +
              bkSumPreservingRecurrence G d children.2
          else 0) hmem
      simp only [dif_pos hmem] at hle
      omega

theorem solution
    {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) :
    bkSeparatorRecurrence G d partition.remainder ≤
      bkSumPreservingRecurrenceTwice G d vertices.card := by
  have h1 := QLAux.S_le_R G d _ partition.remainder rfl
  have h2 := partition.remainder_card_le
  have h3 := QLAux.S_le_R G d _ vertices rfl
  have h4 := QLAux.R_mono G d (h2.trans h3)
  unfold bkSumPreservingRecurrenceTwice
  exact h1.trans h4
