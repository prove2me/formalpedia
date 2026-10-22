-- Prove2me | solution 1 for WagelmansELS.Efficient.threshold_rule_computes_G
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T17:22:00.565747+00:00
-- url     : https://prove2.me/submissions/735b3d5c-b0bf-4de7-b99b-6788aae58aa8

import Mathlib
import Definitions.Def_WagelmansELS_Efficient_ThresholdRule

set_option autoImplicit false

namespace WagelmansELS.Efficient.Instance

variable (P : Instance)

lemma wD_nonneg {u : ℕ} (hu : 1 ≤ u) : 0 ≤ P.D u := by
  unfold Instance.D
  refine Finset.sum_nonneg (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  exact P.d_nonneg j (by omega) hj.2

lemma wD_pos {u : ℕ} (hu : 1 ≤ u) (hun : u ≤ P.n) : 0 < P.D u := by
  unfold Instance.D
  refine lt_of_lt_of_le P.d_last_pos ?_
  refine Finset.single_le_sum (f := P.d) (fun j hj => ?_) (by simp; omega)
  rw [Finset.mem_Icc] at hj
  exact P.d_nonneg j (by omega) hj.2

lemma wD_top : P.D (P.n + 1) = 0 := by
  unfold Instance.D
  rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]

lemma wD_anti {t s : ℕ} (ht : 1 ≤ t) (hts : t ≤ s) : P.D s ≤ P.D t := by
  unfold Instance.D
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left hts) ?_
  intro j hj _
  rw [Finset.mem_Icc] at hj
  exact P.d_nonneg j (by omega) hj.2

lemma wD_step {i : ℕ} (hin : i ≤ P.n) : P.D i = P.d i + P.D (i + 1) := by
  unfold Instance.D
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hin, Finset.sum_insert (by simp)]

lemma wmem_E {i t : ℕ} : t ∈ P.E i ↔ P.IsEfficient i t := by
  unfold Instance.E
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

lemma wtop_eff {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ P.n) : P.IsEfficient i (P.n + 1) := by
  refine ⟨by simp; omega, ?_, ?_⟩
  · intro u hu hne hD
    exfalso
    rw [Finset.mem_Ioc] at hu
    have := P.wD_pos (u := u) (by omega) (by omega)
    rw [hD, P.wD_top] at this
    exact lt_irrefl _ this
  · rintro ⟨u, hu, w, hw, h1, h2, h3⟩
    rw [Finset.mem_Ioc] at hu
    have := P.wD_nonneg (u := u) (by omega)
    rw [P.wD_top] at h1
    linarith

lemma weff_D_lt {i t s : ℕ} (hi : 1 ≤ i) (ht : P.IsEfficient i t) (hs : P.IsEfficient i s)
    (hts : t < s) : P.D s < P.D t := by
  have ht1 := ht.1
  rw [Finset.mem_Ioc] at ht1
  refine lt_of_le_of_ne (P.wD_anti (by omega) hts.le) (fun heq => ?_)
  have A := ht.2.1 s hs.1 (by omega) heq
  have B := hs.2.1 t ht.1 (by omega) heq.symm
  rcases A with A | ⟨A1, A2⟩ <;> rcases B with B | ⟨B1, B2⟩
  · linarith
  · omega
  · linarith
  · omega

lemma wsucc_spec {i t : ℕ} (hi : 1 ≤ i) (hin : i ≤ P.n) (ht : t < P.n + 1) :
    P.IsEfficient i (P.succ i t) ∧ t < P.succ i t := by
  unfold Instance.succ
  dsimp only
  split_ifs with h
  · have hm := Finset.min'_mem _ h
    rw [Finset.mem_filter, wmem_E] at hm
    exact hm
  · exact ⟨P.wtop_eff hi hin, ht⟩

lemma wsucc_le {i t a : ℕ} (ha : P.IsEfficient i a) (hta : t < a) : P.succ i t ≤ a := by
  unfold Instance.succ
  dsimp only
  have hmem : a ∈ (P.E i).filter (fun u => t < u) := by
    rw [Finset.mem_filter, wmem_E]; exact ⟨ha, hta⟩
  rw [dif_pos ⟨a, hmem⟩]
  exact Finset.min'_le _ _ hmem

lemma wchord (i x y z : ℕ) :
    (P.D z - P.D y) * P.G x + (P.D y - P.D x) * P.G z - (P.D z - P.D x) * P.G y =
      (P.D z - P.D y) * (P.score i x - P.score i y) +
        (P.D y - P.D x) * (P.score i z - P.score i y) := by
  unfold Instance.score
  ring

/-- The threshold period minimizes the score. -/
lemma wq_min {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ P.n) :
    P.q i ∈ Finset.Ioc i (P.n + 1) ∧
      ∀ t ∈ Finset.Ioc i (P.n + 1), P.score i (P.q i) ≤ P.score i t := by
  classical
  set S := Finset.Ioc i (P.n + 1) with hSdef
  have hS : S.Nonempty := ⟨P.n + 1, by simp [S]; omega⟩
  obtain ⟨b, hbS, hb⟩ := S.exists_min_image (P.score i) hS
  set M := S.filter (fun t => P.score i t = P.score i b) with hMdef
  have hbM : b ∈ M := by simp [M, hbS]
  obtain ⟨b2, hb2M, hb2⟩ := M.exists_min_image P.D ⟨b, hbM⟩
  set M2 := M.filter (fun t => P.D t = P.D b2) with hM2def
  have hb2M2 : b2 ∈ M2 := by simp [M2, hb2M]
  set a := M2.min' ⟨b2, hb2M2⟩ with hadef
  have haM2 : a ∈ M2 := Finset.min'_mem _ _
  simp only [M2, M, Finset.mem_filter] at haM2 hb2M
  obtain ⟨⟨haS, has⟩, haD⟩ := haM2
  -- key properties of a
  have hmin : ∀ t ∈ S, P.score i a ≤ P.score i t := fun t ht => by rw [has]; exact hb t ht
  have hDmin : ∀ t ∈ S, P.score i t = P.score i a → P.D a ≤ P.D t := by
    intro t ht hst
    rw [haD]
    exact hb2 t (by simp only [M, Finset.mem_filter]; exact ⟨ht, by rw [hst, has]⟩)
  have hidx : ∀ t ∈ S, P.score i t = P.score i a → P.D t = P.D a → a ≤ t := by
    intro t ht hst hDt
    exact Finset.min'_le _ _ (by
      simp only [M2, M, Finset.mem_filter]
      exact ⟨⟨ht, by rw [hst, has]⟩, by rw [hDt, haD]⟩)
  have haS' := haS
  rw [hSdef, Finset.mem_Ioc] at haS'
  -- a is efficient
  have haE : P.IsEfficient i a := by
    refine ⟨haS, ?_, ?_⟩
    · intro u hu hne hDu
      have h1 := hmin u hu
      unfold Instance.score at h1
      rw [hDu] at h1
      rcases lt_or_eq_of_le (show P.G a ≤ P.G u by linarith) with h | h
      · exact Or.inl h
      · refine Or.inr ⟨h, lt_of_le_of_ne (hidx u hu ?_ hDu) (Ne.symm hne)⟩
        unfold Instance.score; rw [hDu, h]
    · rintro ⟨u, hu, w, hw, h1, h2, h3⟩
      have key := P.wchord i u a w
      have hu' := hmin u hu
      have hw' := hmin w hw
      have hsu : P.score i u ≤ P.score i a := by
        by_contra hlt
        push Not at hlt
        have e1 := mul_pos (sub_pos.2 h2) (sub_pos.2 hlt)
        have e2 := mul_nonneg (sub_pos.2 h1).le (sub_nonneg.2 hw')
        linarith
      have := hDmin u hu (le_antisymm hsu hu')
      linarith
  -- efficient periods before a have ratio ≥ c
  have hbefore : ∀ t, P.IsEfficient i t → t < a → ¬ P.ratio i t < P.c i := by
    intro t htE hta
    have hsp := P.wsucc_spec hi hin (t := t) (by omega)
    set s := P.succ i t with hsdef
    have hsa : s ≤ a := P.wsucc_le haE hta
    have hDst : P.D s < P.D t := P.weff_D_lt hi htE hsp.1 hsp.2
    have hst : P.score i s ≤ P.score i t := by
      rcases lt_or_eq_of_le hsa with hlt | heq
      · have hDas : P.D a < P.D s := P.weff_D_lt hi hsp.1 haE hlt
        have hno := hsp.1.2.2
        have hc : ¬ ((P.D t - P.D a) * P.G s ≥
            (P.D t - P.D s) * P.G a + (P.D s - P.D a) * P.G t) :=
          fun hge => hno ⟨a, haS, t, htE.1, hDas, hDst, hge⟩
        push Not at hc
        have key := P.wchord i a s t
        have hsa' := hmin s hsp.1.1
        by_contra hlt2
        push Not at hlt2
        have e1 := mul_nonneg (sub_pos.2 hDst).le (sub_nonneg.2 hsa')
        have e2 := mul_pos (sub_pos.2 hDas) (sub_pos.2 hlt2)
        nlinarith
      · rw [heq]; exact hmin t htE.1
    unfold Instance.ratio
    rw [← hsdef, not_lt, le_div_iff₀ (sub_pos.2 hDst)]
    unfold Instance.score at hst
    linarith
  -- a itself passes the threshold when it is not the sentinel
  have hat : a < P.n + 1 → P.ratio i a < P.c i := by
    intro han
    have hsp := P.wsucc_spec hi hin (t := a) han
    set s := P.succ i a with hsdef
    have hDsa : P.D s < P.D a := P.weff_D_lt hi haE hsp.1 hsp.2
    have hss : P.score i a < P.score i s := by
      rcases lt_or_eq_of_le (hmin s hsp.1.1) with h | h
      · exact h
      · have := hDmin s hsp.1.1 h.symm
        linarith
    unfold Instance.ratio
    rw [← hsdef, div_lt_iff₀ (sub_pos.2 hDsa)]
    unfold Instance.score at hss
    linarith
  have hqa : P.q i = a := by
    unfold Instance.q
    dsimp only
    apply le_antisymm
    · apply Finset.min'_le
      rcases lt_or_eq_of_le haS'.2 with h | h
      · rw [Finset.mem_insert, Finset.mem_filter, wmem_E]
        exact Or.inr ⟨haE, h, hat h⟩
      · rw [h]; exact Finset.mem_insert_self _ _
    · apply Finset.le_min'
      intro x hx
      rw [Finset.mem_insert, Finset.mem_filter, wmem_E] at hx
      rcases hx with hx | ⟨hxE, _, hxr⟩
      · rw [hx]; exact haS'.2
      · by_contra hlt
        push Not at hlt
        exact hbefore x hxE hlt hxr
  rw [hqa]
  exact ⟨haS, hmin⟩

lemma wGtable_stable (m k t : ℕ) (hk : m + k ≤ P.n) (ht : P.n - m < t) :
    P.Gtable (m + k) t = P.Gtable m t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, Instance.Gtable]
    dsimp only
    rw [if_neg (by omega)]
    exact ih (by omega)

end WagelmansELS.Efficient.Instance

-- Section 2, pp. S149-S150: the ratio threshold selects a minimizing next period,
-- and the corrected Iterations assignment gives the backward value.
open WagelmansELS.Efficient in
theorem solution (P : Instance) (i : ℕ)
    (hi : 1 ≤ i) (hin : i ≤ P.n) :
    (Finset.Ioc i (P.n + 1)).inf' (by simp; omega) (P.score i) =
      P.score i (P.q i) ∧
    P.G i = (if 0 < P.d i then P.f i + P.score i (P.q i)
      else min (P.G (i + 1)) (P.f i + P.score i (P.q i))) := by
  obtain ⟨hqS, hqmin⟩ := Instance.wq_min P hi hin
  refine ⟨le_antisymm (Finset.inf'_le _ hqS) (Finset.le_inf' _ _ hqmin), ?_⟩
  have hG : ∀ t, i < t → P.G t = P.Gtable (P.n - i) t := by
    intro t ht
    unfold Instance.G
    have := Instance.wGtable_stable P (P.n - i) i t (by omega) (by omega)
    rw [show P.n - i + i = P.n by omega] at this
    exact this
  have hGi : P.G i = P.Gtable (P.n - i + 1) i := by
    unfold Instance.G
    have := Instance.wGtable_stable P (P.n - i + 1) (i - 1) i (by omega) (by omega)
    rw [show P.n - i + 1 + (i - 1) = P.n by omega] at this
    exact this
  have hidx : P.n - (P.n - i) = i := by omega
  rw [hGi, Instance.Gtable]
  dsimp only
  simp only [hidx, ↓reduceIte]
  -- replace the old table by G on later periods
  have hcost : ∀ t ∈ Finset.Ioc i (P.n + 1),
      P.setupCost i t (P.Gtable (P.n - i)) = P.f i + P.score i t := by
    intro t ht
    rw [Finset.mem_Ioc] at ht
    unfold Instance.setupCost Instance.score
    rw [← hG t ht.1]
    ring
  have hY : (Finset.Ioc i (P.n + 1)).inf' (by simp; omega)
      (fun t => P.setupCost i t (P.Gtable (P.n - i))) = P.f i + P.score i (P.q i) := by
    apply le_antisymm
    · exact Finset.inf'_le_of_le _ hqS (le_of_eq (hcost _ hqS))
    · apply Finset.le_inf'
      intro t ht
      rw [hcost t ht]
      linarith [hqmin t ht]
  have hold : P.Gtable (P.n - i) (i + 1) = P.G (i + 1) := (hG (i + 1) (by omega)).symm
  split_ifs with hd hne
  · exact hY
  · -- zero demand, a later candidate exists
    have hd0 : P.d i = 0 := le_antisymm (not_lt.1 hd) (P.d_nonneg i hi hin)
    rw [hold]
    have hX : P.f i + P.score i (P.q i) ≤ (Finset.Ioc (i + 1) (P.n + 1)).inf' hne
        (fun t => P.setupCost i t (P.Gtable (P.n - i))) := by
      apply Finset.le_inf'
      intro t ht
      have ht' : t ∈ Finset.Ioc i (P.n + 1) := by
        rw [Finset.mem_Ioc] at ht ⊢; omega
      rw [hcost t ht']
      linarith [hqmin t ht']
    apply le_antisymm
    · apply le_min (min_le_left _ _)
      have hq' := hqS
      rw [Finset.mem_Ioc] at hq'
      rcases Nat.lt_or_ge (i + 1) (P.q i) with h | h
      · have hqX : P.q i ∈ Finset.Ioc (i + 1) (P.n + 1) := by
          rw [Finset.mem_Ioc]; omega
        refine le_trans (min_le_right _ _) ?_
        refine le_trans (Finset.inf'_le _ hqX) (le_of_eq ?_)
        exact hcost _ hqS
      · have hq1 : P.q i = i + 1 := by omega
        refine le_trans (min_le_left _ _) ?_
        rw [hq1]
        unfold Instance.score
        rw [P.wD_step hin, hd0]
        have := P.f_nonneg i hi hin
        linarith
    · exact le_min (min_le_left _ _) (le_trans (min_le_right _ _) hX)
  · -- zero demand, i = n
    rw [hold]
    exact le_antisymm
      (le_min (min_le_left _ _) (le_trans (min_le_left _ _) (by
        have : i = P.n := by
          by_contra hne'
          exact hne ⟨P.n + 1, by rw [Finset.mem_Ioc]; omega⟩
        have hq' := hqS
        rw [Finset.mem_Ioc] at hq'
        have hq1 : P.q i = i + 1 := by omega
        have hd0 : P.d i = 0 := le_antisymm (not_lt.1 hd) (P.d_nonneg i hi hin)
        rw [hq1]
        unfold Instance.score
        rw [P.wD_step hin, hd0]
        have := P.f_nonneg i hi hin
        linarith)))
      (le_min (min_le_left _ _) (min_le_left _ _))
