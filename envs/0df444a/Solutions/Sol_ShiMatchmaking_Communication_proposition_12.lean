-- Prove2me | solution 1 for ShiMatchmaking.Communication.proposition_12
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T14:15:31.833633+00:00
-- url     : https://prove2.me/submissions/72fdfe39-1f2d-4bf1-904a-e243490bb4e3

import Definitions.Def_ShiMatchmaking_Communication_Matchmaking

noncomputable section
open ShiMatchmaking.Communication
open scoped BigOperators

namespace ShiDisproof

def IsGoodMatching {n : ℕ} (ω : Profile n) (M : Fin n → Fin n → Bool) : Prop :=
  (∀ i j k, M i j = true → M i k = true → j = k) ∧
  (∀ i k j, M i j = true → M k j = true → i = k) ∧
  (∀ i j, M i j = true → Good ω i j)

def edgeSet {n : ℕ} (M : Fin n → Fin n → Bool) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun ij => M ij.1 ij.2 = true)

lemma empty_isGoodMatching {n : ℕ} (ω : Profile n) :
    IsGoodMatching ω (fun _ _ => false) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro i j <;> simp

lemma exists_max_goodMatching {n : ℕ} (ω : Profile n) :
    ∃ M : Fin n → Fin n → Bool, IsGoodMatching ω M ∧
      ∀ M' : Fin n → Fin n → Bool, IsGoodMatching ω M' →
        (edgeSet M').card ≤ (edgeSet M).card := by
  classical
  let S : Finset (Fin n → Fin n → Bool) := Finset.univ.filter (IsGoodMatching ω)
  have hne : S.Nonempty := ⟨fun _ _ => false, Finset.mem_filter.mpr ⟨Finset.mem_univ _, empty_isGoodMatching ω⟩⟩
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image S (fun M => (edgeSet M).card) hne
  refine ⟨M, (Finset.mem_filter.mp hM).2, fun M' hM' => ?_⟩
  exact hmax M' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM'⟩)

def maxMatching {n : ℕ} (ω : Profile n) : Fin n → Fin n → Bool :=
  Classical.choose (exists_max_goodMatching ω)

lemma maxMatching_isGood {n : ℕ} (ω : Profile n) :
    IsGoodMatching ω (maxMatching ω) :=
  (Classical.choose_spec (exists_max_goodMatching ω)).1

lemma maxMatching_max {n : ℕ} (ω : Profile n) (M' : Fin n → Fin n → Bool)
    (hM' : IsGoodMatching ω M') :
    (edgeSet M').card ≤ (edgeSet (maxMatching ω)).card :=
  (Classical.choose_spec (exists_max_goodMatching ω)).2 M' hM'

lemma maxMatching_maximal {n : ℕ} (ω : Profile n) (i j : Fin n) (hg : Good ω i j) :
    (∃ k, maxMatching ω i k = true) ∨ (∃ k, maxMatching ω k j = true) := by
  classical
  by_contra hnot
  have hrow : ∀ k, ¬ maxMatching ω i k = true := fun k hk => hnot (Or.inl ⟨k, hk⟩)
  have hcol : ∀ k, ¬ maxMatching ω k j = true := fun k hk => hnot (Or.inr ⟨k, hk⟩)
  have hrow' : ∀ k, maxMatching ω i k = false := fun k => Bool.eq_false_iff.mpr (hrow k)
  have hcol' : ∀ k, maxMatching ω k j = false := fun k => Bool.eq_false_iff.mpr (hcol k)
  let M' : Fin n → Fin n → Bool := fun a b => if a = i ∧ b = j then true else maxMatching ω a b
  have hgood := maxMatching_isGood ω
  have hM' : IsGoodMatching ω M' := by
    refine ⟨?_, ?_, ?_⟩
    · intro a b c hab hac
      dsimp [M'] at hab hac
      split_ifs at hab with h1 <;> split_ifs at hac with h2
      · exact h1.2.trans h2.2.symm
      · exfalso; rw [h1.1, hrow' c] at hac; revert hac; decide
      · exfalso; rw [h2.1, hrow' b] at hab; revert hab; decide
      · exact hgood.1 a b c hab hac
    · intro a c b hab hcb
      dsimp [M'] at hab hcb
      split_ifs at hab with h1 <;> split_ifs at hcb with h2
      · exact h1.1.trans h2.1.symm
      · exfalso; rw [h1.2, hcol' c] at hcb; revert hcb; decide
      · exfalso; rw [h2.2, hcol' a] at hab; revert hab; decide
      · exact hgood.2.1 a c b hab hcb
    · intro a b hab
      dsimp [M'] at hab
      split_ifs at hab with h1
      · rcases h1 with ⟨rfl, rfl⟩; exact hg
      · exact hgood.2.2 a b hab
  have hssub : edgeSet (maxMatching ω) ⊂ edgeSet M' := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(i, j), ?_, ?_⟩
      · simp [edgeSet, M']
      · simp [edgeSet, hrow' j]
    · intro pq hpq
      simp only [edgeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hpq ⊢
      dsimp [M']
      split_ifs with h1
      · rfl
      · exact hpq
  have hlt : (edgeSet (maxMatching ω)).card < (edgeSet M').card := Finset.card_lt_card hssub
  have hle := maxMatching_max ω M' hM'
  omega

def stableOutcome {n : ℕ} (ω : Profile n) : Outcome n := by
  classical
  exact {
    matched := maxMatching ω
    row_unique := (maxMatching_isGood ω).1
    col_unique := (maxMatching_isGood ω).2.1
    price := fun i => if ∃ j, maxMatching ω i j = true then 1 / 2 else 0
    unmatched_price := fun i hi => by
      rw [if_neg]
      rintro ⟨j, hj⟩
      exact Bool.noConfusion ((hi j).symm.trans hj)
  }

lemma customerSurplus_stableOutcome {n : ℕ} (ω : Profile n) (i : Fin n) :
    customerSurplus (binaryGame ω) (stableOutcome ω) i =
      if ∃ j, maxMatching ω i j = true then 49 / 100 else 0 := by
  classical
  unfold customerSurplus
  by_cases hex : ∃ j, maxMatching ω i j = true
  · rw [if_pos hex]
    rcases hex with ⟨j0, hj0⟩
    have hex' : ∃ j, maxMatching ω i j = true := ⟨j0, hj0⟩
    rw [Finset.sum_eq_single j0]
    · have hg : Good ω i j0 := (maxMatching_isGood ω).2.2 i j0 hj0
      simp only [stableOutcome, hj0, hex', ↓reduceIte, binaryGame, hg.1]
      norm_num
    · intro j _ hjne
      have hfalse : (stableOutcome ω).matched i j = false := by
        by_contra htr
        have htr' : maxMatching ω i j = true := Bool.eq_true_of_not_eq_false htr
        exact hjne ((maxMatching_isGood ω).1 i j j0 htr' hj0)
      simp [hfalse]
    · intro hj0mem; exact False.elim (hj0mem (Finset.mem_univ j0))
  · rw [if_neg hex]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hfalse : ¬ (stableOutcome ω).matched i j = true := fun hj => hex ⟨j, hj⟩
    simp [hfalse]

lemma providerSurplus_stableOutcome {n : ℕ} (ω : Profile n) (j : Fin n) :
    providerSurplus (binaryGame ω) (stableOutcome ω) j =
      if ∃ i, maxMatching ω i j = true then 49 / 100 else 0 := by
  classical
  unfold providerSurplus
  by_cases hex : ∃ i, maxMatching ω i j = true
  · rw [if_pos hex]
    rcases hex with ⟨i0, hi0⟩
    have hex' : ∃ k, maxMatching ω i0 k = true := ⟨j, hi0⟩
    rw [Finset.sum_eq_single i0]
    · have hg : Good ω i0 j := (maxMatching_isGood ω).2.2 i0 j hi0
      simp only [stableOutcome, hi0, hex', ↓reduceIte, binaryGame, hg.2]
      norm_num
    · intro i _ hine
      have hfalse : (stableOutcome ω).matched i j = false := by
        by_contra htr
        have htr' : maxMatching ω i j = true := Bool.eq_true_of_not_eq_false htr
        exact hine ((maxMatching_isGood ω).2.1 i i0 j htr' hi0)
      simp [hfalse]
    · intro hi0mem; exact False.elim (hi0mem (Finset.mem_univ i0))
  · rw [if_neg hex]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hfalse : ¬ (stableOutcome ω).matched i j = true := fun hi => hex ⟨i, hi⟩
    simp [hfalse]

lemma stableOutcome_isStable {n : ℕ} (ω : Profile n) {ε : ℝ} (hε : 49 / 200 ≤ ε) :
    Stable (binaryGame ω) ε (stableOutcome ω) := by
  classical
  refine ⟨fun i => ?_, fun j => ?_, fun i j => ?_⟩
  · rw [customerSurplus_stableOutcome]; split_ifs <;> norm_num
  · rw [providerSurplus_stableOutcome]; split_ifs <;> norm_num
  · rw [customerSurplus_stableOutcome, providerSurplus_stableOutcome]
    have hcs : 0 ≤ (if ∃ k, maxMatching ω i k = true then (49 / 100 : ℝ) else 0) := by split_ifs <;> norm_num
    have hps : 0 ≤ (if ∃ k, maxMatching ω k j = true then (49 / 100 : ℝ) else 0) := by split_ifs <;> norm_num
    by_cases hg : Good ω i j
    · rcases maxMatching_maximal ω i j hg with h1 | h2
      · rw [if_pos h1]
        simp only [binaryGame, hg.1, hg.2, ↓reduceIte]
        linarith
      · rw [if_pos h2]
        simp only [binaryGame, hg.1, hg.2, ↓reduceIte]
        linarith
    · have hle0 : (binaryGame ω).benefit i j - (binaryGame ω).cost i j ≤ 0 := by
        unfold Good at hg
        simp only [binaryGame]
        cases h1 : ω.1 i j <;> cases h2 : ω.2 i j
        · norm_num
        · norm_num
        · norm_num
        · exfalso; exact hg ⟨h1, h2⟩
      linarith

def B (n : ℕ) : ℕ := Fintype.card (Fin n → Bool)
def N (n : ℕ) : ℕ := Fintype.card (Agents n)
def M (n : ℕ) : ℕ := N n * B n

def code (n : ℕ) : (Fin n → Bool) ≃ Fin (B n) := Fintype.equivFin (Fin n → Bool)
def agentEquiv (n : ℕ) : Agents n ≃ Fin (N n) := Fintype.equivFin (Agents n)

lemma B_pos (n : ℕ) : 0 < B n := Fintype.card_pos

lemma N_pos (n : ℕ) [NeZero n] : 0 < N n := by
  have : Nonempty (Agents n) := ⟨Sum.inl ⟨0, NeZero.pos n⟩⟩
  exact Fintype.card_pos

def agentOf (n : ℕ) [NeZero n] (s : ℕ) : Agents n :=
  (agentEquiv n).symm ⟨(s / B n) % N n, Nat.mod_lt _ (N_pos n)⟩

def msg (n : ℕ) [NeZero n] (y : Agents n → (Fin n → Bool)) (s : ℕ) : Message :=
  if s % B n = (code n (y (agentOf n s))).val then [true] else []

def encHistory (n : ℕ) [NeZero n] (y : Agents n → (Fin n → Bool)) : History :=
  (List.range (M n)).map (msg n y)

lemma encHistory_injective (n : ℕ) [NeZero n] :
    Function.Injective (encHistory n) := by
  intro y1 y2 hEq
  funext a
  let k : Fin (N n) := agentEquiv n a
  let r : Fin (B n) := code n (y1 a)
  let s : ℕ := B n * k.val + r.val
  have hs : s < M n := by
    unfold M
    calc B n * k.val + r.val < B n * k.val + B n := Nat.add_lt_add_left r.isLt _
    _ = (k.val + 1) * B n := by ring
    _ ≤ N n * B n := Nat.mul_le_mul_right (B n) (Nat.succ_le_of_lt k.isLt)
  have hget := congr_arg (fun l : History => l[s]?) hEq
  simp only [encHistory, List.getElem?_map, List.getElem?_range hs, Option.map_some, Option.some.injEq] at hget
  have hmod : s % B n = r.val := by
    dsimp [s]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt r.isLt]
  have hdiv : s / B n = k.val := by
    dsimp [s]
    rw [Nat.mul_add_div (B_pos n), Nat.div_eq_of_lt r.isLt, add_zero]
  have hag : agentOf n s = a := by
    unfold agentOf
    have hk : (⟨(s / B n) % N n, Nat.mod_lt _ (N_pos n)⟩ : Fin (N n)) = k := by
      ext
      dsimp only
      rw [hdiv, Nat.mod_eq_of_lt k.isLt]
    rw [hk]
    exact (agentEquiv n).symm_apply_apply a
  unfold msg at hget
  rw [hmod, hag, if_pos rfl] at hget
  split_ifs at hget with hr2
  apply (code n).injective
  ext
  exact hr2

def decodeProfile (n : ℕ) [NeZero n] (h : History) : Profile n := by
  classical
  exact if hex : ∃ ω : Profile n, encHistory n (privateInput ω) = h then
    Classical.choose hex
  else
    (fun _ _ => false, fun _ _ => false)

lemma decodeProfile_encHistory (n : ℕ) [NeZero n] (ω : Profile n) :
    decodeProfile n (encHistory n (privateInput ω)) = ω := by
  classical
  unfold decodeProfile
  have hex : ∃ ω' : Profile n, encHistory n (privateInput ω') = encHistory n (privateInput ω) := ⟨ω, rfl⟩
  rw [dif_pos hex]
  have hspec := Classical.choose_spec hex
  have hinj := encHistory_injective n hspec
  ext i j
  · exact congr_fun (congr_fun hinj (Sum.inl i)) j
  · exact congr_fun (congr_fun hinj (Sum.inr j)) i

def fullRevBB (n : ℕ) [NeZero n] : Blackboard (Agents n) (fun _ => Fin n → Bool) (Outcome n) where
  first := agentOf n 0
  control := fun h =>
    if h.length < M n then
      Sum.inl (agentOf n h.length)
    else
      Sum.inr (stableOutcome (decodeProfile n h))
  send := fun _ loc h =>
    if h.length % B n = (code n loc).val then [true] else []

lemma M_pos (n : ℕ) [NeZero n] : 0 < M n :=
  Nat.mul_pos (N_pos n) (B_pos n)

lemma fullRevBB_historyAt (n : ℕ) [NeZero n] (y : Agents n → (Fin n → Bool)) :
    ∀ t < M n, (fullRevBB n).historyAt y t = (List.range (t + 1)).map (msg n y)
  | 0, _ => rfl
  | t + 1, ht => by
    have ih := fullRevBB_historyAt n y t (Nat.lt_of_succ_lt ht)
    have hlen : ((fullRevBB n).historyAt y t).length = t + 1 := by
      rw [ih, List.length_map, List.length_range]
    have hctrl : (fullRevBB n).control ((fullRevBB n).historyAt y t) = Sum.inl (agentOf n (t + 1)) := by
      change (if ((fullRevBB n).historyAt y t).length < M n then Sum.inl (agentOf n ((fullRevBB n).historyAt y t).length) else _) = _
      rw [hlen, if_pos ht]
    unfold Blackboard.historyAt
    dsimp only
    rw [hctrl]
    dsimp only
    have hsend : (fullRevBB n).send (agentOf n (t + 1)) (y (agentOf n (t + 1))) ((fullRevBB n).historyAt y t) = msg n y (t + 1) := by
      change (if ((fullRevBB n).historyAt y t).length % B n = (code n (y (agentOf n (t + 1)))).val then [true] else []) = msg n y (t + 1)
      rw [hlen]
      rfl
    rw [hsend, ih, List.range_succ (n := t + 1), List.map_append, List.map_singleton]

lemma fullRevBB_control_at_end (n : ℕ) [NeZero n] (y : Agents n → (Fin n → Bool)) :
    (fullRevBB n).control ((fullRevBB n).historyAt y (M n - 1)) =
      Sum.inr (stableOutcome (decodeProfile n ((fullRevBB n).historyAt y (M n - 1)))) := by
  have hM : 0 < M n := M_pos n
  have hhist := fullRevBB_historyAt n y (M n - 1) (Nat.sub_lt hM zero_lt_one)
  have hlen : ((fullRevBB n).historyAt y (M n - 1)).length = M n := by
    rw [hhist, List.length_map, List.length_range]
    omega
  change (if ((fullRevBB n).historyAt y (M n - 1)).length < M n then _ else _) = _
  rw [hlen, if_neg (lt_irrefl _)]

lemma fullRevBB_terminates (n : ℕ) [NeZero n] (y : Agents n → (Fin n → Bool)) :
    (fullRevBB n).Terminates y :=
  ⟨M n - 1, _, fullRevBB_control_at_end n y⟩

lemma fullRevBB_find_eq (n : ℕ) [NeZero n] (y : Agents n → (Fin n → Bool)) :
    @Nat.find _ (Classical.decPred _) (fullRevBB_terminates n y) = M n - 1 := by
  classical
  have hM : 0 < M n := M_pos n
  apply le_antisymm
  · exact Nat.find_min' (fullRevBB_terminates n y) ⟨_, fullRevBB_control_at_end n y⟩
  · by_contra hlt
    let t := Nat.find (fullRevBB_terminates n y)
    have htM : t + 1 < M n := by omega
    have hhist := fullRevBB_historyAt n y t (by omega)
    have hlen : ((fullRevBB n).historyAt y t).length = t + 1 := by
      rw [hhist, List.length_map, List.length_range]
    rcases Nat.find_spec (fullRevBB_terminates n y) with ⟨o, ho⟩
    change (if ((fullRevBB n).historyAt y t).length < M n then Sum.inl (agentOf n ((fullRevBB n).historyAt y t).length) else Sum.inr _) = Sum.inr o at ho
    rw [hlen, if_pos htM] at ho
    cases ho

lemma fullRevBB_history (n : ℕ) [NeZero n] (y : Agents n → (Fin n → Bool)) :
    (fullRevBB n).history y = encHistory n y := by
  classical
  have hM : 0 < M n := M_pos n
  unfold Blackboard.history
  rw [dif_pos (fullRevBB_terminates n y), fullRevBB_find_eq n y,
      fullRevBB_historyAt n y (M n - 1) (Nat.sub_lt hM zero_lt_one)]
  have hsub : M n - 1 + 1 = M n := by omega
  rw [hsub]
  rfl

lemma fullRevBB_result (n : ℕ) [NeZero n] (ω : Profile n) :
    (fullRevBB n).result (privateInput ω) = stableOutcome ω := by
  unfold Blackboard.result
  rw [fullRevBB_history n (privateInput ω)]
  have hlen : (encHistory n (privateInput ω)).length = M n := by
    simp [encHistory]
  have hctrl : (fullRevBB n).control (encHistory n (privateInput ω)) =
      Sum.inr (stableOutcome (decodeProfile n (encHistory n (privateInput ω)))) := by
    change (if (encHistory n (privateInput ω)).length < M n then _ else _) = _
    rw [hlen, if_neg (lt_irrefl _)]
  rw [hctrl]
  dsimp only
  rw [decodeProfile_encHistory n ω]

lemma flatten_range_eq_nil (B0 c : ℕ) (hc : B0 ≤ c) :
    ((List.range B0).map (fun r => if r = c then [true] else ([] : Message))).flatten = [] := by
  induction B0 with
  | zero => simp
  | succ b ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih (by omega)]
    simp [Nat.ne_of_lt hc]

lemma flatten_range_ite (B0 c : ℕ) (hc : c < B0) :
    ((List.range B0).map (fun r => if r = c then [true] else ([] : Message))).flatten = [true] := by
  induction B0 with
  | zero => omega
  | succ b ih =>
    rw [List.range_succ, List.map_append, List.flatten_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hlt | rfl
    · rw [ih hlt]
      simp [Nat.ne_of_gt hlt]
    · rw [flatten_range_eq_nil c c le_rfl]
      simp

lemma flatten_blocks (N0 B0 : ℕ) (f : ℕ → Message)
    (hblock : ∀ k < N0, ((List.range B0).map (fun r => f (k * B0 + r))).flatten = [true]) :
    ((List.range (N0 * B0)).map f).flatten = List.replicate N0 true := by
  induction N0 with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, List.range_add, List.map_append, List.flatten_append,
        ih (fun k hk => hblock k (Nat.lt_succ_of_lt hk))]
    have hm := hblock m (Nat.lt_succ_self m)
    simp only [List.map_map, Function.comp_def]
    rw [hm, List.replicate_succ']

lemma fullRevBB_transcript (n : ℕ) [NeZero n] (y : Agents n → (Fin n → Bool)) :
    (fullRevBB n).transcript y = List.replicate (N n) true := by
  unfold Blackboard.transcript
  rw [fullRevBB_history n y]
  unfold encHistory M
  refine flatten_blocks (N n) (B n) (msg n y) (fun k hk => ?_)
  let a := (agentEquiv n).symm ⟨k, hk⟩
  have hcongr : (List.range (B n)).map (fun r => msg n y (k * B n + r)) =
      (List.range (B n)).map (fun r => if r = (code n (y a)).val then [true] else ([] : Message)) := by
    refine List.map_congr_left fun r hr => ?_
    have hrB : r < B n := List.mem_range.mp hr
    have hcomm : k * B n + r = B n * k + r := by ring
    have hmod : (k * B n + r) % B n = r := by
      rw [hcomm, Nat.mul_add_mod, Nat.mod_eq_of_lt hrB]
    have hdiv : (k * B n + r) / B n = k := by
      rw [hcomm, Nat.mul_add_div (B_pos n), Nat.div_eq_of_lt hrB, add_zero]
    have hag : agentOf n (k * B n + r) = a := by
      unfold agentOf
      have hk' : (⟨((k * B n + r) / B n) % N n, Nat.mod_lt _ (N_pos n)⟩ : Fin (N n)) = ⟨k, hk⟩ := by
        ext
        dsimp only
        rw [hdiv, Nat.mod_eq_of_lt hk]
      rw [hk']
    unfold msg
    rw [hmod, hag]
  rw [hcongr]
  exact flatten_range_ite (B n) (code n (y a)).val (code n (y a)).isLt

def fullRevProto (n : ℕ) [NeZero n] (dI dJ : ℝ) : MatchmakingProtocol n dI dJ where
  protocol := fullRevBB n
  terminates := fun ω _ => fullRevBB_terminates n (privateInput ω)

lemma sum_bernoulliProduct {K : Type} [Fintype K] [DecidableEq K] (d : K → ℝ) :
    ∑ x : K → Bool, bernoulliProduct d x = 1 := by
  unfold bernoulliProduct
  have h := (Fintype.prod_sum (fun (k : K) (b : Bool) => if b then d k else 1 - d k)).symm
  rw [h]
  refine Finset.prod_eq_one fun k _ => ?_
  simp

lemma sum_matrix_bernoulli (n : ℕ) (d : ℝ) :
    ∑ m : Fin n → Fin n → Bool, bernoulliProduct (fun _ : Fin n × Fin n => d) (fun ij => m ij.1 ij.2) = 1 := by
  have heq := Fintype.sum_equiv (Equiv.curry (Fin n) (Fin n) Bool)
    (fun f : Fin n × Fin n → Bool => bernoulliProduct (fun _ : Fin n × Fin n => d) f)
    (fun m : Fin n → Fin n → Bool => bernoulliProduct (fun _ : Fin n × Fin n => d) (fun ij => m ij.1 ij.2))
    (fun _ => rfl)
  rw [← heq]
  exact sum_bernoulliProduct (fun _ : Fin n × Fin n => d)

lemma sum_marketMass (n : ℕ) (dI dJ : ℝ) :
    ∑ ω : Profile n, marketMass n dI dJ ω = 1 := by
  unfold marketMass
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [← Finset.sum_mul_sum, sum_matrix_bernoulli, sum_matrix_bernoulli, mul_one]

lemma fullRevProto_success (n : ℕ) [NeZero n] (dI dJ : ℝ) {ε : ℝ} (hε : 49 / 200 ≤ ε) :
    (fullRevProto n dI dJ).success ε = 1 := by
  classical
  unfold MatchmakingProtocol.success probability
  have h1 : ∀ ω : Profile n, Stable (binaryGame ω) ε ((fullRevProto n dI dJ).outcome ω) := by
    intro ω
    unfold MatchmakingProtocol.outcome fullRevProto
    rw [fullRevBB_result n ω]
    exact stableOutcome_isStable ω hε
  simp only [h1, ↓reduceIte]
  exact sum_marketMass n dI dJ

lemma N_eq (n : ℕ) : N n = 2 * n := by
  unfold N Agents
  simp [Fintype.card_sum, Fintype.card_fin, two_mul]

lemma fullRevBB_bits (n : ℕ) [NeZero n] (y : Agents n → (Fin n → Bool)) :
    (fullRevBB n).bits y = 2 * n := by
  unfold Blackboard.bits
  rw [← List.length_flatten]
  change ((fullRevBB n).transcript y).length = 2 * n
  rw [fullRevBB_transcript n y, List.length_replicate, N_eq]

lemma fullRevProto_cost_le_one (n : ℕ) [NeZero n] (dI dJ : ℝ) :
    (fullRevProto n dI dJ).cost ≤ 1 := by
  unfold MatchmakingProtocol.cost
  have hsup : (marketSupport n dI dJ).sup (fun ω => (fullRevProto n dI dJ).protocol.bits (privateInput ω)) ≤ 2 * n := by
    refine Finset.sup_le fun ω _ => ?_
    change (fullRevBB n).bits (privateInput ω) ≤ 2 * n
    rw [fullRevBB_bits]
  have hsupR : (((marketSupport n dI dJ).sup (fun ω => (fullRevProto n dI dJ).protocol.bits (privateInput ω)) : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast hsup
  have hn : (0 : ℝ) < 2 * (n : ℝ) := by
    have : 0 < n := NeZero.pos n
    positivity
  exact (div_le_one hn).mpr hsupR

end ShiDisproof

open ShiDisproof

theorem solution : ¬ (∃ κ₁ κ₂ κ₃ : ℝ, 0 < κ₁ ∧ 0 < κ₂ ∧ 0 < κ₃ ∧
    ∀ (n : ℕ), 64 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 49 / 100 →
      (∀ P : MatchmakingProtocol n (1 / (n : ℝ)) 1,
        99 / 100 ≤ P.success ε → κ₁ * Real.log (n : ℝ) ≤ P.cost) ∧
      (∀ dJ : ℝ, 1 / Real.sqrt (n : ℝ) ≤ dJ → dJ ≤ 1 / 2 →
        ∀ P : MatchmakingProtocol n (1 / ((n : ℝ) * dJ)) dJ,
        99 / 100 ≤ P.success ε → κ₂ / dJ ≤ P.cost) ∧
      (∀ P : OneRoundProtocol n,
        99 / 100 ≤ oneRoundSuccess P (1 / 2) (1 / 2) ε →
        κ₃ * Real.log (n : ℝ) ≤ oneRoundCost P (1 / 2) (1 / 2))) := by
  rintro ⟨κ₁, κ₂, κ₃, _, hκ₂, _, H⟩
  let m : ℕ := max 8 (Nat.ceil (2 / κ₂))
  let n : ℕ := m * m
  have hm8 : 8 ≤ m := le_max_left 8 _
  have hn64 : 64 ≤ n := by
    change 8 * 8 ≤ m * m
    exact Nat.mul_le_mul hm8 hm8
  haveI : NeZero n := ⟨by omega⟩
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    positivity
  let dJ : ℝ := 1 / (m : ℝ)
  have hsqrt : Real.sqrt (n : ℝ) = (m : ℝ) := by
    have hn_sq : (n : ℝ) = (m : ℝ) ^ 2 := by
      dsimp [n]
      push_cast
      ring
    rw [hn_sq, Real.sqrt_sq (le_of_lt hm_pos)]
  have hdlo : 1 / Real.sqrt (n : ℝ) ≤ dJ := by
    rw [hsqrt]
  have hdhi : dJ ≤ 1 / 2 := by
    dsimp [dJ]
    rw [div_le_div_iff₀ hm_pos (by norm_num)]
    have hm8R : (8 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm8
    linarith
  let P0 := fullRevProto n (1 / ((n : ℝ) * dJ)) dJ
  have hsucc : 99 / 100 ≤ P0.success (48 / 100) := by
    rw [fullRevProto_success n (1 / ((n : ℝ) * dJ)) dJ (by norm_num)]
    norm_num
  have hcost := (H n hn64 (48 / 100) (by norm_num) (by norm_num)).2.1 dJ hdlo hdhi P0 hsucc
  have hcost1 : P0.cost ≤ 1 := fullRevProto_cost_le_one n (1 / ((n : ℝ) * dJ)) dJ
  have hm_ge : 2 / κ₂ ≤ (m : ℝ) :=
    le_trans (Nat.le_ceil (2 / κ₂)) (by exact_mod_cast le_max_right 8 (Nat.ceil (2 / κ₂)))
  have h2 : 2 ≤ κ₂ / dJ := by
    dsimp [dJ]
    rw [div_div_eq_mul_div, div_one]
    have hmul := mul_le_mul_of_nonneg_left hm_ge (le_of_lt hκ₂)
    rw [mul_div_cancel₀ _ (ne_of_gt hκ₂)] at hmul
    exact hmul
  linarith
