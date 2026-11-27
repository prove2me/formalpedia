-- Prove2me | solution 1 for RankingQueryCost.Joint.lemma_4_9
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:55:26.272871+00:00
-- url     : https://prove2.me/submissions/f3395b00-44e4-46cf-8a70-f8236932aa42

import Definitions.Def_RankingQueryCost_Joint_Interaction
import Definitions.Def_RankingQueryCost_Joint_Scale

set_option autoImplicit false

namespace RQCLemma49
open RankingQueryCost.Joint MeasureTheory

variable {n : ℕ}

instance : IsProbabilityMeasure privateLaw := by unfold privateLaw; infer_instance

def stateEquiv : InteractionState n ≃
    (Pair n → Option Bool) × PublicHistory n × Finset (Pair n) where
  toFun S := (S.ledger, S.history, S.online)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Countable (InteractionState n) := Countable.of_equiv _ stateEquiv.symm

theorem meas_request (A : QueryPolicy n) (H : PublicHistory n) (x : Option (Option (Pair n))) :
    MeasurableSet {ω | A.request ω H = x} :=
  (A.request_measurable H) (MeasurableSpace.measurableSet_top (s := {x}))

theorem meas_message (A : QueryPolicy n) (H : PublicHistory n) (x : List ℕ) :
    MeasurableSet {ω | A.message ω H = x} :=
  (A.message_measurable H) (MeasurableSpace.measurableSet_top (s := {x}))

theorem prefix_running_succ (A : QueryPolicy n) (W : ComparisonWorld n) (h : ℕ) (ω : PrivateTape)
    (t : ℕ) (S : InteractionState n) :
    executionPrefix A W h ω (t + 1) = .running S ↔
      ∃ S0 : InteractionState n, executionPrefix A W h ω t = .running S0 ∧
        ∃ (e : Pair n) (msg : List ℕ), A.request ω S0.history = some (some e) ∧
          A.message ω S0.history = msg ∧ (readIdentity h W S0 msg e).2 = S := by
  simp only [executionPrefix]
  generalize executionPrefix A W h ω t = X
  constructor
  · intro hX
    cases X with
    | running S0 =>
      refine ⟨S0, rfl, ?_⟩
      simp only [advance] at hX
      revert hX
      rcases hr : A.request ω S0.history with _ | _ | e
      · simp
      · simp
      · intro hX
        simp only [Execution.running.injEq] at hX
        exact ⟨e, _, rfl, rfl, hX⟩
    | halted o => simp [advance] at hX
    | diverged S0 => simp [advance] at hX
  · rintro ⟨S0, rfl, e, msg, hr, hm, hS⟩
    simp only [advance, hr, hm, hS]

theorem meas_running (A : QueryPolicy n) (W : ComparisonWorld n) (h : ℕ) :
    ∀ t (S : InteractionState n), MeasurableSet {ω | executionPrefix A W h ω t = .running S} := by
  intro t
  induction t with
  | zero =>
    intro S
    by_cases hS : initialState n = S
    · simp [executionPrefix, hS]
    · simp [executionPrefix, hS]
  | succ t ih =>
    intro S
    have : {ω | executionPrefix A W h ω (t + 1) = .running S} =
        ⋃ (S0 : InteractionState n), ⋃ (e : Pair n), ⋃ (msg : List ℕ),
          ({ω | executionPrefix A W h ω t = .running S0} ∩
            {ω | A.request ω S0.history = some (some e)} ∩ {ω | A.message ω S0.history = msg} ∩
            {_ω | (readIdentity h W S0 msg e).2 = S}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      rw [prefix_running_succ]
      constructor
      · rintro ⟨S0, h1, e, msg, h2, h3, h4⟩; exact ⟨S0, e, msg, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩
      · rintro ⟨S0, e, msg, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩; exact ⟨S0, h1, e, msg, h2, h3, h4⟩
    rw [this]
    refine MeasurableSet.iUnion fun S0 => MeasurableSet.iUnion fun e => MeasurableSet.iUnion fun msg => ?_
    exact (((ih S0).inter (meas_request A _ _)).inter (meas_message A _ _)).inter (MeasurableSet.const _)

theorem halted_absorb (A : QueryPolicy n) (W : ComparisonWorld n) (h : ℕ) (ω : PrivateTape)
    (t : ℕ) (o : InteractionResult n) (ht : executionPrefix A W h ω t = .halted o) :
    ∀ k, executionPrefix A W h ω (t + k) = .halted o := by
  intro k
  induction k with
  | zero => exact ht
  | succ k ih => rw [← Nat.add_assoc, executionPrefix, ih]; rfl

theorem returns_unique (A : QueryPolicy n) (W : ComparisonWorld n) (h : ℕ) (ω : PrivateTape)
    (o o' : InteractionResult n) (h1 : Returns A W h ω o) (h2 : Returns A W h ω o') : o = o' := by
  obtain ⟨t, ht⟩ := h1
  obtain ⟨t', ht'⟩ := h2
  rcases le_total t t' with hle | hle
  · have := halted_absorb A W h ω t o ht (t' - t)
    rw [Nat.add_sub_cancel' hle, ht'] at this
    exact (Execution.halted.inj this).symm
  · have := halted_absorb A W h ω t' o' ht' (t - t')
    rw [Nat.add_sub_cancel' hle, ht] at this
    exact Execution.halted.inj this

theorem returns_iff (A : QueryPolicy n) (W : ComparisonWorld n) (h : ℕ) (ω : PrivateTape)
    (o : InteractionResult n) :
    Returns A W h ω o ↔ ∃ t, executionPrefix A W h ω t = .running o.state ∧
      A.request ω o.state.history = some none ∧
      o = ⟨o.state, A.estimate ω o.state.history, A.emission ω o.state.history,
        A.certificate ω o.state.history⟩ := by
  constructor
  · rintro ⟨t, ht⟩
    induction t with
    | zero => simp [executionPrefix] at ht
    | succ t ih =>
      simp only [executionPrefix] at ht
      generalize hX : executionPrefix A W h ω t = X at ht
      cases X with
      | running S =>
        simp only [advance] at ht
        revert ht
        rcases hr : A.request ω S.history with _ | _ | e
        · simp
        · intro ht
          simp only [Execution.halted.injEq] at ht
          subst ht
          exact ⟨t, hX, hr, rfl⟩
        · simp
      | halted o' =>
        simp only [advance, Execution.halted.injEq] at ht
        subst ht
        exact ih hX
      | diverged S => simp [advance] at ht
  · rintro ⟨t, ht, hr, ho⟩
    refine ⟨t + 1, ?_⟩
    simp only [executionPrefix, ht, advance, hr]
    rw [ho]

/-- Events determined by a returned result are measurable. -/
theorem meas_returns (A : QueryPolicy n) (W : ComparisonWorld n) (h : ℕ)
    (P : InteractionResult n → Prop)
    (hP : ∀ S : InteractionState n, MeasurableSet {ω | P ⟨S, A.estimate ω S.history,
      A.emission ω S.history, A.certificate ω S.history⟩}) :
    MeasurableSet {ω | ∃ o, Returns A W h ω o ∧ P o} := by
  have : {ω | ∃ o, Returns A W h ω o ∧ P o} =
      ⋃ (t : ℕ), ⋃ (S : InteractionState n),
        ({ω | executionPrefix A W h ω t = .running S} ∩ {ω | A.request ω S.history = some none} ∩
          {ω | P ⟨S, A.estimate ω S.history, A.emission ω S.history, A.certificate ω S.history⟩}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨o, hR, hPo⟩
      obtain ⟨t, ht, hr, ho⟩ := (returns_iff A W h ω o).1 hR
      refine ⟨t, o.state, ⟨ht, hr⟩, ?_⟩
      rw [ho] at hPo; exact hPo
    · rintro ⟨t, S, ⟨ht, hr⟩, hPS⟩
      refine ⟨_, (returns_iff A W h ω _).2 ⟨t, ht, hr, rfl⟩, hPS⟩
  rw [this]
  exact MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun S =>
    ((meas_running A W h t S).inter (meas_request A _ _)).inter (hP S)


/-- The clean world with true order `r`. -/
def W (r : Rank n) : ComparisonWorld n := ⟨r, ∅, fun _ _ _ _ => (false, false)⟩

theorem acquired_mono_step (h : ℕ) (W' : ComparisonWorld n) (S : InteractionState n) (msg : List ℕ)
    (e : Pair n) : acquired S.ledger ⊆ acquired (readIdentity h W' S msg e).2.ledger := by
  intro f hf
  unfold readIdentity
  cases hle : S.ledger e with
  | some b => simpa [hle] using hf
  | none =>
    simp only [hle]
    unfold acquired at hf ⊢
    rw [Finset.mem_filter] at hf ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases hfe : f = e
    · subst hfe; simp
    · rw [Function.update_of_ne hfe]; exact hf.2

theorem acquired_mono_prefix (A : QueryPolicy n) (W' : ComparisonWorld n) (h : ℕ) (ω : PrivateTape)
    (t k : ℕ) : acquired (executionState (executionPrefix A W' h ω t)).ledger ⊆
      acquired (executionState (executionPrefix A W' h ω (t + k))).ledger := by
  induction k with
  | zero => exact le_refl _
  | succ k ih =>
    refine le_trans ih ?_
    rw [← Nat.add_assoc]
    show _ ⊆ acquired (executionState (advance A W' h ω _)).ledger
    generalize executionPrefix A W' h ω (t + k) = X
    cases X with
    | running S =>
      simp only [advance]
      rcases A.request ω S.history with _ | _ | e
      · exact le_refl _
      · exact le_refl _
      · exact acquired_mono_step h W' S _ e
    | halted o => exact le_refl _
    | diverged S => exact le_refl _

theorem readIdentity_agree (r r' : Rank n) (S : InteractionState n) (msg : List ℕ) (e : Pair n)
    (hag : S.ledger e = none → truthful r e = truthful r' e) :
    readIdentity 0 (W r) S msg e = readIdentity 0 (W r') S msg e := by
  unfold readIdentity
  cases hle : S.ledger e with
  | some b => rfl
  | none => simp [W, hag hle]

theorem mem_acquired_readIdentity (h : ℕ) (W' : ComparisonWorld n) (S : InteractionState n)
    (msg : List ℕ) (e : Pair n) : e ∈ acquired (readIdentity h W' S msg e).2.ledger := by
  unfold readIdentity acquired
  cases hle : S.ledger e with
  | some b => simp [hle]
  | none => simp

/-- Agreement on every finally acquired pair transfers the whole execution. -/
theorem agree_prefix (A : QueryPolicy n) (r r' : Rank n) (ω : PrivateTape) :
    ∀ t, (∀ e ∈ acquired (executionState (executionPrefix A (W r) 0 ω t)).ledger,
        truthful r e = truthful r' e) →
      executionPrefix A (W r) 0 ω t = executionPrefix A (W r') 0 ω t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro hag
    have hmono := acquired_mono_prefix A (W r) 0 ω t 1
    have ih' := ih (fun e he => hag e (hmono he))
    revert hag
    simp only [executionPrefix]
    rw [← ih']
    generalize executionPrefix A (W r) 0 ω t = X
    intro hag
    cases X with
    | running S =>
      simp only [advance] at hag ⊢
      revert hag
      rcases A.request ω S.history with _ | _ | e
      · intro _; rfl
      · intro _; rfl
      · intro hag
        simp only at hag ⊢
        rw [readIdentity_agree r r' S _ e (fun _ => hag e (mem_acquired_readIdentity 0 _ S _ e))]
    | halted o => rfl
    | diverged S => rfl

theorem agree_returns (A : QueryPolicy n) (r r' : Rank n) (ω : PrivateTape) (o : InteractionResult n)
    (hR : Returns A (W r) 0 ω o) (hag : ∀ e ∈ acquired o.state.ledger, truthful r e = truthful r' e) :
    Returns A (W r') 0 ω o := by
  obtain ⟨t, ht⟩ := hR
  refine ⟨t, ?_⟩
  rw [← agree_prefix A r r' ω t (by rw [ht]; exact hag), ht]

/-! New-answer bits of a history. -/

def nbStep (p : List (Pair n) × List Bool) (x : List ℕ × Pair n × Bool) : List (Pair n) × List Bool :=
  if x.2.1 ∈ p.1 then p else (x.2.1 :: p.1, p.2 ++ [x.2.2])

def nb (H : PublicHistory n) : List (Pair n) × List Bool := H.foldl nbStep ([], [])

theorem nb_append (H : PublicHistory n) (x : List ℕ × Pair n × Bool) :
    nb (H ++ [x]) = nbStep (nb H) x := by
  simp [nb, List.foldl_append]

theorem foldl_nb_prefix (K : PublicHistory n) : ∀ p : List (Pair n) × List Bool,
    p.2 <+: (K.foldl nbStep p).2 := by
  induction K with
  | nil => intro p; exact List.prefix_refl _
  | cons x K ih =>
    intro p
    simp only [List.foldl_cons]
    refine List.IsPrefix.trans ?_ (ih _)
    unfold nbStep
    split_ifs
    · exact List.prefix_refl _
    · exact List.prefix_append _ _

theorem nb_prefix (H K : PublicHistory n) : (nb H).2 <+: (nb (H ++ K)).2 := by
  unfold nb
  rw [List.foldl_append]
  exact foldl_nb_prefix K _

def NbInv (S : InteractionState n) : Prop :=
  (∀ e, e ∈ (nb S.history).1 ↔ S.ledger e ≠ none) ∧ (nb S.history).1.Nodup ∧
    (nb S.history).2.length = (nb S.history).1.length

theorem nbInv_step (h : ℕ) (W' : ComparisonWorld n) (S : InteractionState n) (msg : List ℕ)
    (e : Pair n) (hS : NbInv S) : NbInv (readIdentity h W' S msg e).2 := by
  obtain ⟨hmem, hnd, hlen⟩ := hS
  unfold readIdentity
  cases hle : S.ledger e with
  | some b =>
    simp only [hle]
    have he : e ∈ (nb S.history).1 := (hmem e).2 (by simp [hle])
    refine ⟨?_, ?_, ?_⟩ <;> simp only [nb_append, nbStep, he, if_true]
    · exact hmem
    · exact hnd
    · exact hlen
  | none =>
    simp only [hle]
    have he : e ∉ (nb S.history).1 := fun h' => (hmem e).1 h' hle
    refine ⟨?_, ?_, ?_⟩ <;> simp only [nb_append, nbStep, he, if_false]
    · intro f
      simp only [List.mem_cons]
      by_cases hfe : f = e
      · subst hfe; simp
      · rw [Function.update_of_ne hfe]; simp [hfe, hmem f]
    · exact List.nodup_cons.2 ⟨he, hnd⟩
    · simp [hlen]

theorem nbInv_prefix (A : QueryPolicy n) (W' : ComparisonWorld n) (h : ℕ) (ω : PrivateTape) :
    ∀ t, NbInv (executionState (executionPrefix A W' h ω t)) := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun e => ?_, ?_, ?_⟩ <;>
      simp [executionPrefix, executionState, initialState, nb, emptyTranscript]
  | succ t ih =>
    simp only [executionPrefix]
    generalize executionPrefix A W' h ω t = X at ih
    cases X with
    | running S =>
      simp only [advance]
      rcases A.request ω S.history with _ | _ | e
      · exact ih
      · exact ih
      · exact nbInv_step h W' S _ e ih
    | halted o => exact ih
    | diverged S => exact ih

theorem history_prefix (A : QueryPolicy n) (W' : ComparisonWorld n) (h : ℕ) (ω : PrivateTape)
    (t k : ℕ) : ∃ K, (executionState (executionPrefix A W' h ω (t + k))).history =
      (executionState (executionPrefix A W' h ω t)).history ++ K := by
  induction k with
  | zero => exact ⟨[], by simp⟩
  | succ k ih =>
    obtain ⟨K, hK⟩ := ih
    rw [← Nat.add_assoc]
    show ∃ K', (executionState (advance A W' h ω (executionPrefix A W' h ω (t + k)))).history = _
    generalize hX : executionPrefix A W' h ω (t + k) = X at hK
    cases X with
    | running S =>
      simp only [advance]
      rcases A.request ω S.history with _ | _ | e
      · exact ⟨K, hK⟩
      · exact ⟨K, hK⟩
      · refine ⟨K ++ [(A.message ω S.history, e, (readIdentity h W' S (A.message ω S.history) e).1)], ?_⟩
        simp only [executionState] at hK ⊢
        unfold readIdentity
        cases S.ledger e <;> simp [hK]
    | halted o => exact ⟨K, hK⟩
    | diverged S => exact ⟨K, hK⟩

theorem readIdentity_new_history (r : Rank n) (S : InteractionState n) (msg : List ℕ) (e : Pair n)
    (hle : S.ledger e = none) :
    (readIdentity 0 (W r) S msg e).2.history = S.history ++ [(msg, e, truthful r e)] := by
  unfold readIdentity; simp [hle, W]

theorem prefix_halted_of_ge (A : QueryPolicy n) (W' : ComparisonWorld n) (h : ℕ) (ω : PrivateTape)
    (t : ℕ) (o : InteractionResult n) (ht : executionPrefix A W' h ω t = .halted o) (k : ℕ) (hk : t ≤ k) :
    executionPrefix A W' h ω k = .halted o := by
  have := halted_absorb A W' h ω t o ht (k - t)
  rwa [Nat.add_sub_cancel' hk] at this

theorem same_bits (A : QueryPolicy n) (r r' : Rank n) (ω : PrivateTape) (o o' : InteractionResult n)
    (hR : Returns A (W r) 0 ω o) (hR' : Returns A (W r') 0 ω o')
    (hbits : (nb o.state.history).2 = (nb o'.state.history).2) : o = o' := by
  obtain ⟨t, ht⟩ := hR
  obtain ⟨t', ht'⟩ := hR'
  have key : ∀ k, executionPrefix A (W r) 0 ω k = executionPrefix A (W r') 0 ω k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [executionPrefix]
      rw [← ih]
      generalize hX : executionPrefix A (W r) 0 ω k = X
      have hX' : executionPrefix A (W r') 0 ω k = X := by rw [← ih, hX]
      cases X with
      | running S =>
        have hkt : k < t := by
          by_contra hc; push Not at hc
          rw [prefix_halted_of_ge A _ 0 ω t o ht k hc] at hX; cases hX
        have hkt' : k < t' := by
          by_contra hc; push Not at hc
          rw [prefix_halted_of_ge A _ 0 ω t' o' ht' k hc] at hX'; cases hX'
        simp only [advance]
        rcases hreq : A.request ω S.history with _ | _ | e
        · rfl
        · rfl
        · simp only
          rw [readIdentity_agree r r' S _ e]
          intro hle
          have hinv := (nbInv_prefix A (W r) 0 ω k)
          rw [hX] at hinv
          have he : e ∉ (nb S.history).1 := fun h' => (hinv.1 e).1 h' hle
          -- the history after this step, in both runs
          have hstep : ∀ (ρ : Rank n) (tt : ℕ) (oo : InteractionResult n),
              executionPrefix A (W ρ) 0 ω k = .running S → k < tt →
              executionPrefix A (W ρ) 0 ω tt = .halted oo →
              (nb S.history).2 ++ [truthful ρ e] <+: (nb oo.state.history).2 := by
            intro ρ tt oo hk hlt hoo
            obtain ⟨K, hK⟩ := history_prefix A (W ρ) 0 ω (k + 1) (tt - (k + 1))
            rw [Nat.add_sub_cancel' hlt, hoo] at hK
            simp only [executionState] at hK
            have h1 : executionPrefix A (W ρ) 0 ω (k + 1) =
                .running (readIdentity 0 (W ρ) S (A.message ω S.history) e).2 := by
              simp only [executionPrefix, hk, advance, hreq]
            rw [h1] at hK
            simp only [executionState] at hK
            rw [readIdentity_new_history ρ S _ e hle] at hK
            rw [hK]
            have := nb_prefix (S.history ++ [(A.message ω S.history, e, truthful ρ e)]) K
            rw [nb_append] at this
            simpa [nbStep, he] using this
          have p1 := hstep r t o hX hkt ht
          have p2 := hstep r' t' o' hX' hkt' ht'
          rw [← hbits] at p2
          have := List.prefix_of_prefix_length_le p1 p2 (by simp)
          have hl := (List.prefix_iff_eq_take.1 this)
          have hl2 : ((nb S.history).2 ++ [truthful r e]).length =
              ((nb S.history).2 ++ [truthful r' e]).length := by simp
          have := List.IsPrefix.eq_of_length this hl2
          simpa using this
      | halted oo => rfl
      | diverged S => rfl
  have : executionPrefix A (W r') 0 ω t = .halted o := by rw [← key, ht]
  exact returns_unique A (W r') 0 ω o o' ⟨t, this⟩ ⟨t', ht'⟩

theorem bits_length (A : QueryPolicy n) (r : Rank n) (ω : PrivateTape) (o : InteractionResult n)
    (hR : Returns A (W r) 0 ω o) : (nb o.state.history).2.length ≤ (acquired o.state.ledger).card := by
  obtain ⟨t, ht⟩ := hR
  have hinv := nbInv_prefix A (W r) 0 ω t
  rw [ht] at hinv
  simp only [executionState] at hinv
  obtain ⟨hmem, hnd, hlen⟩ := hinv
  rw [hlen, ← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card
  intro e he
  rw [List.mem_toFinset] at he
  have := (hmem e).1 he
  unfold acquired
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  cases h' : o.state.ledger e
  · exact absurd h' this
  · rfl

end RQCLemma49

namespace RQCCount
open RankingQueryCost.Joint

variable {n : ℕ}

/-- Vectors with bounded total. -/
def KS (n L : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (L + 1)).filter fun k => ∑ i, k i ≤ L

def toMS (n L : ℕ) (k : Fin n → ℕ) : Multiset (Option (Fin n)) :=
  Multiset.replicate (L - ∑ i, k i) none + ∑ i, Multiset.replicate (k i) (some i)

theorem toMS_card (L : ℕ) (k : Fin n → ℕ) (hk : ∑ i, k i ≤ L) : Multiset.card (toMS n L k) = L := by
  unfold toMS
  rw [Multiset.card_add, Multiset.card_replicate, Multiset.card_sum]
  simp only [Multiset.card_replicate]
  omega

theorem toMS_count (L : ℕ) (k : Fin n → ℕ) (i : Fin n) : Multiset.count (some i) (toMS n L k) = k i := by
  unfold toMS
  rw [Multiset.count_add, Multiset.count_replicate, Multiset.count_sum']
  simp [Multiset.count_replicate]

theorem KS_card (L : ℕ) : (KS n L).card ≤ (n + L).choose L := by
  classical
  have hcard : Fintype.card (Sym (Option (Fin n)) L) = (n + L).choose L := by
    rw [Sym.card_sym_eq_choose]; simp
  rw [← hcard]
  let emb : Sym (Option (Fin n)) L ↪ Multiset (Option (Fin n)) := ⟨fun s => (s : Multiset _), Sym.coe_injective⟩
  have : (KS n L).card ≤ ((Finset.univ : Finset (Sym (Option (Fin n)) L)).map emb).card := by
    apply Finset.card_le_card_of_injOn (fun k => toMS n L k)
    · intro k hk
      have hk1 : ∑ i, k i ≤ L := (Finset.mem_filter.1 hk).2
      rw [Finset.mem_coe, Finset.mem_map]
      exact ⟨Sym.mk (toMS n L k) (toMS_card L k hk1), Finset.mem_univ _, rfl⟩
    · intro k _ k' _ h
      funext i
      rw [← toMS_count L k i, ← toMS_count L k' i]
      simp only at h
      rw [h]
  rw [Finset.card_map, Finset.card_univ] at this
  exact this

theorem sum_abs_le (a : Fin n → ℝ) : ∑ i, |a i| ≤ Real.sqrt (n * ∑ i, a i ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => |a i|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, sq_abs] at this
  exact this

theorem near_count (q : Fin n → ℝ) (R2 : ℝ) :
    ((Finset.univ : Finset (Rank n)).filter fun r => squaredError q (rankVector r) ≤ R2).card ≤
      2 ^ n * (n + ⌊Real.sqrt (n * R2)⌋₊).choose ⌊Real.sqrt (n * R2)⌋₊ := by
  classical
  set L := ⌊Real.sqrt (n * R2)⌋₊
  let φ : Rank n → (Fin n → ℕ) × (Fin n → Bool) := fun r =>
    (fun i => ⌊|q i - rankVector r i|⌋₊, fun i => decide (q i ≤ rankVector r i))
  have hmaps : ∀ r ∈ ((Finset.univ : Finset (Rank n)).filter fun r => squaredError q (rankVector r) ≤ R2),
      φ r ∈ KS n L ×ˢ (Finset.univ : Finset (Fin n → Bool)) := by
    intro r hr
    have hr2 := (Finset.mem_filter.1 hr).2
    have hsum : ∑ i, ⌊|q i - rankVector r i|⌋₊ ≤ L := by
      apply Nat.le_floor
      push_cast
      calc ∑ i, (⌊|q i - rankVector r i|⌋₊ : ℝ) ≤ ∑ i, |q i - rankVector r i| :=
            Finset.sum_le_sum fun i _ => Nat.floor_le (abs_nonneg _)
        _ ≤ Real.sqrt (n * ∑ i, (q i - rankVector r i) ^ 2) := sum_abs_le _
        _ ≤ Real.sqrt (n * R2) := by
            apply Real.sqrt_le_sqrt
            exact mul_le_mul_of_nonneg_left hr2 (Nat.cast_nonneg _)
    refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨?_, hsum⟩, Finset.mem_univ _⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    show ⌊|q i - rankVector r i|⌋₊ < L + 1
    have := Finset.single_le_sum (f := fun i => ⌊|q i - rankVector r i|⌋₊) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
    omega
  have hinj : Set.InjOn φ (((Finset.univ : Finset (Rank n)).filter
      fun r => squaredError q (rankVector r) ≤ R2) : Set (Rank n)) := by
    intro r _ r' _ h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    apply Equiv.ext
    intro i
    have e1 := congrFun h1 i
    have e2 := congrFun h2 i
    simp only [decide_eq_decide] at e2
    apply Fin.ext
    set x := rankVector r i
    set y := rankVector r' i
    have hx : x = ((r i : ℕ) : ℝ) := rfl
    have hy : y = ((r' i : ℕ) : ℝ) := rfl
    set k := ⌊|q i - x|⌋₊
    have a1 : (k : ℝ) ≤ |q i - x| := Nat.floor_le (abs_nonneg _)
    have a2 : |q i - x| < k + 1 := Nat.lt_floor_add_one _
    have b1 : (k : ℝ) ≤ |q i - y| := by rw [e1]; exact Nat.floor_le (abs_nonneg _)
    have b2 : |q i - y| < k + 1 := by rw [e1]; exact Nat.lt_floor_add_one _
    have hxy : |x - y| < 1 := by
      by_cases hq : q i ≤ x
      · have hq' : q i ≤ y := e2.1 hq
        rw [abs_of_nonpos (by linarith)] at a1 a2
        rw [abs_of_nonpos (by linarith)] at b1 b2
        rw [abs_lt]; constructor <;> linarith
      · have hq' : ¬ q i ≤ y := fun h => hq (e2.2 h)
        push Not at hq hq'
        rw [abs_of_pos (by linarith)] at a1 a2
        rw [abs_of_pos (by linarith)] at b1 b2
        rw [abs_lt]; constructor <;> linarith
    rw [hx, hy] at hxy
    have : ((r i : ℕ) : ℤ) = ((r' i : ℕ) : ℤ) := by
      have h3 : |(((r i : ℕ) : ℤ) : ℝ) - (((r' i : ℕ) : ℤ) : ℝ)| < 1 := by push_cast; exact hxy
      rw [← Int.cast_sub, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at h3
      have := abs_lt.1 h3
      omega
    exact_mod_cast this
  calc _ ≤ (KS n L ×ˢ (Finset.univ : Finset (Fin n → Bool))).card :=
        Finset.card_le_card_of_injOn φ hmaps hinj
    _ = (KS n L).card * 2 ^ n := by simp [Finset.card_product]
    _ ≤ (n + L).choose L * 2 ^ n := Nat.mul_le_mul_right _ (KS_card L)
    _ = 2 ^ n * (n + L).choose L := by ring

end RQCCount

namespace RQCRefl
open RankingQueryCost.Joint

variable {n : ℕ}

noncomputable def iso (V : Finset (Fin n)) : Fin V.card ≃o { x // x ∈ V } := V.orderIsoOfFin rfl

noncomputable def reflectFun (V : Finset (Fin n)) (x : Fin n) : Fin n :=
  if hx : x ∈ V then ((iso V) (Fin.rev ((iso V).symm ⟨x, hx⟩)) : Fin n) else x

theorem reflectFun_mem (V : Finset (Fin n)) (x : Fin n) (hx : x ∈ V) : reflectFun V x ∈ V := by
  unfold reflectFun; rw [dif_pos hx]; exact ((iso V) _).2

theorem reflectFun_pos (V : Finset (Fin n)) (x : Fin n) (hx : x ∈ V) :
    reflectFun V x = ((iso V) (Fin.rev ((iso V).symm ⟨x, hx⟩)) : Fin n) := by
  unfold reflectFun; rw [dif_pos hx]

theorem reflectFun_invol (V : Finset (Fin n)) : Function.Involutive (reflectFun V) := by
  intro x
  by_cases hx : x ∈ V
  · have h1 := reflectFun_mem V x hx
    rw [reflectFun_pos V _ h1]
    have : (⟨reflectFun V x, h1⟩ : { y // y ∈ V }) = (iso V) (Fin.rev ((iso V).symm ⟨x, hx⟩)) := by
      apply Subtype.ext; exact reflectFun_pos V x hx
    rw [this]
    simp
  · unfold reflectFun; simp [hx]

theorem reflectFun_not_mem (V : Finset (Fin n)) (x : Fin n) (hx : x ∉ V) : reflectFun V x = x := by
  unfold reflectFun; rw [dif_neg hx]

noncomputable def touched (T : Transcript n) : Finset (Fin n) :=
  (acquired T).image (fun e => e.1.1) ∪ (acquired T).image (fun e => e.1.2)

theorem touched_card (T : Transcript n) : (touched T).card ≤ 2 * (acquired T).card := by
  unfold touched
  refine le_trans (Finset.card_union_le _ _) ?_
  have := Finset.card_image_le (s := acquired T) (f := fun e => e.1.1)
  have := Finset.card_image_le (s := acquired T) (f := fun e => e.1.2)
  omega

noncomputable def rankSet (r : Rank n) (T : Transcript n) : Finset (Fin n) := (touched T)ᶜ.image r

noncomputable def reflectRank (r : Rank n) (T : Transcript n) : Rank n :=
  r.trans (Function.Involutive.toPerm _ (reflectFun_invol (rankSet r T)))

theorem reflectRank_apply (r : Rank n) (T : Transcript n) (i : Fin n) :
    reflectRank r T i = reflectFun (rankSet r T) (r i) := rfl

theorem reflectRank_touched (r : Rank n) (T : Transcript n) (i : Fin n) (hi : i ∈ touched T) :
    reflectRank r T i = r i := by
  rw [reflectRank_apply, reflectFun_not_mem]
  intro h
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 h
  have := r.injective hji
  subst this
  exact (Finset.mem_compl.1 hj) hi

theorem rankSet_reflect (r : Rank n) (T : Transcript n) :
    rankSet (reflectRank r T) T = rankSet r T := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    rw [reflectRank_apply]
    exact reflectFun_mem _ _ (Finset.mem_image_of_mem r hj)
  · unfold rankSet
    rw [Finset.card_image_of_injective _ r.injective,
      Finset.card_image_of_injective _ (reflectRank r T).injective]

theorem reflectRank_invol (r : Rank n) (T : Transcript n) :
    reflectRank (reflectRank r T) T = r := by
  apply Equiv.ext
  intro i
  rw [reflectRank_apply, rankSet_reflect, reflectRank_apply, reflectFun_invol]

theorem truthful_reflect (r : Rank n) (T : Transcript n) (e : Pair n) (he : e ∈ acquired T) :
    truthful r e = truthful (reflectRank r T) e := by
  have h1 : e.1.1 ∈ touched T := Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)
  have h2 : e.1.2 ∈ touched T := Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)
  simp [truthful, reflectRank_touched r T _ h1, reflectRank_touched r T _ h2]

theorem gap (u : ℕ) (g : Fin u → ℕ) (hg : StrictMono g) (a : Fin u) :
    ∀ d, ∀ (h : a.val + d < u), g a + d ≤ g ⟨a.val + d, h⟩ := by
  intro d
  induction d with
  | zero => intro h; simp
  | succ d ih =>
    intro h
    have h1 := ih (by omega)
    have h2 : g ⟨a.val + d, by omega⟩ < g ⟨a.val + (d + 1), h⟩ := hg (by simp [Fin.lt_def])
    omega

theorem reflect_sum_lower (V : Finset (Fin n)) :
    (((V.card + 3) / 4 : ℕ) : ℝ) * (((V.card : ℝ) / 2 - 1) ^ 2) ≤
      ∑ x : Fin n, (((x : ℕ) : ℝ) - ((reflectFun V x : Fin n) : ℕ)) ^ 2 ∨ V.card < 2 := by
  by_cases hu : V.card < 2
  · exact Or.inr hu
  left
  push Not at hu
  set u := V.card
  set g : Fin u → ℕ := fun j => (((iso V) j : Fin n) : ℕ)
  have hg : StrictMono g := by
    intro a b hab
    simp only [g]
    have := (iso V).strictMono hab
    exact this
  -- restrict the sum to `V` and reindex by `Fin u`
  have hsub : ∑ x ∈ V, (((x : ℕ) : ℝ) - ((reflectFun V x : Fin n) : ℕ)) ^ 2 ≤
      ∑ x : Fin n, (((x : ℕ) : ℝ) - ((reflectFun V x : Fin n) : ℕ)) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  refine le_trans ?_ hsub
  have hre : ∑ x ∈ V, (((x : ℕ) : ℝ) - ((reflectFun V x : Fin n) : ℕ)) ^ 2 =
      ∑ j : Fin u, ((g j : ℝ) - (g (Fin.rev j) : ℝ)) ^ 2 := by
    rw [← Finset.sum_coe_sort V]
    refine Fintype.sum_equiv (iso V).toEquiv.symm _ _ ?_
    intro x
    simp only [g]
    unfold reflectFun
    rw [dif_pos x.2]
    simp
  rw [hre]
  have hcnt : ((Finset.univ : Finset (Fin u)).filter fun j => j.val < (u + 3) / 4).card = (u + 3) / 4 := by
    rw [Fin.card_filter_val_lt]; omega
  have hsub2 : ∑ j ∈ (Finset.univ : Finset (Fin u)).filter (fun j => j.val < (u + 3) / 4),
      ((g j : ℝ) - (g (Fin.rev j) : ℝ)) ^ 2 ≤ ∑ j : Fin u, ((g j : ℝ) - (g (Fin.rev j) : ℝ)) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  refine le_trans ?_ hsub2
  have := Finset.card_nsmul_le_sum ((Finset.univ : Finset (Fin u)).filter fun j => j.val < (u + 3) / 4)
    (fun j => ((g j : ℝ) - (g (Fin.rev j) : ℝ)) ^ 2) (((u : ℝ) / 2 - 1) ^ 2) (by
      intro j hj
      have hj4 : 4 * j.val < u := by have := (Finset.mem_filter.1 hj).2; omega
      have hrev : (Fin.rev j).val = j.val + (u - 1 - 2 * j.val) := by simp [Fin.val_rev]; omega
      have hgap := gap u g hg j (u - 1 - 2 * j.val) (by omega)
      have heq : (⟨j.val + (u - 1 - 2 * j.val), by omega⟩ : Fin u) = Fin.rev j := Fin.ext hrev.symm
      rw [heq] at hgap
      have hgapR : (g j : ℝ) + ((u - 1 - 2 * j.val : ℕ) : ℝ) ≤ g (Fin.rev j) := by exact_mod_cast hgap
      have hdR : ((u : ℝ) / 2 - 1) ≤ ((u - 1 - 2 * j.val : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        have : (4 * j.val : ℝ) + 1 ≤ u := by exact_mod_cast hj4
        push_cast; linarith
      have hu2 : (0 : ℝ) ≤ (u : ℝ) / 2 - 1 := by
        have : (2 : ℝ) ≤ u := by exact_mod_cast hu
        linarith
      nlinarith)
  rw [hcnt, nsmul_eq_mul] at this
  exact this

end RQCRefl

namespace RQCLemma49Main
open RankingQueryCost.Joint RQCLemma49 RQCCount RQCRefl MeasureTheory

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem loss_le_iff (q : Fin n → ℝ) (r : Rank n) (ε : ℝ) (hn : 0 < n) :
    loss q r ≤ ε ↔ squaredError q (rankVector r) ≤ ε * (n : ℝ) ^ 3 := by
  unfold loss
  rw [div_le_iff₀ (by positivity)]

/-- Averaging: a pointwise bound on the number of successful orders bounds the total success. -/
theorem average_bound (S : Rank n → Set PrivateTape) (hS : ∀ r, MeasurableSet (S r)) (K : ℝ)
    (hK : ∀ ω, (((Finset.univ : Finset (Rank n)).filter fun r => ω ∈ S r).card : ℝ) ≤ K) :
    ∑ r, privateLaw.real (S r) ≤ K := by
  classical
  have hint : ∑ r, privateLaw.real (S r) = ∫ ω, ∑ r, (S r).indicator (1 : PrivateTape → ℝ) ω ∂privateLaw := by
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun r _ => (integral_indicator_one (hS r)).symm
    · intro r _; exact (integrable_const (1 : ℝ)).indicator (hS r)
  rw [hint]
  have : ∫ ω, ∑ r, (S r).indicator (1 : PrivateTape → ℝ) ω ∂privateLaw ≤ ∫ _ω, K ∂privateLaw := by
    apply integral_mono
    · exact integrable_finsetSum _ fun r _ => (integrable_const (1 : ℝ)).indicator (hS r)
    · exact integrable_const _
    · intro ω
      have hsum : ∑ r, (S r).indicator (1 : PrivateTape → ℝ) ω =
          (((Finset.univ : Finset (Rank n)).filter fun r => ω ∈ S r).card : ℝ) := by
        rw [Finset.card_filter, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro r _
        by_cases hr : ω ∈ S r <;> simp [hr]
      simp only
      rw [hsum]; exact hK ω
  simpa using this

def Ssucc (A : QueryPolicy n) (ε : ℝ) (r : Rank n) : Set PrivateTape :=
  {ω | ∃ o, Returns A (W r) 0 ω o ∧ loss o.estimate r ≤ ε}

theorem sqErr_triangle (x y z : Fin n → ℝ) :
    squaredError x z ≤ 2 * squaredError x y + 2 * squaredError y z := by
  unfold squaredError
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (x i + z i - 2 * y i)]

theorem sqErr_symm (x y : Fin n → ℝ) : squaredError x y = squaredError y x := by
  unfold squaredError; congr 1; ext i; ring

theorem reflect_far (r : Rank n) (T : Transcript n) (B : ℕ) (hn : 16 ≤ n)
    (hT : (acquired T).card ≤ B) (h8 : 8 * B < n) :
    (n : ℝ) ^ 3 / 256 < squaredError (rankVector r) (rankVector (reflectRank r T)) := by
  set V := rankSet r T
  have hVcard : V.card + (touched T).card = n := by
    have : V.card = (touched T)ᶜ.card := Finset.card_image_of_injective _ r.injective
    rw [this, Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_univ (touched T); simp at this; omega
  have htouch := touched_card T
  have h4u : 3 * n < 4 * V.card := by omega
  have hre : squaredError (rankVector r) (rankVector (reflectRank r T)) =
      ∑ x : Fin n, (((x : ℕ) : ℝ) - ((reflectFun V x : Fin n) : ℕ)) ^ 2 := by
    unfold squaredError rankVector
    exact Fintype.sum_equiv r _ _ (fun i => by rw [reflectRank_apply])
  rw [hre]
  rcases reflect_sum_lower V with hl | hl
  · refine lt_of_lt_of_le ?_ hl
    have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
    have huR : 3 * (n : ℝ) < 4 * V.card := by exact_mod_cast h4u
    have hcR : (V.card : ℝ) ≤ 4 * (((V.card + 3) / 4 : ℕ) : ℝ) := by
      have : V.card ≤ 4 * ((V.card + 3) / 4) := by omega
      exact_mod_cast this
    have h1 : (0 : ℝ) ≤ (V.card : ℝ) / 2 - 1 := by linarith
    have h2 : (3 * (n : ℝ) / 8 - 1) ≤ (V.card : ℝ) / 2 - 1 := by linarith
    have h3 : (3 * (n : ℝ) / 8 - 1) ^ 2 ≤ ((V.card : ℝ) / 2 - 1) ^ 2 := by
      apply pow_le_pow_left₀ (by linarith) h2
    have h4 : (3 * (n : ℝ) / 16) ≤ (((V.card + 3) / 4 : ℕ) : ℝ) := by linarith
    have h5 : (3 * (n : ℝ) / 16) * (3 * (n : ℝ) / 8 - 1) ^ 2 ≤
        (((V.card + 3) / 4 : ℕ) : ℝ) * ((V.card : ℝ) / 2 - 1) ^ 2 :=
      mul_le_mul h4 h3 (sq_nonneg _) (by positivity)
    nlinarith
  · omega

theorem partI_pointwise (A : QueryPolicy n) (B : ℕ) (ε : ℝ) (hn : 16 ≤ n) (hε : ε ≤ 1 / 1024)
    (hB : HardBudget 0 0 B A) (h8 : 8 * B < n) (ω : PrivateTape) :
    2 * ((Finset.univ : Finset (Rank n)).filter fun r => ω ∈ Ssucc A ε r).card ≤ n.factorial := by
  set Sω := (Finset.univ : Finset (Rank n)).filter fun r => ω ∈ Ssucc A ε r
  have hlegal : ∀ r : Rank n, LegalWorld 0 (W r) := fun r => by simp [LegalWorld, W]
  let Φ : Rank n → Rank n := fun r =>
    if h : ∃ o, Returns A (W r) 0 ω o then reflectRank r (Classical.choose h).state.ledger else r
  have hΦ : ∀ r o, Returns A (W r) 0 ω o → Φ r = reflectRank r o.state.ledger := by
    intro r o hR
    have h : ∃ o, Returns A (W r) 0 ω o := ⟨o, hR⟩
    simp only [Φ, dif_pos h]
    rw [returns_unique A (W r) 0 ω _ o (Classical.choose_spec h) hR]
  have hbud : ∀ r o, Returns A (W r) 0 ω o → (acquired o.state.ledger).card ≤ B := by
    intro r o hR
    obtain ⟨t, ht⟩ := hR
    have := hB (W r) (hlegal r) ω t
    rw [ht] at this; exact this
  have hnpos : 0 < n := by omega
  have hmaps : ∀ r ∈ Sω, Φ r ∈ Sωᶜ := by
    intro r hr
    obtain ⟨o, hR, hl⟩ := (Finset.mem_filter.1 hr).2
    rw [hΦ r o hR, Finset.mem_compl]
    intro hr'
    obtain ⟨o', hR', hl'⟩ := (Finset.mem_filter.1 hr').2
    have hR2 := agree_returns A r (reflectRank r o.state.ledger) ω o hR
      (fun e he => truthful_reflect r _ e he)
    have := returns_unique A _ 0 ω o o' hR2 hR'
    subst this
    rw [loss_le_iff _ _ _ hnpos] at hl hl'
    have hfar := reflect_far r o.state.ledger B hn (hbud r o hR) h8
    have htri := sqErr_triangle (rankVector r) o.estimate (rankVector (reflectRank r o.state.ledger))
    have hs := sqErr_symm (rankVector r) o.estimate
    have hs2 := sqErr_symm (rankVector r) (rankVector (reflectRank r o.state.ledger))
    have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
    have hεn := mul_le_mul_of_nonneg_right hε hn3.le
    linarith
  have hinj : Set.InjOn Φ Sω := by
    intro r hr r' hr' h
    obtain ⟨o, hR, -⟩ := (Finset.mem_filter.1 hr).2
    obtain ⟨o', hR', -⟩ := (Finset.mem_filter.1 hr').2
    rw [hΦ r o hR, hΦ r' o' hR'] at h
    -- both reflections return the common outputs
    have hR2 := agree_returns A r (reflectRank r o.state.ledger) ω o hR
      (fun e he => truthful_reflect r _ e he)
    have hR2' := agree_returns A r' (reflectRank r' o'.state.ledger) ω o' hR'
      (fun e he => truthful_reflect r' _ e he)
    rw [h] at hR2
    have := returns_unique A _ 0 ω o o' hR2 hR2'
    subst this
    rw [← reflectRank_invol r o.state.ledger, h, reflectRank_invol]
  have hle := Finset.card_le_card_of_injOn Φ hmaps hinj
  have hsum := Finset.card_add_card_compl Sω
  rw [Fintype.card_perm, Fintype.card_fin] at hsum
  omega

theorem partII_pointwise (A : QueryPolicy n) (B : ℕ) (ε : ℝ) (hn : 16 ≤ n)
    (hB : HardBudget 0 0 B A) (ω : PrivateTape) :
    ((Finset.univ : Finset (Rank n)).filter fun r => ω ∈ Ssucc A ε r).card ≤
      (2 ^ n * (n + ⌊Real.sqrt (n * (ε * (n : ℝ) ^ 3))⌋₊).choose
        ⌊Real.sqrt (n * (ε * (n : ℝ) ^ 3))⌋₊) * 3 ^ B := by
  set Sω := (Finset.univ : Finset (Rank n)).filter fun r => ω ∈ Ssucc A ε r
  have hlegal : ∀ r : Rank n, LegalWorld 0 (W r) := fun r => by simp [LegalWorld, W]
  have hnpos : 0 < n := by omega
  let code : Rank n → (Fin B → Option Bool) := fun r =>
    if h : ∃ o, Returns A (W r) 0 ω o then fun i => (nb (Classical.choose h).state.history).2[i.val]?
    else fun _ => none
  have hcode : ∀ r o, Returns A (W r) 0 ω o → code r = fun i => (nb o.state.history).2[i.val]? := by
    intro r o hR
    have h : ∃ o, Returns A (W r) 0 ω o := ⟨o, hR⟩
    simp only [code, dif_pos h]
    rw [returns_unique A (W r) 0 ω _ o (Classical.choose_spec h) hR]
  have hbud : ∀ r o, Returns A (W r) 0 ω o → (nb o.state.history).2.length ≤ B := by
    intro r o hR
    refine le_trans (bits_length A r ω o hR) ?_
    obtain ⟨t, ht⟩ := hR
    have := hB (W r) (hlegal r) ω t
    rw [ht] at this; exact this
  have h1 := Finset.card_le_mul_card_image (f := code) Sω
    (2 ^ n * (n + ⌊Real.sqrt (n * (ε * (n : ℝ) ^ 3))⌋₊).choose ⌊Real.sqrt (n * (ε * (n : ℝ) ^ 3))⌋₊) (by
      intro c hc
      obtain ⟨r0, hr0, hc0⟩ := Finset.mem_image.1 hc
      obtain ⟨o0, hR0, -⟩ := (Finset.mem_filter.1 hr0).2
      refine le_trans (Finset.card_le_card ?_) (near_count o0.estimate (ε * (n : ℝ) ^ 3))
      intro r hr
      rw [Finset.mem_filter] at hr ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      obtain ⟨o, hR, hl⟩ := (Finset.mem_filter.1 hr.1).2
      have heq : (nb o.state.history).2 = (nb o0.state.history).2 := by
        have hc1 := hcode r o hR
        have hc2 := hcode r0 o0 hR0
        rw [hr.2, ← hc0, hc2] at hc1
        apply List.ext_getElem?
        intro i
        by_cases hi : i < B
        · exact (congrFun hc1 ⟨i, hi⟩).symm
        · push Not at hi
          rw [List.getElem?_eq_none (le_trans (hbud r o hR) hi),
            List.getElem?_eq_none (le_trans (hbud r0 o0 hR0) hi)]
      have := same_bits A r r0 ω o o0 hR hR0 heq
      subst this
      exact (loss_le_iff _ _ _ hnpos).1 hl)
  have h2 : (Sω.image code).card ≤ 3 ^ B := by
    refine le_trans (Finset.card_le_univ _) ?_
    simp
  calc Sω.card ≤ _ := h1
    _ ≤ _ := Nat.mul_le_mul_left _ h2

end RQCLemma49Main

open RankingQueryCost.Joint RQCLemma49 RQCCount RQCRefl RQCLemma49Main MeasureTheory

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ (n B : ℕ) (ε : ℝ),
      Admissible n 0 → 0 ≤ ε → ε ≤ precisionCeiling →
      ∀ A : QueryPolicy n, HardBudget 0 0 B A → Actual 0 0 ε A →
        c * resolutionCost n ε ≤ (B : ℝ) := by
  classical
  refine ⟨1 / 96, by norm_num, ?_⟩
  intro n B ε hadm hε0 hεc A hB hA
  have hn : 16 ≤ n := hadm.1
  have hε : ε ≤ 1 / 1024 := by simpa [precisionCeiling] using hεc
  have hnpos : 0 < n := by omega
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hlegal : ∀ r : Rank n, LegalWorld 0 (W r) := fun r => by simp [LegalWorld, W]
  have hmeas : ∀ r, MeasurableSet (Ssucc A ε r) := by
    intro r
    apply meas_returns A (W r) 0 (fun o => loss o.estimate r ≤ ε)
    intro S
    have hc : Continuous fun q : Fin n → ℝ => loss q r := by
      unfold loss squaredError; fun_prop
    exact measurableSet_le (hc.measurable.comp (A.estimate_measurable S.history)) measurable_const
  have hS : ∀ r, (3 / 4 : ℝ) ≤ privateLaw.real (Ssucc A ε r) := by
    intro r
    have := hA.2 (W r) (hlegal r)
    have h2 := ENNReal.toReal_mono (measure_ne_top privateLaw _) this
    rw [measureReal_def]; norm_num at h2 ⊢; exact h2
  have hfact : (Fintype.card (Rank n) : ℝ) = (n.factorial : ℝ) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have hsumlow : (3 / 4 : ℝ) * n.factorial ≤ ∑ r, privateLaw.real (Ssucc A ε r) := by
    calc (3 / 4 : ℝ) * n.factorial = ∑ _r : Rank n, (3 / 4 : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hfact]; ring
      _ ≤ _ := Finset.sum_le_sum fun r _ => hS r
  have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  -- Part I
  have h8 : n ≤ 8 * B := by
    by_contra hc
    push Not at hc
    have := average_bound (Ssucc A ε) hmeas ((n.factorial : ℝ) / 2) (by
      intro ω
      have := partI_pointwise A B ε hn hε hB hc ω
      have : (2 * ((Finset.univ : Finset (Rank n)).filter fun r => ω ∈ Ssucc A ε r).card : ℝ) ≤
          n.factorial := by exact_mod_cast this
      linarith)
    linarith
  -- Part II
  set L := ⌊Real.sqrt (n * (ε * (n : ℝ) ^ 3))⌋₊ with hL
  have hII := average_bound (Ssucc A ε) hmeas
    (((2 ^ n * (n + L).choose L * 3 ^ B : ℕ)) : ℝ) (by
      intro ω
      have h := (show _ ≤ 2 ^ n * (n + L).choose L * 3 ^ B from partII_pointwise A B ε hn hB ω)
      exact_mod_cast h)
  have hmain : (3 / 4 : ℝ) * n.factorial ≤ 2 ^ n * ((n + L).choose L : ℝ) * 3 ^ B := by
    have := le_trans hsumlow hII
    push_cast at this; linarith
  have hchoose : ((n + L).choose L : ℝ) ≤ ((n + L : ℕ) : ℝ) ^ n / n.factorial := by
    rw [show (n + L).choose L = (n + L).choose n from by
      rw [Nat.choose_symm_add]]
    exact Nat.choose_le_pow_div n (n + L)
  have hstir : (n : ℝ) ^ n ≤ Real.exp n * n.factorial := by
    have := Real.pow_div_factorial_le_exp (x := (n : ℝ)) (by positivity) n
    rwa [div_le_iff₀ hfpos] at this
  -- combine: (3/4) n^(2n) ≤ e^(2n) 2^n 3^B (n+L)^n
  have hcomb : (3 / 4 : ℝ) * ((n : ℝ) ^ n) ^ 2 ≤
      Real.exp n ^ 2 * (2 ^ n * 3 ^ B * ((n + L : ℕ) : ℝ) ^ n) := by
    have h1 : (3 / 4 : ℝ) * (n.factorial : ℝ) ^ 2 ≤ 2 ^ n * 3 ^ B * ((n + L : ℕ) : ℝ) ^ n := by
      have h2 : 2 ^ n * ((n + L).choose L : ℝ) * 3 ^ B ≤
          2 ^ n * (((n + L : ℕ) : ℝ) ^ n / n.factorial) * 3 ^ B := by gcongr
      have h3 : 2 ^ n * (((n + L : ℕ) : ℝ) ^ n / n.factorial) * 3 ^ B * n.factorial =
          2 ^ n * 3 ^ B * ((n + L : ℕ) : ℝ) ^ n := by field_simp
      nlinarith
    have h4 : ((n : ℝ) ^ n) ^ 2 ≤ (Real.exp n * n.factorial) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hstir 2
    nlinarith [Real.exp_pos (n : ℝ)]
  -- the resolution argument m
  set m : ℝ := if ε = 0 then (n : ℝ) else min (n : ℝ) (1 / Real.sqrt ε) with hm
  have hmpos : 0 < m := by
    rw [hm]; split_ifs with h0
    · positivity
    · have : 0 < ε := lt_of_le_of_ne hε0 (Ne.symm h0)
      exact lt_min (by positivity) (by positivity)
  have hLle : (L : ℝ) ≤ Real.sqrt ε * (n : ℝ) ^ 2 := by
    have h1 : (L : ℝ) ≤ Real.sqrt (n * (ε * (n : ℝ) ^ 3)) := Nat.floor_le (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (n * (ε * (n : ℝ) ^ 3)) = Real.sqrt ε * (n : ℝ) ^ 2 := by
      rw [show (n : ℝ) * (ε * (n : ℝ) ^ 3) = ε * ((n : ℝ) ^ 2) ^ 2 by ring,
        Real.sqrt_mul hε0, Real.sqrt_sq (by positivity)]
    linarith
  have hnLm : ((n + L : ℕ) : ℝ) * m ≤ 2 * (n : ℝ) ^ 2 := by
    push_cast
    rw [hm]; split_ifs with h0
    · subst h0
      have : (L : ℝ) = 0 := by
        apply le_antisymm _ (Nat.cast_nonneg _)
        simpa using hLle
      rw [this]; nlinarith
    · have hεpos : 0 < ε := lt_of_le_of_ne hε0 (Ne.symm h0)
      have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.2 hεpos
      have hm1 : min (n : ℝ) (1 / Real.sqrt ε) ≤ n := min_le_left _ _
      have hm2 : min (n : ℝ) (1 / Real.sqrt ε) ≤ 1 / Real.sqrt ε := min_le_right _ _
      have hm0 : 0 ≤ min (n : ℝ) (1 / Real.sqrt ε) := le_min (by positivity) (by positivity)
      have h5 : Real.sqrt ε * (1 / Real.sqrt ε) = 1 := by field_simp
      have h6 : (L : ℝ) * min (n : ℝ) (1 / Real.sqrt ε) ≤ (n : ℝ) ^ 2 := by
        calc (L : ℝ) * min (n : ℝ) (1 / Real.sqrt ε) ≤ (Real.sqrt ε * (n : ℝ) ^ 2) * (1 / Real.sqrt ε) :=
              mul_le_mul hLle hm2 hm0 (by positivity)
          _ = (n : ℝ) ^ 2 := by rw [mul_comm (Real.sqrt ε), mul_assoc, h5, mul_one]
      nlinarith
  -- logarithms
  generalize hNL : ((n + L : ℕ) : ℝ) = NL at hcomb hnLm
  have hnLpos : (0 : ℝ) < NL := by
    rw [← hNL]
    have : 0 < n + L := by omega
    exact_mod_cast this
  have hlogcomb : Real.log (3 / 4) + 2 * n * Real.log n ≤
      2 * n + n * Real.log 2 + B * Real.log 3 + n * Real.log NL := by
    have hl := Real.log_le_log (by positivity) hcomb
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_exp] at hl
    rw [Real.log_pow] at hl
    push_cast at hl
    linarith
  have hlogm : Real.log NL + Real.log m ≤ Real.log 2 + 2 * Real.log n := by
    have := Real.log_le_log (by positivity) hnLm
    rw [Real.log_mul hnLpos.ne' hmpos.ne', Real.log_mul (by norm_num) (by positivity),
      Real.log_pow] at this
    push_cast at this; linarith
  have hlog34 : -1 ≤ Real.log (3 / 4) := by
    have := Real.add_one_le_exp (-1 : ℝ)
    have h2 : Real.exp (-1) ≤ 3 / 4 := by
      have := Real.exp_one_gt_d9
      rw [Real.exp_neg]
      rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith
    have := Real.log_le_log (Real.exp_pos _) h2
    rwa [Real.log_exp] at this
  have hlog2 : Real.log 2 < 0.7 := by have := Real.log_two_lt_d9; linarith
  have hlog2' : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have hnlogn : (n : ℝ) * Real.log m - 4 * n ≤ B * Real.log 3 := by
    have : (n : ℝ) * Real.log NL ≤ n * (Real.log 2 + 2 * Real.log n - Real.log m) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  -- resolution cost
  have hres : resolutionCost n ε = n * Real.log m / Real.log 2 := by
    unfold resolutionCost
    rw [hm]
    split_ifs with h0
    · rw [Real.logb]; ring
    · rw [Real.logb]; ring
  rw [hres]
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have h8R : (n : ℝ) ≤ 8 * B := by exact_mod_cast h8
  rw [show (1 / 96 : ℝ) * (n * Real.log m / Real.log 2) = n * Real.log m / (96 * Real.log 2) by ring,
    div_le_iff₀ (by linarith)]
  have hB2 : (B : ℝ) * (96 * 0.69) ≤ B * (96 * Real.log 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hB0
  by_cases hcase : Real.log m ≤ 8
  · have : (n : ℝ) * Real.log m ≤ n * 8 := mul_le_mul_of_nonneg_left hcase (by positivity)
    linarith
  · push Not at hcase
    have ha : (n : ℝ) * 8 ≤ n * Real.log m := mul_le_mul_of_nonneg_left hcase.le (by positivity)
    have h2 : (B : ℝ) * Real.log 3 ≤ B * 2 := mul_le_mul_of_nonneg_left hlog3 hB0
    linarith
