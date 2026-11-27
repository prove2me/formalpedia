-- Prove2me | solution 1 for RankingQueryCost.Joint.lemma_4_11
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:39:09.076741+00:00
-- url     : https://prove2.me/submissions/7f504b21-85e6-4a58-97ba-a9dc631b9e4b

import Definitions.Def_RankingQueryCost_Joint_Interaction

set_option autoImplicit false

namespace RQCLemma411
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


/-- Move the set `M` to the top ranks, keeping the order of the complement. -/
def moveFun (M : Finset (Fin n)) (i : Fin n) : ℕ :=
  if i ∈ M then n - M.card + (M.filter fun j => j < i).card
  else (Mᶜ.filter fun j => j < i).card

theorem moveFun_lt (M : Finset (Fin n)) (i : Fin n) : moveFun M i < n := by
  unfold moveFun
  split_ifs with hi
  · have : (M.filter fun j => j < i).card < M.card :=
      Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h =>
        lt_irrefl i (Finset.mem_filter.1 (h hi)).2⟩
    have hM : M.card ≤ n := by simpa using Finset.card_le_univ M
    omega
  · have : (Mᶜ.filter fun j => j < i).card < Mᶜ.card :=
      Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h =>
        lt_irrefl i (Finset.mem_filter.1 (h (Finset.mem_compl.2 hi))).2⟩
    have : Mᶜ.card ≤ n := by simpa using Finset.card_le_univ Mᶜ
    omega

theorem moveFun_compl_lt (M : Finset (Fin n)) (i : Fin n) (hi : i ∉ M) : moveFun M i < n - M.card := by
  unfold moveFun
  rw [if_neg hi]
  have : (Mᶜ.filter fun j => j < i).card < Mᶜ.card :=
    Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h =>
        lt_irrefl i (Finset.mem_filter.1 (h (Finset.mem_compl.2 hi))).2⟩
  rw [Finset.card_compl, Fintype.card_fin] at this
  exact this

theorem moveFun_mono_in (M : Finset (Fin n)) (i j : Fin n) (hi : i ∈ M) (hj : j ∈ M) (hij : i < j) :
    moveFun M i < moveFun M j := by
  unfold moveFun
  rw [if_pos hi, if_pos hj]
  have : (M.filter fun k => k < i).card < (M.filter fun k => k < j).card := by
    apply Finset.card_lt_card
    refine ⟨fun k hk => ?_, fun h => ?_⟩
    · simp only [Finset.mem_filter] at hk ⊢; exact ⟨hk.1, lt_trans hk.2 hij⟩
    · have := h (Finset.mem_filter.2 ⟨hi, hij⟩); simp at this
  omega

theorem moveFun_mono_out (M : Finset (Fin n)) (i j : Fin n) (hi : i ∉ M) (hj : j ∉ M) (hij : i < j) :
    moveFun M i < moveFun M j := by
  unfold moveFun
  rw [if_neg hi, if_neg hj]
  apply Finset.card_lt_card
  refine ⟨fun k hk => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter] at hk ⊢; exact ⟨hk.1, lt_trans hk.2 hij⟩
  · have := h (Finset.mem_filter.2 ⟨by simpa using hi, hij⟩); simp at this

theorem moveFun_ge (M : Finset (Fin n)) (i : Fin n) (hi : i ∈ M) : n - M.card ≤ moveFun M i := by
  unfold moveFun; rw [if_pos hi]; omega

theorem moveFun_injective (M : Finset (Fin n)) : Function.Injective (moveFun M) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · by_cases hi : i ∈ M <;> by_cases hj : j ∈ M
    · exact absurd hij (moveFun_mono_in M i j hi hj h).ne
    · have := moveFun_ge M i hi; have := moveFun_compl_lt M j hj; omega
    · have := moveFun_ge M j hj; have := moveFun_compl_lt M i hi; omega
    · exact absurd hij (moveFun_mono_out M i j hi hj h).ne
  · by_cases hi : i ∈ M <;> by_cases hj : j ∈ M
    · exact absurd hij (moveFun_mono_in M j i hj hi h).ne'
    · have := moveFun_ge M i hi; have := moveFun_compl_lt M j hj; omega
    · have := moveFun_ge M j hj; have := moveFun_compl_lt M i hi; omega
    · exact absurd hij (moveFun_mono_out M j i hj hi h).ne'

def moveFin (M : Finset (Fin n)) (i : Fin n) : Fin n := ⟨moveFun M i, moveFun_lt M i⟩

theorem moveFin_injective (M : Finset (Fin n)) : Function.Injective (moveFin M) := by
  intro i j h
  exact moveFun_injective M (congrArg Fin.val h)

noncomputable def movePerm (M : Finset (Fin n)) : Rank n :=
  Equiv.ofBijective (moveFin M) (Finite.injective_iff_bijective.mp (moveFin_injective M))

theorem movePerm_apply (M : Finset (Fin n)) (i : Fin n) : ((movePerm M i : Fin n) : ℕ) = moveFun M i := rfl

/-- Pairs whose orientation changes under `movePerm M` have their lower endpoint in `M`. -/
theorem flip_lower_mem (M : Finset (Fin n)) (e : Pair n)
    (h : truthful (movePerm M) e ≠ truthful (Equiv.refl _) e) : e.1.1 ∈ M := by
  by_contra hM
  apply h
  have he : e.1.1 < e.1.2 := e.2
  have h1 : truthful (Equiv.refl (Fin n)) e = true := by simp [truthful, he]
  rw [h1]
  simp only [truthful, decide_eq_true_eq]
  show moveFin M e.1.1 < moveFin M e.1.2
  show moveFun M e.1.1 < moveFun M e.1.2
  by_cases h2 : e.1.2 ∈ M
  · have := moveFun_ge M e.1.2 h2; have := moveFun_compl_lt M e.1.1 hM; omega
  · exact moveFun_mono_out M _ _ hM h2 he


theorem sqErr_triangle (x y z : Fin n → ℝ) :
    squaredError x z ≤ 2 * squaredError x y + 2 * squaredError y z := by
  unfold squaredError
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (x i + z i - 2 * y i)]


def ExecRel (Inv : InteractionState n → InteractionState n → Prop) :
    Execution n → Execution n → Prop
  | .running S, .running S' => Inv S S'
  | .halted o, .halted o' => Inv o.state o'.state ∧ o.estimate = o'.estimate ∧
      o.emission = o'.emission ∧ o.certificate = o'.certificate
  | .diverged S, .diverged S' => Inv S S'
  | _, _ => False

def cleanWorld (n : ℕ) : ComparisonWorld n := ⟨Equiv.refl _, ∅, fun _ _ _ _ => (false, false)⟩

noncomputable def flipSet (σ : Rank n) (L : Transcript n) : Finset (Pair n) :=
  (acquired L).filter fun e => truthful σ e ≠ truthful (Equiv.refl _) e

def flipWorld (σ : Rank n) : ComparisonWorld n :=
  ⟨σ, ∅, fun _ _ _ e => (decide (truthful σ e ≠ truthful (Equiv.refl _) e), truthful (Equiv.refl _) e)⟩

def FlipInv (σ : Rank n) (S S' : InteractionState n) : Prop :=
  S.ledger = S'.ledger ∧ S.history = S'.history ∧ S'.online = flipSet σ S.ledger

theorem acquired_mono_step (h : ℕ) (W : ComparisonWorld n) (S : InteractionState n) (msg : List ℕ)
    (e : Pair n) : acquired S.ledger ⊆ acquired (readIdentity h W S msg e).2.ledger := by
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

theorem acquired_mono_advance (A : QueryPolicy n) (W : ComparisonWorld n) (h : ℕ) (ω : PrivateTape)
    (X : Execution n) : acquired (executionState X).ledger ⊆
      acquired (executionState (advance A W h ω X)).ledger := by
  cases X with
  | running S =>
    simp only [advance]
    rcases A.request ω S.history with _ | _ | e
    · exact le_refl _
    · exact le_refl _
    · exact acquired_mono_step h W S _ e
  | halted o => exact le_refl _
  | diverged S => exact le_refl _

theorem acquired_mono_prefix (A : QueryPolicy n) (W : ComparisonWorld n) (h : ℕ) (ω : PrivateTape)
    (t k : ℕ) : acquired (executionState (executionPrefix A W h ω t)).ledger ⊆
      acquired (executionState (executionPrefix A W h ω (t + k))).ledger := by
  induction k with
  | zero => exact le_refl _
  | succ k ih =>
    refine le_trans ih ?_
    rw [← Nat.add_assoc]
    exact acquired_mono_advance A W h ω _

theorem flip_step (σ : Rank n) (s : ℕ) (S S' : InteractionState n) (msg : List ℕ) (e : Pair n)
    (hI : FlipInv σ S S')
    (hc : (flipSet σ (readIdentity s (cleanWorld n) S msg e).2.ledger).card ≤ s) :
    FlipInv σ (readIdentity s (cleanWorld n) S msg e).2 (readIdentity s (flipWorld σ) S' msg e).2 := by
  obtain ⟨L, H, O⟩ := S
  obtain ⟨L', H', O'⟩ := S'
  obtain ⟨hL, hH, hO⟩ := hI
  simp only at hL hH hO
  subst hL hH hO
  unfold readIdentity at hc ⊢
  cases hle : L e with
  | some b =>
    simp only [hle]
    exact ⟨rfl, rfl, rfl⟩
  | none =>
    simp only [hle] at hc ⊢
    have heo : e ∉ flipSet σ L := by
      intro he; have := (Finset.mem_filter.1 (Finset.mem_filter.1 he).1).2; simp [hle] at this
    by_cases hflip : truthful σ e ≠ truthful (Equiv.refl _) e
    · -- the new flip set is the old one with `e` inserted
      have hnew : flipSet σ (Function.update L e (some (truthful (Equiv.refl _) e))) =
          insert e (flipSet σ L) := by
        ext f
        simp only [flipSet, acquired, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        by_cases hfe : f = e
        · subst hfe; simp [hflip]
        · rw [Function.update_of_ne hfe]; simp [hfe]
      have hc' : (flipSet σ L).card < s := by
        simp only [cleanWorld, Finset.notMem_empty, false_or, Bool.false_eq_true, false_and,
          and_false, if_false] at hc
        rw [hnew, Finset.card_insert_of_notMem heo] at hc
        omega
      have hd : decide (truthful σ e ≠ truthful (Equiv.refl _) e) = true := decide_eq_true hflip
      simp only [cleanWorld, flipWorld, Finset.notMem_empty, false_or, Bool.false_eq_true,
        false_and, and_false, if_false, not_false_eq_true, true_and, hd, hc', and_true, if_true]
      exact ⟨rfl, rfl, hnew.symm⟩
    · push Not at hflip
      have hnew : flipSet σ (Function.update L e (some (truthful (Equiv.refl _) e))) =
          flipSet σ L := by
        ext f
        simp only [flipSet, acquired, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hfe : f = e
        · subst hfe; simp [hflip, hle]
        · rw [Function.update_of_ne hfe]
      simp only [cleanWorld, flipWorld, Finset.notMem_empty, false_or, Bool.false_eq_true,
        false_and, and_false, if_false, not_false_eq_true, true_and, hflip, ne_eq,
        not_true_eq_false, decide_false]
      exact ⟨rfl, rfl, hnew.symm⟩

theorem flip_prefix (A : QueryPolicy n) (σ : Rank n) (s : ℕ) (ω : PrivateTape) :
    ∀ t, (flipSet σ (executionState (executionPrefix A (cleanWorld n) s ω t)).ledger).card ≤ s →
      ExecRel (FlipInv σ) (executionPrefix A (cleanWorld n) s ω t)
        (executionPrefix A (flipWorld σ) s ω t) := by
  intro t
  induction t with
  | zero => intro _; exact ⟨rfl, rfl, by simp [flipSet, acquired, initialState, emptyTranscript]⟩
  | succ t ih =>
    intro hc
    have hmono := acquired_mono_prefix A (cleanWorld n) s ω t 1
    have hc' : (flipSet σ (executionState (executionPrefix A (cleanWorld n) s ω t)).ledger).card ≤ s := by
      refine le_trans (Finset.card_le_card ?_) hc
      intro f hf
      simp only [flipSet, Finset.mem_filter] at hf ⊢
      exact ⟨hmono hf.1, hf.2⟩
    have ih' := ih hc'
    revert hc
    simp only [executionPrefix]
    generalize executionPrefix A (cleanWorld n) s ω t = X at ih'
    generalize executionPrefix A (flipWorld σ) s ω t = X' at ih'
    intro hc
    cases X <;> cases X' <;> simp only [ExecRel] at ih'
    · rename_i S S'
      have hH := ih'.2.1
      simp only [advance] at hc ⊢
      rw [hH] at hc ⊢
      revert hc
      rcases A.request ω S'.history with _ | _ | e
      · intro _; exact ih'
      · intro _; exact ⟨ih', rfl, rfl, rfl⟩
      · intro hc; rw [← hH] at hc ⊢; exact flip_step σ s S S' _ e ih' hc
    · exact ih'
    · exact ih'

theorem flip_returns (A : QueryPolicy n) (σ : Rank n) (s : ℕ) (ω : PrivateTape)
    (o : InteractionResult n) (hR : Returns A (cleanWorld n) s ω o)
    (hc : (flipSet σ o.state.ledger).card ≤ s) :
    ∃ o', Returns A (flipWorld σ) s ω o' ∧ o'.estimate = o.estimate := by
  obtain ⟨t, ht⟩ := hR
  have := flip_prefix A σ s ω t (by rw [ht]; exact hc)
  rw [ht] at this
  generalize hX : executionPrefix A (flipWorld σ) s ω t = X at this
  cases X <;> simp only [ExecRel] at this
  rename_i o'
  exact ⟨o', ⟨t, hX⟩, this.2.1.symm⟩

theorem two_close_false (n : ℕ) (M : Finset (Fin n)) (ε : ℝ) (hn : 16 ≤ n) (h4 : 4 ∣ n)
    (hε : 0 < ε) (hM : ∀ i ∈ M, i.val < n / 4) (hm1 : 32 * (n : ℝ) * ε ≤ M.card)
    (h8m : 8 * M.card ≤ n) (q : Fin n → ℝ)
    (l1 : loss q (Equiv.refl (Fin n)) ≤ ε) (l2 : loss q (movePerm M) ≤ ε) : False := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  unfold loss at l1 l2
  rw [div_le_iff₀ hn3] at l1 l2
  have hsymm : squaredError (rankVector (Equiv.refl (Fin n))) q =
      squaredError q (rankVector (Equiv.refl (Fin n))) := by
    unfold squaredError; congr 1; ext i; ring
  have htri := sqErr_triangle (rankVector (Equiv.refl (Fin n))) q (rankVector (movePerm M))
  rw [hsymm] at htri
  have hlow : (M.card : ℝ) * ((n : ℝ) ^ 2 / 4) ≤
      squaredError (rankVector (Equiv.refl (Fin n))) (rankVector (movePerm M)) := by
    unfold squaredError
    have hsub : ∑ i ∈ M, (rankVector (Equiv.refl (Fin n)) i - rankVector (movePerm M) i) ^ 2 ≤
        ∑ i, (rankVector (Equiv.refl (Fin n)) i - rankVector (movePerm M) i) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    refine le_trans ?_ hsub
    have := Finset.card_nsmul_le_sum M
      (fun i => (rankVector (Equiv.refl (Fin n)) i - rankVector (movePerm M) i) ^ 2)
      ((n : ℝ) ^ 2 / 4) (by
        intro i hi
        have hi4 : i.val < n / 4 := hM i hi
        have hσ := moveFun_ge M i hi
        have hi4R : ((i.val : ℕ) : ℝ) + 1 ≤ n / 4 := by
          obtain ⟨k, hk⟩ := h4
          subst hk
          have : i.val + 1 ≤ k := by omega
          have : ((i.val : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast this
          push_cast; linarith
        have hσR : (n : ℝ) - M.card ≤ (moveFun M i : ℝ) := by
          have : ((n - M.card : ℕ) : ℝ) ≤ (moveFun M i : ℝ) := by exact_mod_cast hσ
          rw [Nat.cast_sub (by omega)] at this; exact this
        have h8mR : (8 * M.card : ℝ) ≤ n := by exact_mod_cast h8m
        simp only [rankVector, Equiv.refl_apply]
        rw [movePerm_apply]
        nlinarith)
    simpa [smul_eq_mul] using this
  have : (M.card : ℝ) * ((n : ℝ) ^ 2 / 4) ≥ 8 * ε * (n : ℝ) ^ 3 := by
    have : (32 * (n : ℝ) * ε) * ((n : ℝ) ^ 2 / 4) ≤ M.card * ((n : ℝ) ^ 2 / 4) :=
      mul_le_mul_of_nonneg_right hm1 (by positivity)
    nlinarith
  nlinarith

/-- Cyclic windows of length `m` inside the first `f` labels. -/
def cyc (n f m : ℕ) (hf : f ≤ n) (k : Fin f) : Finset (Fin n) :=
  (Finset.univ.filter fun d : Fin f => d.val < m).image fun d => Fin.castLE hf (k + d)

theorem cyc_lt (n f m : ℕ) (hf : f ≤ n) (k : Fin f) : ∀ i ∈ cyc n f m hf k, i.val < f := by
  intro i hi
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hi
  simp [Fin.castLE]

theorem cyc_card (n f m : ℕ) (hf : f ≤ n) (hmf : m ≤ f) (k : Fin f) [NeZero f] :
    (cyc n f m hf k).card = m := by
  unfold cyc
  rw [Finset.card_image_of_injective]
  · rw [Fin.card_filter_val_lt]; omega
  · intro d d' h
    have := Fin.castLE_injective hf h
    exact add_left_cancel this

theorem cyc_count (n f m : ℕ) (hf : f ≤ n) [NeZero f] (i : Fin n) :
    (Finset.univ.filter fun k : Fin f => i ∈ cyc n f m hf k).card ≤ m := by
  by_cases hi : i.val < f
  · set i' : Fin f := ⟨i.val, hi⟩
    have : (Finset.univ.filter fun k : Fin f => i ∈ cyc n f m hf k).card ≤
        (Finset.univ.filter fun d : Fin f => d.val < m).card := by
      apply Finset.card_le_card_of_injOn (fun k => i' - k)
      · intro k hk
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hk ⊢
        obtain ⟨d, hd, hdi⟩ := Finset.mem_image.1 hk
        have hkd : k + d = i' := by
          apply Fin.ext
          have := congrArg Fin.val hdi
          simpa [Fin.castLE, i'] using this
        have : i' - k = d := by rw [← hkd]; abel
        rw [Finset.mem_filter] at hd
        simpa [this] using hd.2
      · intro k _ k' _ h
        simpa using h
    rw [Fin.card_filter_val_lt] at this
    omega
  · have : (Finset.univ.filter fun k : Fin f => i ∈ cyc n f m hf k) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro k _ hk
      exact hi (cyc_lt n f m hf k i hk)
    rw [this]; simp

end RQCLemma411

open RankingQueryCost.Joint RQCLemma411 MeasureTheory

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ (n s B : ℕ) (ε : ℝ),
      Admissible n s → 1 ≤ s → 0 < ε → ε ≤ precisionCeiling →
      ∀ A : QueryPolicy n, HardBudget 0 s B A → Actual 0 s ε A →
        c * min ((n : ℝ) * s) ((s : ℝ) / ε) ≤ (B : ℝ) := by
  refine ⟨1 / 2048, by norm_num, ?_⟩
  intro n s B ε hadm hs1 hε hεc A hB hA
  by_contra hlt
  push Not at hlt
  have hn16 := hadm.1
  have h4 := hadm.2.1
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hnpos : (0 : ℝ) < n := by linarith
  have hεc' : ε ≤ 1 / 1024 := by simpa [precisionCeiling] using hεc
  set f := n / 4 with hfdef
  have hf4 : 4 ≤ f := by omega
  have hfn : f ≤ n := Nat.div_le_self _ _
  have : NeZero f := ⟨by omega⟩
  set m := ⌈32 * (n : ℝ) * ε⌉₊ with hm
  have hm_lt : (m : ℝ) < 32 * n * ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm_ge : 32 * (n : ℝ) * ε ≤ m := Nat.le_ceil _
  have h8m : 8 * m ≤ n := by
    have : (8 * m : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hmf : m ≤ f := by omega
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hBm : 32 * B * m < n * s := by
    have hB1 : (B : ℝ) * (2048 * ε) < s := by
      have h := lt_of_lt_of_le hlt (mul_le_mul_of_nonneg_left (min_le_right ((n : ℝ) * s) ((s : ℝ) / ε))
        (by norm_num : (0 : ℝ) ≤ 1 / 2048))
      have : (1 / 2048 : ℝ) * ((s : ℝ) / ε) * (2048 * ε) = s := by field_simp
      nlinarith
    have hB2 : (B : ℝ) * 2048 < n * s := by
      have h := lt_of_lt_of_le hlt (mul_le_mul_of_nonneg_left (min_le_left ((n : ℝ) * s) ((s : ℝ) / ε))
        (by norm_num : (0 : ℝ) ≤ 1 / 2048))
      linarith
    have hB0 : (0 : ℝ) ≤ B := by positivity
    have : (32 * B * m : ℝ) < n * s := by
      have : (B : ℝ) * m ≤ B * (32 * n * ε + 1) := mul_le_mul_of_nonneg_left hm_lt.le hB0
      nlinarith
    exact_mod_cast this
  set M : Fin f → Finset (Fin n) := cyc n f m hfn with hMdef
  have hMcard : ∀ k, (M k).card = m := fun k => cyc_card n f m hfn hmf k
  have hMlt : ∀ k, ∀ i ∈ M k, i.val < n / 4 := fun k => cyc_lt n f m hfn k
  set μ := privateLaw with hμ
  set S0 : Set PrivateTape :=
    {ω | ∃ o, Returns A (cleanWorld n) s ω o ∧ loss o.estimate (Equiv.refl (Fin n)) ≤ ε} with hS0def
  set Ab : Fin f → Set PrivateTape := fun k =>
    {ω | ∃ o, Returns A (cleanWorld n) s ω o ∧ s < (flipSet (movePerm (M k)) o.state.ledger).card}
    with hAbdef
  have hlossmeas : ∀ (H : PublicHistory n) (r : Rank n),
      MeasurableSet {ω | loss (A.estimate ω H) r ≤ ε} := by
    intro H r
    have hc : Continuous fun q : Fin n → ℝ => loss q r := by
      unfold loss squaredError; fun_prop
    exact measurableSet_le (hc.measurable.comp (A.estimate_measurable H)) measurable_const
  have hS0meas : MeasurableSet S0 :=
    meas_returns A (cleanWorld n) s (fun o => loss o.estimate (Equiv.refl (Fin n)) ≤ ε)
      (fun S => hlossmeas S.history _)
  have hAbmeas : ∀ k, MeasurableSet (Ab k) := fun k =>
    meas_returns A (cleanWorld n) s (fun o => s < (flipSet (movePerm (M k)) o.state.ledger).card)
      (fun S => MeasurableSet.const (s < (flipSet (movePerm (M k)) S.ledger).card))
  have hlegal0 : LegalWorld 0 (cleanWorld n) := by simp [LegalWorld, cleanWorld]
  have hS0 : (3 / 4 : ℝ) ≤ μ.real S0 := by
    have := hA.2 (cleanWorld n) hlegal0
    have h2 := ENNReal.toReal_mono (measure_ne_top μ _) this
    rw [measureReal_def]; norm_num at h2 ⊢; exact h2
  -- Claim 1
  have claim1 : ∀ k, (1 / 2 : ℝ) ≤ μ.real (Ab k) := by
    intro k
    set σ := movePerm (M k)
    have hlegalM : LegalWorld 0 (flipWorld σ) := by simp [LegalWorld, flipWorld]
    set SM : Set PrivateTape :=
      {ω | ∃ o, Returns A (flipWorld σ) s ω o ∧ loss o.estimate (flipWorld σ).rank ≤ ε}
    have hSM : (3 / 4 : ℝ) ≤ μ.real SM := by
      have := hA.2 (flipWorld σ) hlegalM
      have h2 := ENNReal.toReal_mono (measure_ne_top μ _) this
      rw [measureReal_def]; norm_num at h2 ⊢; exact h2
    have hsub : SM ⊆ S0ᶜ ∪ Ab k := by
      rintro ω ⟨o', hR', hl'⟩
      by_cases h0 : ω ∈ S0
      · obtain ⟨o, hR, hl⟩ := h0
        by_cases hc : s < (flipSet σ o.state.ledger).card
        · exact Or.inr ⟨o, hR, hc⟩
        · push Not at hc
          obtain ⟨o'', hR'', hest⟩ := flip_returns A σ s ω o hR hc
          have := returns_unique A (flipWorld σ) s ω o' o'' hR' hR''
          subst this
          exfalso
          refine two_close_false n (M k) ε hn16 h4 hε (hMlt k) (by rw [hMcard]; exact hm_ge)
            (by rw [hMcard]; exact h8m) o.estimate hl ?_
          rw [← hest]; exact hl'
      · exact Or.inl h0
    have h1 : μ.real SM ≤ μ.real S0ᶜ + μ.real (Ab k) :=
      le_trans (measureReal_mono hsub) (measureReal_union_le _ _)
    rw [probReal_compl_eq_one_sub hS0meas] at h1
    linarith
  -- Claim 2: averaging
  classical
  have hcount : ∀ ω, (8 : ℝ) * ∑ k, (Ab k).indicator 1 ω ≤ f := by
    intro ω
    have hsum : ∑ k, (Ab k).indicator (1 : PrivateTape → ℝ) ω =
        ((Finset.univ.filter fun k => ω ∈ Ab k).card : ℝ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : ω ∈ Ab k <;> simp [hk]
    rw [hsum]
    by_cases hret : ∃ o, Returns A (cleanWorld n) s ω o
    · obtain ⟨o, hR⟩ := hret
      set G := acquired o.state.ledger
      have hG : G.card ≤ B := by
        obtain ⟨t, ht⟩ := hR
        have := hB (cleanWorld n) hlegal0 ω t
        rw [ht] at this; exact this
      have hbad : ∀ k, ω ∈ Ab k → s < (flipSet (movePerm (M k)) o.state.ledger).card := by
        rintro k ⟨o', hR', hc⟩
        rw [returns_unique A (cleanWorld n) s ω o o' hR hR']; exact hc
      have hflipcount : ∀ k, (flipSet (movePerm (M k)) o.state.ledger).card ≤
          (G.filter fun e => e.1.1 ∈ M k).card := by
        intro k
        apply Finset.card_le_card
        intro e he
        unfold flipSet at he
        rw [Finset.mem_filter] at he ⊢
        exact ⟨he.1, flip_lower_mem (M k) e he.2⟩
      have hdouble : ∑ k, (G.filter fun e => e.1.1 ∈ M k).card ≤ B * m := by
        have : ∑ k, (G.filter fun e => e.1.1 ∈ M k).card =
            ∑ e ∈ G, (Finset.univ.filter fun k => e.1.1 ∈ M k).card := by
          simp only [Finset.card_filter]
          exact Finset.sum_comm
        rw [this]
        calc ∑ e ∈ G, (Finset.univ.filter fun k => e.1.1 ∈ M k).card ≤ ∑ _e ∈ G, m :=
              Finset.sum_le_sum fun e _ => cyc_count n f m hfn e.1.1
          _ = G.card * m := by simp
          _ ≤ B * m := Nat.mul_le_mul_right _ hG
      have hbadcount : (Finset.univ.filter fun k => ω ∈ Ab k).card * (s + 1) ≤ B * m := by
        calc (Finset.univ.filter fun k => ω ∈ Ab k).card * (s + 1)
            = ∑ k ∈ Finset.univ.filter (fun k => ω ∈ Ab k), (s + 1) := by simp
          _ ≤ ∑ k ∈ Finset.univ.filter (fun k => ω ∈ Ab k), (G.filter fun e => e.1.1 ∈ M k).card := by
              apply Finset.sum_le_sum
              intro k hk
              have := hbad k (Finset.mem_filter.1 hk).2
              have := hflipcount k
              omega
          _ ≤ ∑ k, (G.filter fun e => e.1.1 ∈ M k).card :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
          _ ≤ B * m := hdouble
      have hfin : 8 * (Finset.univ.filter fun k => ω ∈ Ab k).card ≤ f := by
        set c := (Finset.univ.filter fun k => ω ∈ Ab k).card
        have hf' : 4 * f = n := by omega
        nlinarith
      exact_mod_cast hfin
    · have : (Finset.univ.filter fun k => ω ∈ Ab k) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro k _ ⟨o, hR, -⟩
        exact hret ⟨o, hR⟩
      rw [this]; simp
  have hint : ∀ k, μ.real (Ab k) = ∫ ω, (Ab k).indicator (1 : PrivateTape → ℝ) ω ∂μ := by
    intro k; rw [integral_indicator_one (hAbmeas k)]
  have hsumint : ∑ k, μ.real (Ab k) = ∫ ω, ∑ k, (Ab k).indicator (1 : PrivateTape → ℝ) ω ∂μ := by
    rw [integral_finset_sum]
    · exact Finset.sum_congr rfl fun k _ => hint k
    · intro k _; exact (integrable_const (1 : ℝ)).indicator (hAbmeas k)
  have hle : ∑ k, μ.real (Ab k) ≤ (f : ℝ) / 8 := by
    rw [hsumint]
    have : ∫ ω, ∑ k, (Ab k).indicator (1 : PrivateTape → ℝ) ω ∂μ ≤ ∫ _ω, (f : ℝ) / 8 ∂μ := by
      apply integral_mono
      · exact integrable_finset_sum _ fun k _ => (integrable_const (1 : ℝ)).indicator (hAbmeas k)
      · exact integrable_const _
      · intro ω; have := hcount ω; simp only; linarith
    simpa using this
  have hge : (f : ℝ) * (1 / 2) ≤ ∑ k, μ.real (Ab k) := by
    calc (f : ℝ) * (1 / 2) = ∑ _k : Fin f, (1 / 2 : ℝ) := by simp
      _ ≤ ∑ k, μ.real (Ab k) := Finset.sum_le_sum fun k _ => claim1 k
  have hfR : (4 : ℝ) ≤ f := by exact_mod_cast hf4
  linarith
