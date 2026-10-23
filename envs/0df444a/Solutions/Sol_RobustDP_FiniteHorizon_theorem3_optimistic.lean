-- Prove2me | solution 1 for RobustDP.FiniteHorizon.theorem3_optimistic
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T02:06:00.008538+00:00
-- url     : https://prove2.me/submissions/d540e74f-6133-4398-b1a6-334512b76945

/- Optimistic sup-sup completion: new joint epsilon choices and backward value. Retains the actual accepted robust Bellman and history-rebasing helpers below, with their attribution. -/
/-
Complete finite-horizon robust Markov-optimality formalization, 22 October 2026.
Alexander Richard Towell (queelius): research direction and verification standards.
OpenAI Codex: substantial mathematical argument, Lean implementation and checks.
Source: Garud N. Iyengar, CORC TR-2002-07, revised 4 May 2004, Theorem 2,
pp.7-8. The platform explicitly adds bounded rewards; mikedeng1 supplied that
model. Shuze Chen confirmed the statement, not this proof. Lean/Mathlib supply
foundations. Our accepted Bellman proof (target52a0de31-f82a-4d2c-8d6e-7944cdfc5745,
submission61082df2-3f9e-4d42-aab8-756ac051ff64) is reused with its helpers intact;
Lean's syntax extractor removed only its top-level solution command. Our accepted
deterministic-policy corollary supplies the epsilon-greedy comparison pattern.
New: an explicit history-rebasing map, a matching rectangular adversary, equality
of achievable reward ranges for every deterministic Markov policy, robust and
optimistic policy-value invariance, and the complete robust Markov-optimality
root. Neither exact optimizer attainment nor the full optimistic Bellman theorem
is claimed. No mathematical novelty or independent human review is claimed.
-/
/-
Complete finite-horizon robust Bellman formalization by Alexander Richard Towell
(queelius), with substantial OpenAI Codex assistance in construction, verification
and documentation. Mathematical source: Garud N. Iyengar, Robust dynamic
programming, CORC TR-2002-07, revised 4 May 2004, Theorem 1, eq.(11), p.6.
The platform model adds an explicit bounded-reward hypothesis; credit mikedeng1.
Shuze Chen's statement confirmation is not review of this proof. Lean and Mathlib
contributors supply the foundational countable probability and real-extrema API.
This proof constructs finite backward values, uniform epsilon-greedy Markov
policies and rectangular adversaries, bounds total horizon error by induction,
and identifies the actual supremum-infimum value over history-dependent policies.
It does not assume attainment, compactness or finite state/action spaces.
Checked helpers from our accepted eq.(15) formalization are reused; that earlier
result is completed work, not counted again. No mathematical novelty or independent
human proof review is claimed. The corrected bounded platform model is explicit.
-/
import Mathlib
import Definitions.Def_RobustDP_FiniteHorizon_Value
set_option autoImplicit false
namespace RobustDP.FiniteHorizon
variable {S A : Type*} [Countable S] [Countable A]
lemma weights_summable (p : PMF S) : Summable (fun s => (p s).toReal) :=
  ENNReal.summable_toReal (by simp)
lemma weights_sum (p : PMF S) : (∑' s, (p s).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun s => p.apply_ne_top s)]
  simp
lemma weighted_summable (p : PMF S) (f : S → ℝ) (B : ℝ)
    (hf : ∀ s, |f s| ≤ B) : Summable (fun s => (p s).toReal * f s) := by
  apply Summable.of_norm_bounded ((weights_summable p).mul_right B)
  intro s
  simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg] using
    mul_le_mul_of_nonneg_left (hf s) (ENNReal.toReal_nonneg : 0 ≤ (p s).toReal)
lemma expect_abs_le (p : PMF S) (f : S → ℝ) (B : ℝ)
    (hf : ∀ s, |f s| ≤ B) : |expect p f| ≤ B := by
  have hs := weighted_summable p f B hf
  calc
    |expect p f| ≤ ∑' s, |(p s).toReal * f s| := by
      simpa [expect, Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' s, (p s).toReal * B := by
      apply hs.abs.tsum_le_tsum _ ((weights_summable p).mul_right B)
      intro s
      simpa [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg] using
        mul_le_mul_of_nonneg_left (hf s) (ENNReal.toReal_nonneg : 0 ≤ (p s).toReal)
    _ = B := by rw [tsum_mul_right, weights_sum]; simp


lemma deterministic_markov_exists (M : AMDP S A) : ∃ π : Policy M, IsDetMarkov π := by
  classical
  have hN : 0 < M.N := by have := M.one_le_N; omega
  let f : ℕ → S → A := fun t s => if ht : t < M.N then
    (M.Aset_nonempty t ht s).choose else (M.Aset_nonempty 0 hN s).choose
  have hf : ∀ t < M.N, ∀ s, f t s ∈ M.Aset t s := by
    intro t ht s
    simp only [f, dif_pos ht]
    exact (M.Aset_nonempty t ht s).choose_spec
  let π : Policy M := ⟨fun t h => PMF.pure (f t h.cur), by
    intro t ht h a ha
    have ha' : a = f t h.cur := by simpa only [PMF.support_pure, Set.mem_singleton_iff] using ha
    rw [ha']
    exact hf t ht h.cur⟩
  exact ⟨π, f, fun _ _ _ => rfl⟩

lemma adversary_nonempty (M : AMDP S A) : Nonempty (Adversary M) := by
  classical
  let σ : (t : ℕ) → History S A t → A → PMF S := fun t h a =>
    if ht : t < M.N ∧ a ∈ M.Aset t h.cur then
      (M.P_nonempty t ht.1 h.cur a ht.2).choose else PMF.pure h.cur
  refine ⟨⟨σ, ?_⟩⟩
  intro t ht h a ha
  simp only [σ, dif_pos (And.intro ht ha)]
  exact (M.P_nonempty t ht h.cur a ha).choose_spec

lemma expTail_abs_le (M : AMDP S A) (R : ℝ)
    (hr : ∀ t s a s', |M.r t s a s'| ≤ R) (hN : ∀ s, |M.rN s| ≤ R)
    (d : (t : ℕ) → History S A t → PMF A)
    (σ : (t : ℕ) → History S A t → A → PMF S) :
    ∀ k n (h : History S A n), |expTail M d σ k n h| ≤ ((k : ℝ) + 1) * R := by
  intro k
  induction k with
  | zero => intro n h; simpa [expTail] using hN h.cur
  | succ k ih =>
    intro n h
    change |expect (d n h) (fun a => expect (σ n h a)
      (fun s => M.r n h.cur a s + expTail M d σ k (n+1) (h.extend a s)))| ≤ _
    apply expect_abs_le
    intro a
    apply expect_abs_le
    intro s
    calc
      |M.r n h.cur a s + expTail M d σ k (n+1) (h.extend a s)|
        ≤ |M.r n h.cur a s| + |expTail M d σ k (n+1) (h.extend a s)| := abs_add_le _ _
      _ ≤ R + ((k : ℝ)+1)*R := add_le_add (hr n h.cur a s) (ih (n+1) (h.extend a s))
      _ = ((↑(k+1) : ℝ)+1)*R := by push_cast; ring

lemma inf_abs_le {ι : Type*} [Nonempty ι] (f : ι → ℝ) (B : ℝ)
    (hf : ∀ i, |f i| ≤ B) : |⨅ i, f i| ≤ B := by
  rw [abs_le]
  have hl : ∀ i, -B ≤ f i := fun i => (abs_le.mp (hf i)).1
  have hu : ∀ i, f i ≤ B := fun i => (abs_le.mp (hf i)).2
  refine ⟨le_ciInf hl, ?_⟩
  exact (ciInf_le ⟨-B, Set.forall_mem_range.mpr hl⟩ (Classical.arbitrary ι)).trans (hu _)

lemma sup_abs_le {ι : Type*} [Nonempty ι] (f : ι → ℝ) (B : ℝ)
    (hf : ∀ i, |f i| ≤ B) : |⨆ i, f i| ≤ B := by
  rw [abs_le]
  have hl : ∀ i, -B ≤ f i := fun i => (abs_le.mp (hf i)).1
  have hu : ∀ i, f i ≤ B := fun i => (abs_le.mp (hf i)).2
  exact ⟨(hl (Classical.arbitrary ι)).trans (le_ciSup ⟨B, Set.forall_mem_range.mpr hu⟩ _), ciSup_le hu⟩

lemma all_values_bounded (M : AMDP S A) (R : ℝ)
    (hr : ∀ t s a s', |M.r t s a s'| ≤ R) (hN : ∀ s, |M.rN s| ≤ R)
    (n : ℕ) (h : History S A n) :
    (∀ π σ, |expectedReward M π σ n h| ≤ ((M.N-n : ℕ)+1 : ℝ)*R) ∧
    (∀ π, |V M π n h| ≤ ((M.N-n : ℕ)+1 : ℝ)*R) ∧
    |Vstar M n h| ≤ ((M.N-n : ℕ)+1 : ℝ)*R ∧
    (∀ π, |Vbar M π n h| ≤ ((M.N-n : ℕ)+1 : ℝ)*R) ∧
    |VbarStar M n h| ≤ ((M.N-n : ℕ)+1 : ℝ)*R := by
  haveI : Nonempty (Policy M) := ⟨(deterministic_markov_exists M).choose⟩
  haveI := adversary_nonempty M
  have he : ∀ π σ, |expectedReward M π σ n h| ≤ ((M.N-n : ℕ)+1 : ℝ)*R :=
    fun π σ => expTail_abs_le M R hr hN π.1 σ.1 (M.N-n) n h
  have hv : ∀ π, |V M π n h| ≤ ((M.N-n : ℕ)+1 : ℝ)*R :=
    fun π => inf_abs_le _ _ (he π)
  have hvb : ∀ π, |Vbar M π n h| ≤ ((M.N-n : ℕ)+1 : ℝ)*R :=
    fun π => sup_abs_le _ _ (he π)
  exact ⟨he, hv, sup_abs_le _ _ hv, hvb, sup_abs_le _ _ hvb⟩

lemma terminal_values (M : AMDP S A) (n : ℕ) (hn : M.N ≤ n) (h : History S A n) :
    Vstar M n h = M.rN h.cur ∧ VbarStar M n h = M.rN h.cur := by
  haveI : Nonempty (Policy M) := ⟨(deterministic_markov_exists M).choose⟩
  haveI := adversary_nonempty M
  simp [Vstar, VbarStar, V, Vbar, expectedReward, Nat.sub_eq_zero_of_le hn, expTail]


lemma expect_le_of_support (p : PMF S) (f : S → ℝ) (B c : ℝ)
    (hf : ∀ s, |f s| ≤ B) (hc : ∀ s ∈ p.support, f s ≤ c) : expect p f ≤ c := by
  classical
  calc
    expect p f ≤ ∑' s, (p s).toReal*c := by
      apply (weighted_summable p f B hf).tsum_le_tsum _ ((weights_summable p).mul_right c)
      intro s
      by_cases hs : s ∈ p.support
      · exact mul_le_mul_of_nonneg_left (hc s hs) ENNReal.toReal_nonneg
      · simp [(p.apply_eq_zero_iff s).mpr hs]
    _ = c := by rw [tsum_mul_right, weights_sum]; simp

lemma expect_pure (s : S) (f : S → ℝ) : expect (PMF.pure s) f = f s := by
  classical
  unfold expect
  rw [tsum_eq_single s]
  · simp
  · intro b hb
    simp [PMF.pure_apply, hb]

lemma sup_expect_eq_pure (U : Set S) (hU : U.Nonempty) (f : S → ℝ) (B : ℝ)
    (hf : ∀ s, |f s| ≤ B) :
    (⨆ q : {q : PMF S // ∀ s ∈ q.support, s ∈ U}, expect q.1 f) =
      ⨆ s : U, f s := by
  classical
  let Q := {q : PMF S // ∀ s ∈ q.support, s ∈ U}
  let pureQ : U → Q := fun s => ⟨PMF.pure s, by simpa only [PMF.support_pure,
    Set.mem_singleton_iff, forall_eq] using s.2⟩
  haveI : Nonempty U := hU.to_subtype
  haveI : Nonempty Q := ⟨pureQ (Classical.arbitrary U)⟩
  have hb : BddAbove (Set.range (fun s : U => f s)) :=
    ⟨B, Set.forall_mem_range.mpr (fun s => (abs_le.mp (hf s)).2)⟩
  apply le_antisymm
  · apply ciSup_le
    intro q
    apply expect_le_of_support q.1 f B _ hf
    intro s hs
    exact le_ciSup hb ⟨s, q.2 s hs⟩
  · apply ciSup_le
    intro s
    have hbQ : BddAbove (Set.range (fun q : Q => expect q.1 f)) :=
      ⟨B, Set.forall_mem_range.mpr (fun q => (abs_le.mp (expect_abs_le q.1 f B hf)).2)⟩
    calc
      f s = expect (pureQ s).1 f := (expect_pure (s : S) f).symm
      _ ≤ ⨆ q : Q, expect q.1 f := le_ciSup hbQ (pureQ s)


lemma expect_mono_support (p : PMF S) (f g : S → ℝ) (B C : ℝ)
    (hf : ∀ s, |f s| ≤ B) (hg : ∀ s, |g s| ≤ C)
    (hfg : ∀ s ∈ p.support, f s ≤ g s) : expect p f ≤ expect p g := by
  classical
  apply (weighted_summable p f B hf).tsum_le_tsum _ (weighted_summable p g C hg)
  intro s
  by_cases hs : s ∈ p.support
  · exact mul_le_mul_of_nonneg_left (hfg s hs) ENNReal.toReal_nonneg
  · simp [(p.apply_eq_zero_iff s).mpr hs]

lemma expect_add_const (p : PMF S) (f : S → ℝ) (B c : ℝ)
    (hf : ∀ s, |f s| ≤ B) : expect p (fun s => f s+c) = expect p f+c := by
  unfold expect
  simp_rw [mul_add]
  rw [Summable.tsum_add (weighted_summable p f B hf) ((weights_summable p).mul_right c),
    tsum_mul_right, weights_sum, one_mul]

lemma inf_abs_le_empty {ι : Type*} (f : ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ i, |f i| ≤ B) : |⨅ i, f i| ≤ B := by
  cases isEmpty_or_nonempty ι with
  | inl h => simp_all
  | inr h => exact inf_abs_le f B hf



lemma rectangular_inf_expect {X : Type*} (x₀ : X) (U : Set A) (T : A → Set X)
    (hT : ∀ a ∈ U, (T a).Nonempty) (F : A → X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ a x, |F a x| ≤ B) (q : PMF A) (hq : ∀ a ∈ q.support, a ∈ U) :
    (⨅ p : {p : A → X // ∀ a ∈ U, p a ∈ T a}, expect q (fun a => F a (p.1 a))) =
      expect q (fun a => ⨅ x : T a, F a x) := by
  classical
  let Sel := {p : A → X // ∀ a ∈ U, p a ∈ T a}
  let g : A → ℝ := fun a => ⨅ x : T a, F a x
  have hg : ∀ a, |g a| ≤ B := fun a => inf_abs_le_empty _ B hB (fun x => hF a x)
  let p₀ : Sel := ⟨fun a => if ha : a ∈ U then (hT a ha).choose else x₀, by
    intro a ha
    simp only [dif_pos ha]
    exact (hT a ha).choose_spec⟩
  haveI : Nonempty Sel := ⟨p₀⟩
  have hb : BddBelow (Set.range (fun p : Sel => expect q (fun a => F a (p.1 a)))) :=
    ⟨-B, Set.forall_mem_range.mpr (fun p =>
      (abs_le.mp (expect_abs_le q _ B (fun a => hF a (p.1 a)))).1)⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hex : ∀ a ∈ U, ∃ x : T a, F a x < g a + ε := by
      intro a ha
      haveI : Nonempty (T a) := (hT a ha).to_subtype
      exact exists_lt_of_ciInf_lt (lt_add_of_pos_right (g a) hε)
    let p : Sel := ⟨fun a => if ha : a ∈ U then (hex a ha).choose.1 else x₀, by
      intro a ha
      simp only [dif_pos ha]
      exact (hex a ha).choose.2⟩
    have hp : ∀ a ∈ q.support, F a (p.1 a) ≤ g a + ε := by
      intro a ha
      have hu := hq a ha
      change F a (if _ : a ∈ U then _ else _) ≤ _
      rw [dif_pos hu]
      exact (hex a hu).choose_spec.le
    calc
      (⨅ p : Sel, expect q (fun a => F a (p.1 a)))
        ≤ expect q (fun a => F a (p.1 a)) := ciInf_le hb p
      _ ≤ expect q (fun a => g a + ε) :=
        expect_mono_support q _ _ B (B+|ε|) (fun a => hF a (p.1 a))
          (fun a => (abs_add_le _ _).trans (add_le_add (hg a) (le_refl |ε|))) hp
      _ = expect q g + ε := expect_add_const q g B ε hg
  · apply le_ciInf
    intro p
    apply expect_mono_support q _ _ B B hg (fun a => hF a (p.1 a))
    intro a ha
    exact ciInf_le (f := fun x : T a => F a x) ⟨-B, Set.forall_mem_range.mpr (fun x => (abs_le.mp (hF a x)).1)⟩
      ⟨p.1 a, p.2 a (hq a ha)⟩
noncomputable def actionValue (M : AMDP S A) (n : ℕ) (s : S) (W : S → ℝ) (a : A) : ℝ :=
  ⨅ p : M.P n s a, expect (p : PMF S) (fun y => M.r n s a y + W y)

noncomputable def bellmanStep (M : AMDP S A) (n : ℕ) (s : S) (W : S → ℝ) : ℝ :=
  ⨆ a : M.Aset n s, actionValue M n s W a

lemma sup_abs_le_empty {ι : Type*} (f : ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ i, |f i| ≤ B) : |⨆ i, f i| ≤ B := by
  cases isEmpty_or_nonempty ι with
  | inl h => simp_all
  | inr h => exact sup_abs_le f B hf

lemma actionValue_bound (M : AMDP S A) (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hr : ∀ t s a y, |M.r t s a y| ≤ R) (W : S → ℝ) (hW : ∀ y, |W y| ≤ B)
    (n : ℕ) (s : S) (a : A) : |actionValue M n s W a| ≤ R+B := by
  apply inf_abs_le_empty _ _ (by positivity)
  intro p
  apply expect_abs_le
  intro y
  exact (abs_add_le _ _).trans (add_le_add (hr n s a y) (hW y))

lemma bellmanStep_bound (M : AMDP S A) (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hr : ∀ t s a y, |M.r t s a y| ≤ R) (W : S → ℝ) (hW : ∀ y, |W y| ≤ B)
    (n : ℕ) (s : S) : |bellmanStep M n s W| ≤ R+B := by
  exact sup_abs_le_empty _ _ (by positivity)
    (fun a => actionValue_bound M R B hR hB hr W hW n s a)

noncomputable def backwardValue (M : AMDP S A) : ℕ → ℕ → S → ℝ
  | 0, _, s => M.rN s
  | k+1, n, s => bellmanStep M n s (backwardValue M k (n+1))

lemma backwardValue_bound (M : AMDP S A) (R : ℝ) (hR : 0 ≤ R)
    (hr : ∀ t s a y, |M.r t s a y| ≤ R) (hrN : ∀ s, |M.rN s| ≤ R) :
    ∀ k n s, |backwardValue M k n s| ≤ ((k : ℝ)+1)*R := by
  intro k
  induction k with
  | zero => intro n s; simpa [backwardValue] using hrN s
  | succ k ih =>
    intro n s
    have hh := bellmanStep_bound M R (((k:ℝ)+1)*R) hR (by positivity) hr
      (backwardValue M k (n+1)) (ih (n+1)) n s
    simpa only [backwardValue, Nat.cast_add, Nat.cast_one] using hh.trans_eq (by ring)

noncomputable def finiteValue (M : AMDP S A) (n : ℕ) (s : S) : ℝ :=
  backwardValue M (M.N-n) n s

lemma finiteValue_terminal (M : AMDP S A) (s : S) : finiteValue M M.N s = M.rN s := by
  simp [finiteValue, backwardValue]

lemma finiteValue_step (M : AMDP S A) (n : ℕ) (hn : n < M.N) (s : S) :
    finiteValue M n s = bellmanStep M n s (finiteValue M (n+1)) := by
  have he : M.N-n = (M.N-(n+1))+1 := by omega
  unfold finiteValue
  conv_lhs => rw [he]
  rfl

lemma finiteValue_bounded (M : AMDP S A) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n s, |finiteValue M n s| ≤ B := by
  obtain ⟨R, hr, hrN⟩ := M.bounded
  refine ⟨((M.N : ℝ)+1)*|R|, by positivity, ?_⟩
  intro n s
  have hh := backwardValue_bound M |R| (abs_nonneg R)
    (fun t s a y => (hr t s a y).trans (le_abs_self R))
    (fun s => (hrN s).trans (le_abs_self R)) (M.N-n) n s
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg R)
  exact add_le_add (show ((M.N-n : ℕ) : ℝ) ≤ (M.N : ℝ) by exact_mod_cast Nat.sub_le M.N n) le_rfl

lemma greedy_policy (M : AMDP S A) (W : ℕ → S → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hW : ∀ n s, |W n s| ≤ B)
    (hrec : ∀ n < M.N, ∀ s, W n s = bellmanStep M n s (W (n+1)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ π : Policy M, ∃ f : ℕ → S → A,
      (∀ t < M.N, ∀ h : History S A t, π.1 t h = PMF.pure (f t h.cur)) ∧
      (∀ t < M.N, ∀ s, f t s ∈ M.Aset t s) ∧
      (∀ t < M.N, ∀ s, ∀ p ∈ M.P t s (f t s),
        W t s - ε ≤ expect p (fun y => M.r t s (f t s) y + W (t+1) y)) := by
  classical
  obtain ⟨R, hr, hrN⟩ := M.bounded
  have hex : ∀ t < M.N, ∀ s, ∃ a : M.Aset t s,
      W t s - ε < actionValue M t s (W (t+1)) a := by
    intro t ht s
    haveI : Nonempty (M.Aset t s) := (M.Aset_nonempty t ht s).to_subtype
    apply exists_lt_of_lt_ciSup
    change W t s - ε < bellmanStep M t s (W (t+1))
    rw [← hrec t ht s]
    linarith
  have hN : 0 < M.N := by have := M.one_le_N; omega
  let f : ℕ → S → A := fun t s => if ht : t < M.N then
    (hex t ht s).choose.1 else (M.Aset_nonempty 0 hN s).choose
  have hf : ∀ t < M.N, ∀ s, f t s ∈ M.Aset t s := by
    intro t ht s
    simp only [f, dif_pos ht]
    exact (hex t ht s).choose.2
  let π : Policy M := ⟨fun t h => PMF.pure (f t h.cur), by
    intro t ht h a ha
    have he : a = f t h.cur := by simpa only [PMF.support_pure, Set.mem_singleton_iff] using ha
    rw [he]
    exact hf t ht h.cur⟩
  refine ⟨π, f, fun _ _ _ => rfl, hf, ?_⟩
  intro t ht s p hp
  have hchoice : W t s - ε < actionValue M t s (W (t+1)) (f t s) := by
    simpa only [f, dif_pos ht] using (hex t ht s).choose_spec
  apply hchoice.le.trans
  apply ciInf_le (f := fun p : M.P t s (f t s) =>
    expect (p : PMF S) (fun y => M.r t s (f t s) y + W (t+1) y)) _ ⟨p,hp⟩
  refine ⟨-(|R|+B), Set.forall_mem_range.mpr ?_⟩
  intro q
  apply (abs_le.mp (expect_abs_le (q : PMF S) _ (|R|+B) ?_)).1
  intro y
  exact (abs_add_le _ _).trans (add_le_add ((hr t s (f t s) y).trans (le_abs_self R)) (hW (t+1) y))

lemma greedy_adversary (M : AMDP S A) (W : ℕ → S → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hW : ∀ n s, |W n s| ≤ B)
    (hrec : ∀ n < M.N, ∀ s, W n s = bellmanStep M n s (W (n+1)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ σ : Adversary M, ∀ t < M.N, ∀ h : History S A t, ∀ a ∈ M.Aset t h.cur,
      expect (σ.1 t h a) (fun y => M.r t h.cur a y + W (t+1) y) ≤ W t h.cur + ε := by
  classical
  obtain ⟨R, hr, hrN⟩ := M.bounded
  have hex : ∀ t < M.N, ∀ s, ∀ a ∈ M.Aset t s,
      ∃ p : M.P t s a, expect (p : PMF S) (fun y => M.r t s a y + W (t+1) y)
        < actionValue M t s (W (t+1)) a + ε := by
    intro t ht s a ha
    haveI : Nonempty (M.P t s a) := (M.P_nonempty t ht s a ha).to_subtype
    exact exists_lt_of_ciInf_lt (lt_add_of_pos_right _ hε)
  let σ : Adversary M := ⟨fun t h a => if ht : t < M.N ∧ a ∈ M.Aset t h.cur then
    (hex t ht.1 h.cur a ht.2).choose.1 else PMF.pure h.cur, by
      intro t ht h a ha
      simp only [dif_pos (And.intro ht ha)]
      exact (hex t ht h.cur a ha).choose.2⟩
  refine ⟨σ, ?_⟩
  intro t ht h a ha
  have hc := (hex t ht h.cur a ha).choose_spec.le
  change expect (if _ : _ then _ else _) _ ≤ _
  rw [dif_pos (And.intro ht ha)]
  apply hc.trans
  apply add_le_add _ (le_refl ε)
  rw [hrec t ht h.cur]
  apply le_ciSup (f := fun a : M.Aset t h.cur => actionValue M t h.cur (W (t+1)) a) _ ⟨a,ha⟩
  refine ⟨|R|+B, Set.forall_mem_range.mpr ?_⟩
  intro a
  exact (abs_le.mp (actionValue_bound M |R| B (abs_nonneg R) hB
    (fun t s a y => (hr t s a y).trans (le_abs_self R)) (W (t+1)) (hW (t+1)) t h.cur a)).2

lemma tail_upper_from_residual (M : AMDP S A) (R : ℝ)
    (hr : ∀ t s a y, |M.r t s a y| ≤ R) (hrN : ∀ s, |M.rN s| ≤ R)
    (W : ℕ → S → ℝ) (B : ℝ) (hW : ∀ n s, |W n s| ≤ B)
    (hWN : ∀ s, W M.N s = M.rN s)
    (ε : ℝ) (σ : Adversary M)
    (hres : ∀ t < M.N, ∀ h : History S A t, ∀ a ∈ M.Aset t h.cur,
      expect (σ.1 t h a) (fun y => M.r t h.cur a y + W (t+1) y) ≤ W t h.cur + ε)
    (π : Policy M) : ∀ k n (h : History S A n), n+k=M.N →
      expTail M π.1 σ.1 k n h ≤ W n h.cur + (k : ℝ)*ε := by
  intro k
  induction k with
  | zero =>
    intro n h he
    have hn : n=M.N := by omega
    simpa [expTail, hn, hWN]
  | succ k ih =>
    intro n h he
    have hn : n < M.N := by omega
    have hnext : n+1+k=M.N := by omega
    change expect (π.1 n h) (fun a => expect (σ.1 n h a)
      (fun y => M.r n h.cur a y + expTail M π.1 σ.1 k (n+1) (h.extend a y))) ≤ _
    apply expect_le_of_support _ _ (R+((k:ℝ)+1)*R)
    · intro a
      apply expect_abs_le
      intro y
      exact (abs_add_le _ _).trans (add_le_add (hr n h.cur a y)
        (expTail_abs_le M R hr hrN π.1 σ.1 k (n+1) (h.extend a y)))
    · intro a ha
      have hcmp := expect_mono_support (σ.1 n h a)
        (fun y => M.r n h.cur a y + expTail M π.1 σ.1 k (n+1) (h.extend a y))
        (fun y => (M.r n h.cur a y + W (n+1) y) + (k:ℝ)*ε)
        (R+((k:ℝ)+1)*R) (R+B+|(k:ℝ)*ε|)
        (fun y => (abs_add_le _ _).trans (add_le_add (hr n h.cur a y)
          (expTail_abs_le M R hr hrN π.1 σ.1 k (n+1) (h.extend a y))))
        (fun y => (abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (hr n h.cur a y) (hW (n+1) y))) le_rfl))
        (fun y _ => by have hh := ih (n+1) (h.extend a y) hnext; simpa only [History.extend, History.cur, add_assoc] using add_le_add (le_refl (M.r n h.cur a y)) hh)
      rw [expect_add_const (σ.1 n h a) _ (R+B) ((k:ℝ)*ε)
        (fun y => (abs_add_le _ _).trans (add_le_add (hr n h.cur a y) (hW (n+1) y)))] at hcmp
      have hh := hres n hn h a (π.2 n hn h a ha)
      push_cast
      linarith

lemma tail_lower_from_residual (M : AMDP S A) (R : ℝ)
    (hr : ∀ t s a y, |M.r t s a y| ≤ R) (hrN : ∀ s, |M.rN s| ≤ R)
    (W : ℕ → S → ℝ) (B : ℝ) (hW : ∀ n s, |W n s| ≤ B)
    (hWN : ∀ s, W M.N s = M.rN s)
    (ε : ℝ) (π : Policy M) (f : ℕ → S → A)
    (hπ : ∀ t < M.N, ∀ h : History S A t, π.1 t h = PMF.pure (f t h.cur))
    (hf : ∀ t < M.N, ∀ s, f t s ∈ M.Aset t s)
    (hres : ∀ t < M.N, ∀ s, ∀ p ∈ M.P t s (f t s),
      W t s - ε ≤ expect p (fun y => M.r t s (f t s) y + W (t+1) y))
    (σ : Adversary M) : ∀ k n (h : History S A n), n+k=M.N →
      W n h.cur - (k : ℝ)*ε ≤ expTail M π.1 σ.1 k n h := by
  intro k
  induction k with
  | zero =>
    intro n h he
    have hn : n=M.N := by omega
    simpa [expTail, hn, hWN]
  | succ k ih =>
    intro n h he
    have hn : n < M.N := by omega
    have hnext : n+1+k=M.N := by omega
    change _ ≤ expect (π.1 n h) (fun a => expect (σ.1 n h a)
      (fun y => M.r n h.cur a y + expTail M π.1 σ.1 k (n+1) (h.extend a y)))
    rw [hπ n hn h, expect_pure]
    let a := f n h.cur
    have hcmp := expect_mono_support (σ.1 n h a)
      (fun y => (M.r n h.cur a y + W (n+1) y) + (-((k:ℝ)*ε)))
      (fun y => M.r n h.cur a y + expTail M π.1 σ.1 k (n+1) (h.extend a y))
      (R+B+|-(k:ℝ)*ε|) (R+((k:ℝ)+1)*R)
      (fun y => (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (hr n h.cur a y) (hW (n+1) y))) (by simp)))
      (fun y => (abs_add_le _ _).trans (add_le_add (hr n h.cur a y)
        (expTail_abs_le M R hr hrN π.1 σ.1 k (n+1) (h.extend a y))))
      (fun y _ => by
        have hh := ih (n+1) (h.extend a y) hnext
        change W (n+1) y - (k:ℝ)*ε ≤ _ at hh
        linarith)
    rw [expect_add_const (σ.1 n h a) _ (R+B) (-((k:ℝ)*ε))
      (fun y => (abs_add_le _ _).trans (add_le_add (hr n h.cur a y) (hW (n+1) y)))] at hcmp
    have hh := hres n hn h.cur (σ.1 n h a) (σ.2 n hn h a (hf n hn h.cur))
    change W n h.cur - ((k+1:ℕ):ℝ)*ε ≤ _
    change W n h.cur - ε ≤ expect (σ.1 n h a) (fun y => M.r n h.cur a y + W (n+1) y) at hh
    change _ ≤ expect (σ.1 n h a) (fun y => M.r n h.cur a y + expTail M π.1 σ.1 k (n+1) (h.extend a y))
    push_cast
    linarith

lemma finiteValue_identification (M : AMDP S A) (n : ℕ) (h : History S A n) :
    Vstar M n h = finiteValue M n h.cur := by
  classical
  by_cases hn : n ≤ M.N
  · obtain ⟨B, hB, hW⟩ := finiteValue_bounded M
    obtain ⟨R, hr, hrN⟩ := M.bounded
    haveI : Nonempty (Policy M) := ⟨(deterministic_markov_exists M).choose⟩
    haveI := adversary_nonempty M
    let K : ℝ := (M.N-n : ℕ)
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have he : n+(M.N-n)=M.N := by omega
    have hbound := all_values_bounded M R hr hrN n h
    apply le_antisymm
    · apply le_of_forall_pos_le_add
      intro ε hε
      let δ : ℝ := ε/(K+1)
      have hδ : 0 < δ := div_pos hε (by positivity)
      have hsmall : K*δ ≤ ε := by
        have hcancel : δ*(K+1)=ε := div_mul_cancel₀ ε (by positivity)
        nlinarith
      obtain ⟨σ, hσ⟩ := greedy_adversary M (finiteValue M) B hB hW
        (finiteValue_step M) δ hδ
      apply ciSup_le
      intro π
      have hb : BddBelow (Set.range (fun σ : Adversary M => expectedReward M π σ n h)) :=
        ⟨-(((M.N-n : ℕ)+1 : ℝ)*R), Set.forall_mem_range.mpr (fun σ => (abs_le.mp (hbound.1 π σ)).1)⟩
      have hv : V M π n h ≤ expectedReward M π σ n h := ciInf_le hb σ
      have ht := tail_upper_from_residual M R hr hrN (finiteValue M) B hW
        (finiteValue_terminal M) δ σ hσ π (M.N-n) n h he
      change expectedReward M π σ n h ≤ finiteValue M n h.cur + K*δ at ht
      exact hv.trans (ht.trans (add_le_add le_rfl hsmall))
    · apply le_of_forall_pos_le_add
      intro ε hε
      let δ : ℝ := ε/(K+1)
      have hδ : 0 < δ := div_pos hε (by positivity)
      have hsmall : K*δ ≤ ε := by
        have hcancel : δ*(K+1)=ε := div_mul_cancel₀ ε (by positivity)
        nlinarith
      obtain ⟨π, f, hπ, hf, hres⟩ := greedy_policy M (finiteValue M) B hB hW
        (finiteValue_step M) δ hδ
      have hl : finiteValue M n h.cur - K*δ ≤ V M π n h := by
        apply le_ciInf
        intro σ
        exact tail_lower_from_residual M R hr hrN (finiteValue M) B hW
          (finiteValue_terminal M) δ π f hπ hf hres σ (M.N-n) n h he
      have hb : BddAbove (Set.range (fun π : Policy M => V M π n h)) :=
        ⟨((M.N-n : ℕ)+1 : ℝ)*R, Set.forall_mem_range.mpr (fun π => (abs_le.mp (hbound.2.1 π)).2)⟩
      have hv : V M π n h ≤ Vstar M n h := le_ciSup hb π
      linarith
  · have hN : M.N ≤ n := by omega
    rw [(terminal_values M n hN h).1]
    simp [finiteValue, Nat.sub_eq_zero_of_le hN, backwardValue]

end RobustDP.FiniteHorizon

open RobustDP.FiniteHorizon



namespace RobustDP.FiniteHorizon
variable {S A : Type*} [Countable S] [Countable A]

def rebaseHistory {k : ℕ} (past : Fin k → S × A) {n : ℕ} (h : History S A n) : History S A n :=
  (fun i => if hi : i.val < k then past ⟨i.val, hi⟩ else h.1 i, h.cur)

@[simp] lemma rebase_cur {k n : ℕ} (past : Fin k → S × A) (h : History S A n) :
    (rebaseHistory past h).cur = h.cur := rfl

lemma rebase_at_start {n : ℕ} (h h' : History S A n) (hc : h.cur = h'.cur) :
    rebaseHistory h.1 h' = h := by
  apply Prod.ext
  · funext i
    simp [rebaseHistory, i.isLt]
  · exact hc.symm

lemma rebase_extend {k n : ℕ} (past : Fin k → S × A) (h : History S A n)
    (hkn : k ≤ n) (a : A) (s : S) :
    rebaseHistory past (h.extend a s) = (rebaseHistory past h).extend a s := by
  apply Prod.ext
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [rebaseHistory, History.extend, show ¬ n < k by omega]
    · simp [rebaseHistory, History.extend]
  · rfl

noncomputable def rebaseAdversary (M : AMDP S A) {k : ℕ} (past : Fin k → S × A)
    (σ : Adversary M) : Adversary M :=
  ⟨fun n h a => σ.1 n (rebaseHistory past h) a,
    fun n hn h a ha => σ.2 n hn (rebaseHistory past h) a ha⟩

lemma expTail_rebase (M : AMDP S A) (π : Policy M) (f : ℕ → S → A)
    (hπ : ∀ n < M.N, ∀ h : History S A n, π.1 n h = PMF.pure (f n h.cur))
    {k : ℕ} (past : Fin k → S × A) (σ : Adversary M) :
    ∀ l n (h : History S A n), k ≤ n → n+l ≤ M.N →
      expTail M π.1 (rebaseAdversary M past σ).1 l n h =
        expTail M π.1 σ.1 l n (rebaseHistory past h) := by
  intro l
  induction l with
  | zero => intro n h _ _; rfl
  | succ l ih =>
    intro n h hkn hn
    have hnN : n < M.N := by omega
    change expect (π.1 n h) (fun a => expect (σ.1 n (rebaseHistory past h) a)
      (fun s => M.r n h.cur a s + expTail M π.1 (rebaseAdversary M past σ).1 l (n+1) (h.extend a s))) =
      expect (π.1 n (rebaseHistory past h)) (fun a => expect (σ.1 n (rebaseHistory past h) a)
      (fun s => M.r n h.cur a s + expTail M π.1 σ.1 l (n+1) ((rebaseHistory past h).extend a s)))
    rw [hπ n hnN h, hπ n hnN (rebaseHistory past h), rebase_cur, expect_pure, expect_pure]
    congr 1
    funext s
    rw [ih (n+1) (h.extend (f n h.cur) s) (by omega) (by omega), rebase_extend past h hkn]

lemma markov_reward_range (M : AMDP S A) (π : Policy M) (hπ : IsDetMarkov π)
    (n : ℕ) (hn : n ≤ M.N) (h h' : History S A n) (hc : h.cur = h'.cur) :
    Set.range (fun σ : Adversary M => expectedReward M π σ n h) =
      Set.range (fun σ : Adversary M => expectedReward M π σ n h') := by
  rcases hπ with ⟨f,hf⟩
  have transport (g g' : History S A n) (hg : g.cur = g'.cur) (σ : Adversary M) :
      expectedReward M π σ n g = expectedReward M π (rebaseAdversary M g.1 σ) n g' := by
    unfold expectedReward
    rw [expTail_rebase M π f hf g.1 σ (M.N-n) n g' le_rfl (by omega), rebase_at_start g g' hg]
  apply Set.ext
  intro x
  constructor
  · rintro ⟨σ,rfl⟩
    exact ⟨rebaseAdversary M h.1 σ, (transport h h' hc σ).symm⟩
  · rintro ⟨σ,rfl⟩
    exact ⟨rebaseAdversary M h'.1 σ, (transport h' h hc.symm σ).symm⟩

lemma markov_values_history_independent (M : AMDP S A) (π : Policy M) (hπ : IsDetMarkov π)
    (n : ℕ) (hn : n ≤ M.N) (h h' : History S A n) (hc : h.cur = h'.cur) :
    V M π n h = V M π n h' ∧ Vbar M π n h = Vbar M π n h' := by
  have he := markov_reward_range M π hπ n hn h h' hc
  constructor
  · change sInf (Set.range (fun σ : Adversary M => expectedReward M π σ n h)) =
      sInf (Set.range (fun σ : Adversary M => expectedReward M π σ n h'))
    rw [he]
  · change sSup (Set.range (fun σ : Adversary M => expectedReward M π σ n h)) =
      sSup (Set.range (fun σ : Adversary M => expectedReward M π σ n h'))
    rw [he]

end RobustDP.FiniteHorizon

namespace RobustDP.FiniteHorizon
variable {S A : Type*} [Countable S] [Countable A]

lemma markov_sup_identification (M : AMDP S A) (n : ℕ) (hn : n ≤ M.N)
    (h : History S A n) :
    (⨆ π : {π : Policy M // IsDetMarkov π}, V M π.1 n h) = finiteValue M n h.cur := by
  classical
  obtain ⟨B, hB, hW⟩ := finiteValue_bounded M
  obtain ⟨R, hr, hrN⟩ := M.bounded
  haveI : Nonempty (Policy M) := ⟨(deterministic_markov_exists M).choose⟩
  haveI := adversary_nonempty M
  haveI : Nonempty {π : Policy M // IsDetMarkov π} :=
    ⟨⟨(deterministic_markov_exists M).choose, (deterministic_markov_exists M).choose_spec⟩⟩
  have hbound := all_values_bounded M R hr hrN n h
  have hb : BddAbove (Set.range (fun π : Policy M => V M π n h)) :=
    ⟨((M.N-n : ℕ)+1 : ℝ)*R, Set.forall_mem_range.mpr (fun π => (abs_le.mp (hbound.2.1 π)).2)⟩
  apply le_antisymm
  · apply ciSup_le
    intro π
    rw [← finiteValue_identification M n h]
    exact le_ciSup hb π.1
  · apply le_of_forall_pos_le_add
    intro ε hε
    let K : ℝ := (M.N-n : ℕ)
    have hK : 0 ≤ K := by dsimp [K]; positivity
    let δ : ℝ := ε/(K+1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hsmall : K*δ ≤ ε := by
      have hcancel : δ*(K+1)=ε := div_mul_cancel₀ ε (by positivity)
      nlinarith
    obtain ⟨π, f, hπ, hf, hres⟩ := greedy_policy M (finiteValue M) B hB hW
      (finiteValue_step M) δ hδ
    have hmd : IsDetMarkov π := ⟨f,hπ⟩
    have hl : finiteValue M n h.cur - K*δ ≤ V M π n h := by
      apply le_ciInf
      intro σ
      exact tail_lower_from_residual M R hr hrN (finiteValue M) B hW
        (finiteValue_terminal M) δ π f hπ hf hres σ (M.N-n) n h (by omega)
    have hbmd : BddAbove (Set.range (fun π : {π : Policy M // IsDetMarkov π} => V M π.1 n h)) :=
      ⟨((M.N-n : ℕ)+1 : ℝ)*R, Set.forall_mem_range.mpr (fun π => (abs_le.mp (hbound.2.1 π.1)).2)⟩
    have hv : V M π n h ≤ ⨆ π : {π : Policy M // IsDetMarkov π}, V M π.1 n h :=
      le_ciSup hbmd ⟨π,hmd⟩
    linarith

end RobustDP.FiniteHorizon

open RobustDP.FiniteHorizon



namespace RobustDP.FiniteHorizon
variable {S A : Type*} [Countable S] [Countable A]

noncomputable def optAction (M : AMDP S A) (n : ℕ) (s : S) (W : S → ℝ) (a : A) : ℝ :=
  ⨆ p : M.P n s a, expect (p : PMF S) (fun y => M.r n s a y + W y)

noncomputable def optStep (M : AMDP S A) (n : ℕ) (s : S) (W : S → ℝ) : ℝ :=
  ⨆ a : M.Aset n s, optAction M n s W a

lemma optAction_bound (M : AMDP S A) (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hr : ∀ t s a y, |M.r t s a y| ≤ R) (W : S → ℝ) (hW : ∀ y, |W y| ≤ B)
    (n : ℕ) (s : S) (a : A) : |optAction M n s W a| ≤ R+B := by
  apply sup_abs_le_empty _ _ (by positivity)
  intro p
  apply expect_abs_le
  intro y
  exact (abs_add_le _ _).trans (add_le_add (hr n s a y) (hW y))

lemma optStep_bound (M : AMDP S A) (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hr : ∀ t s a y, |M.r t s a y| ≤ R) (W : S → ℝ) (hW : ∀ y, |W y| ≤ B)
    (n : ℕ) (s : S) : |optStep M n s W| ≤ R+B := by
  exact sup_abs_le_empty _ _ (by positivity)
    (fun a => optAction_bound M R B hR hB hr W hW n s a)

noncomputable def optBackward (M : AMDP S A) : ℕ → ℕ → S → ℝ
  | 0, _, s => M.rN s
  | k+1, n, s => optStep M n s (optBackward M k (n+1))

lemma optBackward_bound (M : AMDP S A) (R : ℝ) (hR : 0 ≤ R)
    (hr : ∀ t s a y, |M.r t s a y| ≤ R) (hrN : ∀ s, |M.rN s| ≤ R) :
    ∀ k n s, |optBackward M k n s| ≤ ((k : ℝ)+1)*R := by
  intro k
  induction k with
  | zero => intro n s; simpa [optBackward] using hrN s
  | succ k ih =>
    intro n s
    have hh := optStep_bound M R (((k:ℝ)+1)*R) hR (by positivity) hr
      (optBackward M k (n+1)) (ih (n+1)) n s
    simpa only [optBackward, Nat.cast_add, Nat.cast_one] using hh.trans_eq (by ring)

noncomputable def optValue (M : AMDP S A) (n : ℕ) (s : S) : ℝ :=
  optBackward M (M.N-n) n s

lemma optValue_terminal (M : AMDP S A) (s : S) : optValue M M.N s = M.rN s := by
  simp [optValue, optBackward]

lemma optValue_step (M : AMDP S A) (n : ℕ) (hn : n < M.N) (s : S) :
    optValue M n s = optStep M n s (optValue M (n+1)) := by
  have he : M.N-n = (M.N-(n+1))+1 := by omega
  unfold optValue
  conv_lhs => rw [he]
  rfl

lemma optValue_bounded (M : AMDP S A) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n s, |optValue M n s| ≤ B := by
  obtain ⟨R, hr, hrN⟩ := M.bounded
  refine ⟨((M.N : ℝ)+1)*|R|, by positivity, ?_⟩
  intro n s
  have hh := optBackward_bound M |R| (abs_nonneg R)
    (fun t s a y => (hr t s a y).trans (le_abs_self R))
    (fun s => (hrN s).trans (le_abs_self R)) (M.N-n) n s
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg R)
  exact add_le_add (show ((M.N-n : ℕ) : ℝ) ≤ (M.N : ℝ) by exact_mod_cast Nat.sub_le M.N n) le_rfl

lemma opt_residual_upper (M : AMDP S A) (W : ℕ → S → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hW : ∀ n s, |W n s| ≤ B)
    (hrec : ∀ n < M.N, ∀ s, W n s = optStep M n s (W (n+1)))
    (σ : Adversary M) (t : ℕ) (ht : t < M.N) (h : History S A t)
    (a : A) (ha : a ∈ M.Aset t h.cur) :
    expect (σ.1 t h a) (fun y => M.r t h.cur a y + W (t+1) y) ≤ W t h.cur := by
  obtain ⟨R, hr, hrN⟩ := M.bounded
  have hp : BddAbove (Set.range (fun p : M.P t h.cur a =>
      expect (p : PMF S) (fun y => M.r t h.cur a y + W (t+1) y))) := by
    refine ⟨|R|+B, Set.forall_mem_range.mpr ?_⟩
    intro p
    apply (abs_le.mp (expect_abs_le (p : PMF S) _ (|R|+B) ?_)).2
    intro y
    exact (abs_add_le _ _).trans (add_le_add ((hr t h.cur a y).trans (le_abs_self R)) (hW (t+1) y))
  have hq : BddAbove (Set.range (fun a : M.Aset t h.cur => optAction M t h.cur (W (t+1)) a)) := by
    refine ⟨|R|+B, Set.forall_mem_range.mpr ?_⟩
    intro a
    exact (abs_le.mp (optAction_bound M |R| B (abs_nonneg R) hB
      (fun t s a y => (hr t s a y).trans (le_abs_self R)) (W (t+1)) (hW (t+1)) t h.cur a)).2
  rw [hrec t ht h.cur]
  exact (le_ciSup hp ⟨σ.1 t h a, σ.2 t ht h a ha⟩).trans (le_ciSup hq ⟨a,ha⟩)

lemma optimistic_pair (M : AMDP S A) (W : ℕ → S → ℝ)
    (hrec : ∀ n < M.N, ∀ s, W n s = optStep M n s (W (n+1)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ π : Policy M, ∃ f : ℕ → S → A, ∃ σ : Adversary M,
      (∀ t < M.N, ∀ h : History S A t, π.1 t h = PMF.pure (f t h.cur)) ∧
      (∀ t < M.N, ∀ s, f t s ∈ M.Aset t s) ∧
      (∀ t < M.N, ∀ h : History S A t,
        W t h.cur - ε ≤ expect (σ.1 t h (f t h.cur))
          (fun y => M.r t h.cur (f t h.cur) y + W (t+1) y)) := by
  classical
  have hexA : ∀ t < M.N, ∀ s, ∃ a : M.Aset t s,
      W t s - ε/2 < optAction M t s (W (t+1)) a := by
    intro t ht s
    haveI : Nonempty (M.Aset t s) := (M.Aset_nonempty t ht s).to_subtype
    apply exists_lt_of_lt_ciSup
    change W t s - ε/2 < optStep M t s (W (t+1))
    rw [← hrec t ht s]
    linarith
  have hexP : ∀ t < M.N, ∀ s, ∀ a ∈ M.Aset t s,
      ∃ p : M.P t s a, optAction M t s (W (t+1)) a - ε/2 <
        expect (p : PMF S) (fun y => M.r t s a y + W (t+1) y) := by
    intro t ht s a ha
    haveI : Nonempty (M.P t s a) := (M.P_nonempty t ht s a ha).to_subtype
    apply exists_lt_of_lt_ciSup
    change optAction M t s (W (t+1)) a - ε/2 < optAction M t s (W (t+1)) a
    linarith
  have hN : 0 < M.N := by have := M.one_le_N; omega
  let f : ℕ → S → A := fun t s => if ht : t < M.N then
    (hexA t ht s).choose.1 else (M.Aset_nonempty 0 hN s).choose
  have hf : ∀ t < M.N, ∀ s, f t s ∈ M.Aset t s := by
    intro t ht s
    simp only [f, dif_pos ht]
    exact (hexA t ht s).choose.2
  let π : Policy M := ⟨fun t h => PMF.pure (f t h.cur), by
    intro t ht h a ha
    have he : a = f t h.cur := by simpa only [PMF.support_pure, Set.mem_singleton_iff] using ha
    rw [he]
    exact hf t ht h.cur⟩
  let σ : Adversary M := ⟨fun t h a => if ht : t < M.N ∧ a ∈ M.Aset t h.cur then
    (hexP t ht.1 h.cur a ht.2).choose.1 else PMF.pure h.cur, by
      intro t ht h a ha
      simp only [dif_pos (And.intro ht ha)]
      exact (hexP t ht h.cur a ha).choose.2⟩
  refine ⟨π, f, σ, fun _ _ _ => rfl, hf, ?_⟩
  intro t ht h
  have ha : W t h.cur - ε/2 < optAction M t h.cur (W (t+1)) (f t h.cur) := by
    simpa only [f, dif_pos ht] using (hexA t ht h.cur).choose_spec
  have hp := (hexP t ht h.cur (f t h.cur) (hf t ht h.cur)).choose_spec
  change W t h.cur - ε ≤ expect (if _ : _ then _ else _) _
  rw [dif_pos (And.intro ht (hf t ht h.cur))]
  linarith

lemma opt_tail_lower (M : AMDP S A) (R : ℝ)
    (hr : ∀ t s a y, |M.r t s a y| ≤ R) (hrN : ∀ s, |M.rN s| ≤ R)
    (W : ℕ → S → ℝ) (B : ℝ) (hW : ∀ n s, |W n s| ≤ B)
    (hWN : ∀ s, W M.N s = M.rN s)
    (ε : ℝ) (π : Policy M) (f : ℕ → S → A) (σ : Adversary M)
    (hπ : ∀ t < M.N, ∀ h : History S A t, π.1 t h = PMF.pure (f t h.cur))
    (hres : ∀ t < M.N, ∀ h : History S A t,
      W t h.cur - ε ≤ expect (σ.1 t h (f t h.cur))
        (fun y => M.r t h.cur (f t h.cur) y + W (t+1) y)) :
    ∀ k n (h : History S A n), n+k=M.N →
      W n h.cur - (k : ℝ)*ε ≤ expTail M π.1 σ.1 k n h := by
  intro k
  induction k with
  | zero =>
    intro n h he
    have hn : n=M.N := by omega
    simpa [expTail, hn, hWN]
  | succ k ih =>
    intro n h he
    have hn : n < M.N := by omega
    have hnext : n+1+k=M.N := by omega
    change _ ≤ expect (π.1 n h) (fun a => expect (σ.1 n h a)
      (fun y => M.r n h.cur a y + expTail M π.1 σ.1 k (n+1) (h.extend a y)))
    rw [hπ n hn h, expect_pure]
    let a := f n h.cur
    have hcmp := expect_mono_support (σ.1 n h a)
      (fun y => (M.r n h.cur a y + W (n+1) y) + (-((k:ℝ)*ε)))
      (fun y => M.r n h.cur a y + expTail M π.1 σ.1 k (n+1) (h.extend a y))
      (R+B+|-(k:ℝ)*ε|) (R+((k:ℝ)+1)*R)
      (fun y => (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (hr n h.cur a y) (hW (n+1) y))) (by simp)))
      (fun y => (abs_add_le _ _).trans (add_le_add (hr n h.cur a y)
        (expTail_abs_le M R hr hrN π.1 σ.1 k (n+1) (h.extend a y))))
      (fun y _ => by
        have hh := ih (n+1) (h.extend a y) hnext
        change W (n+1) y - (k:ℝ)*ε ≤ _ at hh
        linarith)
    rw [expect_add_const (σ.1 n h a) _ (R+B) (-((k:ℝ)*ε))
      (fun y => (abs_add_le _ _).trans (add_le_add (hr n h.cur a y) (hW (n+1) y)))] at hcmp
    have hh := hres n hn h
    change W n h.cur - ((k+1:ℕ):ℝ)*ε ≤ _
    change W n h.cur - ε ≤ expect (σ.1 n h a) (fun y => M.r n h.cur a y + W (n+1) y) at hh
    change _ ≤ expect (σ.1 n h a) (fun y => M.r n h.cur a y + expTail M π.1 σ.1 k (n+1) (h.extend a y))
    push_cast
    linarith

lemma opt_identification (M : AMDP S A) (n : ℕ) (hn : n ≤ M.N) (h : History S A n) :
    VbarStar M n h = optValue M n h.cur ∧
      (⨆ π : {π : Policy M // IsDetMarkov π}, Vbar M π.1 n h) = optValue M n h.cur := by
  classical
  obtain ⟨B, hB, hW⟩ := optValue_bounded M
  obtain ⟨R, hr, hrN⟩ := M.bounded
  haveI : Nonempty (Policy M) := ⟨(deterministic_markov_exists M).choose⟩
  haveI := adversary_nonempty M
  haveI : Nonempty {π : Policy M // IsDetMarkov π} :=
    ⟨⟨(deterministic_markov_exists M).choose, (deterministic_markov_exists M).choose_spec⟩⟩
  have habs := all_values_bounded M R hr hrN n h
  have hb : BddAbove (Set.range (fun π : Policy M => Vbar M π n h)) :=
    ⟨((M.N-n : ℕ)+1 : ℝ)*R, Set.forall_mem_range.mpr (fun π => (abs_le.mp (habs.2.2.2.1 π)).2)⟩
  have hbm : BddAbove (Set.range (fun π : {π : Policy M // IsDetMarkov π} => Vbar M π.1 n h)) :=
    ⟨((M.N-n : ℕ)+1 : ℝ)*R, Set.forall_mem_range.mpr (fun π => (abs_le.mp (habs.2.2.2.1 π.1)).2)⟩
  have hu : VbarStar M n h ≤ optValue M n h.cur := by
    apply ciSup_le
    intro π
    apply ciSup_le
    intro σ
    have ht := tail_upper_from_residual M R hr hrN (optValue M) B hW
      (optValue_terminal M) 0 σ (fun t ht g a ha => by
        simpa using opt_residual_upper M (optValue M) B hB hW (optValue_step M) σ t ht g a ha)
      π (M.N-n) n h (by omega)
    simpa only [expectedReward, mul_zero, add_zero] using ht
  have hm : (⨆ π : {π : Policy M // IsDetMarkov π}, Vbar M π.1 n h) ≤ VbarStar M n h := by
    apply ciSup_le
    intro π
    exact le_ciSup hb π.1
  have hl : optValue M n h.cur ≤ ⨆ π : {π : Policy M // IsDetMarkov π}, Vbar M π.1 n h := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let K : ℝ := (M.N-n : ℕ)
    have hK : 0 ≤ K := by dsimp [K]; positivity
    let δ : ℝ := ε/(K+1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hsmall : K*δ ≤ ε := by
      have hc : δ*(K+1)=ε := div_mul_cancel₀ ε (by positivity)
      nlinarith
    obtain ⟨π, f, σ, hπ, hf, hres⟩ := optimistic_pair M (optValue M) (optValue_step M) δ hδ
    have ht := opt_tail_lower M R hr hrN (optValue M) B hW (optValue_terminal M)
      δ π f σ hπ hres (M.N-n) n h (by omega)
    have hbs : BddAbove (Set.range (fun σ : Adversary M => expectedReward M π σ n h)) :=
      ⟨((M.N-n : ℕ)+1 : ℝ)*R, Set.forall_mem_range.mpr (fun σ => (abs_le.mp (habs.1 π σ)).2)⟩
    have hs : expectedReward M π σ n h ≤ Vbar M π n h := le_ciSup hbs σ
    have hp : Vbar M π n h ≤ ⨆ π : {π : Policy M // IsDetMarkov π}, Vbar M π.1 n h :=
      le_ciSup hbm ⟨π, f, hπ⟩
    change optValue M n h.cur - K*δ ≤ expectedReward M π σ n h at ht
    linarith
  exact ⟨le_antisymm hu (hl.trans hm), le_antisymm (hm.trans hu) hl⟩

end RobustDP.FiniteHorizon

open RobustDP.FiniteHorizon in
theorem solution {S A : Type*} [Countable S] [Countable A] (M : AMDP S A) :
    ∃ W : ℕ → S → ℝ,
      (∀ n ≤ M.N, ∀ h : History S A n, VbarStar M n h = W n h.cur) ∧
      (∀ n < M.N, ∀ π : Policy M, IsDetMarkov π →
        ∀ h h' : History S A n, h.cur = h'.cur → Vbar M π n h = Vbar M π n h') ∧
      (∀ n < M.N, ∀ h : History S A n,
        W n h.cur = ⨆ π : {π : Policy M // IsDetMarkov π}, Vbar M π.1 n h) ∧
      (∀ n < M.N, ∀ s : S,
        W n s = ⨆ a : M.Aset n s,
          ⨆ p : M.P n s a, expect (p : PMF S) (fun s' => M.r n s a s' + W (n+1) s')) := by
  refine ⟨optValue M, ?_, ?_, ?_, ?_⟩
  · intro n hn h
    exact (opt_identification M n hn h).1
  · intro n hn π hπ h h' hc
    exact (markov_values_history_independent M π hπ n hn.le h h' hc).2
  · intro n hn h
    exact (opt_identification M n hn.le h).2.symm
  · intro n hn s
    exact optValue_step M n hn s
