-- Prove2me | solution 1 for RobustDP.FiniteHorizon.eq15_pure_actions
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T19:47:31.564069+00:00
-- url     : https://prove2.me/submissions/0c49778c-7a5a-4e53-853a-a102c8e17c2b

/-
Formalization by Alexander Richard Towell (queelius), with substantial OpenAI
Codex assistance in proof construction, checking and documentation.
Mathematical source: Garud N. Iyengar, Robust dynamic programming, CORC
TR-2002-07, revised 4 May 2004, proof of Theorem 1, equation (15), p.7.
The source argument is rectangular coordinate selection followed by the fact
that an average is at most a supremum. This formalization supplies countable
summability and boundedness, epsilon selections, and all real infimum/supremum
side conditions. It uses the platform's explicitly strengthened bounded-reward
model, credited to mission captain mikedeng1. Shuze Chen's statement confirmation
is not a review of this proof. Lean and Mathlib contributors supply foundations.
No prior platform proof is used. No mathematical novelty or independent human
proof review is claimed. Supporting terminal-value and finite-value bounds are
proved here, but the full history-dependent Bellman recursion remains open.
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
end RobustDP.FiniteHorizon

open RobustDP.FiniteHorizon

theorem solution {S A : Type*} [Countable S] [Countable A] (M : AMDP S A)
    (t : ℕ) (ht : t < M.N) (s : S) (W : A → S → ℝ) (hW : ∃ B : ℝ, ∀ a s', |W a s'| ≤ B) :
    (⨆ q : {q : PMF A // ∀ a ∈ q.support, a ∈ M.Aset t s},
        ⨅ p : Selection M t s,
          ∑' a, (q.1 a).toReal * expect (p.1 a) (fun s' => M.r t s a s' + W a s')) =
      (⨆ q : {q : PMF A // ∀ a ∈ q.support, a ∈ M.Aset t s},
        ∑' a, (q.1 a).toReal *
          ⨅ p : M.P t s a, expect (p : PMF S) (fun s' => M.r t s a s' + W a s')) ∧
    (⨆ q : {q : PMF A // ∀ a ∈ q.support, a ∈ M.Aset t s},
        ∑' a, (q.1 a).toReal *
          ⨅ p : M.P t s a, expect (p : PMF S) (fun s' => M.r t s a s' + W a s')) =
      ⨆ a : M.Aset t s,
        ⨅ p : M.P t s a, expect (p : PMF S) (fun s' => M.r t s a s' + W a s') := by
  classical
  obtain ⟨R, hr, _⟩ := M.bounded
  obtain ⟨B, hW⟩ := hW
  let C : ℝ := |R| + |B|
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (abs_nonneg _)
  let F : A → PMF S → ℝ := fun a p => expect p (fun s' => M.r t s a s' + W a s')
  have hF : ∀ a p, |F a p| ≤ C := by
    intro a p
    apply expect_abs_le
    intro s'
    exact (abs_add_le _ _).trans (add_le_add ((hr t s a s').trans (le_abs_self R))
      ((hW a s').trans (le_abs_self B)))
  constructor
  · apply iSup_congr
    intro q
    exact rectangular_inf_expect (PMF.pure s) (M.Aset t s) (M.P t s)
      (M.P_nonempty t ht s) F C hC hF q.1 q.2
  · exact sup_expect_eq_pure (M.Aset t s) (M.Aset_nonempty t ht s)
      (fun a => ⨅ p : M.P t s a, F a p) C
      (fun a => inf_abs_le_empty _ C hC (fun p => hF a p))
