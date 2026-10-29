-- Prove2me | solution 1 for PutermanMDP.FiniteHorizon.backward_induction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:19:09.298991+00:00
-- url     : https://prove2.me/submissions/fffde6a1-99a8-499d-be35-effb917db531

import Mathlib
import Definitions.Def_PutermanMDP_FiniteHorizon_BellmanSolution

open MeasureTheory
open PutermanMDP.FiniteHorizon

theorem fh_hasSum_one {X : Type*} (p : PMF X) : HasSum (fun x => (p x).toReal) 1 := by
  have h := ENNReal.hasSum_toReal (f := fun x => p x) (PMF.tsum_coe_ne_top p)
  rw [← ENNReal.tsum_toReal_eq (fun a => PMF.apply_ne_top p a), PMF.tsum_coe] at h
  simpa using h

theorem fh_gen {X : Type*} (p : PMF X) (x : X → ℝ) (B : ℝ)
    (hB : ∀ a, p a ≠ 0 → |x a| ≤ B) :
    Summable (fun a => (p a).toReal * x a) ∧ |∑' a, (p a).toReal * x a| ≤ B := by
  have hn : ∀ a, ‖(p a).toReal * x a‖ ≤ (p a).toReal * B := by
    intro a
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    by_cases ha : p a = 0
    · rw [ha]; simp
    · exact mul_le_mul_of_nonneg_left (hB a ha) ENNReal.toReal_nonneg
  have hg : HasSum (fun a => (p a).toReal * B) B := by
    simpa using (fh_hasSum_one p).mul_right B
  refine ⟨Summable.of_norm_bounded hg.summable hn, ?_⟩
  have := tsum_of_norm_bounded hg hn
  simpa [Real.norm_eq_abs] using this

def Bd (p : PMF ℝ) (B : ℝ) : Prop := ∀ z, p z ≠ 0 → |z| ≤ B

noncomputable def Phi (p : PMF ℝ) : ℝ := ∑' z, (p z).toReal * z

theorem Phi_bound (p : PMF ℝ) (B : ℝ) (h : Bd p B) : |Phi p| ≤ B :=
  (fh_gen p id B h).2

theorem Phi_integral (p : PMF ℝ) (B : ℝ) (h : Bd p B) :
    ∫ z : ℝ, z ∂p.toMeasure = Phi p := by
  have hint : Integrable (fun z : ℝ => z) p.toMeasure := by
    refine Integrable.of_bound (C := B) measurable_id.aestronglyMeasurable ?_
    rw [ae_iff]
    have hms : MeasurableSet {a : ℝ | ¬ ‖a‖ ≤ B} := by
      have : {a : ℝ | ¬ ‖a‖ ≤ B} = (fun a : ℝ => ‖a‖) ⁻¹' Set.Ioi B := by
        ext a; simp
      rw [this]; exact measurable_norm measurableSet_Ioi
    rw [p.toMeasure_apply_eq_zero_iff hms, Set.disjoint_left]
    intro a ha hb
    exact hb (by rw [Real.norm_eq_abs]; exact h a ha)
  rw [PMF.integral_eq_tsum p _ hint]
  rfl

theorem Bd_mono (p : PMF ℝ) (B B' : ℝ) (h : Bd p B) (hB : B ≤ B') : Bd p B' :=
  fun z hz => le_trans (h z hz) hB

theorem map_add_apply (q : PMF ℝ) (c z : ℝ) : (q.map (fun w => c + w)) (c + z) = q z := by
  rw [PMF.map_apply]
  rw [tsum_eq_single z]
  · simp
  · intro b hb
    rw [if_neg]
    intro h; exact hb (by linarith)

theorem Phi_map (q : PMF ℝ) (c B : ℝ) (h : Bd q B) :
    Bd (q.map (fun w => c + w)) (|c| + B) ∧ Phi (q.map (fun w => c + w)) = c + Phi q := by
  constructor
  · intro w hw
    have e : w = c + (w - c) := by ring
    rw [e, map_add_apply] at hw
    have := h _ hw
    rw [e]
    calc |c + (w - c)| ≤ |c| + |w - c| := abs_add_le _ _
      _ ≤ _ := by linarith
  · unfold Phi
    rw [← (Equiv.addLeft c).tsum_eq]
    simp only [Equiv.coe_addLeft, map_add_apply]
    have hs : Summable (fun z => (q z).toReal * z) := (fh_gen q (fun z => z) B h).1
    have hs1 := (fh_hasSum_one q).summable.mul_right c
    simp only [mul_add]
    rw [hs1.tsum_add hs, tsum_mul_right, (fh_hasSum_one q).tsum_eq]
    simp

theorem Phi_bind {α : Type*} (p : PMF α) (f : α → PMF ℝ) (B : ℝ) (h : ∀ a, Bd (f a) B) :
    Bd (p.bind f) B ∧ Phi (p.bind f) = ∑' a, (p a).toReal * Phi (f a) := by
  constructor
  · intro w hw
    have hmem : w ∈ (p.bind f).support := hw
    rw [PMF.mem_support_bind_iff] at hmem
    obtain ⟨a, _, ha⟩ := hmem
    exact h a w ha
  · unfold Phi
    set F : α → ℝ → ℝ := fun a z => (p a * f a z).toReal * z with hF
    have hne : ∑' x : α × ℝ, p x.1 * f x.1 x.2 ≠ ⊤ := by
      rw [ENNReal.tsum_prod (f := fun a z => p a * f a z)]
      simp only [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
      exact ENNReal.one_ne_top
    have hsum : Summable (Function.uncurry F) := by
      refine Summable.of_norm_bounded
        (g := fun x : α × ℝ => (p x.1 * f x.1 x.2).toReal * B)
        ((ENNReal.summable_toReal hne).mul_right B) ?_
      rintro ⟨a, z⟩
      simp only [Function.uncurry_apply_pair, hF]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      by_cases hz : f a z = 0
      · rw [hz]; simp
      · exact mul_le_mul_of_nonneg_left (h a z hz) ENNReal.toReal_nonneg
    have lhs : ∀ z, ((p.bind f) z).toReal * z = ∑' a, F a z := by
      intro z
      rw [PMF.bind_apply, ENNReal.tsum_toReal_eq
        (fun a => ENNReal.mul_ne_top (PMF.apply_ne_top p a) (PMF.apply_ne_top (f a) z)),
        ← tsum_mul_right]
    have rhs : ∀ a, (p a).toReal * ∑' z, (f a z).toReal * z = ∑' z, F a z := by
      intro a
      rw [← tsum_mul_left]
      congr 1; funext z
      simp only [hF, ENNReal.toReal_mul]; ring
    simp only [lhs, rhs]
    exact hsum.tsum_comm

theorem s225_eval_main {S A : Type} [Countable S] (M : Model S A) (π : Policy M) (C : ℝ)
    (hC0 : 0 ≤ C) (hCr : ∀ t, t < M.horizon → ∀ s a, |M.reward t s a| ≤ C)
    (hCt : ∀ s, |M.terminal s| ≤ C) :
    ∀ k : ℕ, ∀ h : History S A, h.time + k ≤ M.horizon →
      Bd (rewardLaw M π k h) ((k + 1) * C) ∧ evaluate M π k h = Phi (rewardLaw M π k h) := by
  have hext : ∀ (h : History S A) (a : A) (j : S), (h.extend a j).time = h.time + 1 := by
    intro h a j; simp [History.extend, History.time]
  intro k
  induction k with
  | zero =>
    intro h _
    have hp : ∀ z, (PMF.pure (M.terminal h.state)) z ≠ 0 → z = M.terminal h.state := by
      intro z hz
      by_contra hne
      exact hz (PMF.pure_apply_of_ne _ _ hne)
    simp only [rewardLaw, evaluate]
    constructor
    · intro z hz
      rw [hp z hz]; simpa using hCt h.state
    · unfold Phi
      rw [tsum_eq_single (M.terminal h.state)]
      · simp
      · intro b hb; rw [PMF.pure_apply_of_ne _ _ hb]; simp
  | succ k ih =>
    intro h hh
    have hlt : h.time < M.horizon := by omega
    have IH : ∀ (a : {a // a ∈ M.available h.state}) (j : S),
        Bd (rewardLaw M π k (h.extend a.val j)) ((k + 1) * C) ∧
          evaluate M π k (h.extend a.val j) = Phi (rewardLaw M π k (h.extend a.val j)) := by
      intro a j; exact ih _ (by rw [hext]; omega)
    have hmapB : ∀ (a : {a // a ∈ M.available h.state}) (j : S),
        Bd ((rewardLaw M π k (h.extend a.val j)).map
          (fun z => M.reward h.time h.state a + z)) ((↑(k + 1) + 1) * C) := by
      intro a j
      refine Bd_mono _ _ _ (Phi_map _ _ _ (IH a j).1).1 ?_
      have := hCr h.time hlt h.state a
      push_cast; linarith
    have hinner : ∀ (a : {a // a ∈ M.available h.state}),
        Bd ((M.transition h.time h.state a).bind fun j =>
          (rewardLaw M π k (h.extend a.val j)).map
            (fun z => M.reward h.time h.state a + z)) ((↑(k + 1) + 1) * C) ∧
        Phi ((M.transition h.time h.state a).bind fun j =>
          (rewardLaw M π k (h.extend a.val j)).map
            (fun z => M.reward h.time h.state a + z)) =
        M.reward h.time h.state a + ∑' j, (M.transition h.time h.state a j).toReal *
          evaluate M π k (h.extend a.val j) := by
      intro a
      obtain ⟨hb1, hb2⟩ := Phi_bind (M.transition h.time h.state a) _ _ (hmapB a)
      refine ⟨hb1, ?_⟩
      rw [hb2]
      have e : ∀ j, Phi ((rewardLaw M π k (h.extend a.val j)).map
          (fun z => M.reward h.time h.state a + z)) =
          M.reward h.time h.state a + evaluate M π k (h.extend a.val j) := by
        intro j
        rw [(Phi_map _ _ _ (IH a j).1).2, (IH a j).2]
      simp only [e, mul_add]
      set T := M.transition h.time h.state a
      have hs1 := (fh_hasSum_one T).summable.mul_right (M.reward h.time h.state a)
      have hs2 := (fh_gen T (fun j => evaluate M π k (h.extend a.val j)) ((k + 1) * C)
        (fun j _ => by rw [(IH a j).2]; exact Phi_bound _ _ (IH a j).1)).1
      rw [hs1.tsum_add hs2, tsum_mul_right, (fh_hasSum_one T).tsum_eq, one_mul]
    have hrl : rewardLaw M π (k + 1) h = (π h).bind fun a =>
        (M.transition h.time h.state a).bind fun j =>
          (rewardLaw M π k (h.extend a.val j)).map
            (fun z => M.reward h.time h.state a + z) := rfl
    have hev : evaluate M π (k + 1) h = ∑' a, (π h a).toReal *
        (M.reward h.time h.state a +
          ∑' j, (M.transition h.time h.state a j).toReal *
            evaluate M π k (h.extend a.val j)) := rfl
    obtain ⟨hB, hP⟩ := Phi_bind (π h) _ _ (fun a => (hinner a).1)
    rw [hrl, hev]
    refine ⟨hB, ?_⟩
    rw [hP]
    congr 1; funext a
    rw [(hinner a).2]

theorem s225_total_eq {S A : Type} [Countable S] (M : Model S A) (π : Policy M) (s : S) :
    totalValue M π s = evaluate M π M.horizon (History.initial s) := by
  obtain ⟨C, hC0, hCr, hCt⟩ := M.bounded
  obtain ⟨hB, hE⟩ := s225_eval_main M π C hC0 hCr hCt M.horizon (History.initial s)
    (by simp [History.initial, History.time])
  rw [hE]
  unfold totalValue continuationValue
  have e : (History.initial s : History S A).time = 0 := rfl
  rw [e, Nat.sub_zero, Phi_integral _ _ hB]

theorem s225_pure_tsum {X : Type*} (a0 : X) (f : X → ℝ) :
    ∑' a, ((PMF.pure a0) a).toReal * f a = f a0 := by
  rw [tsum_eq_single a0]
  · simp
  · intro b hb; rw [PMF.pure_apply_of_ne _ _ hb]; simp

theorem s225_cont_eq {S A : Type} [Countable S] (M : Model S A) (π : Policy M)
    (h : History S A) (hh : h.time ≤ M.horizon) :
    evaluate M π (M.horizon - h.time) h = continuationValue M π h := by
  obtain ⟨C, hC0, hCr, hCt⟩ := M.bounded
  obtain ⟨hB, hE⟩ := s225_eval_main M π C hC0 hCr hCt (M.horizon - h.time) h (by omega)
  rw [hE]
  unfold continuationValue
  rw [Phi_integral _ _ hB]

theorem s225_core {S A : Type} [Countable S] [Nonempty S]
    (M : Model S A) (u : History S A → ℝ) (hu : BellmanSolution M u) :
    (∀ (π : Policy M) (h : History S A), h.time ≤ M.horizon → continuationValue M π h ≤ u h) ∧
    (∀ h : History S A, h.time ≤ M.horizon → u h = optimalContinuation M h) ∧
    (∀ d : HistoryPolicy M, (∀ h, h.time < M.horizon → historyScore M u h (d h) = u h) →
      ∀ h : History S A, h.time ≤ M.horizon → continuationValue M d.randomized h = u h) := by
  obtain ⟨C, hC0, hCr, hCt⟩ := M.bounded
  obtain ⟨hterm, hlub⟩ := hu
  have hext : ∀ (h : History S A) (a : A) (j : S), (h.extend a j).time = h.time + 1 := by
    intro h a j; simp [History.extend, History.time]
  -- clause 1
  have cl1 : ∀ m, ∀ h g : History S A, h.time + m = M.horizon → h.time = g.time →
      h.state = g.state → u h = u g := by
    intro m
    induction m with
    | zero =>
      intro h g h1 h2 h3
      rw [hterm h (by omega), hterm g (by omega), h3]
    | succ m ih =>
      intro h g h1 h2 h3
      obtain ⟨hp, s⟩ := h
      obtain ⟨gp, s'⟩ := g
      simp only at h3
      subst h3
      have hsc : historyScore M u ⟨hp, s⟩ = historyScore M u ⟨gp, s⟩ := by
        funext a
        unfold historyScore
        rw [h2]
        congr 1
        apply tsum_congr; intro j
        congr 1
        apply ih
        · rw [hext]; omega
        · rw [hext, hext, h2]
        · rfl
      have l1 := hlub ⟨hp, s⟩ (by omega)
      have l2 := hlub ⟨gp, s⟩ (by omega)
      rw [← hsc] at l2
      exact l1.unique l2
  have cl1' : ∀ h g : History S A, h.time ≤ M.horizon → h.time = g.time →
      h.state = g.state → u h = u g :=
    fun h g h1 => cl1 (M.horizon - h.time) h g (by omega)
  -- bound on u
  have ubd : ∀ m : ℕ, ∀ h : History S A, h.time + m = M.horizon → |u h| ≤ ((m : ℝ) + 1) * C := by
    intro m
    induction m with
    | zero => intro h hh; rw [hterm h (by omega)]; simpa using hCt h.state
    | succ m ih =>
      intro h hh
      have hlt : h.time < M.horizon := by omega
      have hsb : ∀ a, |historyScore M u h a| ≤ ((m : ℝ) + 2) * C := by
        intro a
        unfold historyScore
        have h1 := hCr h.time hlt h.state a
        have h2 := (fh_gen (M.transition h.time h.state a) (fun j => u (h.extend a.val j))
          (((m : ℝ) + 1) * C) (fun j _ => ih _ (by rw [hext]; omega))).2
        have := abs_add_le (M.reward h.time h.state a)
          (∑' j, (M.transition h.time h.state a j).toReal * u (h.extend a.val j))
        linarith
      obtain ⟨hub, hlb⟩ := hlub h hlt
      obtain ⟨a0, ha0⟩ := M.available_nonempty h.state
      have up : u h ≤ ((m : ℝ) + 2) * C :=
        hlb (by rintro _ ⟨a, rfl⟩; exact (abs_le.mp (hsb a)).2)
      have lo : historyScore M u h ⟨a0, ha0⟩ ≤ u h := hub ⟨_, rfl⟩
      have := (abs_le.mp (hsb ⟨a0, ha0⟩)).1
      rw [abs_le]; push_cast; constructor <;> linarith
  -- evaluation bound
  have ebd : ∀ (π : Policy M) (m : ℕ) (h : History S A), h.time + m ≤ M.horizon →
      |evaluate M π m h| ≤ ((m : ℝ) + 1) * C := by
    intro π m h hh
    obtain ⟨hB, hE⟩ := s225_eval_main M π C hC0 hCr hCt m h hh
    rw [hE]; exact Phi_bound _ _ hB
  -- upper bound for every policy
  have upper : ∀ (π : Policy M) (m : ℕ) (h : History S A), h.time + m = M.horizon →
      evaluate M π m h ≤ u h := by
    intro π m
    induction m with
    | zero =>
      intro h hh
      rw [hterm h (by omega)]
      exact le_refl _
    | succ m ih =>
      intro h hh
      have hlt : h.time < M.horizon := by omega
      show ∑' a, (π h a).toReal * (M.reward h.time h.state a +
        ∑' j, (M.transition h.time h.state a j).toReal * evaluate M π m (h.extend a.val j)) ≤ u h
      have step : ∀ a, M.reward h.time h.state a +
          ∑' j, (M.transition h.time h.state a j).toReal * evaluate M π m (h.extend a.val j)
          ≤ historyScore M u h a := by
        intro a
        unfold historyScore
        have hs1 := (fh_gen (M.transition h.time h.state a)
          (fun j => evaluate M π m (h.extend a.val j)) (((m : ℝ) + 1) * C)
          (fun j _ => ebd π m _ (by rw [hext]; omega))).1
        have hs2 := (fh_gen (M.transition h.time h.state a)
          (fun j => u (h.extend a.val j)) (((m : ℝ) + 1) * C)
          (fun j _ => ubd m _ (by rw [hext]; omega))).1
        have := Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left
          (ih (h.extend a.val j) (by rw [hext]; omega)) ENNReal.toReal_nonneg) hs1 hs2
        linarith
      have hXb : ∀ a, |M.reward h.time h.state a +
          ∑' j, (M.transition h.time h.state a j).toReal * evaluate M π m (h.extend a.val j)|
          ≤ C + ((m : ℝ) + 1) * C := by
        intro a
        have h1 := hCr h.time hlt h.state a
        have h2 := (fh_gen (M.transition h.time h.state a)
          (fun j => evaluate M π m (h.extend a.val j)) (((m : ℝ) + 1) * C)
          (fun j _ => ebd π m _ (by rw [hext]; omega))).2
        have := abs_add_le (M.reward h.time h.state a)
          (∑' j, (M.transition h.time h.state a j).toReal * evaluate M π m (h.extend a.val j))
        linarith
      have hsA := (fh_gen (π h) _ _ (fun a _ => hXb a)).1
      have hsB := (fh_hasSum_one (π h)).summable.mul_right (u h)
      calc _ ≤ ∑' a, (π h a).toReal * u h :=
            Summable.tsum_le_tsum (fun a => mul_le_mul_of_nonneg_left
              (le_trans (step a) ((hlub h hlt).1 ⟨a, rfl⟩)) ENNReal.toReal_nonneg) hsA hsB
        _ = u h := by rw [tsum_mul_right, (fh_hasSum_one _).tsum_eq, one_mul]
  -- canonical histories
  let canon : ℕ → S → History S A := fun t s =>
    ⟨List.replicate t (s, (M.available_nonempty s).some), s⟩
  have canon_time : ∀ t s, (canon t s).time = t := by
    intro t s; simp [canon, History.time]
  -- building a near-optimal Markov policy
  have build : ∀ δ : ℝ, 0 ≤ δ →
      (∀ t, t < M.horizon → ∀ s, ∃ a, u (canon t s) - δ ≤ historyScore M u (canon t s) a) →
      ∃ d : MarkovPolicy M, ∀ h : History S A, h.time ≤ M.horizon →
        u h - M.horizon * δ ≤ continuationValue M d.randomized h := by
    intro δ hδ sel
    classical
    let d : MarkovPolicy M := fun t s =>
      if ht : t < M.horizon then Classical.choose (sel t ht s)
      else ⟨_, (M.available_nonempty s).some_mem⟩
    have hd : ∀ h : History S A, h.time < M.horizon →
        u h - δ ≤ historyScore M u h (d h.time h.state) := by
      rintro ⟨hp, s⟩ hlt
      have hspec := Classical.choose_spec (sel _ hlt s)
      have hdd : d (History.time ⟨hp, s⟩) s = Classical.choose (sel _ hlt s) := by
        simp only [d, dif_pos hlt]
      have hl : (⟨hp, s⟩ : History S A).time = (canon (History.time ⟨hp, s⟩) s).time :=
        (canon_time _ _).symm
      have hu_eq : u ⟨hp, s⟩ = u (canon (History.time ⟨hp, s⟩) s) :=
        cl1' _ _ hlt.le hl rfl
      have hsc : historyScore M u ⟨hp, s⟩ = historyScore M u (canon (History.time ⟨hp, s⟩) s) := by
        funext a
        unfold historyScore
        have e1 : (canon (History.time ⟨hp, s⟩) s).state = s := rfl
        rw [show (canon (History.time ⟨hp, s⟩) s).time = History.time ⟨hp, s⟩ from canon_time _ _]
        congr 1
        apply tsum_congr; intro j
        congr 1
        apply cl1'
        · rw [hext]; omega
        · rw [hext, hext, canon_time]
        · rfl
      show u ⟨hp, s⟩ - δ ≤ historyScore M u ⟨hp, s⟩ (d (History.time ⟨hp, s⟩) s)
      rw [hsc, hdd, hu_eq]
      exact hspec
    have lower : ∀ m : ℕ, ∀ h : History S A, h.time + m = M.horizon →
        u h - m * δ ≤ evaluate M d.randomized m h := by
      intro m
      induction m with
      | zero =>
        intro h hh
        rw [hterm h (by omega)]
        simp [evaluate]
      | succ m ih =>
        intro h hh
        have hlt : h.time < M.horizon := by omega
        show _ ≤ ∑' a, ((PMF.pure (d h.time h.state)) a).toReal *
          (M.reward h.time h.state a + ∑' j, (M.transition h.time h.state a j).toReal *
            evaluate M d.randomized m (h.extend a.val j))
        rw [s225_pure_tsum]
        have hsc := hd h hlt
        unfold historyScore at hsc
        set a := d h.time h.state
        set T := M.transition h.time h.state a
        have hs1 := (fh_gen T (fun j => evaluate M d.randomized m (h.extend a.val j))
          (((m : ℝ) + 1) * C) (fun j _ => ebd _ m _ (by rw [hext]; omega))).1
        have hs2 := (fh_gen T (fun j => u (h.extend a.val j)) (((m : ℝ) + 1) * C)
          (fun j _ => ubd m _ (by rw [hext]; omega))).1
        have hs3 := (fh_hasSum_one T).summable.mul_right ((m : ℝ) * δ)
        have hle := Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left
          (ih (h.extend a.val j) (by rw [hext]; omega)) ENNReal.toReal_nonneg)
          (by simpa only [mul_sub] using hs2.sub hs3) hs1
        have hsplit : ∑' j, (T j).toReal * (u (h.extend a.val j) - m * δ) =
            ∑' j, (T j).toReal * u (h.extend a.val j) - m * δ := by
          simp only [mul_sub]
          rw [hs2.tsum_sub hs3, tsum_mul_right, (fh_hasSum_one T).tsum_eq, one_mul]
        rw [hsplit] at hle
        push_cast
        linarith
    refine ⟨d, fun h hh => ?_⟩
    rw [← s225_cont_eq M _ h hh]
    have := lower (M.horizon - h.time) h (by omega)
    have h1 : ((M.horizon - h.time : ℕ) : ℝ) * δ ≤ M.horizon * δ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) hδ
    linarith
  have nonemptyPol : Nonempty (Policy M) :=
    ⟨fun h => PMF.pure ⟨_, (M.available_nonempty h.state).some_mem⟩⟩
  have upper' : ∀ (π : Policy M) (h : History S A), h.time ≤ M.horizon →
      continuationValue M π h ≤ u h := by
    intro π h hh
    rw [← s225_cont_eq M π h hh]
    exact upper π _ h (by omega)
  refine ⟨upper', ?_, ?_⟩
  · intro h hh
    unfold optimalContinuation
    apply le_antisymm
    · apply le_of_forall_pos_lt_add
      intro ε hε
      have hH : (0 : ℝ) < M.horizon + 1 := by positivity
      set δ := ε / (M.horizon + 1) with hδ
      have hδ0 : 0 < δ := div_pos hε hH
      obtain ⟨d, hd⟩ := build δ hδ0.le (by
        intro t ht s
        obtain ⟨_, ⟨a, rfl⟩, h1, _⟩ :=
          (hlub (canon t s) (by rw [canon_time]; exact ht)).exists_between
          (show u (canon t s) - δ < u (canon t s) by linarith)
        exact ⟨a, h1.le⟩)
      have h1 := hd h hh
      have h3 : (M.horizon : ℝ) * δ < ε := by
        rw [hδ, mul_div_assoc', div_lt_iff₀ hH]; nlinarith
      have h4 : continuationValue M d.randomized h ≤ ⨆ π : Policy M, continuationValue M π h :=
        le_ciSup ⟨u h, by rintro _ ⟨π, rfl⟩; exact upper' π h hh⟩ _
      linarith
    · exact ciSup_le (fun π => upper' π h hh)
  · intro d hd h hh
    rw [← s225_cont_eq M _ h hh]
    have ex : ∀ m : ℕ, ∀ h : History S A, h.time + m = M.horizon →
        evaluate M d.randomized m h = u h := by
      intro m
      induction m with
      | zero =>
        intro h hh
        rw [hterm h (by omega)]
        rfl
      | succ m ih =>
        intro h hh
        have hlt : h.time < M.horizon := by omega
        show ∑' a, ((PMF.pure (d h)) a).toReal *
          (M.reward h.time h.state a + ∑' j, (M.transition h.time h.state a j).toReal *
            evaluate M d.randomized m (h.extend a.val j)) = u h
        rw [s225_pure_tsum, ← hd h hlt]
        unfold historyScore
        congr 1
        apply tsum_congr; intro j
        rw [ih _ (by rw [hext]; omega)]
    exact ex _ h (by omega)

theorem solution {S A : Type} [Countable S] [Nonempty S]
    (M : Model S A) (u : ℕ → S → ℝ) (hu : BackwardSolution M u) :
    (∀ h : History S A, h.time ≤ M.horizon →
      u h.time h.state = ⨆ π : Policy M, continuationValue M π h) ∧
    (∀ d : MarkovPolicy M,
      (∀ t, t < M.horizon → ∀ s, d t s ∈ maximizingActions M u t s) →
      IsOptimal M d.randomized ∧
      (∀ s, totalValue M d.randomized s = ⨆ π : Policy M, totalValue M π s) ∧
      (∀ h : History S A, h.time ≤ M.horizon →
        continuationValue M d.randomized h = u h.time h.state)) := by
  obtain ⟨hterm, hgr⟩ := hu
  let U : History S A → ℝ := fun h => u h.time h.state
  have hext : ∀ (h : History S A) (a : A) (j : S), (h.extend a j).time = h.time + 1 := by
    intro h a j; simp [History.extend, History.time]
  have hsc : ∀ h : History S A, historyScore M U h = stateScore M u h.time h.state := by
    intro h; funext a
    unfold historyScore stateScore
    congr 1
    apply tsum_congr; intro j
    show _ * u (h.extend a.val j).time j = _
    rw [hext]
  have hU : BellmanSolution M U := by
    refine ⟨fun h hh => ?_, fun h hh => ?_⟩
    · show u h.time h.state = _
      rw [hh]; exact hterm _
    · rw [hsc]
      exact (hgr h.time hh h.state).isLUB
  obtain ⟨h1, h2, h3⟩ := s225_core M U hU
  have h0 : ∀ s : S, (History.initial s : History S A).time ≤ M.horizon := by
    intro s; simp [History.initial, History.time]
  refine ⟨fun h hh => h2 h hh, ?_⟩
  intro d hd
  let d' : HistoryPolicy M := fun h => d h.time h.state
  have hd' : ∀ h : History S A, h.time < M.horizon → historyScore M U h (d' h) = U h := by
    intro h hh
    rw [hsc]
    obtain ⟨⟨a, ha⟩, hub⟩ := hgr h.time hh h.state
    apply le_antisymm
    · exact hub ⟨_, rfl⟩
    · show u h.time h.state ≤ _
      rw [← ha]; exact hd h.time hh h.state a
  have hcont := h3 d' hd'
  have hcont' : ∀ h : History S A, h.time ≤ M.horizon →
      continuationValue M d.randomized h = u h.time h.state := hcont
  refine ⟨?_, ?_, hcont'⟩
  · intro s ρ
    show continuationValue M ρ (History.initial s) ≤
      continuationValue M d.randomized (History.initial s)
    rw [hcont' _ (h0 s)]
    exact h1 ρ _ (h0 s)
  · intro s
    show continuationValue M d.randomized (History.initial s) =
      optimalContinuation M (History.initial s)
    rw [hcont' _ (h0 s)]
    exact h2 _ (h0 s)
