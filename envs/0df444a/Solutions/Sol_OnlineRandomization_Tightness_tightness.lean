-- Prove2me | solution 1 for OnlineRandomization.Tightness.tightness
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:47:27.157298+00:00
-- url     : https://prove2.me/submissions/71b44dfa-8df1-47ff-a798-7d7bb983c3f8

import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model
import Definitions.Def_OnlineRandomization_Tightness_MatesGame



namespace OnlineRandomization.Tightness

open MeasureTheory

lemma mate_ne {t : ℕ} (x : Fin t × Bool) : x ≠ mate x := by
  intro h
  have := congrArg Prod.snd h
  simp [mate] at this

lemma mate_mate {t : ℕ} (x : Fin t × Bool) : mate (mate x) = x := by
  simp [mate]

lemma integral_unif (t : ℕ) [NeZero t] (f : Fin t × Bool → ℝ) :
    ∫ ω, f ω ∂(unifAlg t).μ = (∑ ω, f ω) / (2 * (t : ℝ)) := by
  simp only [unifAlg]
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, smul_eq_mul]
  rw [← Finset.mul_sum]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  push_cast
  field_simp

lemma card_A (t : ℕ) : (Finset.univ : Finset (Fin t × Bool)).card = 2 * t := by
  simp [Finset.card_univ, Fintype.card_prod]; ring

lemma sum_pairCost (t : ℕ) (m M : ℝ) (y : Fin t × Bool) :
    ∑ ω, pairCost m M ω y = 1 + M + (2 * (t : ℝ) - 2) * m := by
  have h : ∀ ω : Fin t × Bool, pairCost m M ω y =
      m + ((if ω = y then 1 - m else 0) + (if ω = mate y then M - m else 0)) := by
    intro ω
    unfold pairCost
    by_cases h1 : ω = y
    · subst h1; simp [mate_ne ω]
    · by_cases h2 : ω = mate y
      · subst h2; simp [(mate_ne y).symm]
      · simp [h1, h2]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, card_A, nsmul_eq_mul]
  push_cast; ring

lemma opt_nonneg {t : ℕ} [NeZero t] (m M : ℝ) (hm : 1 ≤ m) (hM1 : 1 ≤ M) (r : List (Fin t × Bool)) :
    0 ≤ (matesGame t m M).opt r ∧ (r ≠ [] → 1 ≤ (matesGame t m M).opt r) := by
  have key : ∀ a : List (Fin t × Bool), a.length = r.length →
      0 ≤ matesCost m M r a ∧ (r ≠ [] → 1 ≤ matesCost m M r a) := by
    intro a hl
    match r, a, hl with
    | [], _, _ => simp [matesCost]
    | [_], _, _ => simp [matesCost]
    | _ :: _ :: _, a1 :: _, _ =>
      simp only [matesCost, pairCost]
      constructor
      · split_ifs <;> linarith
      · intro; split_ifs <;> linarith
    | _ :: _ :: _, [], hl => simp at hl
  constructor
  · apply Finset.le_inf'
    intro f _
    exact (key _ (by simp)).1
  · intro hr
    apply Finset.le_inf'
    intro f _
    exact (key _ (by simp)).2 hr

lemma costOn_const {t : ℕ} (m M : ℝ) (ω : Fin t × Bool) (x y : Fin t × Bool)
    (rest : List (Fin t × Bool)) :
    DetAlg.costOn (matesGame t m M) (fun _ => ω) (x :: y :: rest) = pairCost m M ω y := by
  simp only [DetAlg.costOn, DetAlg.answers, matesGame, List.length_cons]
  rw [List.range_succ_eq_map]
  simp [matesCost]

theorem obl_gen (t : ℕ) [NeZero t] (m M β : ℝ) (hm : 1 ≤ m) (hM : 1 ≤ M)
    (hβ : (2 * (t : ℝ) - 2) * m + M + 1 ≤ 2 * (t : ℝ) * β) :
    IsCompetitiveObl (matesGame t m M) (fun x => β * x) (unifAlg t) := by
  have ht : (1 : ℝ) ≤ t := by
    have := NeZero.pos t
    exact_mod_cast this
  have hβ1 : 1 ≤ β := by
    by_contra h
    push_neg at h
    nlinarith
  intro r
  obtain ⟨h0, h1⟩ := opt_nonneg m M hm hM r
  rw [integral_unif]
  match r, h0, h1 with
  | [], h0, _ =>
    simp [DetAlg.costOn, DetAlg.answers, matesGame, matesCost]
    positivity
  | [x], _, h1 =>
    have := h1 (by simp)
    have hc : ∀ ω : Fin t × Bool, DetAlg.costOn (matesGame t m M) ((unifAlg t).alg ω) [x] = 1 := by
      intro ω; simp [DetAlg.costOn, DetAlg.answers, matesGame, matesCost]
    simp only [hc, Finset.sum_const, card_A, nsmul_eq_mul]
    generalize (matesGame t m M).opt [x] = o at this ⊢
    have h2 : β ≤ β * o := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ 2 * t)]
  | x :: y :: rest, _, h1 =>
    have := h1 (by simp)
    simp only [unifAlg, costOn_const, sum_pairCost]
    generalize (matesGame t m M).opt (x :: y :: rest) = o at this ⊢
    have h2 : β ≤ β * o := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ 2 * t)]

theorem oblivious_core (t : ℕ) [NeZero t] (m M β : ℝ) (hm : 1 ≤ m) (hM : 1 ≤ M)
    (hβ : β = ((2 * (t : ℝ) - 2) * m + M + 1) / (2 * (t : ℝ))) :
    IsCompetitiveObl (matesGame t m M) (fun x => β * x) (unifAlg t) := by
  have ht : (0 : ℝ) < t := by
    have := NeZero.pos t
    exact_mod_cast this
  apply obl_gen t m M β hm hM
  rw [hβ]; field_simp; rfl

section online
variable {t : ℕ}

lemma playAux_prefix (G : DetAlg (Fin t × Bool) (Fin t × Bool)) (Q : OfflineAdv (Fin t × Bool) (Fin t × Bool)) :
    ∀ k r a, ∃ r' a', playAux G Q k r a = (r ++ r', a ++ a') := by
  intro k
  induction k with
  | zero => intro r a; exact ⟨[], [], by simp [playAux]⟩
  | succ k ih =>
    intro r a
    rcases h : Q.next a with _ | x
    · exact ⟨[], [], by simp [playAux, h]⟩
    · obtain ⟨r', a', h'⟩ := ih (r ++ [x]) (a ++ [G (r ++ [x])])
      exact ⟨x :: r', G (r ++ [x]) :: a', by simp [playAux, h, h']⟩

lemma play_nil (G : DetAlg (Fin t × Bool) (Fin t × Bool)) (Q : OfflineAdv (Fin t × Bool) (Fin t × Bool))
    (h : Q.depth = 0 ∨ Q.next [] = none) : play G Q = ([], []) := by
  unfold play
  rcases hd : Q.depth with _ | k
  · rfl
  · rcases h with h | h
    · omega
    · simp [playAux, h]

lemma play_one (ω : Fin t × Bool) (Q : OfflineAdv (Fin t × Bool) (Fin t × Bool)) (x : Fin t × Bool)
    (hx : Q.next [] = some x)
    (h : Q.depth = 1 ∨ (2 ≤ Q.depth ∧ Q.next [ω] = none)) : play (fun _ => ω) Q = ([x], [ω]) := by
  unfold play
  rcases hd : Q.depth with _ | _ | k
  · omega
  · simp [playAux, hx]
  · rcases h with h | ⟨_, h⟩
    · omega
    · simp [playAux, hx, h]

lemma play_two (ω : Fin t × Bool) (Q : OfflineAdv (Fin t × Bool) (Fin t × Bool)) (x y : Fin t × Bool)
    (hx : Q.next [] = some x) (hd : 2 ≤ Q.depth) (hy : Q.next [ω] = some y) :
    ∃ r' a', play (fun _ => ω) Q = (x :: y :: r', ω :: ω :: a') := by
  unfold play
  obtain ⟨k, hk⟩ : ∃ k, Q.depth = k + 2 := ⟨Q.depth - 2, by omega⟩
  rw [hk]
  obtain ⟨r', a', h'⟩ := playAux_prefix (fun _ => ω) Q k [x, y] [ω, ω]
  refine ⟨r', a', ?_⟩
  simp [playAux, hx, hy]
  simpa using h'

lemma onlineAnswers_cons (G : DetAlg (Fin t × Bool) (Fin t × Bool)) (S : OnlineAdv (Fin t × Bool) (Fin t × Bool))
    (ω : Fin t × Bool) (rest : List (Fin t × Bool)) (h : (play G S.toOfflineAdv).2 = ω :: rest) :
    ∃ l, onlineAnswers G S = S.ans [] :: l := by
  unfold onlineAnswers
  simp only [h, List.length_cons, List.range_succ_eq_map]
  simp

lemma pair_bound (m M α : ℝ) (hm : 1 ≤ m) (hmM : m ≤ M) (hα : 1 ≤ α) (hgap : α * (m - 1) ≤ M - m)
    (ω y b : Fin t × Bool) :
    pairCost m M ω y - α * pairCost m M b y ≤
      (M - α * m) + ((if ω = b then (1 - α) - (M - α * m) else 0) +
        (if ω = mate b then (M - α) - (M - α * m) else 0)) := by
  have h1 : α ≤ α * m := by nlinarith
  have h2 : α * m ≤ α * M := by nlinarith
  have hb := mate_ne b
  have hy := mate_ne y
  unfold pairCost
  by_cases e1 : ω = b
  · subst e1
    rw [if_pos rfl, if_neg hb]
    split_ifs <;> nlinarith
  · by_cases e2 : ω = mate b
    · subst e2
      rw [if_neg e1, if_pos rfl]
      by_cases f1 : b = y
      · subst f1; simp [hb.symm] <;> nlinarith
      · by_cases f2 : b = mate y
        · subst f2; simp [mate_mate, hy, hy.symm] <;> nlinarith
        · have f3 : mate b ≠ y := fun h => f2 (by rw [← h, mate_mate])
          have f4 : mate b ≠ mate y := fun h => f1 (by rw [← mate_mate b, h, mate_mate])
          simp [f1, f2, f3, f4]; nlinarith
    · rw [if_neg e1, if_neg e2]
      split_ifs <;> first | nlinarith | (subst_vars; simp_all [mate_mate])

lemma sum_g (m M α : ℝ) (b : Fin t × Bool) :
    ∑ ω : Fin t × Bool, ((M - α * m) + ((if ω = b then (1 - α) - (M - α * m) else 0) +
        (if ω = mate b then (M - α) - (M - α * m) else 0))) =
      1 + (2 * (t : ℝ) - 1) * M - α * (2 + (2 * (t : ℝ) - 2) * m) := by
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, card_A, nsmul_eq_mul]
  push_cast; ring

theorem online_gen (t : ℕ) [NeZero t] (m M α : ℝ) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hA : 1 + (2 * (t : ℝ) - 1) * M ≤ α * (2 + (2 * (t : ℝ) - 2) * m))
    (hgap : α * (m - 1) ≤ M - m) :
    IsCompetitiveOnline (matesGame t m M) (fun x => α * x) (unifAlg t) := by
  have ht : (1 : ℝ) ≤ t := by
    have := NeZero.pos t
    exact_mod_cast this
  have hα : 1 ≤ α := by
    by_contra h
    push_neg at h
    nlinarith [mul_le_mul_of_nonneg_left hm (by linarith : (0:ℝ) ≤ 2 * t - 2)]
  intro S
  rw [integral_unif, integral_unif, div_le_div_iff_of_pos_right (by positivity)]
  rw [← sub_nonpos, ← Finset.sum_sub_distrib]
  simp only [unifAlg]
  set Q := S.toOfflineAdv with hQ
  by_cases h0 : Q.depth = 0 ∨ Q.next [] = none
  · apply Finset.sum_nonpos
    intro ω _
    simp only [algCostOffline, advCostOffline, advCostOnline, ← hQ, play_nil _ Q h0, matesGame,
      matesCost]
    simp
  push_neg at h0
  obtain ⟨hd, hx⟩ := h0
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hx
  by_cases h1 : Q.depth = 1
  · apply Finset.sum_nonpos
    intro ω _
    simp only [algCostOffline, advCostOffline, advCostOnline, ← hQ,
      play_one ω Q x hx (Or.inl h1), matesGame, matesCost]
    linarith
  have h2 : 2 ≤ Q.depth := by omega
  calc _ ≤ ∑ ω : Fin t × Bool, ((M - α * m) + ((if ω = S.ans [] then (1 - α) - (M - α * m) else 0) +
        (if ω = mate (S.ans []) then (M - α) - (M - α * m) else 0))) := by
        apply Finset.sum_le_sum
        intro ω _
        have hg := pair_bound m M α hm hmM hα hgap ω ω (S.ans [])
        have hg1 : 1 - α ≤ (M - α * m) + ((if ω = S.ans [] then (1 - α) - (M - α * m) else 0) +
            (if ω = mate (S.ans []) then (M - α) - (M - α * m) else 0)) := by
          split_ifs <;> nlinarith
        rcases hy : Q.next [ω] with _ | y
        · simp only [algCostOffline, advCostOffline, advCostOnline, ← hQ,
            play_one ω Q x hx (Or.inr ⟨h2, hy⟩), matesGame, matesCost]
          linarith
        · obtain ⟨r', a', hp⟩ := play_two ω Q x y hx h2 hy
          obtain ⟨l, hl⟩ := onlineAnswers_cons (fun _ => ω) S ω (ω :: a') (by rw [← hQ, hp])
          simp only [algCostOffline, advCostOnline, ← hQ, hp, hl, matesGame, matesCost]
          exact pair_bound m M α hm hmM hα hgap ω y (S.ans [])
    _ = _ := sum_g m M α (S.ans [])
    _ ≤ 0 := by linarith

theorem online_core (t : ℕ) [NeZero t] (m M α : ℝ) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hα : α = (1 + (2 * (t : ℝ) - 1) * M) / (2 + (2 * (t : ℝ) - 2) * m))
    (hgap : α * (m - 1) ≤ M - m) :
    IsCompetitiveOnline (matesGame t m M) (fun x => α * x) (unifAlg t) := by
  have ht : (1 : ℝ) ≤ t := by
    have := NeZero.pos t
    exact_mod_cast this
  have hpos : 0 < 2 + (2 * (t : ℝ) - 2) * m := by nlinarith
  apply online_gen t m M α hm hmM _ hgap
  rw [hα, div_mul_cancel₀ _ hpos.ne']

end online

def offQ {t : ℕ} (x0 : Fin t × Bool) : OfflineAdv (Fin t × Bool) (Fin t × Bool) where
  next a := match a with
    | [] => some x0
    | [a1] => some (mate a1)
    | _ :: _ :: _ => none
  depth := 2
  stop_of_le a h := by
    match a, h with
    | _ :: _ :: _, _ => rfl

lemma play_offQ {t : ℕ} (x0 : Fin t × Bool) (G : DetAlg (Fin t × Bool) (Fin t × Bool)) :
    play G (offQ x0) = ([x0, mate (G [x0])], [G [x0], G [x0, mate (G [x0])]]) := by
  simp [play, offQ, playAux]

lemma opt_two {t : ℕ} [NeZero t] (m M : ℝ) (hm : 1 ≤ m) (hmM : m ≤ M) (x y : Fin t × Bool) :
    (matesGame t m M).opt [x, y] = 1 := by
  unfold Game.opt
  apply le_antisymm
  · have := Finset.inf'_le (s := Finset.univ) (fun a : Fin [x, y].length → Fin t × Bool =>
      (matesGame t m M).cost [x, y] (List.ofFn a)) (Finset.mem_univ (fun _ => y))
    refine this.trans (le_of_eq ?_)
    simp [matesGame, matesCost, pairCost, List.ofFn_succ]
  · apply Finset.le_inf'
    intro a _
    simp only [matesGame, List.length_cons, List.length_nil, List.ofFn_succ, matesCost, pairCost]
    split_ifs <;> linarith

theorem offline_core (t : ℕ) [NeZero t] (m M : ℝ) (hm : 1 ≤ m) (hmM : m ≤ M)
    (Ω : Type) [MeasurableSpace Ω] (K : RandAlg (Fin t × Bool) (Fin t × Bool) Ω) :
    ∃ Q : OfflineAdv (Fin t × Bool) (Fin t × Bool),
      ∫ ω, algCostOffline (matesGame t m M) (K.alg ω) Q ∂K.μ = M ∧
      ∫ ω, advCostOffline (matesGame t m M) (K.alg ω) Q ∂K.μ = 1 := by
  have := K.isProb
  refine ⟨offQ (0, false), ?_, ?_⟩
  · have : ∀ ω, algCostOffline (matesGame t m M) (K.alg ω) (offQ (0, false)) = M := by
      intro ω
      simp only [algCostOffline, play_offQ, matesGame, matesCost, pairCost]
      rw [if_neg (mate_ne _), if_pos (mate_mate _).symm]
    simp [this]
  · have : ∀ ω, advCostOffline (matesGame t m M) (K.alg ω) (offQ (0, false)) = 1 := by
      intro ω
      simp only [advCostOffline, play_offQ]
      exact opt_two m M hm hmM _ _
    simp [this]


def offQ' : OfflineAdv Unit Unit where
  next _ := none
  depth := 0
  stop_of_le _ _ := rfl

theorem tight_main (α β C : ℝ) (h1β : 1 < β) (hβα : β ≤ α) (hC : C < α * β) :
    ∃ (t : ℕ) (_ : NeZero t) (m M : ℝ), 1 ≤ m ∧ m ≤ M ∧
      (2 * (t : ℝ) - 2) * m + M + 1 ≤ 2 * (t : ℝ) * β ∧
      1 + (2 * (t : ℝ) - 1) * M ≤ α * (2 + (2 * (t : ℝ) - 2) * m) ∧
      α * (m - 1) ≤ M - m ∧ C ≤ M := by
  have hα1 : 1 < α := lt_of_lt_of_le h1β hβα
  have hP : 0 < α * β - C := by linarith
  have hαβ : 0 < α * β := by nlinarith
  set δ := min (β - 1) ((α * β - C) / (2 * α)) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
  have hδ1 : δ ≤ β - 1 := min_le_left _ _
  have hδ2 : α * δ ≤ (α * β - C) / 2 := by
    have := min_le_right (β - 1) ((α * β - C) / (2 * α))
    rw [← hδ] at this
    have h2 : α * δ ≤ α * ((α * β - C) / (2 * α)) := mul_le_mul_of_nonneg_left this (by linarith)
    rw [mul_div_assoc', mul_comm 2 α, ← div_div, mul_div_cancel_left₀ _ (by linarith)] at h2
    linarith
  obtain ⟨t, ht⟩ := exists_nat_gt ((α * β + 1) / δ + 1 + 2 * (α * β) / (α * β - C) + α / (α - 1))
  have e1 : 0 ≤ (α * β + 1) / δ := by positivity
  have e2 : 0 ≤ 2 * (α * β) / (α * β - C) := by positivity
  have e3 : 0 ≤ α / (α - 1) := div_nonneg (by linarith) (by linarith)
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have htn : t ≠ 0 := by rintro rfl; norm_num at ht1
  set k : ℝ := 2 * (t : ℝ) - 1 with hk
  have hk1 : (t : ℝ) ≤ k := by linarith
  have hkpos : 0 < k := by linarith
  have f1 : α * β + 1 < (k - 1) * δ := by
    have : (α * β + 1) / δ < k - 1 := by linarith
    rwa [div_lt_iff₀ hδpos] at this
  have f2 : 2 * (α * β) < k * (α * β - C) := by
    have : 2 * (α * β) / (α * β - C) < k := by linarith
    rwa [div_lt_iff₀ hP] at this
  have f3 : α < k * (α - 1) := by
    have : α / (α - 1) < k := by linarith
    rwa [div_lt_iff₀ (by linarith)] at this
  set m := β - δ with hm
  have hm1 : 1 ≤ m := by linarith
  set M := α * m * (k - 1) / k with hM
  have hMk : M * k = α * m * (k - 1) := by rw [hM]; field_simp
  have hαm : 0 < α * m := by nlinarith
  have hMle : M ≤ α * m := by
    have : M * k ≤ α * m * k := by rw [hMk]; nlinarith
    exact le_of_mul_le_mul_right this hkpos
  have hαmβ : α * m ≤ α * β := by nlinarith
  refine ⟨t, ⟨htn⟩, m, M, hm1, ?_, ?_, ?_, ?_, ?_⟩
  · have : m * k ≤ M * k := by rw [hMk]; nlinarith
    exact le_of_mul_le_mul_right this hkpos
  · have e : 2 * (t : ℝ) - 2 = k - 1 := by rw [hk]; ring
    have e' : 2 * (t : ℝ) = k + 1 := by rw [hk]; ring
    rw [e, e']
    nlinarith
  · have e : 2 * (t : ℝ) - 2 = k - 1 := by rw [hk]; ring
    rw [e, ← hk]
    nlinarith
  · have hgk : α * m ≤ k * (α - m) := by
      have : k * δ ≤ k * (α - m) := mul_le_mul_of_nonneg_left (by linarith) hkpos.le
      nlinarith
    have : k * (α * (m - 1)) ≤ k * (M - m) := by nlinarith
    exact le_of_mul_le_mul_left this hkpos
  · have hαm2 : (α * β + C) / 2 ≤ α * m := by
      have : α * m = α * β - α * δ := by rw [hm]; ring
      linarith
    have hk1' : 0 ≤ k - 1 := by linarith
    have : C * k ≤ M * k := by
      rw [hMk]
      nlinarith [mul_le_mul_of_nonneg_right hαm2 hk1']
    exact le_of_mul_le_mul_right this hkpos

theorem tightness_core (α β C : ℝ) (hαβ : (1 < β ∧ β ≤ α) ∨ (β = 1 ∧ α = 1)) (hC : C < α * β) :
    ∃ (R A Ω : Type) (_ : Fintype A) (_ : Nonempty A) (_ : MeasurableSpace Ω)
      (F : Game R A) (G : RandAlg R A Ω),
      IsCompetitiveOnline F (fun x => α * x) G ∧
      IsCompetitiveObl F (fun x => β * x) G ∧
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (K : RandAlg R A Ω'),
        ∃ Q : OfflineAdv R A,
          0 < ∫ ω, advCostOffline F (K.alg ω) Q ∂K.μ ∧
          C * ∫ ω, advCostOffline F (K.alg ω) Q ∂K.μ ≤
            ∫ ω, algCostOffline F (K.alg ω) Q ∂K.μ := by
  rcases hαβ with ⟨h1β, hβα⟩ | ⟨hβ, hα⟩
  · obtain ⟨t, _, m, M, hm, hmM, hobl, hA, hgap, hCM⟩ := tight_main α β C h1β hβα hC
    refine ⟨Fin t × Bool, Fin t × Bool, Fin t × Bool, inferInstance, inferInstance, inferInstance,
      matesGame t m M, unifAlg t, online_gen t m M α hm hmM hA hgap,
      obl_gen t m M β hm (by linarith) hobl, ?_⟩
    intro Ω' _ K
    obtain ⟨Q, hQ1, hQ2⟩ := offline_core t m M hm hmM Ω' K
    exact ⟨Q, by rw [hQ2]; norm_num, by rw [hQ1, hQ2]; linarith⟩
  · subst hβ hα
    let F : Game Unit Unit := ⟨fun _ _ => 1⟩
    have hopt : ∀ r, F.opt r = 1 := by
      intro r
      simp [Game.opt, F]
    let G : RandAlg Unit Unit Unit :=
      { μ := Measure.dirac ()
        isProb := inferInstance
        alg := fun _ _ => ()
        meas := fun _ _ => MeasurableSet.of_discrete }
    refine ⟨Unit, Unit, Unit, inferInstance, inferInstance, inferInstance, F, G, ?_, ?_, ?_⟩
    · intro S
      simp [algCostOffline, advCostOnline, F, G]
    · intro r
      simp [DetAlg.costOn, hopt, G, F]
    · intro Ω' _ K
      have := K.isProb
      refine ⟨offQ' , ?_, ?_⟩
      · simp [advCostOffline, hopt]
      · simp [advCostOffline, algCostOffline, hopt, F]
        linarith

end OnlineRandomization.Tightness

open OnlineRandomization.Tightness
open MeasureTheory

theorem solution (α β C : ℝ) (hαβ : (1 < β ∧ β ≤ α) ∨ (β = 1 ∧ α = 1)) (hC : C < α * β) :
    ∃ (R A Ω : Type) (_ : Fintype A) (_ : Nonempty A) (_ : MeasurableSpace Ω)
      (F : Game R A) (G : RandAlg R A Ω),
      IsCompetitiveOnline F (fun x => α * x) G ∧
      IsCompetitiveObl F (fun x => β * x) G ∧
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (K : RandAlg R A Ω'),
        ∃ Q : OfflineAdv R A,
          0 < ∫ ω, advCostOffline F (K.alg ω) Q ∂K.μ ∧
          C * ∫ ω, advCostOffline F (K.alg ω) Q ∂K.μ ≤
            ∫ ω, algCostOffline F (K.alg ω) Q ∂K.μ := by
  exact tightness_core α β C hαβ hC
