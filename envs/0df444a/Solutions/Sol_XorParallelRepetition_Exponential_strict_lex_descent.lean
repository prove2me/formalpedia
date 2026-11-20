-- Prove2me | solution 1 for XorParallelRepetition.Exponential.strict_lex_descent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:02:24.583956+00:00
-- url     : https://prove2.me/submissions/f5219f50-1b1d-4408-bb43-37d6080596f3

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_Contradiction
import Definitions.Def_XorParallelRepetition_Exponential_Gluing
universe u

section
set_option autoImplicit false

namespace XorParallelRepetition.Dev.StrictLexDescent

open FreeGroup

section Stack

variable {α : Type*} [DecidableEq α]

/-- Greedy step: appending one letter to a reduced word either cancels its last letter or
keeps the word reduced. -/
theorem reduce_append_single (M : List (α × Bool)) (hM : IsReduced M) (x : α × Bool) :
    (∃ M', M = M' ++ [(x.1, !x.2)] ∧ reduce (M ++ [x]) = M') ∨
      reduce (M ++ [x]) = M ++ [x] := by
  rcases List.eq_nil_or_concat' M with rfl | ⟨M', y, rfl⟩
  · right; exact IsReduced.singleton.reduce_eq
  · by_cases hy : y = (x.1, !x.2)
    · left
      refine ⟨M', by rw [hy], ?_⟩
      subst hy
      have hstep : Red.Step (M' ++ [(x.1, !x.2)] ++ [x]) M' := by
        have := @Red.Step.not α M' [] x.1 (!x.2)
        simpa using this
      rw [reduce.Step.eq hstep]
      exact (hM.infix (List.prefix_append M' _).isInfix).reduce_eq
    · right
      apply IsReduced.reduce_eq
      have h2 : IsReduced ([y] ++ [x]) := by
        rw [List.singleton_append, isReduced_cons_cons]
        refine ⟨fun h1 => ?_, IsReduced.singleton⟩
        by_contra h2
        apply hy
        obtain ⟨y1, y2⟩ := y
        obtain ⟨x1, x2⟩ := x
        simp only at h1 h2 ⊢
        subst h1
        cases x2 <;> cases y2 <;> simp_all
      exact hM.append_overlap h2 (by simp)

/-- Reduced prefix of length `j` of the infinite letter sequence `L`. -/
def red (L : ℕ → α × Bool) (j : ℕ) : List (α × Bool) := reduce ((List.range j).map L)

/-- Reading sequence of `L`. -/
def gs (L : ℕ → α × Bool) (j : ℕ) : ℕ := (red L j).length

/-- Up-steps of the reading sequence. -/
def up (L : ℕ → α × Bool) (k : ℕ) : Bool := decide (gs L k < gs L (k + 1))

theorem red_isReduced (L : ℕ → α × Bool) (j : ℕ) : IsReduced (red L j) :=
  isReduced_iff_reduce_eq.2 reduce.idem

theorem red_succ (L : ℕ → α × Bool) (k : ℕ) :
    red L (k + 1) = reduce (red L k ++ [L k]) := by
  unfold red
  rw [List.range_succ, List.map_append, List.map_singleton, ← reduce_append_reduce_reduce,
    IsReduced.singleton.reduce_eq]

theorem step (L : ℕ → α × Bool) (k : ℕ) :
    (up L k = true ∧ red L (k + 1) = red L k ++ [L k]) ∨
    (up L k = false ∧ ∃ M', red L k = M' ++ [((L k).1, !(L k).2)] ∧ red L (k + 1) = M') := by
  rcases reduce_append_single (red L k) (red_isReduced L k) (L k) with ⟨M', h1, h2⟩ | h
  · right
    rw [red_succ]
    refine ⟨?_, M', h1, h2⟩
    have e1 : gs L (k + 1) = M'.length := by rw [gs, red_succ, h2]
    have e2 : gs L k = M'.length + 1 := by rw [gs, h1]; simp
    simp [up, e1, e2]
  · left
    rw [red_succ]
    refine ⟨?_, h⟩
    simp [up, gs, red_succ, h]

theorem gs_up (L : ℕ → α × Bool) (k : ℕ) (hk : up L k = true) : gs L (k + 1) = gs L k + 1 := by
  rcases step L k with ⟨_, h⟩ | ⟨h, _⟩
  · simp [gs, h]
  · simp [hk] at h

theorem gs_down (L : ℕ → α × Bool) (k : ℕ) (hk : up L k = false) :
    gs L (k + 1) + 1 = gs L k := by
  rcases step L k with ⟨h, _⟩ | ⟨_, M', h1, h2⟩
  · simp [hk] at h
  · simp [gs, h1, h2]

end Stack

/-- The stack of open positions for an up/down pattern `u`. -/
def pst (u : ℕ → Bool) : ℕ → List ℕ
  | 0 => []
  | k + 1 => if u k then k :: pst u k else (pst u k).tail

theorem pst_congr (u₁ u₂ : ℕ → Bool) (K : ℕ) (h : ∀ k < K, u₁ k = u₂ k) :
    ∀ j ≤ K, pst u₁ j = pst u₂ j := by
  intro j hj
  induction j with
  | zero => rfl
  | succ k ih => simp [pst, ih (by omega), h k (by omega)]

section Stack2

variable {α : Type*} [DecidableEq α]

theorem red_eq_pst (L : ℕ → α × Bool) (j : ℕ) :
    red L j = (pst (up L) j).reverse.map L := by
  induction j with
  | zero => simp [red, pst]
  | succ k ih =>
    rcases step L k with ⟨hu, h⟩ | ⟨hu, M', h1, h2⟩
    · simp [pst, hu, h, ih]
    · rw [h2]
      simp only [pst, hu, Bool.false_eq_true, if_false]
      rw [ih] at h1
      rcases hp : pst (up L) k with _ | ⟨m, t⟩
      · rw [hp] at h1; simp at h1
      · rw [hp] at h1
        simp only [List.reverse_cons, List.map_append, List.map_singleton] at h1
        simpa using (List.append_inj' h1 rfl).1.symm

theorem pst_length (L : ℕ → α × Bool) (j : ℕ) : (pst (up L) j).length = gs L j := by
  simp [gs, red_eq_pst]

theorem down_pst (L : ℕ → α × Bool) (k : ℕ) (hk : up L k = false) :
    ∃ m t, pst (up L) k = m :: t ∧ L k = ((L m).1, !(L m).2) := by
  rcases step L k with ⟨h, _⟩ | ⟨_, M', h1, _⟩
  · simp [hk] at h
  · rw [red_eq_pst] at h1
    rcases hp : pst (up L) k with _ | ⟨m, t⟩
    · rw [hp] at h1; simp at h1
    · rw [hp] at h1
      simp only [List.reverse_cons, List.map_append, List.map_singleton] at h1
      have := (List.append_inj' h1 rfl).2
      simp only [List.cons.injEq, and_true] at this
      refine ⟨m, t, rfl, ?_⟩
      rw [this]
      simp

omit [DecidableEq α] in
/-- Cancellation along a non-crossing pairing given by `pst u`. -/
theorem red_of_pst (u : ℕ → Bool) (F L' : ℕ → α × Bool) (K : ℕ)
    (hup : ∀ k < K, u k = true → L' k = F k)
    (hdown : ∀ k < K, u k = false → ∃ m t, pst u k = m :: t ∧ L' k = ((F m).1, !(F m).2)) :
    ∀ j ≤ K, Red ((List.range j).map L') ((pst u j).reverse.map F) := by
  intro j hj
  induction j with
  | zero => simp [pst]; exact Red.refl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_singleton]
    have ih := ih (by omega)
    cases hu : u k
    · obtain ⟨m, t, hp, hL⟩ := hdown k (by omega) hu
      simp only [pst, hu, Bool.false_eq_true, if_false, hp, List.tail_cons]
      rw [hp] at ih
      simp only [List.reverse_cons, List.map_append, List.map_singleton] at ih
      refine (Red.append_append ih (Red.refl (L := [L' k]))).trans ?_
      rw [hL]
      have := (@Red.Step.not α (t.reverse.map F) [] (F m).1 (F m).2).to_red
      simpa using this
    · simp only [pst, hu, if_true, List.reverse_cons, List.map_append, List.map_singleton]
      rw [hup k (by omega) hu]
      exact Red.append_append ih Red.refl

/-- Telescoping sum along the pairing. -/
theorem sum_pst {A : Type*} [CommRing A] (u : ℕ → Bool) (w σ : ℕ → A) (a : ℕ → ℕ) (K : ℕ)
    (hup : ∀ k < K, u k = true → a k = k)
    (hdown : ∀ k < K, u k = false → ∃ m t, pst u k = m :: t ∧ a k = m ∧ σ k = -σ m) :
    ∀ j ≤ K, ∑ k ∈ Finset.range j, σ k * w (a k) = ((pst u j).map (fun m => σ m * w m)).sum := by
  intro j hj
  induction j with
  | zero => simp [pst]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    cases hu : u k
    · obtain ⟨m, t, hp, ha, hs⟩ := hdown k (by omega) hu
      simp [pst, hu, hp, ha, hs]
    · simp [pst, hu, hup k (by omega) hu, add_comm]

end Stack2

theorem agree_down {β γ : Type*} [DecidableEq β] [DecidableEq γ] (L₁ : ℕ → β × Bool)
    (L₂ : ℕ → γ × Bool) (k : ℕ) (hg : ∀ j ≤ k + 1, gs L₁ j = gs L₂ j) (hk : up L₂ k = false) :
    ∃ m t, pst (up L₂) k = m :: t ∧ L₁ k = ((L₁ m).1, !(L₁ m).2) := by
  have hu : ∀ k' ≤ k, up L₁ k' = up L₂ k' := by
    intro k' hk'
    simp only [up, hg k' (by omega), hg (k' + 1) (by omega)]
  have hp : pst (up L₁) k = pst (up L₂) k :=
    pst_congr _ _ k (fun k' hk' => hu k' hk'.le) k le_rfl
  obtain ⟨m, t, h1, h2⟩ := down_pst L₁ k (by rw [hu k le_rfl, hk])
  exact ⟨m, t, hp ▸ h1, h2⟩

theorem gs_step {β : Type*} [DecidableEq β] (L : ℕ → β × Bool) (k : ℕ) :
    gs L (k + 1) = gs L k + 1 ∨ gs L (k + 1) + 1 = gs L k := by
  cases hu : up L k
  · exact Or.inr (gs_down L k hu)
  · exact Or.inl (gs_up L k hu)

theorem gs_one {β : Type*} [DecidableEq β] (L : ℕ → β × Bool) : gs L 1 = 1 := by
  simp [gs, red, IsReduced.singleton.reduce_eq]

open XorParallelRepetition.Exponential

theorem signedWord_take {β : Type*} {N : ℕ} (q : Fin N → β) (s : Fin N → Bool)
    (L : ℕ → β × Bool) (hL : ∀ k (hk : k < N), L k = (q ⟨k, hk⟩, s ⟨k, hk⟩)) (j : ℕ)
    (hj : j ≤ N) : (signedWord q s).take j = (List.range j).map L := by
  apply List.ext_getElem
  · simp [signedWord]; omega
  · intro k h1 h2
    simp only [List.getElem_take, signedWord, List.getElem_ofFn, List.getElem_map,
      List.getElem_range]
    simp at h2
    rw [hL k (by omega)]

theorem signedWord_eq {β : Type*} {N : ℕ} (q : Fin N → β) (s : Fin N → Bool)
    (L : ℕ → β × Bool) (hL : ∀ k (hk : k < N), L k = (q ⟨k, hk⟩, s ⟨k, hk⟩)) :
    signedWord q s = (List.range N).map L := by
  rw [← signedWord_take q s L hL N le_rfl, List.take_of_length_le (by simp [signedWord])]

theorem readingSeq_eq {p : ℕ} {κ : Type} {Φ : GeneralizedXorGame p κ} {N : ℕ}
    (R : OrderedContradiction Φ N) (i : κ) [DecidableEq (Φ.Q i)] (L : ℕ → Φ.Q i × Bool)
    (hL : ∀ k (hk : k < N), L k = ((R.challenge ⟨k, hk⟩).1 i, R.sign ⟨k, hk⟩)) :
    R.readingSeq i = toLex fun j : Fin (N + 1) => gs L j := by
  unfold OrderedContradiction.readingSeq
  congr 1
  funext j
  rw [signedWord_take _ _ L hL j (by omega)]
  simp only [gs, red]
  congr 2
  exact Subsingleton.elim _ _

theorem gs_end {p : ℕ} {κ : Type} {Φ : GeneralizedXorGame p κ} {N : ℕ}
    (R : OrderedContradiction Φ N) (i : κ) [DecidableEq (Φ.Q i)] (L : ℕ → Φ.Q i × Bool)
    (hL : ∀ k (hk : k < N), L k = ((R.challenge ⟨k, hk⟩).1 i, R.sign ⟨k, hk⟩)) :
    gs L N = 0 := by
  have h := R.word_cancels i
  rw [signedWord_eq _ _ L hL] at h
  simp [gs, red, reduce.eq_of_red h]

theorem omega_pow_p (p : ℕ) [Fact p.Prime] : omega p ^ p = 1 :=
  (Complex.isPrimitiveRoot_exp p (Fact.out : p.Prime).ne_zero).pow_eq_one

theorem phase_add (p : ℕ) [Fact p.Prime] (x y : ZMod p) :
    phase p (x + y) = phase p x * phase p y := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  unfold phase
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (x.val + y.val) p, pow_add, pow_mul, omega_pow_p, one_pow,
    mul_one]

theorem phase_zero (p : ℕ) : phase p 0 = 1 := by simp [phase]

theorem prod_phase (p : ℕ) [Fact p.Prime] {κ : Type*} (s : Finset κ) (f : κ → ZMod p) :
    ∏ j ∈ s, phase p (f j) = phase p (∑ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phase_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, phase_add]

theorem signValue_not (p : ℕ) (b : Bool) : signValue p (!b) = -signValue p b := by
  cases b <;> simp [signValue]

theorem main {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (Ψ : GeneralizedXorGame p ι) (N : ℕ) (hc : HasOrderedContradiction Ψ N) :
    ∃ I : Finset ι, I.Nonempty ∧ ∃ h' : HasOrderedContradiction (Ψ.glue I) N,
      heightParam (Ψ.glue I) N h' < heightParam Ψ N hc := by
  classical
  obtain ⟨R, hR⟩ : ∃ R : OrderedContradiction Ψ N, R.maxReadingSeq = heightParam Ψ N hc :=
    (wellFounded_lt (α := Lex (Fin (N + 1) → ℕ))).min_mem
      (Set.range fun R : OrderedContradiction Ψ N => R.maxReadingSeq)
      (Set.range_nonempty_iff_nonempty.2 hc)
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := by
    rcases N with _ | n
    · exact absurd (by simp) R.rhs_ne_one
    · exact ⟨n, rfl⟩
  set ec : ℕ → (∀ i, Ψ.Q i) × ZMod p := fun k => R.challenge (Fin.ofNat (n + 1) k) with hec
  set sc : ℕ → Bool := fun k => R.sign (Fin.ofNat (n + 1) k) with hsc
  have hcast : ∀ k (hk : k < n + 1), Fin.ofNat (n + 1) k = ⟨k, hk⟩ := fun k hk =>
    Fin.ext (by simp [Nat.mod_eq_of_lt hk])
  set L : ∀ i, ℕ → Ψ.Q i × Bool := fun i k => ((ec k).1 i, sc k) with hLdef
  have hL : ∀ i k (hk : k < n + 1), L i k = ((R.challenge ⟨k, hk⟩).1 i, R.sign ⟨k, hk⟩) := by
    intro i k hk
    simp only [hLdef, hec, hsc, hcast k hk]
  have hRS : ∀ i, R.readingSeq i = toLex fun j : Fin (n + 2) => gs (L i) j :=
    fun i => readingSeq_eq R i (L i) (hL i)
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty R.readingSeq
  have hmax : R.maxReadingSeq = R.readingSeq i0 := by
    rw [OrderedContradiction.maxReadingSeq, dif_pos Finset.univ_nonempty, hi0]
  set u := up (L i0) with hu_def
  set a : ℕ → ℕ := fun k => if u k then k else (pst u k).headD k with ha_def
  set I : Finset ι := Finset.univ.filter (fun i => R.readingSeq i = R.readingSeq i0) with hI
  -- the pattern of a player of `I` is that of `i0`
  have hgI : ∀ i ∈ I, ∀ j ≤ n + 1, gs (L i) j = gs (L i0) j := by
    intro i hi j hj
    simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and, hRS, toLex_inj] at hi
    exact congrFun hi ⟨j, by omega⟩
  have hfib : ∀ i ∈ I, ∀ k < n + 1, (ec (a k)).1 i = (ec k).1 i := by
    intro i hi k hk
    cases hu : u k
    · obtain ⟨m, t, hp, hLk⟩ := agree_down (L i) (L i0) k (fun j hj => hgI i hi j (by omega)) hu
      rw [← hu_def] at hp
      have ham : a k = m := by simp [ha_def, hu, hp]
      rw [ham]
      have := congrArg Prod.fst hLk
      simp only [hLdef] at this
      exact this.symm
    · simp [ha_def, hu]
  have hsign : ∀ k, u k = false → ∃ m t, pst u k = m :: t ∧ a k = m ∧ sc k = !sc m := by
    intro k hk
    obtain ⟨m, t, hp, hLk⟩ := down_pst (L i0) k hk
    rw [← hu_def] at hp
    refine ⟨m, t, hp, by simp [ha_def, hk, hp], ?_⟩
    have := congrArg Prod.snd hLk
    simpa [hLdef] using this
  have hend : pst u (n + 1) = [] := by
    rw [← List.length_eq_zero_iff, hu_def, pst_length, gs_end R i0 (L i0) (hL i0)]
  have hdownF : ∀ (β : Type u_1) (F : ℕ → β × Bool) (L' : ℕ → β × Bool),
      (∀ k, L' k = ((F (a k)).1, sc k)) → (∀ k, (F k).2 = sc k) →
      ∀ k < n + 1, u k = false → ∃ m t, pst u k = m :: t ∧ L' k = ((F m).1, !(F m).2) := by
    intro β F L' hL' hF k _ hk
    obtain ⟨m, t, hp, ham, hs⟩ := hsign k hk
    exact ⟨m, t, hp, by rw [hL', ham, hF, hs]⟩
  -- the new contradiction
  let c : Fin (n + 1) → (∀ s : {i // i ∉ I} × Bool, Ψ.Q s.1.1) × ZMod p :=
    fun j => Ψ.glueChallenge I (ec j) (ec (a j))
  have hsum : ∑ j : Fin (n + 1), signValue p (R.sign j) * (ec (a j)).2 = 0 := by
    have h1 := sum_pst u (fun m => (ec m).2) (fun k => signValue p (sc k)) a (n + 1)
      (fun k _ hk => by simp [ha_def, hk])
      (fun k _ hk => by
        obtain ⟨m, t, hp, ham, hs⟩ := hsign k hk
        exact ⟨m, t, hp, ham, by rw [hs, signValue_not]⟩) (n + 1) le_rfl
    rw [hend] at h1
    simp only [List.map_nil, List.sum_nil] at h1
    rw [← h1, ← Fin.sum_univ_eq_sum_range (fun k => signValue p (sc k) * (ec (a k)).2)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hsc]
  have hrhs : ∏ j, phase p (signValue p (R.sign j) * (c j).2) =
      ∏ j, phase p (signValue p (R.sign j) * (R.challenge j).2) := by
    rw [prod_phase, prod_phase]
    congr 1
    simp only [c, GeneralizedXorGame.glueChallenge, mul_sub, Finset.sum_sub_distrib, hsum,
      sub_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hec]
  let R' : OrderedContradiction (Ψ.glue I) (n + 1) :=
    { challenge := c
      sign := R.sign
      mem_support := by
        intro j
        show c j ∈ (Ψ.μ.bindOnSupport fun ω hω =>
          (Ψ.conditional I ω hω).map (Ψ.glueChallenge I ω)).support
        rw [PMF.mem_support_bindOnSupport_iff]
        refine ⟨ec j, R.mem_support _, ?_⟩
        rw [PMF.support_map]
        refine ⟨ec (a j), ?_, rfl⟩
        rw [GeneralizedXorGame.conditional, PMF.mem_support_filter_iff]
        exact ⟨fun i hi => hfib i hi j j.isLt, R.mem_support _⟩
      rhs_ne_one := by rw [hrhs]; exact R.rhs_ne_one
      word_cancels := by
        rintro ⟨⟨i, hi⟩, b⟩
        cases b
        · have e : (fun j : Fin (n + 1) => ((c j).1 (⟨i, hi⟩, false) : Ψ.Q i)) =
              fun j => (R.challenge j).1 i := by
            funext j
            simp only [c, GeneralizedXorGame.glueChallenge, hec, hcast j j.isLt]
            rfl
          show Red (signedWord (fun j : Fin (n + 1) => ((c j).1 (⟨i, hi⟩, false) : Ψ.Q i))
            R.sign) []
          rw [e]
          exact R.word_cancels i
        · let L' : ℕ → Ψ.Q i × Bool := fun k => ((ec (a k)).1 i, sc k)
          have hw : signedWord (fun j : Fin (n + 1) => ((c j).1 (⟨i, hi⟩, true) : Ψ.Q i))
              R.sign = (List.range (n + 1)).map L' := by
            apply signedWord_eq
            intro k hk
            simp only [L', c, GeneralizedXorGame.glueChallenge, hsc, hcast k hk]
            rfl
          show Red (signedWord (fun j : Fin (n + 1) => ((c j).1 (⟨i, hi⟩, true) : Ψ.Q i))
            R.sign) []
          rw [hw]
          have := red_of_pst u (L i) L' (n + 1)
            (fun k _ hk => by simp [L', hLdef, ha_def, hk])
            (hdownF _ (L i) L' (fun k => rfl) (fun k => rfl)) (n + 1) le_rfl
          rwa [hend] at this }
  -- strict decrease
  have hle : ∀ i, R.readingSeq i ≤ R.readingSeq i0 := fun i => by
    rw [← hi0]; exact Finset.le_sup' _ (Finset.mem_univ i)
  have hlt : ∀ i, i ∉ I → R.readingSeq i < R.readingSeq i0 := fun i hi =>
    lt_of_le_of_ne (hle i) (by simpa [hI] using hi)
  have hstrict : ∀ P, R'.readingSeq P < R.readingSeq i0 := by
    rintro ⟨⟨i, hi⟩, b⟩
    cases b
    · have e : R'.readingSeq (⟨i, hi⟩, false) = toLex fun j : Fin (n + 2) => gs (L i) j :=
        readingSeq_eq R' (⟨i, hi⟩, false) (L i) (fun k hk => by
          simp only [R', c, GeneralizedXorGame.glueChallenge, hLdef, hec, hsc, hcast k hk]
          rfl)
      rw [e, ← hRS]
      exact hlt i hi
    · let L' : ℕ → Ψ.Q i × Bool := fun k => ((ec (a k)).1 i, sc k)
      have e : R'.readingSeq (⟨i, hi⟩, true) = toLex fun j : Fin (n + 2) => gs L' j :=
        readingSeq_eq R' (⟨i, hi⟩, true) L' (fun k hk => by
          simp only [R', c, GeneralizedXorGame.glueChallenge, L', hec, hsc, hcast k hk]
          rfl)
      have h := hlt i hi
      rw [hRS, hRS] at h
      obtain ⟨b, hb1, hb2⟩ := h
      have hb1' : ∀ j < (b : ℕ), gs (L i) j = gs (L i0) j := fun j hj =>
        hb1 ⟨j, by omega⟩ (Fin.lt_def.2 hj)
      have hagree : ∀ k < (b : ℕ), L' k = L i k := by
        intro k hk
        cases hu : u k
        · by_cases hk1 : k + 1 < (b : ℕ)
          · obtain ⟨m, t, hp, hLk⟩ :=
              agree_down (L i) (L i0) k (fun j hj => hb1' j (by omega)) hu
            rw [← hu_def] at hp
            have ham : a k = m := by simp [ha_def, hu, hp]
            have := congrArg Prod.fst hLk
            simp only [hLdef] at this
            simp only [L', hLdef, ham, this]
          · exfalso
            have hd := gs_down (L i0) k hu
            have e1 := hb1' k hk
            have e2 : k + 1 = (b : ℕ) := by omega
            have hb2' : gs (L i) (k + 1) < gs (L i0) (k + 1) := by rw [e2]; exact hb2
            rcases gs_step (L i) k with h3 | h3 <;> omega
        · simp [L', hLdef, ha_def, hu]
      have hgs : ∀ j ≤ (b : ℕ), gs L' j = gs (L i) j := by
        intro j hj
        simp only [gs, red]
        congr 2
        exact List.map_congr_left fun k hk => hagree k (by simp at hk; omega)
      rw [e, hRS]
      refine ⟨b, fun j hj => ?_, ?_⟩
      · change gs L' j = gs (L i0) j
        rw [hgs j (Fin.lt_def.1 hj).le]
        exact hb1 j hj
      · change gs L' b < gs (L i0) b
        rw [hgs b le_rfl]
        exact hb2
  have hmax' : R'.maxReadingSeq < R.readingSeq i0 := by
    unfold OrderedContradiction.maxReadingSeq
    split_ifs with hne
    · exact (Finset.sup'_lt_iff hne).2 fun P _ => hstrict P
    · rw [hRS]
      have h0 : (fun _ => 0 : Fin (n + 2) → ℕ) < fun j : Fin (n + 2) => gs (L i0) (j : ℕ) := by
        rw [Pi.lt_def]
        refine ⟨fun j => Nat.zero_le _, ⟨1, by omega⟩, ?_⟩
        show 0 < gs (L i0) 1
        rw [gs_one]; exact Nat.one_pos
      exact Pi.lex_lt_of_lt wellFounded_lt h0
  refine ⟨I, (show I.Nonempty from ⟨i0, by simp [hI]⟩), Nonempty.intro R', ?_⟩
  calc heightParam (Ψ.glue I) (n + 1) (Nonempty.intro R') ≤ R'.maxReadingSeq :=
        WellFounded.min_le _ (Set.mem_range_self
          (f := fun R : OrderedContradiction (Ψ.glue I) (n + 1) => R.maxReadingSeq) R')
    _ < R.readingSeq i0 := hmax'
    _ = heightParam Ψ (n + 1) hc := by rw [← hmax, hR]

end XorParallelRepetition.Dev.StrictLexDescent

namespace XorParallelRepetition.Exponential


theorem chk_strict_lex_descent {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (Ψ : GeneralizedXorGame.{u} p ι) (N : ℕ) (h : HasOrderedContradiction Ψ N) :
    ∃ I : Finset ι, I.Nonempty ∧ ∃ h' : HasOrderedContradiction (Ψ.glue I) N,
      heightParam (Ψ.glue I) N h' < heightParam Ψ N h :=
  XorParallelRepetition.Dev.StrictLexDescent.main Ψ N h

end XorParallelRepetition.Exponential
end

theorem solution : type_of% @XorParallelRepetition.Exponential.chk_strict_lex_descent := @XorParallelRepetition.Exponential.chk_strict_lex_descent
