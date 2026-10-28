-- Prove2me | solution 1 for ObliviousRAM.LowerBound.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T16:53:22.36975+00:00
-- url     : https://prove2.me/submissions/92df49d0-f81f-4a88-a5c9-2cf030e56011

import Mathlib
import Definitions.Def_ObliviousRAM_LowerBound_Game

open ObliviousRAM.LowerBound
open Classical

noncomputable def oram_run {m : ℕ} (b : ℕ) (s : Option (State m)) (l : List (Action m)) :
    Option (State m) :=
  l.foldl (fun os act => os.bind (fun s => step b s act)) s

theorem oram_run_none {m : ℕ} (b : ℕ) (l : List (Action m)) : oram_run b none l = none := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa [oram_run, List.foldl_cons] using ih

theorem oram_run_cons {m : ℕ} (b : ℕ) (s : State m) (a : Action m) (l : List (Action m)) :
    oram_run b (some s) (a :: l) = oram_run b (step b s a) l := by
  simp [oram_run, List.foldl_cons]

theorem oram_step_hand {m : ℕ} (b : ℕ) (s s' : State m) (a : Action m)
    (h : step b s a = some s') (hs : s.hand.card ≤ b) : s'.hand.card ≤ b := by
  obtain ⟨v, h0⟩ := a
  cases h0 with
  | take =>
    simp only [step] at h
    split at h
    · simp at h
    · split_ifs at h with hc
      simp only [Option.some.injEq] at h
      subst h
      exact (Finset.card_insert_le _ _).trans (by omega)
  | place β =>
    simp only [step] at h
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    exact (Finset.card_erase_le).trans hs
  | nothing =>
    simp only [step, Option.some.injEq] at h
    subst h; exact hs

theorem oram_heads {m : ℕ} (b : ℕ) (s : State m) (v : Fin m) (hs : s.hand.card ≤ b) :
    (Finset.univ.filter fun h : Hidden m => (step b s (v, h)).isSome).card ≤ b + 2 := by
  have hsub : (Finset.univ.filter fun h : Hidden m => (step b s (v, h)).isSome) ⊆
      insert Hidden.take (insert Hidden.nothing (s.hand.image Hidden.place)) := by
    intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    cases h with
    | take => simp
    | nothing => simp
    | place β =>
      simp only [step] at hh
      split_ifs at hh with hc
      · simp [hc.2]
      · simp at hh
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_insert_le _ _).trans ?_
  have := Finset.card_insert_le Hidden.nothing (s.hand.image Hidden.place)
  have := Finset.card_image_le (s := s.hand) (f := Hidden.place)
  omega

theorem oram_main {m : ℕ} (b : ℕ) (V : List (Fin m)) :
    ∀ s : State m, s.hand.card ≤ b →
      (Finset.univ.filter fun H : Fin V.length → Hidden m =>
        (oram_run b (some s) (List.ofFn fun i => (V.get i, H i))).isSome).card ≤ (b + 2) ^ V.length := by
  induction V with
  | nil =>
    intro s _
    simp only [List.length_nil, pow_zero]
    refine (Finset.card_filter_le _ _).trans ?_
    simp
  | cons v V ih =>
    intro s hs
    set n := V.length
    let P : (Fin (n + 1) → Hidden m) → Prop := fun H =>
      (oram_run b (some s) (List.ofFn fun i => ((v :: V).get i, H i))).isSome
    have key : ∀ H : Fin (n + 1) → Hidden m, P H ↔
        (oram_run b (step b s (v, H 0)) (List.ofFn fun i : Fin n => (V.get i, H i.succ))).isSome := by
      intro H
      simp only [P, List.ofFn_succ, oram_run_cons]
      rfl
    show (Finset.univ.filter P).card ≤ (b + 2) ^ (n + 1)
    rw [Finset.card_eq_sum_card_fiberwise (f := fun H => H 0) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    -- bound each fiber
    have hfib : ∀ h : Hidden m, ((Finset.univ.filter P).filter (fun H => H 0 = h)).card ≤
        if (step b s (v, h)).isSome then (b + 2) ^ n else 0 := by
      intro h
      rcases hst : step b s (v, h) with _ | s'
      · simp only [Option.isSome_none, Bool.false_eq_true, if_false, Nat.le_zero,
          Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro H hH h0
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH
        rw [key, h0, hst, oram_run_none] at hH
        simp at hH
      · simp only [Option.isSome_some, if_true]
        have hs' := oram_step_hand b s s' _ hst hs
        refine le_trans ?_ (ih s' hs')
        apply Finset.card_le_card_of_injOn (fun H => fun i : Fin n => H i.succ)
        · intro H hH
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_setOf_eq] at hH ⊢
          have := (key H).1 hH.1
          rw [hH.2, hst] at this
          exact this
        · intro H1 hH1 H2 hH2 heq
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_setOf_eq] at hH1 hH2
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · rw [hH1.2, hH2.2]
          · exact congrFun heq j
    calc ∑ h : Hidden m, ((Finset.univ.filter P).filter (fun H => H 0 = h)).card
        ≤ ∑ h : Hidden m, (if (step b s (v, h)).isSome then (b + 2) ^ n else 0) :=
          Finset.sum_le_sum (fun h _ => hfib h)
      _ = (Finset.univ.filter fun h : Hidden m => (step b s (v, h)).isSome).card * (b + 2) ^ n := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
      _ ≤ (b + 2) * (b + 2) ^ n := Nat.mul_le_mul_right _ (oram_heads b s v hs)
      _ = (b + 2) ^ (n + 1) := by ring

theorem oram_card_hidden {b m : ℕ} (V : List (Fin m)) :
    (Finset.univ.filter fun H : Fin V.length → Hidden m =>
      Legal b (List.ofFn fun i => (V.get i, H i))).card ≤ (b + 2) ^ V.length := by
  have h := oram_main b V (initState m) (by simp [initState])
  convert h using 3 with H
  simp only [Legal, stateAfter, List.length_ofFn, oram_run]
  rw [List.take_of_length_le (by simp)]

theorem oram_run_hand {m : ℕ} (b : ℕ) (l : List (Action m)) :
    ∀ s s' : State m, s.hand.card ≤ b → oram_run b (some s) l = some s' → s'.hand.card ≤ b := by
  induction l with
  | nil =>
    intro s s' hs h
    simp only [oram_run, List.foldl_nil, Option.some.injEq] at h
    subst h; exact hs
  | cons a l ih =>
    intro s s' hs h
    rw [oram_run_cons] at h
    rcases hst : step b s a with _ | s1
    · rw [hst, oram_run_none] at h; simp at h
    · rw [hst] at h
      exact ih s1 s' (oram_step_hand b s s1 a hst hs) h

theorem oram_handAfter_card {m : ℕ} (b : ℕ) (a : List (Action m)) (k : ℕ) :
    (handAfter b a k).card ≤ b := by
  unfold handAfter
  rcases h : stateAfter b a k with _ | s
  · simp
  · simp only [Option.map_some, Option.getD_some]
    have : oram_run b (some (initState m)) (a.take k) = some s := h
    exact oram_run_hand b _ _ _ (by simp [initState]) this

theorem oram_mono_inj {t L : ℕ} (g1 g2 : Fin t → Fin L) (h1 : Monotone g1) (h2 : Monotone g2)
    (h : Finset.univ.val.map g1 = Finset.univ.val.map g2) : g1 = g2 := by
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at h
  exact List.ofFn_injective (List.Perm.eq_of_sortedLE h1.sortedLE_ofFn h2.sortedLE_ofFn h)

theorem oram_card_mono (t L : ℕ) :
    (Finset.univ.filter fun g : Fin t → Fin L => Monotone g).card ≤ Nat.multichoose L t := by
  let f : (Fin t → Fin L) → Sym (Fin L) t := fun g => ⟨Finset.univ.val.map g, by simp⟩
  have hinj : Set.InjOn f ↑(Finset.univ.filter fun g : Fin t → Fin L => Monotone g) := by
    intro g1 hg1 g2 hg2 heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg1 hg2
    apply oram_mono_inj g1 g2 hg1 hg2
    exact congrArg Subtype.val heq
  rw [← Finset.card_image_of_injOn hinj, ← Sym.card_sym_fin_eq_multichoose L t]
  exact Finset.card_le_univ _

theorem oram_card_sat {b m t : ℕ} (a : List (Action m)) :
    (Finset.univ.filter fun r : Fin t → Fin m => Satisfies b a r).card ≤
      Nat.multichoose a.length t * b ^ t := by
  set L := a.length with hL
  let J : Finset (Fin t → Fin L) := Finset.univ.filter fun g => Monotone g
  have hsub : (Finset.univ.filter fun r : Fin t → Fin m => Satisfies b a r) ⊆
      J.biUnion (fun g => Fintype.piFinset (fun i => handAfter b a (g i + 1))) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    obtain ⟨-, j, hjm, hj1, hjL, -, hjr⟩ := hr
    rw [Finset.mem_biUnion]
    refine ⟨fun i => ⟨j i - 1, by have := hj1 i; have := hjL i; omega⟩, ?_, ?_⟩
    · simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
      intro x y hxy
      have := hjm hxy
      simp only [Fin.mk_le_mk]
      omega
    · rw [Fintype.mem_piFinset]
      intro i
      have : j i - 1 + 1 = j i := by have := hj1 i; omega
      simp only
      rw [this]; exact hjr i
  calc _ ≤ (J.biUnion (fun g => Fintype.piFinset (fun i => handAfter b a (g i + 1)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ g ∈ J, (Fintype.piFinset (fun i => handAfter b a (g i + 1))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ J, b ^ t := by
        apply Finset.sum_le_sum
        intro g _
        rw [Fintype.card_piFinset]
        calc ∏ i, (handAfter b a (g i + 1)).card ≤ ∏ _i : Fin t, b :=
              Finset.prod_le_prod' (fun i _ => oram_handAfter_card b a _)
          _ = b ^ t := by simp
    _ = J.card * b ^ t := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Nat.multichoose L t * b ^ t := Nat.mul_le_mul_right _ (oram_card_mono t L)

theorem oram_reconstruct {m : ℕ} (a' : List (Action m)) (V : List (Fin m)) (hV : visible a' = V) :
    ∃ H : Fin V.length → Hidden m, List.ofFn (fun i => (V.get i, H i)) = a' := by
  subst hV
  have hlen : (visible a').length = a'.length := by simp [visible]
  refine ⟨fun i => (a'.get (i.cast hlen)).2, ?_⟩
  apply List.ext_get
  · simp [visible]
  · intro n h1 h2
    simp only [List.get_eq_getElem, List.getElem_ofFn, Fin.val_cast]
    simp [visible]

theorem oram_counting {b m t : ℕ} (P : ObliviousPlayer b m t)
    (r : Fin t → Fin m) (a : List (Action m)) (ha : a ∈ (P.play r).support) :
    m ^ t ≤ (b + 2) ^ a.length * (Nat.multichoose a.length t * b ^ t) := by
  set V := visible a with hVdef
  have hVlen : V.length = a.length := by simp [V, visible]
  -- every r' is satisfied by some run with visible sequence V
  have hcover : ∀ r' : Fin t → Fin m, ∃ H : Fin V.length → Hidden m,
      Legal b (List.ofFn fun i => (V.get i, H i)) ∧ Satisfies b (List.ofFn fun i => (V.get i, H i)) r' := by
    intro r'
    have hmem : V ∈ ((P.play r').map visible).support := by
      rw [← P.oblivious r r', PMF.support_map]
      exact ⟨a, ha, rfl⟩
    rw [PMF.support_map] at hmem
    obtain ⟨a', ha', hva'⟩ := hmem
    obtain ⟨H, hH⟩ := oram_reconstruct a' V hva'
    have hsat := P.correct r' a' ha'
    rw [← hH] at hsat
    exact ⟨H, hsat.1, hsat⟩
  let LH : Finset (Fin V.length → Hidden m) :=
    Finset.univ.filter fun H => Legal b (List.ofFn fun i => (V.get i, H i))
  have hsub : (Finset.univ : Finset (Fin t → Fin m)) ⊆ LH.biUnion (fun H =>
      Finset.univ.filter fun r' : Fin t → Fin m => Satisfies b (List.ofFn fun i => (V.get i, H i)) r') := by
    intro r' _
    obtain ⟨H, hl, hs⟩ := hcover r'
    rw [Finset.mem_biUnion]
    exact ⟨H, Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hcard
  refine hcard.trans ?_
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ H ∈ LH, (Finset.univ.filter fun r' : Fin t → Fin m =>
          Satisfies b (List.ofFn fun i => (V.get i, H i)) r').card
      ≤ ∑ _H ∈ LH, Nat.multichoose a.length t * b ^ t := by
        apply Finset.sum_le_sum
        intro H _
        have := oram_card_sat (b := b) (t := t) (List.ofFn fun i => (V.get i, H i))
        refine this.trans (le_of_eq ?_)
        rw [List.length_ofFn, hVlen]
    _ = LH.card * (Nat.multichoose a.length t * b ^ t) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (b + 2) ^ a.length * (Nat.multichoose a.length t * b ^ t) := by
        apply Nat.mul_le_mul_right
        have := oram_card_hidden (b := b) V
        refine this.trans (le_of_eq ?_)
        rw [hVlen]


theorem oram_log3 : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem oram_asym (K : ℝ) (hK : 0 ≤ K) : ∃ T : ℕ, 3 ≤ T ∧ ∀ x : ℝ, (T : ℝ) ≤ x →
    Real.log (Real.log x) + K ≤ Real.log x / 2 := by
  refine ⟨⌈Real.exp ((4 + 2 * K) ^ 2)⌉₊ + 3, by omega, ?_⟩
  intro x hx
  have hx0 : Real.exp ((4 + 2 * K) ^ 2) ≤ x := by
    have := Nat.le_ceil (Real.exp ((4 + 2 * K) ^ 2))
    push_cast at hx
    linarith
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx0
  set u := Real.log x with hu
  have hu1 : (4 + 2 * K) ^ 2 ≤ u := by
    rw [hu, Real.le_log_iff_exp_le hxpos]; exact hx0
  have hupos : 0 < u := lt_of_lt_of_le (by positivity) hu1
  set s := Real.sqrt u with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsu : s ^ 2 = u := Real.sq_sqrt hupos.le
  have hs4 : 4 + 2 * K ≤ s := by
    rw [hs]; exact Real.le_sqrt_of_sq_le hu1
  have hlogu : Real.log u ≤ 2 * s := by
    have h1 : Real.log u = 2 * Real.log s := by
      rw [← hsu, Real.log_pow]; push_cast; ring
    have h2 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
    linarith
  nlinarith

/-- From `x^t x^t ≤ (b+2)^L (L+x)^t b^t e^x` deduce the `t log t` lower bound. -/
theorem oram_lower (b : ℕ) (hb : 1 ≤ b) : ∃ T : ℕ, 3 ≤ T ∧ ∀ t : ℕ, T ≤ t → ∀ L : ℕ,
    ((t : ℝ) ^ t * (t : ℝ) ^ t ≤
      ((b : ℝ) + 2) ^ L * ((L : ℝ) + t) ^ t * (b : ℝ) ^ t * Real.exp t) →
    (1 / (2 * Real.log ((b : ℝ) + 2))) * (t : ℝ) * Real.log t ≤ (L : ℝ) := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  set K := Real.log 2 + Real.log b + 1 with hKdef
  have hK : 0 ≤ K := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hb1
    linarith
  obtain ⟨T, hT3, hT⟩ := oram_asym K hK
  refine ⟨T, hT3, ?_⟩
  intro t ht L hineq
  have hx3 : (3 : ℝ) ≤ t := by exact_mod_cast le_trans hT3 ht
  have hxT : (T : ℝ) ≤ t := by exact_mod_cast ht
  set x : ℝ := (t : ℝ) with hx
  set ℓ : ℝ := (L : ℝ) with hℓ
  have hxpos : 0 < x := by linarith
  have hℓ0 : 0 ≤ ℓ := Nat.cast_nonneg _
  have hlog3 := oram_log3
  have hlogx1 : 1 ≤ Real.log x := by
    have : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3
    linarith
  have hlb2 : 1 < Real.log ((b : ℝ) + 2) := by
    have : Real.log 3 ≤ Real.log ((b : ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  -- take logs
  have hlog : 2 * x * Real.log x ≤
      ℓ * Real.log ((b : ℝ) + 2) + x * Real.log (ℓ + x) + x * Real.log b + x := by
    have hL : 0 < x ^ t * x ^ t := by positivity
    have h := Real.log_le_log hL hineq
    have e1 : Real.log (x ^ t * x ^ t) = 2 * x * Real.log x := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; rw [hx]; ring
    have e2 : Real.log (((b : ℝ) + 2) ^ L * (ℓ + x) ^ t * (b : ℝ) ^ t * Real.exp x) =
        ℓ * Real.log ((b : ℝ) + 2) + x * Real.log (ℓ + x) + x * Real.log b + x := by
      have hb2 : (0 : ℝ) < (b : ℝ) + 2 := by linarith
      have hlx : 0 < ℓ + x := by linarith
      have hbp : (0 : ℝ) < b := by linarith
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
        Real.log_exp]
    rw [e1, e2] at h
    exact h
  have hc : 1 / (2 * Real.log ((b : ℝ) + 2)) * x * Real.log x =
      x * Real.log x / (2 * Real.log ((b : ℝ) + 2)) := by ring
  rw [hc, div_le_iff₀ (by linarith)]
  by_cases hcase : x * Real.log x ≤ ℓ
  · have : 0 ≤ x * Real.log x := by positivity
    nlinarith
  · push_neg at hcase
    have hsum : ℓ + x ≤ 2 * x * Real.log x := by nlinarith
    have hlogsum : Real.log (ℓ + x) ≤ Real.log 2 + Real.log x + Real.log (Real.log x) := by
      have := Real.log_le_log (by linarith) hsum
      rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) (by linarith)] at this
      exact this
    have hasym := hT x hxT
    have : x * Real.log (ℓ + x) ≤ x * (Real.log 2 + Real.log x + Real.log (Real.log x)) :=
      mul_le_mul_of_nonneg_left hlogsum hxpos.le
    have : x * (Real.log (Real.log x) + K) ≤ x * (Real.log x / 2) :=
      mul_le_mul_of_nonneg_left hasym hxpos.le
    rw [hKdef] at this
    nlinarith

def oram_Inv {m : ℕ} (s : State m) (W : Finset (Fin m)) : Prop :=
  ∀ β, β ∉ W → s.cell β = some β ∧ β ∉ s.hand ∧ ∀ v, v ≠ β → s.cell v ≠ some β

theorem oram_Inv_step {m : ℕ} (b : ℕ) (s s' : State m) (W : Finset (Fin m)) (a : Action m)
    (hI : oram_Inv s W) (h : step b s a = some s') : oram_Inv s' (insert a.1 W) := by
  obtain ⟨v, h0⟩ := a
  intro β hβ
  simp only [Finset.mem_insert, not_or] at hβ
  obtain ⟨hvβ, hβW⟩ := hβ
  obtain ⟨hc, hh, hother⟩ := hI β hβW
  cases h0 with
  | take =>
    simp only [step] at h
    split at h
    · simp at h
    · rename_i γ hγ
      split_ifs at h with hcard
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨?_, ?_, ?_⟩
      · simp only; rw [Function.update_of_ne hvβ]; exact hc
      · simp only [Finset.mem_insert, not_or]
        refine ⟨?_, hh⟩
        intro hγβ; subst hγβ
        exact hother v (Ne.symm hvβ) hγ
      · intro w hw
        simp only
        by_cases hwv : w = v
        · subst hwv; simp
        · rw [Function.update_of_ne hwv]; exact hother w hw
  | place γ =>
    simp only [step] at h
    split_ifs at h with hcond
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨?_, ?_, ?_⟩
    · simp only; rw [Function.update_of_ne hvβ]; exact hc
    · simp only [Finset.mem_erase, not_and]; intro _; exact hh
    · intro w hw
      simp only
      by_cases hwv : w = v
      · subst hwv
        simp only [Function.update_self, ne_eq, Option.some.injEq]
        intro hγβ; subst hγβ; exact hh hcond.2
      · rw [Function.update_of_ne hwv]; exact hother w hw
  | nothing =>
    simp only [step, Option.some.injEq] at h
    subst h
    exact ⟨hc, hh, hother⟩

theorem oram_Inv_run {m : ℕ} (b : ℕ) (l : List (Action m)) :
    ∀ (s s' : State m) (W : Finset (Fin m)), oram_Inv s W → oram_run b (some s) l = some s' →
      oram_Inv s' (W ∪ (l.map Prod.fst).toFinset) := by
  induction l with
  | nil =>
    intro s s' W hI h
    simp only [oram_run, List.foldl_nil, Option.some.injEq] at h
    subst h; simpa using hI
  | cons a l ih =>
    intro s s' W hI h
    rw [oram_run_cons] at h
    rcases hst : step b s a with _ | s1
    · rw [hst, oram_run_none] at h; simp at h
    · rw [hst] at h
      have := ih s1 s' _ (oram_Inv_step b s s1 W a hI hst) h
      intro β hβ
      apply this β
      simp only [List.map_cons, List.toFinset_cons, Finset.mem_union, Finset.mem_insert,
        not_or] at hβ ⊢
      tauto

theorem oram_hand_visible {m : ℕ} (b : ℕ) (a : List (Action m)) (j : ℕ) (β : Fin m)
    (h : β ∈ handAfter b a j) : β ∈ visible a := by
  unfold handAfter at h
  rcases hs : stateAfter b a j with _ | s
  · rw [hs] at h; simp at h
  · rw [hs] at h
    simp only [Option.map_some, Option.getD_some] at h
    have hrun : oram_run b (some (initState m)) (a.take j) = some s := hs
    have hI0 : oram_Inv (initState m) ∅ := by
      intro β' _
      refine ⟨rfl, by simp [initState], ?_⟩
      intro v hv; simp [initState, hv]
    have := oram_Inv_run b _ _ _ _ hI0 hrun β
    by_contra hnot
    have hnot' : β ∉ (∅ ∪ ((a.take j).map Prod.fst).toFinset) := by
      simp only [Finset.empty_union, List.mem_toFinset]
      intro hm
      apply hnot
      simp only [visible]
      exact (List.take_sublist j a |>.map Prod.fst).subset hm
    exact (this hnot').2.1 h

theorem solution :
    (∀ (b m t : ℕ), 1 ≤ t → ∀ P : ObliviousPlayer b m t, ∀ r, ∀ a ∈ (P.play r).support,
      m ≤ a.length) ∧
    (∀ b : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      ∀ P : ObliviousPlayer b t t, ∀ r, ∀ a ∈ (P.play r).support,
        c * (t : ℝ) * Real.log t ≤ (a.length : ℝ)) := by
  constructor
  · intro b m t ht P r a ha
    have hall : ∀ β : Fin m, β ∈ visible a := by
      intro β
      let r' : Fin t → Fin m := fun _ => β
      have hmem : visible a ∈ ((P.play r').map visible).support := by
        rw [← P.oblivious r r', PMF.support_map]
        exact ⟨a, ha, rfl⟩
      rw [PMF.support_map] at hmem
      obtain ⟨a', ha', hva'⟩ := hmem
      obtain ⟨-, j, -, -, -, -, hj⟩ := P.correct r' a' ha'
      have := oram_hand_visible b a' (j ⟨0, ht⟩) β (hj ⟨0, ht⟩)
      rwa [hva'] at this
    have hsub : (Finset.univ : Finset (Fin m)) ⊆ (visible a).toFinset := by
      intro β _; exact List.mem_toFinset.2 (hall β)
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at this
    refine this.trans ((List.toFinset_card_le _).trans ?_)
    simp [visible]
  · intro b
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · subst hb0
      refine ⟨1, one_pos, 1, ?_⟩
      intro t ht P r a ha
      exfalso
      have h := oram_counting P r a ha
      rw [zero_pow (by omega), mul_zero, mul_zero] at h
      have : 0 < t ^ t := Nat.pow_pos (by omega)
      omega
    · obtain ⟨T, hT3, hT⟩ := oram_lower b hbpos
      have hlb : 0 < Real.log ((b : ℝ) + 2) := Real.log_pos (by
        have : (0 : ℝ) ≤ b := Nat.cast_nonneg _
        linarith)
      refine ⟨1 / (2 * Real.log ((b : ℝ) + 2)), by positivity, T, ?_⟩
      intro t ht P r a ha
      apply hT t ht a.length
      set L := a.length
      have h := oram_counting P r a ha
      have hR : ((t : ℝ) ^ t) ≤ ((b : ℝ) + 2) ^ L * ((Nat.multichoose L t : ℝ) * (b : ℝ) ^ t) := by
        exact_mod_cast h
      have hmc : (Nat.multichoose L t : ℝ) ≤ ((L : ℝ) + t) ^ t / (t.factorial : ℝ) := by
        rw [Nat.multichoose_eq]
        refine (Nat.choose_le_pow_div t (L + t - 1)).trans ?_
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        have : ((L + t - 1 : ℕ) : ℝ) ≤ ((L + t : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
        push_cast at this ⊢; linarith
      have hexp : (t : ℝ) ^ t / (t.factorial : ℝ) ≤ Real.exp t :=
        Real.pow_div_factorial_le_exp _ (Nat.cast_nonneg _) t
      have hfpos : (0 : ℝ) < t.factorial := by exact_mod_cast Nat.factorial_pos t
      have hA : (0 : ℝ) ≤ ((b : ℝ) + 2) ^ L := by positivity
      have hB : (0 : ℝ) ≤ (b : ℝ) ^ t := by positivity
      have hC : (0 : ℝ) ≤ ((L : ℝ) + t) ^ t := by positivity
      have hD : (0 : ℝ) ≤ (t : ℝ) ^ t := by positivity
      calc (t : ℝ) ^ t * (t : ℝ) ^ t
          ≤ (((b : ℝ) + 2) ^ L * ((Nat.multichoose L t : ℝ) * (b : ℝ) ^ t)) * (t : ℝ) ^ t :=
            mul_le_mul_of_nonneg_right hR hD
        _ ≤ (((b : ℝ) + 2) ^ L * ((((L : ℝ) + t) ^ t / (t.factorial : ℝ)) * (b : ℝ) ^ t)) * (t : ℝ) ^ t := by
            gcongr
        _ = ((b : ℝ) + 2) ^ L * ((L : ℝ) + t) ^ t * (b : ℝ) ^ t * ((t : ℝ) ^ t / (t.factorial : ℝ)) := by
            ring
        _ ≤ ((b : ℝ) + 2) ^ L * ((L : ℝ) + t) ^ t * (b : ℝ) ^ t * Real.exp t := by
            gcongr
