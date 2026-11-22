-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.halts_iff_compiled_observations
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T18:03:00.324651+00:00
-- url     : https://prove2.me/submissions/c35dfd22-0aa5-4259-9951-1d00bf17105e

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_4_2
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_5
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_6

namespace TreeEquivalenceHORS.Equivalence

private theorem snoc_all (P : List Choice → Choice → Prop) (v : List Choice) (e : Choice) :
    (∀ (k : ℕ) (hk : k < (v ++ [e]).length), P ((v ++ [e]).take k) (v ++ [e])[k]) ↔
      (∀ (k : ℕ) (hk : k < v.length), P (v.take k) v[k]) ∧ P v e := by
  constructor
  · exact fun h => ⟨fun k hk => by
      have hk' : k < (v ++ [e]).length := by simp; omega
      simpa only [List.take_append_of_le_length hk.le, List.getElem_append_left hk (h' := hk')] using
        h k hk', by simpa using h v.length (by simp)⟩
  · rintro ⟨h, he⟩ k hk
    by_cases hlt : k < v.length
    · simpa only [List.take_append_of_le_length hlt.le, List.getElem_append_left hlt (h' := hk)] using h k hlt
    · have : k = v.length := by simp at hk; omega
      simpa [this] using he

theorem cand_snoc (M : Machine) (v : List Choice) (e : Choice) :
    M.IsCand (v ++ [e]) ↔ M.IsCand v ∧ M.Active (M.pc v) :=
  snoc_all (fun u _ => M.Active (M.pc u)) v e

private theorem go_snoc (M : Machine) (v : List Choice) (e : Choice)
    (m : ℕ) (sw : (ℕ × ℤ × ℤ) × ℤ) :
    M.go m sw (v ++ [e]) =
      (M.delta e (M.go m sw v).1, (M.go m sw v).2 * M.phi (m + v.length) e (M.go m sw v).1) := by
  induction v generalizing m sw with
  | nil => rfl
  | cons c v ih =>
    have clock : m + 1 + v.length = m + (v.length + 1) := by omega
    simpa only [List.cons_append, Machine.go, List.length_cons, clock] using
      ih (m + 1) (M.delta c sw.1, sw.2 * M.phi m c sw.1)

theorem conf_snoc (M : Machine) (v : List Choice) (e : Choice) :
    M.conf (v ++ [e]) = M.delta e (M.conf v) := by simp [Machine.conf, go_snoc]

private theorem along_snoc (M : Machine) (v : List Choice) (e : Choice) (m i : ℕ)
    (t : StateArgs) (R : PairState) :
    M.along m i t R (v ++ [e]) =
      let s := M.along m i t R v
      (M.nextPos s.1 e, M.contArgs s.1 e s.2.1, M.pairStep (m + v.length) s.1 e s.2.2) := by
  induction v generalizing m i t R with
  | nil => rfl
  | cons c v ih =>
    have clock : m + 1 + v.length = m + (v.length + 1) := by omega
    simpa only [List.cons_append, Machine.along, List.length_cons, clock] using
      ih (m + 1) (M.nextPos i c) (M.contArgs i c t) (M.pairStep m i c R)

private theorem next_delta (M : Machine) (s : ℕ × ℤ × ℤ) (e : Choice) :
    M.nextPos s.1 e = (M.delta e s).1 := by
  cases h : M.lookup s.1 with
  | none => cases e <;> simp [Machine.nextPos, Machine.delta, h]
  | some ins => cases e <;> cases ins <;> simp [Machine.nextPos, Machine.delta, h]

private theorem along_pc (M : Machine) (v : List Choice) :
    (M.along 0 1 Machine.initArgs Machine.initPairs v).1 = M.pc v := by
  induction v using List.reverseRecOn with
  | nil => rfl
  | append_singleton v e ih =>
    simp only [along_snoc, ih, Machine.pc, conf_snoc, next_delta]

theorem pairs_snoc (M : Machine) (v : List Choice) (e : Choice) :
    M.pairsAlong (v ++ [e]) = M.pairStep v.length (M.pc v) e (M.pairsAlong v) := by
  simp [Machine.pairsAlong, along_snoc, along_pc]

theorem pc_snoc (M : Machine) (v : List Choice) (e : Choice) :
    M.pc (v ++ [e]) = M.nextPos (M.pc v) e := by simp [Machine.pc, conf_snoc, next_delta]

private theorem headConv_step {G : HORS} {t u : Tm} (step : G.HeadStep t u) (a : ℕ) (us : List Tm) :
    G.HeadConv t a us ↔ G.HeadConv u a us := by
  constructor
  · rintro ⟨s, hs, spine⟩
    rcases hs.cases_head with rfl | ⟨s', h', htail⟩
    · simp [HORS.HeadStep, HORS.headStep, spine] at step
    · have eq : u = s' := Option.some.inj (step.symm.trans h')
      exact ⟨s, eq ▸ htail, spine⟩
  · rintro ⟨s, hs, spine⟩
    exact ⟨s, hs.head step, spine⟩

theorem obs_step {G : HORS} {t u : Tm} (hs : G.HeadStep t u) (w : List ℕ) (c : ℕ) :
    G.Obs t w c ↔ G.Obs u w c := by
  cases w <;> simp only [HORS.Obs, headConv_step hs]

private def signed (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - p.2

private theorem signed_mul (p q : ℕ × ℕ) : signed (pmul p q) = signed p * signed q := by
  simp [signed, pmul]
  ring

private theorem poly_shift (m : ℕ) (x : ℤ) : Zpoly (m+1) x = (x-1) * Zpoly m (x-1) := by
  rw [Zpoly, Finset.prod_range_succ', Zpoly, mul_comm]
  simp only [Nat.cast_succ, Nat.cast_zero, zero_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  ring

private theorem signed_poly (m u v : ℕ) : signed (Cpoly m u v) = Zpoly m ((u : ℤ) - v) := by
  induction m generalizing u v with
  | zero => simp [Cpoly, Zpoly, signed]
  | succ m ih =>
    rw [Cpoly, signed_mul, ih, poly_shift]
    simp [signed, sub_add_eq_sub_sub]

private def project (i : ℕ) (R : PairState) : (ℕ × ℤ × ℤ) × ℤ :=
  ((i, signed R.A, signed R.B), signed R.W)

private theorem project_step (M : Machine) (m i : ℕ) (R : PairState) (e : Choice) :
    project (M.nextPos i e) (M.pairStep m i e R) =
      (M.delta e (project i R).1, (project i R).2 * M.phi m e (project i R).1) := by
  cases h : M.lookup i with
  | none => cases e <;> simp [project, Machine.nextPos, Machine.pairStep, Machine.delta, Machine.phi, h]
  | some ins =>
    cases ins <;> cases e <;>
      simp only [project, Machine.nextPos, Machine.pairStep, Machine.delta, Machine.phi, h,
        signed_mul, signed_poly] <;> simp [pinc, pdec, signed] <;> omega

private theorem project_along (M : Machine) (v : List Choice) (m i : ℕ) (t : StateArgs) (R : PairState) :
    let s := M.along m i t R v
    project s.1 s.2.2 = M.go m (project i R) v := by
  induction v generalizing m i t R with
  | nil => rfl
  | cons e v ih =>
    simpa only [Machine.along, Machine.go, project_step] using
      ih (m+1) (M.nextPos i e) (M.contArgs i e t) (M.pairStep m i e R)

private theorem signed_weight (M : Machine) (v : List Choice) :
    signed (M.pairsAlong v).W = M.weight v :=
  congrArg Prod.snd (project_along M v 0 1 Machine.initArgs Machine.initPairs)

private def Diff (T U : Val .o) (w : List ℕ) : Prop :=
  ∃ a b : Fin 3, a ≠ b ∧ T w = some a ∧ U w = some b

private theorem unequal_at {T U : Val .o} {w : List ℕ} (h : Diff T U w) : T w ≠ U w := by
  obtain ⟨a, b, hab, h₁, h₂⟩ := h
  simpa [h₁, h₂] using hab

private theorem diff_chains {m n : ℕ} (h : m ≠ n) :
    ∃ w, Diff (chainVal m) (chainVal n) w := by
  rcases lt_or_gt_of_ne h with h | h
  · exact ⟨List.replicate m 0, 0, 1, by decide, by simp [chainVal], by simp [chainVal, h]⟩
  · exact ⟨List.replicate n 0, 1, 0, by decide, by simp [chainVal, h], by simp [chainVal]⟩

private theorem candidate_path (side : Side) (M : Machine) (v : List Choice) (hv : M.IsCand v)
    (w : List ℕ) :
    Tmap side M 0 1 Machine.initPairs (v.map Choice.child ++ w) =
      Tmap side M v.length (M.pc v) (M.pairsAlong v) w := by
  induction v using List.reverseRecOn generalizing w with
  | nil => rfl
  | append_singleton v e ih =>
    obtain ⟨hc, ha⟩ := (cand_snoc M v e).mp hv
    rw [List.map_append, List.append_assoc, ih hc]
    cases e <;> simp [Choice.child, Tmap, ha, pc_snoc, pairs_snoc]

private theorem mismatch_of_halt {M : Machine} (h : M.Halts) :
    ∃ w, Diff (Tmap .L M 0 1 Machine.initPairs) (Tmap .R M 0 1 Machine.initPairs) w := by
  obtain ⟨v, hc, halt, hw⟩ := (lemma_4_2 M).mp h
  have hne : (M.pairsAlong v).W.1 ≠ (M.pairsAlong v).W.2 := by
    intro heq
    exact hw (by rw [← signed_weight, signed, heq, sub_self])
  obtain ⟨w, a, b, hab, h₁, h₂⟩ := diff_chains hne
  refine ⟨v.map Choice.child ++ 0 :: w, a, b, hab, ?_, ?_⟩ <;>
    rw [candidate_path _ _ _ hc] <;> simpa [Tmap, halt, Side.pick] using ‹_›

private theorem halts_of_mismatch (M : Machine) (v : List Choice) (hv : M.IsCand v)
    (w : List ℕ)
    (hd : Diff (Tmap .L M v.length (M.pc v) (M.pairsAlong v))
               (Tmap .R M v.length (M.pc v) (M.pairsAlong v)) w) : M.Halts := by
  induction w generalizing v with
  | nil => exact (unequal_at hd rfl).elim
  | cons i w ih =>
    by_cases ha : M.Active (M.pc v)
    · rcases i with _ | _ | _ | i
      · exact (unequal_at hd (by simp [Tmap, ha])).elim
      · apply ih (v ++ [.one]) ((cand_snoc ..).mpr ⟨hv, ha⟩)
        simpa [Diff, pc_snoc, pairs_snoc, Tmap, ha] using hd
      · apply ih (v ++ [.two]) ((cand_snoc ..).mpr ⟨hv, ha⟩)
        simpa [Diff, pc_snoc, pairs_snoc, Tmap, ha] using hd
      · exact (unequal_at hd (by simp [Tmap, ha])).elim
    · apply (lemma_4_2 M).mpr
      refine ⟨v, hv, ha, ?_⟩
      rw [← signed_weight]
      intro hz
      have he : (M.pairsAlong v).W.1 = (M.pairsAlong v).W.2 := by unfold signed at hz; omega
      exact unequal_at hd (by simp [Tmap, ha, Side.pick, he])

private theorem start_obs (side : Side) (M : Machine) (w : List ℕ) (a : Fin 3) :
    (compile side M).Obs (.nt (compile side M).start) w a.val ↔
      Tmap side M 0 1 Machine.initPairs w = some a := by
  have start : (compile side M).HeadStep (.nt (compile side M).start)
      (callF M 1 Machine.initArgs.toList) := rfl
  exact (obs_step start w a).trans
    (lemma_5_6 side M 0 1 _ _ ((lemma_5_5 side M).2 [] (by simp [Machine.IsCand])) w a)

/-- The observational equivalence in Theorem 5.8, including both directions of the reduction. -/
private theorem proved_here (M : Machine) :
    M.Halts ↔ ∃ (w : List ℕ) (a b : ℕ), a < sigma0.length ∧ b < sigma0.length ∧ a ≠ b ∧
      (compile .L M).Obs (.nt (compile .L M).start) w a ∧
      (compile .R M).Obs (.nt (compile .R M).start) w b := by
  constructor
  · intro halt
    obtain ⟨w, a, b, hne, h₁, h₂⟩ := mismatch_of_halt halt
    exact ⟨w, a.val, b.val, a.isLt, b.isLt, fun eq => hne (Fin.ext eq),
      (start_obs .L M w a).mpr h₁, (start_obs .R M w b).mpr h₂⟩
  · rintro ⟨w, a, b, ha, hb, hne, h₁, h₂⟩
    let x : Fin 3 := ⟨a, ha⟩
    let y : Fin 3 := ⟨b, hb⟩
    exact halts_of_mismatch M [] (by simp [Machine.IsCand]) w
      ⟨x, y, fun eq => hne (congrArg Fin.val eq), (start_obs .L M w x).mp h₁, (start_obs .R M w y).mp h₂⟩

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution (M : Machine) :
    M.Halts ↔ ∃ (w : List ℕ) (a b : ℕ), a < sigma0.length ∧ b < sigma0.length ∧ a ≠ b ∧
      (compile .L M).Obs (.nt (compile .L M).start) w a ∧
      (compile .R M).Obs (.nt (compile .R M).start) w b := proved_here M
