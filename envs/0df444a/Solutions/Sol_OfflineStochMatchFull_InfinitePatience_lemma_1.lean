-- Prove2me | solution 1 for OfflineStochMatchFull.InfinitePatience.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:17:03.402611+00:00
-- url     : https://prove2.me/submissions/2a598587-1253-4ddf-bbba-ba52aa677a38

import Mathlib
import Definitions.Def_OfflineStochMatchFull_InfinitePatience_Values

open OfflineStochMatch.InfinitePatience
open OfflineStochMatchFull.InfinitePatience

set_option linter.unusedSectionVars false

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

private lemma pmf_sum_toReal {α : Type*} [Fintype α] (μ : PMF α) :
    ∑ a : α, (μ a).toReal = 1 := by
  have hsum : ∑ a : α, μ a = 1 := by
    simpa [tsum_fintype] using μ.tsum_coe
  have htop : ∀ a ∈ (Finset.univ : Finset α), μ a ≠ ⊤ := fun a _ => μ.apply_ne_top a
  rw [← ENNReal.toReal_sum htop, hsum, ENNReal.toReal_one]

private lemma sum_pmf_pure_toReal {α : Type*} [Fintype α] [DecidableEq α]
    (a₀ : α) (f : α → ℝ) :
    ∑ a : α, (PMF.pure a₀ a).toReal * f a = f a₀ := by
  have h : ∀ a : α, (PMF.pure a₀ a).toReal * f a = if a = a₀ then f a₀ else 0 := by
    intro a
    by_cases ha : a = a₀ <;> simp [PMF.pure_apply, ha]
  simp_rw [h]
  simp

private def actVal (p : E → ℝ) (terminal V_next : ProbeHistory E → ℝ)
    (h : ProbeHistory E) : Option E → ℝ
  | none => terminal h
  | some e => (1 - p e) * V_next (h ++ [(e, false)]) + p e * V_next (h ++ [(e, true)])

private lemma policyEvalFrom_succ (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (p : E → ℝ) (π : ProbingPolicy G t)
    (terminal : ProbeHistory E → ℝ) (n : ℕ) (h : ProbeHistory E) :
    policyEvalFrom G t p π terminal (n + 1) h =
      ∑ act : Option E, (π.choose h act).toReal *
        actVal p terminal (policyEvalFrom G t p π terminal n) h act := rfl

private lemma policyEvalFrom_add (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (p : E → ℝ) (π : ProbingPolicy G t)
    (f1 f2 : ProbeHistory E → ℝ) (n : ℕ) (h : ProbeHistory E) :
    policyEvalFrom G t p π (fun h' => f1 h' + f2 h') n h =
      policyEvalFrom G t p π f1 n h + policyEvalFrom G t p π f2 n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [policyEvalFrom_succ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun act _ => ?_
    cases act with
    | none => simp [actVal]; ring
    | some e => simp [actVal, ih]; ring

private lemma policyEvalFrom_smul (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (p : E → ℝ) (π : ProbingPolicy G t)
    (c : ℝ) (f : ProbeHistory E → ℝ) (n : ℕ) (h : ProbeHistory E) :
    policyEvalFrom G t p π (fun h' => c * f h') n h =
      c * policyEvalFrom G t p π f n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [policyEvalFrom_succ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun act _ => ?_
    cases act with
    | none => simp [actVal]; ring
    | some e => simp [actVal, ih]; ring

private lemma policyEvalFrom_const (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (p : E → ℝ) (π : ProbingPolicy G t)
    (c : ℝ) (n : ℕ) (h : ProbeHistory E) :
    policyEvalFrom G t p π (fun _ => c) n h = c := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [policyEvalFrom_succ]
    have hact : ∀ act : Option E,
        actVal p (fun _ => c) (policyEvalFrom G t p π (fun _ => c) n) h act = c := by
      intro act
      cases act with
      | none => rfl
      | some e => simp [actVal, ih]; ring
    simp_rw [hact, ← Finset.sum_mul, pmf_sum_toReal, one_mul]

private lemma policyEvalFrom_sum {ι : Type*} (s : Finset ι)
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (p : E → ℝ) (π : ProbingPolicy G t)
    (f : ι → ProbeHistory E → ℝ) (n : ℕ) (h : ProbeHistory E) :
    policyEvalFrom G t p π (fun h' => ∑ i ∈ s, f i h') n h =
      ∑ i ∈ s, policyEvalFrom G t p π (f i) n h := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using policyEvalFrom_const G t p π 0 n h
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [policyEvalFrom_add, ih]

private lemma policyEvalFrom_mono_legal (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (π : ProbingPolicy G t) (f1 f2 : ProbeHistory E → ℝ)
    (hle : ∀ h', LegalHistory G t h' → f1 h' ≤ f2 h')
    (n : ℕ) (h : ProbeHistory E) (hh : LegalHistory G t h) :
    policyEvalFrom G t p π f1 n h ≤ policyEvalFrom G t p π f2 n h := by
  induction n generalizing h with
  | zero => exact hle h hh
  | succ n ih =>
    simp only [policyEvalFrom_succ]
    refine Finset.sum_le_sum fun act _ => ?_
    cases act with
    | none =>
      exact mul_le_mul_of_nonneg_left (hle h hh) ENNReal.toReal_nonneg
    | some e =>
      by_cases hleg : LegalNext G t h e
      · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        simp only [actVal]
        have h0 := ih (h ++ [(e, false)]) (LegalHistory.snoc hh hleg)
        have h1 := ih (h ++ [(e, true)]) (LegalHistory.snoc hh hleg)
        have hpe := hp e
        nlinarith
      · have hzero : π.choose h (some e) = 0 := π.legal h hh e hleg
        simp [hzero]

private def probedInd (e : E) (h : ProbeHistory E) : ℝ :=
  if e ∈ h.map Prod.fst then 1 else 0

private def matchedInd (e : E) (h : ProbeHistory E) : ℝ :=
  if e ∈ historyMatching h then 1 else 0

private lemma mem_historyMatching_iff (e : E) (h : ProbeHistory E) :
    e ∈ historyMatching h ↔ (e, true) ∈ h := by
  simp only [historyMatching, List.mem_toFinset, List.mem_map, List.mem_filter, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨hmem, rfl⟩, rfl⟩
    exact hmem
  · intro hmem
    exact ⟨e, true, ⟨hmem, rfl⟩, rfl⟩

private lemma mem_map_fst_of_mem_historyMatching {e : E} {h : ProbeHistory E}
    (hm : e ∈ historyMatching h) : e ∈ h.map Prod.fst := by
  rw [mem_historyMatching_iff] at hm
  exact List.mem_map_of_mem hm

private lemma probedInd_snoc_of_not_mem {e e' : E} {h : ProbeHistory E} (b : Bool)
    (hne : e' ∉ h.map Prod.fst) :
    probedInd e (h ++ [(e', b)]) = probedInd e h + if e = e' then 1 else 0 := by
  unfold probedInd
  by_cases hee : e = e'
  · subst hee
    simp [hne]
  · simp [List.map_append, hee]

private lemma matchedInd_snoc_of_not_mem {e e' : E} {h : ProbeHistory E} (b : Bool)
    (hne : e' ∉ h.map Prod.fst) :
    matchedInd e (h ++ [(e', b)]) = matchedInd e h + if b = true ∧ e = e' then 1 else 0 := by
  unfold matchedInd
  have hnm : e' ∉ historyMatching h := fun hm => hne (mem_map_fst_of_mem_historyMatching hm)
  have hnt : (e', true) ∉ h := (mem_historyMatching_iff e' h).not.mp hnm
  by_cases hee : e = e'
  · subst hee
    cases b <;> simp [mem_historyMatching_iff, hnt]
  · simp [mem_historyMatching_iff, hee]

private def martingaleDiff (p : E → ℝ) (e : E) (h : ProbeHistory E) : ℝ :=
  matchedInd e h - p e * probedInd e h

private lemma policyEvalFrom_martingaleDiff (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (p : E → ℝ) (π : ProbingPolicy G t) (e : E)
    (n : ℕ) (h : ProbeHistory E) (hh : LegalHistory G t h) :
    policyEvalFrom G t p π (martingaleDiff p e) n h = martingaleDiff p e h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [policyEvalFrom_succ]
    have hterm : ∀ act : Option E,
        (π.choose h act).toReal *
          actVal p (martingaleDiff p e) (policyEvalFrom G t p π (martingaleDiff p e) n) h act =
        (π.choose h act).toReal * martingaleDiff p e h := by
      intro act
      cases act with
      | none => rfl
      | some e' =>
        by_cases hleg : LegalNext G t h e'
        · congr 1
          simp only [actVal, ih (h ++ [(e', false)]) (LegalHistory.snoc hh hleg),
            ih (h ++ [(e', true)]) (LegalHistory.snoc hh hleg)]
          simp only [martingaleDiff, probedInd_snoc_of_not_mem false hleg.1,
            probedInd_snoc_of_not_mem true hleg.1,
            matchedInd_snoc_of_not_mem false hleg.1,
            matchedInd_snoc_of_not_mem true hleg.1]
          by_cases hee : e = e' <;> simp [hee] <;> ring
        · have hzero : π.choose h (some e') = 0 := π.legal h hh e' hleg
          simp [hzero]
    simp_rw [hterm, ← Finset.sum_mul, pmf_sum_toReal, one_mul]

private noncomputable def policyProbeProb (G : EdmondsMatching65.Polyhedron.Graph V E)
    (p : E → ℝ) (t : V → ℕ∞) (π : ProbingPolicy G t) (e : E) : ℝ :=
  policyEvalFrom G t p π (probedInd e) (Fintype.card E) []

private lemma policyEvalFrom_matchedInd_nil (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (p : E → ℝ) (π : ProbingPolicy G t) (e : E) :
    policyEvalFrom G t p π (matchedInd e) (Fintype.card E) [] =
      p e * policyProbeProb G p t π e := by
  have hm := policyEvalFrom_martingaleDiff G t p π e (Fintype.card E) [] LegalHistory.nil
  have hlin : policyEvalFrom G t p π (martingaleDiff p e) (Fintype.card E) [] =
      policyEvalFrom G t p π (matchedInd e) (Fintype.card E) [] -
        p e * policyProbeProb G p t π e := by
    unfold martingaleDiff policyProbeProb
    have h1 := policyEvalFrom_add G t p π (matchedInd e) (fun h' => -p e * probedInd e h')
      (Fintype.card E) []
    have h2 := policyEvalFrom_smul G t p π (-p e) (probedInd e) (Fintype.card E) []
    simp only [sub_eq_add_neg, neg_mul] at h1 h2 ⊢
    linarith
  have hnil : martingaleDiff p e [] = 0 := by
    simp [martingaleDiff, matchedInd, probedInd, historyMatching]
  linarith

private lemma policyReward_eq_lpObjective (G : EdmondsMatching65.Polyhedron.Graph V E)
    (p : E → ℝ) (t : V → ℕ∞) (w : E → ℝ) (π : ProbingPolicy G t) :
    policyReward G p t w π = lpObjective p w (policyProbeProb G p t π) := by
  unfold policyReward lpObjective
  have hterm : (fun h : ProbeHistory E => ∑ e ∈ historyMatching h, w e) =
      (fun h : ProbeHistory E => ∑ e : E, w e * matchedInd e h) := by
    ext h
    simp only [matchedInd, mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
  rw [hterm, policyEvalFrom_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [policyEvalFrom_smul, policyEvalFrom_matchedInd_nil]
  ring

private lemma sum_matchedInd_delta_le_one (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (v : V) (h : ProbeHistory E) (hh : LegalHistory G t h) :
    ∑ f ∈ delta G v, matchedInd f h ≤ 1 := by
  induction hh with
  | nil =>
    simp [matchedInd, historyMatching]
  | @snoc h e b hh hleg ih =>
    have hsum : ∑ f ∈ delta G v, matchedInd f (h ++ [(e, b)]) =
        (∑ f ∈ delta G v, matchedInd f h) +
          ∑ f ∈ delta G v, (if b = true ∧ f = e then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun f _ => ?_
      exact matchedInd_snoc_of_not_mem b hleg.1
    cases b with
    | false =>
      simp only [Bool.false_eq_true, false_and, ↓reduceIte, Finset.sum_const_zero, add_zero] at hsum
      linarith
    | true =>
      by_cases hve : v ∈ G.ends e
      · have hnotmatched : v ∉ (historyState G h).matched := (hleg.2 v hve).1
        have hzero : ∑ f ∈ delta G v, matchedInd f h = 0 := by
          refine Finset.sum_eq_zero fun f hf => ?_
          simp only [delta, Finset.mem_filter, Finset.mem_univ, true_and] at hf
          have hnm : f ∉ historyMatching h := by
            intro hfm
            apply hnotmatched
            simp only [historyState, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨f, hfm, hf⟩
          simp [matchedInd, hnm]
        have he_mem : e ∈ delta G v := by
          simp [delta, hve]
        have h1 : ∑ f ∈ delta G v, (if true = true ∧ f = e then (1 : ℝ) else 0) = 1 := by
          simp [he_mem]
        linarith
      · have h0 : ∑ f ∈ delta G v, (if true = true ∧ f = e then (1 : ℝ) else 0) = 0 := by
          refine Finset.sum_eq_zero fun f hf => ?_
          simp only [delta, Finset.mem_filter, Finset.mem_univ, true_and] at hf
          have hne : f ≠ e := fun hfe => hve (hfe ▸ hf)
          simp [hne]
        linarith

private lemma sum_probedInd_delta_eq_probes (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (v : V) (h : ProbeHistory E) (hh : LegalHistory G t h) :
    ∑ f ∈ delta G v, probedInd f h = ((historyState G h).probes v : ℝ) := by
  induction hh with
  | nil =>
    simp [probedInd, historyState]
  | @snoc h e b hh hleg ih =>
    have hsum : ∑ f ∈ delta G v, probedInd f (h ++ [(e, b)]) =
        (∑ f ∈ delta G v, probedInd f h) +
          ∑ f ∈ delta G v, (if f = e then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun f _ => ?_
      exact probedInd_snoc_of_not_mem b hleg.1
    rw [hsum, ih]
    simp only [historyState, List.filter_append, List.filter_cons, List.filter_nil,
      List.length_append]
    by_cases hve : v ∈ G.ends e
    · have he_mem : e ∈ delta G v := by simp [delta, hve]
      simp [hve, he_mem]
    · have he_nmem : e ∉ delta G v := by simp [delta, hve]
      simp [hve, he_nmem]

private lemma probes_le_patience (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (v : V) (m : ℕ) (htv : t v = m)
    (h : ProbeHistory E) (hh : LegalHistory G t h) :
    (historyState G h).probes v ≤ m := by
  induction hh with
  | nil =>
    simp [historyState]
  | @snoc h e b hh hleg ih =>
    simp only [historyState, List.filter_append, List.filter_cons, List.filter_nil,
      List.length_append]
    by_cases hve : v ∈ G.ends e
    · have hlt : ((historyState G h).probes v : ℕ∞) < t v := (hleg.2 v hve).2
      rw [htv] at hlt
      have hlt_nat : (historyState G h).probes v < m := WithTop.coe_lt_coe.mp hlt
      dsimp [historyState] at hlt_nat
      simp [hve]
      omega
    · dsimp [historyState] at ih
      simp [hve]
      exact ih

private lemma lpFeasible_policyProbeProb (G : EdmondsMatching65.Polyhedron.Graph V E)
    (p : E → ℝ) (t : V → ℕ∞) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (π : ProbingPolicy G t) :
    LPFeasible G p t (policyProbeProb G p t π) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    unfold policyProbeProb
    constructor
    · rw [← policyEvalFrom_const G t p π 0 (Fintype.card E) []]
      refine policyEvalFrom_mono_legal G t p hp π _ _ (fun h _ => ?_) (Fintype.card E) [] LegalHistory.nil
      unfold probedInd
      split_ifs <;> norm_num
    · rw [← policyEvalFrom_const G t p π 1 (Fintype.card E) []]
      refine policyEvalFrom_mono_legal G t p hp π _ _ (fun h _ => ?_) (Fintype.card E) [] LegalHistory.nil
      unfold probedInd
      split_ifs <;> norm_num
  · intro v
    have hsum : ∑ f ∈ delta G v, policyProbeProb G p t π f * p f =
        policyEvalFrom G t p π (fun h => ∑ f ∈ delta G v, matchedInd f h) (Fintype.card E) [] := by
      rw [policyEvalFrom_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [policyEvalFrom_matchedInd_nil]
      ring
    rw [hsum, ← policyEvalFrom_const G t p π 1 (Fintype.card E) []]
    refine policyEvalFrom_mono_legal G t p hp π _ _ (fun h hh => ?_) (Fintype.card E) [] LegalHistory.nil
    exact sum_matchedInd_delta_le_one G t v h hh
  · intro v m htv
    have hsum : ∑ f ∈ delta G v, policyProbeProb G p t π f =
        policyEvalFrom G t p π (fun h => ∑ f ∈ delta G v, probedInd f h) (Fintype.card E) [] := by
      unfold policyProbeProb
      rw [policyEvalFrom_sum]
    rw [hsum, ← policyEvalFrom_const G t p π (m : ℝ) (Fintype.card E) []]
    refine policyEvalFrom_mono_legal G t p hp π _ _ (fun h hh => ?_) (Fintype.card E) [] LegalHistory.nil
    rw [sum_probedInd_delta_eq_probes G t v h hh]
    exact Nat.cast_le.mpr (probes_le_patience G t v m htv h hh)

private lemma lpObjective_bounds (G : EdmondsMatching65.Polyhedron.Graph V E)
    (p w : E → ℝ) (t : V → ℕ∞) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hw : ∀ e, 0 ≤ w e)
    (y : E → ℝ) (hy : LPFeasible G p t y) :
    0 ≤ lpObjective p w y ∧ lpObjective p w y ≤ ∑ e, w e := by
  unfold lpObjective
  constructor
  · refine Finset.sum_nonneg fun e _ => ?_
    have hpe := (hp e).1
    have hye := (hy.1 e).1
    have hwe := hw e
    positivity
  · refine Finset.sum_le_sum fun e _ => ?_
    have hpe := hp e
    have hye := hy.1 e
    have hwe := hw e
    have hpy : p e * y e ≤ 1 := by nlinarith
    nlinarith

private lemma lpFeasible_zero (G : EdmondsMatching65.Polyhedron.Graph V E)
    (p : E → ℝ) (t : V → ℕ∞) : LPFeasible G p t (fun _ => 0) := by
  refine ⟨fun _ => ⟨le_refl 0, zero_le_one⟩, fun _ => by simp, fun _ m _ => by simp⟩

private lemma exists_lpMaximizer (G : EdmondsMatching65.Polyhedron.Graph V E)
    (p w : E → ℝ) (t : V → ℕ∞) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hw : ∀ e, 0 ≤ w e) :
    ∃ y, IsLPMaximizer G p t w y := by
  let S : Set (E → ℝ) := {y | LPFeasible G p t y}
  have hS_nonempty : S.Nonempty := ⟨fun _ => 0, lpFeasible_zero G p t⟩
  have hS_sub : S ⊆ Set.pi Set.univ (fun _ : E => Set.Icc (0 : ℝ) 1) := by
    intro y hy e _
    exact hy.1 e
  have hS_closed : IsClosed S := by
    have hS_eq : S =
        (⋂ f : E, {y : E → ℝ | 0 ≤ y f} ∩ {y : E → ℝ | y f ≤ 1}) ∩
        ((⋂ v : V, {y : E → ℝ | ∑ f ∈ delta G v, y f * p f ≤ 1}) ∩
         (⋂ (v : V) (m : ℕ), {y : E → ℝ | t v = (m : ℕ∞) → ∑ f ∈ delta G v, y f ≤ (m : ℝ)})) := by
      ext y
      simp [S, LPFeasible]
    rw [hS_eq]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · exact isClosed_iInter fun f => IsClosed.inter
        (isClosed_le continuous_const (continuous_apply f))
        (isClosed_le (continuous_apply f) continuous_const)
    · exact isClosed_iInter fun v => isClosed_le
        (continuous_finsetSum _ fun f _ => (continuous_apply f).mul continuous_const)
        continuous_const
    · refine isClosed_iInter fun v => isClosed_iInter fun m => ?_
      by_cases htv : t v = (m : ℕ∞)
      · simp only [htv, forall_const]
        exact isClosed_le (continuous_finsetSum _ fun f _ => continuous_apply f) continuous_const
      · simp [htv]
  have hS_compact : IsCompact S :=
    IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc) hS_closed hS_sub
  have hcont : Continuous (lpObjective p w) := by
    unfold lpObjective
    exact continuous_finsetSum _ fun e _ => continuous_const.mul (continuous_apply e)
  obtain ⟨yStar, hyStar_mem, hyStar_max⟩ :=
    hS_compact.exists_isMaxOn hS_nonempty hcont.continuousOn
  refine ⟨yStar, hyStar_mem, ?_⟩
  unfold lpValue
  have hrew_eq : lpRewards G p t w = (lpObjective p w) '' S := by
    ext r
    simp [lpRewards, S, eq_comm]
  rw [hrew_eq]
  refine le_antisymm ?_ ?_
  · refine le_csSup ?_ (Set.mem_image_of_mem _ hyStar_mem)
    refine ⟨lpObjective p w yStar, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hyStar_max hy
  · refine csSup_le (hS_nonempty.image _) ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hyStar_max hy

/-! ### Dynamic Programming for Optimal Probing Policy -/

open Classical in
private noncomputable def legalActs (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (h : ProbeHistory E) : Finset (Option E) :=
  insert none ((Finset.univ.filter fun e : E => LegalNext G t h e).map
    ⟨some, Option.some_injective E⟩)

private lemma legalActs_nonempty (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (h : ProbeHistory E) : (legalActs G t h).Nonempty :=
  Finset.insert_nonempty _ _

private lemma mem_legalActs_some (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (h : ProbeHistory E) (e : E) :
    some e ∈ legalActs G t h ↔ LegalNext G t h e := by
  simp [legalActs]

private noncomputable def optVal (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (p : E → ℝ) (terminal : ProbeHistory E → ℝ) :
    ℕ → ProbeHistory E → ℝ
  | 0, h => terminal h
  | n + 1, h =>
      (legalActs G t h).sup' (legalActs_nonempty G t h)
        (actVal p terminal (optVal G t p terminal n) h)

private noncomputable def bestAct (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (p : E → ℝ) (terminal : ProbeHistory E → ℝ)
    (n : ℕ) (h : ProbeHistory E) : Option E :=
  Classical.choose <| Finset.exists_mem_eq_sup' (legalActs_nonempty G t h)
    (actVal p terminal (optVal G t p terminal n) h)

private lemma bestAct_spec (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (p : E → ℝ) (terminal : ProbeHistory E → ℝ)
    (n : ℕ) (h : ProbeHistory E) :
    bestAct G t p terminal n h ∈ legalActs G t h ∧
      optVal G t p terminal (n + 1) h =
        actVal p terminal (optVal G t p terminal n) h (bestAct G t p terminal n h) :=
  Classical.choose_spec <| Finset.exists_mem_eq_sup' (legalActs_nonempty G t h)
    (actVal p terminal (optVal G t p terminal n) h)

private noncomputable def optPolicy (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (p : E → ℝ) (terminal : ProbeHistory E → ℝ) : ProbingPolicy G t where
  choose := fun h => PMF.pure (bestAct G t p terminal (Fintype.card E - h.length - 1) h)
  legal := by
    intro h _ e hnot
    have hmem := (bestAct_spec G t p terminal (Fintype.card E - h.length - 1) h).1
    have hne : some e ≠ bestAct G t p terminal (Fintype.card E - h.length - 1) h := by
      intro heq
      rw [← heq, mem_legalActs_some] at hmem
      exact hnot hmem
    simp [PMF.pure_apply, hne]

private lemma policyEvalFrom_le_optVal (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (π : ProbingPolicy G t) (terminal : ProbeHistory E → ℝ)
    (n : ℕ) (h : ProbeHistory E) (hh : LegalHistory G t h) :
    policyEvalFrom G t p π terminal n h ≤ optVal G t p terminal n h := by
  induction n generalizing h with
  | zero => exact le_refl _
  | succ n ih =>
    simp only [policyEvalFrom_succ]
    have hle : ∀ act : Option E,
        (π.choose h act).toReal * actVal p terminal (policyEvalFrom G t p π terminal n) h act ≤
          (π.choose h act).toReal * optVal G t p terminal (n + 1) h := by
      intro act
      cases act with
      | none =>
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        have hmem : (none : Option E) ∈ legalActs G t h := Finset.mem_insert_self _ _
        exact Finset.le_sup' (actVal p terminal (optVal G t p terminal n) h) hmem
      | some e =>
        by_cases hleg : LegalNext G t h e
        · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          have hmem : some e ∈ legalActs G t h := (mem_legalActs_some G t h e).mpr hleg
          have hsup : actVal p terminal (optVal G t p terminal n) h (some e) ≤
              optVal G t p terminal (n + 1) h :=
            Finset.le_sup' (actVal p terminal (optVal G t p terminal n) h) hmem
          have h0 := ih (h ++ [(e, false)]) (LegalHistory.snoc hh hleg)
          have h1 := ih (h ++ [(e, true)]) (LegalHistory.snoc hh hleg)
          have hpe := hp e
          simp only [actVal] at hsup ⊢
          nlinarith
        · have hzero : π.choose h (some e) = 0 := π.legal h hh e hleg
          simp [hzero]
    calc
      ∑ act : Option E, (π.choose h act).toReal *
          actVal p terminal (policyEvalFrom G t p π terminal n) h act
        ≤ ∑ act : Option E, (π.choose h act).toReal * optVal G t p terminal (n + 1) h :=
          Finset.sum_le_sum fun act _ => hle act
      _ = optVal G t p terminal (n + 1) h := by
          rw [← Finset.sum_mul, pmf_sum_toReal, one_mul]

private lemma policyEvalFrom_optPolicy_eq_optVal (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (p : E → ℝ) (terminal : ProbeHistory E → ℝ)
    (n : ℕ) (h : ProbeHistory E) (hlen : n + h.length = Fintype.card E) :
    policyEvalFrom G t p (optPolicy G t p terminal) terminal n h =
      optVal G t p terminal n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    rw [policyEvalFrom_succ]
    have hidx : Fintype.card E - h.length - 1 = n := by omega
    have hchoose : (optPolicy G t p terminal).choose h =
        PMF.pure (bestAct G t p terminal n h) := by
      simp [optPolicy, hidx]
    rw [hchoose, sum_pmf_pure_toReal, (bestAct_spec G t p terminal n h).2]
    cases bestAct G t p terminal n h with
    | none => rfl
    | some e =>
      simp only [actVal]
      have hlen0 : n + (h ++ [(e, false)]).length = Fintype.card E := by simp; omega
      have hlen1 : n + (h ++ [(e, true)]).length = Fintype.card E := by simp; omega
      rw [ih _ hlen0, ih _ hlen1]

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (p w : E → ℝ) (t : V → ℕ∞)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hw : ∀ e, 0 ≤ w e) :
    OptimaAttained G p t w ∧
    (∀ π : ProbingPolicy G t, policyReward G p t w π ≤ lpValue G p t w) ∧
    OPT G p t w ≤ lpValue G p t w := by
  have hlp_nonempty : (lpRewards G p t w).Nonempty :=
    ⟨lpObjective p w (fun _ => 0), fun _ => 0, lpFeasible_zero G p t, rfl⟩
  have hlp_bounds : ∀ y, LPFeasible G p t y →
      0 ≤ lpObjective p w y ∧ lpObjective p w y ≤ ∑ e, w e :=
    lpObjective_bounds G p w t hp hw
  have hlp_bdd : BddAbove (lpRewards G p t w) := by
    refine ⟨∑ e, w e, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (hlp_bounds y hy).2
  have hpol_nonempty : (policyRewards G p t w).Nonempty :=
    ⟨policyReward G p t w (stopPolicy G t), stopPolicy G t, rfl⟩
  have hpol_bounds : ∀ π : ProbingPolicy G t,
      0 ≤ policyReward G p t w π ∧ policyReward G p t w π ≤ ∑ e, w e := by
    intro π
    rw [policyReward_eq_lpObjective]
    exact hlp_bounds _ (lpFeasible_policyProbeProb G p t hp π)
  have hpol_bdd : BddAbove (policyRewards G p t w) := by
    refine ⟨∑ e, w e, ?_⟩
    rintro _ ⟨π, rfl⟩
    exact (hpol_bounds π).2
  have hpol_le_lp : ∀ π : ProbingPolicy G t, policyReward G p t w π ≤ lpValue G p t w := by
    intro π
    rw [policyReward_eq_lpObjective]
    exact le_csSup hlp_bdd ⟨policyProbeProb G p t π, lpFeasible_policyProbeProb G p t hp π, rfl⟩
  have hopt_le_lp : OPT G p t w ≤ lpValue G p t w := by
    unfold OPT
    refine csSup_le hpol_nonempty ?_
    rintro _ ⟨π, rfl⟩
    exact hpol_le_lp π
  have hex_pol : ∃ π : ProbingPolicy G t, policyReward G p t w π = OPT G p t w := by
    let term : ProbeHistory E → ℝ := fun h => ∑ e ∈ historyMatching h, w e
    let πStar := optPolicy G t p term
    refine ⟨πStar, ?_⟩
    unfold OPT
    have hπStar_eq : policyReward G p t w πStar = optVal G t p term (Fintype.card E) [] :=
      policyEvalFrom_optPolicy_eq_optVal G t p term (Fintype.card E) [] (by simp)
    have hπ_le : ∀ π : ProbingPolicy G t, policyReward G p t w π ≤ policyReward G p t w πStar := by
      intro π
      rw [hπStar_eq]
      exact policyEvalFrom_le_optVal G t p hp π term (Fintype.card E) [] LegalHistory.nil
    refine le_antisymm (le_csSup hpol_bdd ⟨πStar, rfl⟩) ?_
    refine csSup_le hpol_nonempty ?_
    rintro _ ⟨π, rfl⟩
    exact hπ_le π
  exact ⟨⟨hlp_nonempty, hlp_bdd, hpol_nonempty, hpol_bdd,
    exists_lpMaximizer G p w t hp hw, hex_pol, hpol_bounds, hlp_bounds⟩,
    hpol_le_lp, hopt_le_lp⟩
