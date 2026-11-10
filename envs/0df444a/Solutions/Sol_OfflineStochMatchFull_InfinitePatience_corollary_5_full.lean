-- Prove2me | solution 1 for OfflineStochMatchFull.InfinitePatience.corollary_5_full
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T13:29:13.597199+00:00
-- url     : https://prove2.me/submissions/cca2fb9c-df21-4e2b-9e42-01bc8b06f917

import Mathlib
import Definitions.Def_OfflineStochMatchFull_InfinitePatience_Values
import Definitions.Def_OfflineStochMatchFull_InfinitePatience_RCRS

set_option autoImplicit false

namespace OSM8A

open OfflineStochMatch.InfinitePatience OfflineStochMatchFull.InfinitePatience

lemma bern_sum (q : ℝ) : ∑ b : Bool, bern q b = 1 := by
  simp [bern]

lemma bern_nonneg (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (b : Bool) : 0 ≤ bern q b := by
  cases b <;> simp [bern] <;> linarith

lemma coinWeight_sum {ι : Type} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) :
    ∑ c : ι → Bool, coinWeight q c = 1 := by
  unfold coinWeight
  rw [← Fintype.prod_sum (fun i b => bern (q i) b)]
  exact Finset.prod_eq_one fun i _ => bern_sum (q i)

lemma coinWeight_nonneg {ι : Type} [Fintype ι] (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (c : ι → Bool) : 0 ≤ coinWeight q c :=
  Finset.prod_nonneg fun i _ => bern_nonneg _ (hq i).1 (hq i).2 _

lemma aT_range (aT : ℝ → ℝ) (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) (z : ℝ)
    (h0 : 0 ≤ z) (h1 : z ≤ 1) : 0 ≤ aT z ∧ aT z ≤ 1 := by
  rcases haT with rfl | rfl
  · refine ⟨(Real.exp_pos _).le, ?_⟩
    unfold expAtt
    rw [Real.exp_le_one_iff]
    linarith
  · unfold linAtt
    constructor <;> linarith

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma coin_triple_sum (p y : E → ℝ) (aT : ℝ → ℝ) :
    ∑ Y : E → Bool, ∑ A : E → Bool, ∑ P : E → Bool,
      coinWeight y Y * coinWeight (fun f => aT (p f * y f)) A * coinWeight p P = 1 := by
  simp only [← Finset.mul_sum, coinWeight_sum, mul_one]

lemma prob_sigma_only (p y : E → ℝ) (aT : ℝ → ℝ) (Q : (E ≃ Fin (Fintype.card E)) → Prop)
    [DecidablePred Q] :
    prob p y aT (fun σ _ _ _ => Q σ) =
      (1 / ((Fintype.card E).factorial : ℝ)) *
        ∑ σ : E ≃ Fin (Fintype.card E), (if Q σ then (1:ℝ) else 0) := by
  unfold prob
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : Q σ
  · simp only [h, if_true, mul_one]
    exact coin_triple_sum p y aT
  · simp only [h, if_false, mul_zero, Finset.sum_const_zero]

lemma prob_nonneg (p y : E → ℝ) (aT : ℝ → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (hy : ∀ e, 0 ≤ y e ∧ y e ≤ 1) (ha : ∀ e, 0 ≤ aT (p e * y e) ∧ aT (p e * y e) ≤ 1) ev :
    0 ≤ prob p y aT ev := by
  classical
  unfold prob
  refine mul_nonneg (by positivity) ?_
  refine Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun Y _ =>
    Finset.sum_nonneg fun A _ => Finset.sum_nonneg fun P _ => ?_
  refine mul_nonneg (mul_nonneg (mul_nonneg (coinWeight_nonneg _ hy _)
    (coinWeight_nonneg _ ha _)) (coinWeight_nonneg _ hp _)) ?_
  split_ifs <;> norm_num

lemma card_perms : (Finset.univ : Finset (E ≃ Fin (Fintype.card E))).card =
    (Fintype.card E).factorial := by
  rw [Finset.card_univ]
  convert Fintype.card_equiv (Fintype.equivFin E)

lemma law (p y : E → ℝ) (aT : ℝ → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (hy : ∀ e, 0 ≤ y e ∧ y e ≤ 1) (ha : ∀ e, 0 ≤ aT (p e * y e) ∧ aT (p e * y e) ≤ 1) :
    AlgorithmProbabilityLaw p y aT := by
  classical
  have hn : ((Fintype.card E).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  refine ⟨?_, prob_nonneg p y aT hp hy ha, ?_⟩
  · rw [prob_sigma_only p y aT (fun _ => True)]
    have hs : ∑ σ : E ≃ Fin (Fintype.card E), (if True then (1:ℝ) else 0) =
        ((Fintype.card E).factorial : ℝ) := by
      simp only [if_true, Finset.sum_const, card_perms, nsmul_eq_mul, mul_one]
    rw [hs, one_div_mul_cancel hn]
  · intro σ₀
    rw [prob_sigma_only p y aT (fun σ => σ = σ₀)]
    have hs : ∑ σ : E ≃ Fin (Fintype.card E), (if σ = σ₀ then (1:ℝ) else 0) = 1 := by
      rw [Finset.sum_eq_single σ₀ (fun b _ hb => if_neg hb)
        (fun h => absurd (Finset.mem_univ _) h)]
      exact if_pos rfl
    rw [hs, mul_one]

lemma law_of_feasible (G : EdmondsMatching65.Polyhedron.Graph V E) (p y : E → ℝ) (t : V → ℕ∞)
    (aT : ℝ → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) (hy : LPFeasible G p t y) :
    AlgorithmProbabilityLaw p y aT := by
  refine law p y aT hp hy.1 fun e => aT_range aT haT _ (mul_nonneg (hp e).1 (hy.1 e).1) ?_
  exact mul_le_one₀ (hp e).2 (hy.1 e).1 (hy.1 e).2

end OSM8A

set_option autoImplicit false

namespace OSM8A

open OfflineStochMatch.InfinitePatience OfflineStochMatchFull.InfinitePatience

lemma finRange_filter_lt (n : ℕ) (j : Fin n) :
    (List.finRange n).filter (fun i => decide (i < j)) = (List.finRange n).take j.val := by
  conv_lhs => rw [← List.take_append_drop j.val (List.finRange n)]
  rw [List.filter_append, List.filter_eq_self.2, List.filter_eq_nil_iff.2, List.append_nil]
  · intro x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [List.getElem_drop, List.getElem_finRange, decide_eq_true_eq, Fin.lt_def,
      Fin.val_cast, not_lt]
    omega
  · intro x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [List.getElem_take, List.getElem_finRange, decide_eq_true_eq, Fin.lt_def,
      Fin.val_cast]
    simp only [List.length_take, List.length_finRange] at hi
    omega

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma stateBefore_eq (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) :
    stateBefore G t σ Y A P e =
      ((arrivalList σ).take (σ e).val).foldl (step G t Y A P) initState := by
  unfold stateBefore arrivalList
  rw [finRange_filter_lt, List.map_take]

lemma take_succ_arrival (σ : E ≃ Fin (Fintype.card E)) (k : ℕ) (hk : k < Fintype.card E) :
    (arrivalList σ).take (k + 1) = (arrivalList σ).take k ++ [σ.symm ⟨k, hk⟩] := by
  rw [List.take_add_one]
  congr 1
  simp [arrivalList, hk]

lemma step_matched (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (Y A P : E → Bool) (st : RunState V) (f : E) (v : V) :
    v ∈ (step G t Y A P st f).matched ↔
      v ∈ st.matched ∨ ((CanProbe G t st f ∧ Y f = true ∧ A f = true) ∧ P f = true ∧
        v ∈ G.ends f) := by
  unfold step
  by_cases hc : CanProbe G t st f ∧ Y f = true ∧ A f = true
  · rw [if_pos hc]
    by_cases hP : P f = true
    · simp [hP, hc]
    · simp [hP, hc]
  · rw [if_neg hc]
    simp [hc]

lemma matched_take (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) :
    ∀ k, k ≤ Fintype.card E → ∀ v,
      (v ∈ (((arrivalList σ).take k).foldl (step G t Y A P) initState).matched ↔
        ∃ f, (σ f).val < k ∧ IsProbed G t σ Y A P f ∧ P f = true ∧ v ∈ G.ends f)
  | 0, _, v => by simp [initState]
  | k + 1, hk, v => by
    have hk' : k < Fintype.card E := hk
    have ih := matched_take G t σ Y A P k hk'.le
    obtain ⟨f0, hf0⟩ : ∃ f0, f0 = σ.symm ⟨k, hk'⟩ := ⟨_, rfl⟩
    have hσ0 : σ f0 = ⟨k, hk'⟩ := by rw [hf0, Equiv.apply_symm_apply]
    have hsb : stateBefore G t σ Y A P f0 =
        ((arrivalList σ).take k).foldl (step G t Y A P) initState := by
      rw [stateBefore_eq, hσ0]
    rw [take_succ_arrival σ k hk', ← hf0, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hprob : IsProbed G t σ Y A P f0 ↔
        (CanProbe G t (((arrivalList σ).take k).foldl (step G t Y A P) initState) f0 ∧
          Y f0 = true ∧ A f0 = true) := by
      unfold IsProbed IsFree; rw [hsb]
    have hsplit : (∃ f, (σ f).val < k + 1 ∧ IsProbed G t σ Y A P f ∧ P f = true ∧ v ∈ G.ends f) ↔
        (∃ f, (σ f).val < k ∧ IsProbed G t σ Y A P f ∧ P f = true ∧ v ∈ G.ends f) ∨
          (IsProbed G t σ Y A P f0 ∧ P f0 = true ∧ v ∈ G.ends f0) := by
      constructor
      · rintro ⟨f, hf, h1, h2, h3⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hf with h | h
        · exact Or.inl ⟨f, h, h1, h2, h3⟩
        · have hff : f = f0 := by rw [hf0, Equiv.eq_symm_apply]; exact Fin.ext h
          rw [hff] at h1 h2 h3
          exact Or.inr ⟨h1, h2, h3⟩
      · rintro (⟨f, hf, h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
        · exact ⟨f, by omega, h1, h2, h3⟩
        · exact ⟨f0, by rw [hσ0]; exact Nat.lt_succ_self k, h1, h2, h3⟩
    rw [hsplit, ← ih v, hprob, step_matched]

lemma matched_stateBefore (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) (v : V) :
    v ∈ (stateBefore G t σ Y A P e).matched ↔
      ∃ f, σ f < σ e ∧ IsProbed G t σ Y A P f ∧ P f = true ∧ v ∈ G.ends f := by
  rw [stateBefore_eq, matched_take G t σ Y A P _ (σ e).isLt.le]
  simp only [Fin.lt_def]

lemma matchedPrefix_isMatching (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (k : ℕ) :
    EdmondsMatching65.Polyhedron.IsMatching G (matchedPrefix G t σ Y A P k) := by
  -- an earlier probed active edge at v makes v matched before any later edge at v
  have key : ∀ e f, σ f < σ e → IsProbed G t σ Y A P e → IsProbed G t σ Y A P f →
      P f = true → ∀ v, v ∈ G.ends e → v ∉ G.ends f := by
    intro e f hlt he hf hPf v hve hvf
    exact (he.1 v hve).1 ((matched_stateBefore G t σ Y A P e v).2 ⟨f, hlt, hf, hPf, hvf⟩)
  intro e he f hf hne v hve hvf
  simp only [matchedPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at he hf
  rcases lt_trichotomy (σ e) (σ f) with h | h | h
  · exact key f e h hf.2.1 he.2.1 he.2.2 v hvf hve
  · exact hne (σ.injective h)
  · exact key e f h he.2.1 hf.2.1 hf.2.2 v hve hvf

lemma probed_of_no_active_nbr (G : EdmondsMatching65.Polyhedron.Graph V E)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) (hY : Y e = true)
    (hA : A e = true)
    (h : ∀ f, σ f < σ e → (∃ v, v ∈ G.ends e ∧ v ∈ G.ends f) →
      ¬ (Y f = true ∧ A f = true ∧ P f = true)) :
    IsProbed G (fun _ => ⊤) σ Y A P e := by
  refine ⟨fun v hv => ⟨?_, ?_⟩, hY, hA⟩
  · intro hm
    obtain ⟨f, hlt, hpr, hPf, hvf⟩ := (matched_stateBefore G _ σ Y A P e v).1 hm
    exact h f hlt ⟨v, hv, hvf⟩ ⟨hpr.2.1, hpr.2.2, hPf⟩
  · exact ENat.natCast_lt_top _

lemma foldl_step_congrP (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (Y A P P' : E → Bool) (l : List E) (h : ∀ f ∈ l, P f = P' f) (st : RunState V) :
    l.foldl (step G t Y A P) st = l.foldl (step G t Y A P') st := by
  induction l generalizing st with
  | nil => rfl
  | cons f l ih =>
    simp only [List.foldl_cons]
    have hs : step G t Y A P st f = step G t Y A P' st f := by
      unfold step; rw [h f (by simp)]
    rw [hs]
    exact ih (fun g hg => h g (by simp [hg])) _

lemma isProbed_congrP (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P P' : E → Bool) (e : E)
    (h : ∀ f, f ≠ e → P f = P' f) :
    IsProbed G t σ Y A P e ↔ IsProbed G t σ Y A P' e := by
  have hst : stateBefore G t σ Y A P e = stateBefore G t σ Y A P' e := by
    unfold stateBefore
    refine foldl_step_congrP G t Y A P P' _ (fun f hf => h f ?_) _
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] at hf
    obtain ⟨i, hi, rfl⟩ := hf
    intro heq
    rw [← heq, Equiv.apply_symm_apply] at hi
    exact lt_irrefl _ hi
  unfold IsProbed IsFree
  rw [hst]

lemma mem_take_arrival (σ : E ≃ Fin (Fintype.card E)) (e x : E) :
    x ∈ (arrivalList σ).take (σ e).val ↔ σ x < σ e := by
  rw [arrivalList, ← List.map_take, ← finRange_filter_lt]
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simpa using hi
  · intro h
    exact ⟨σ x, h, by simp⟩

lemma mem_historyMatching_observedBefore (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e f : E) :
    f ∈ historyMatching (observedBefore G t σ Y A P e) ↔
      σ f < σ e ∧ IsProbed G t σ Y A P f ∧ P f = true := by
  unfold historyMatching observedBefore
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_filterMap,
    mem_take_arrival]
  constructor
  · rintro ⟨⟨g, b⟩, ⟨⟨x, hx, hxe⟩, hb⟩, rfl⟩
    split_ifs at hxe with hpx
    · simp only [Option.some.injEq, Prod.mk.injEq] at hxe
      obtain ⟨rfl, rfl⟩ := hxe
      exact ⟨hx, hpx, by simpa using hb⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(f, true), ⟨⟨f, h1, ?_⟩, rfl⟩, rfl⟩
    rw [if_pos h2, h3]

lemma historyState_matched_eq (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) (v : V) :
    v ∈ (historyState G (observedBefore G t σ Y A P e)).matched ↔
      v ∈ (stateBefore G t σ Y A P e).matched := by
  rw [matched_stateBefore]
  simp only [historyState, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_historyMatching_observedBefore]
  constructor
  · rintro ⟨f, ⟨h1, h2, h3⟩, h4⟩
    exact ⟨f, h1, h2, h3, h4⟩
  · rintro ⟨f, h1, h2, h3, h4⟩
    exact ⟨f, ⟨h1, h2, h3⟩, h4⟩

lemma not_mem_observedBefore (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) :
    e ∉ (observedBefore G t σ Y A P e).map Prod.fst := by
  intro h
  obtain ⟨⟨g, b⟩, hm, hg⟩ := List.mem_map.1 h
  unfold observedBefore at hm
  obtain ⟨x, hx, hxe⟩ := List.mem_filterMap.1 hm
  rw [mem_take_arrival] at hx
  split_ifs at hxe
  · simp only [Option.some.injEq, Prod.mk.injEq] at hxe
    simp only at hg
    rw [hxe.1, hg] at hx
    exact lt_irrefl _ hx

lemma probed_iff_legal (G : EdmondsMatching65.Polyhedron.Graph V E)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) :
    IsProbed G (fun _ => ⊤) σ Y A P e ↔
      LegalNext G (fun _ => ⊤) (observedBefore G (fun _ => ⊤) σ Y A P e) e ∧
        Y e = true ∧ A e = true := by
  constructor
  · rintro ⟨hc, hY, hA⟩
    refine ⟨⟨not_mem_observedBefore G _ σ Y A P e, fun v hv => ⟨fun hm => ?_,
      ENat.natCast_lt_top _⟩⟩, hY, hA⟩
    exact (hc v hv).1 ((historyState_matched_eq G _ σ Y A P e v).1 hm)
  · rintro ⟨⟨_, hc⟩, hY, hA⟩
    refine ⟨fun v hv => ⟨fun hm => ?_, ENat.natCast_lt_top _⟩, hY, hA⟩
    exact (hc v hv).1 ((historyState_matched_eq G _ σ Y A P e v).2 hm)

open Classical in
lemma legal_take (G : EdmondsMatching65.Polyhedron.Graph V E)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) :
    ∀ k, k ≤ Fintype.card E → LegalHistory G (fun _ => ⊤)
      (((arrivalList σ).take k).filterMap fun f =>
        if IsProbed G (fun _ => ⊤) σ Y A P f then some (f, P f) else none)
  | 0, _ => by simpa using LegalHistory.nil
  | k + 1, hk => by
    have hk' : k < Fintype.card E := hk
    have ih := legal_take G σ Y A P k hk'.le
    obtain ⟨f0, hf0⟩ : ∃ f0, f0 = σ.symm ⟨k, hk'⟩ := ⟨_, rfl⟩
    have hσ0 : σ f0 = ⟨k, hk'⟩ := by rw [hf0, Equiv.apply_symm_apply]
    have hob : observedBefore G (fun _ => ⊤) σ Y A P f0 =
        ((arrivalList σ).take k).filterMap fun f =>
          if IsProbed G (fun _ => ⊤) σ Y A P f then some (f, P f) else none := by
      unfold observedBefore; rw [hσ0]
    rw [take_succ_arrival σ k hk', ← hf0, List.filterMap_append]
    by_cases hp : IsProbed G (fun _ => ⊤) σ Y A P f0
    · have hs : [f0].filterMap (fun f =>
          if IsProbed G (fun _ => ⊤) σ Y A P f then some (f, P f) else none) = [(f0, P f0)] := by
        simp [hp]
      rw [hs]
      refine LegalHistory.snoc ih ?_
      have := ((probed_iff_legal G σ Y A P f0).1 hp).1
      rwa [hob] at this
    · have hs : [f0].filterMap (fun f =>
          if IsProbed G (fun _ => ⊤) σ Y A P f then some (f, P f) else none) = [] := by
        simp [hp]
      rw [hs, List.append_nil]
      exact ih

lemma legal_observedBefore (G : EdmondsMatching65.Polyhedron.Graph V E)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) :
    LegalHistory G (fun _ => ⊤) (observedBefore G (fun _ => ⊤) σ Y A P e) := by
  unfold observedBefore
  exact legal_take G σ Y A P _ (σ e).isLt.le

lemma operational (G : EdmondsMatching65.Polyhedron.Graph V E) :
    AlgorithmOperational G (fun _ => ⊤) := by
  refine ⟨fun σ Y A P e => ⟨legal_observedBefore G σ Y A P e, probed_iff_legal G σ Y A P e⟩,
    fun σ Y A P k => ⟨matchedPrefix_isMatching G _ σ Y A P k, ?_, ?_⟩, ?_⟩
  · intro e he
    simp only [matchedPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact he.2.2
  · intro e he
    simp only [matchedPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact ⟨by omega, he.2⟩
  · intro σ σ' Y A P Y' A' P' e hob hY hA
    rw [probed_iff_legal, probed_iff_legal, hob, hY, hA]

end OSM8A

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OSM8A

open OfflineStochMatch.InfinitePatience OfflineStochMatchFull.InfinitePatience

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### C4: Pr[e ∈ terminal] = p e * Pr[e probed] -/

lemma mem_terminal_iff (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) :
    e ∈ terminalMatching G t σ Y A P ↔ IsProbed G t σ Y A P e ∧ P e = true := by
  simp only [terminalMatching, matchedPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨(σ e).isLt, h⟩⟩

/-- Flip the coin at `e`. -/
def flipF (e : E) (P : E → Bool) : E → Bool := fun f => if f = e then !(P f) else P f

lemma flipF_invol (e : E) : Function.Involutive (flipF e) := by
  intro P
  funext f
  by_cases h : f = e <;> simp [flipF, h]

lemma flipF_e (e : E) (P : E → Bool) : flipF e P e = !(P e) := by simp [flipF]

lemma flipF_ne (e : E) (P : E → Bool) (f : E) (hf : f ≠ e) : flipF e P f = P f := by
  simp [flipF, hf]

/-- The coin weight away from `e`. -/
noncomputable def restW (q : E → ℝ) (e : E) (P : E → Bool) : ℝ :=
  ∏ f ∈ Finset.univ.erase e, bern (q f) (P f)

lemma coinWeight_split (q : E → ℝ) (e : E) (P : E → Bool) :
    coinWeight q P = bern (q e) (P e) * restW q e P := by
  unfold coinWeight restW
  exact (Finset.mul_prod_erase Finset.univ (fun f => bern (q f) (P f)) (Finset.mem_univ e)).symm

lemma restW_flip (q : E → ℝ) (e : E) (P : E → Bool) : restW q e (flipF e P) = restW q e P := by
  unfold restW
  exact Finset.prod_congr rfl fun f hf => by rw [flipF_ne e P f (Finset.ne_of_mem_erase hf)]

open Classical in
lemma sum_P_split (q : E → ℝ) (e : E) (I : (E → Bool) → Prop)
    (hI : ∀ P, I (flipF e P) ↔ I P) :
    ∑ P, coinWeight q P * (if I P ∧ P e = true then (1:ℝ) else 0) =
      q e * ∑ P, coinWeight q P * (if I P then (1:ℝ) else 0) := by
  have hsum : ∀ g : (E → Bool) → ℝ, ∑ P, g (flipF e P) = ∑ P, g P := fun g =>
    Equiv.sum_comp (Function.Involutive.toPerm _ (flipF_invol e)) g
  have hA : ∑ P, coinWeight q (flipF e P) *
      (if I (flipF e P) ∧ flipF e P e = true then (1:ℝ) else 0) =
      ∑ P, coinWeight q P * (if I P ∧ P e = true then (1:ℝ) else 0) :=
    hsum (fun P => coinWeight q P * (if I P ∧ P e = true then (1:ℝ) else 0))
  have hB : ∑ P, coinWeight q (flipF e P) * (if I (flipF e P) then (1:ℝ) else 0) =
      ∑ P, coinWeight q P * (if I P then (1:ℝ) else 0) :=
    hsum (fun P => coinWeight q P * (if I P then (1:ℝ) else 0))
  have key1 : ∀ P, coinWeight q P * (if I P ∧ P e = true then (1:ℝ) else 0) +
      coinWeight q (flipF e P) * (if I (flipF e P) ∧ flipF e P e = true then (1:ℝ) else 0) =
      q e * (restW q e P * (if I P then (1:ℝ) else 0)) := by
    intro P
    rw [coinWeight_split q e P, coinWeight_split q e (flipF e P), restW_flip, flipF_e, hI]
    cases h : P e <;> by_cases hP : I P <;> simp [hP, bern]
  have key0 : ∀ P, coinWeight q P * (if I P then (1:ℝ) else 0) +
      coinWeight q (flipF e P) * (if I (flipF e P) then (1:ℝ) else 0) =
      restW q e P * (if I P then (1:ℝ) else 0) := by
    intro P
    rw [coinWeight_split q e P, coinWeight_split q e (flipF e P), restW_flip, flipF_e, hI]
    cases h : P e <;> by_cases hP : I P <;> simp [hP, bern] <;> ring
  have e1 : ∑ P, coinWeight q P * (if I P ∧ P e = true then (1:ℝ) else 0) +
      ∑ P, coinWeight q P * (if I P ∧ P e = true then (1:ℝ) else 0) =
      q e * ∑ P, restW q e P * (if I P then (1:ℝ) else 0) := by
    nth_rewrite 2 [← hA]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun P _ => key1 P
  have e0 : ∑ P, coinWeight q P * (if I P then (1:ℝ) else 0) +
      ∑ P, coinWeight q P * (if I P then (1:ℝ) else 0) =
      ∑ P, restW q e P * (if I P then (1:ℝ) else 0) := by
    nth_rewrite 2 [← hB]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun P _ => key0 P
  have e2 : ∑ P, coinWeight q P * (if I P ∧ P e = true then (1:ℝ) else 0) +
      ∑ P, coinWeight q P * (if I P ∧ P e = true then (1:ℝ) else 0) =
      q e * ∑ P, coinWeight q P * (if I P then (1:ℝ) else 0) +
        q e * ∑ P, coinWeight q P * (if I P then (1:ℝ) else 0) := by
    rw [e1, ← e0]; ring
  linarith

lemma prob_terminal (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (p y : E → ℝ) (aT : ℝ → ℝ) (e : E)
    (hc : ∀ σ Y A P, IsProbed G t σ Y A (flipF e P) e ↔ IsProbed G t σ Y A P e) :
    prob p y aT (fun σ Y A P => e ∈ terminalMatching G t σ Y A P) =
      p e * probProbed G p t y aT e := by
  unfold probProbed prob
  rw [mul_left_comm (p e)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun Y _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun A _ => ?_
  have h := sum_P_split p e (fun P => IsProbed G t σ Y A P e) (hc σ Y A)
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [mul_left_comm (p e), mul_left_comm (p e)]
  congr 2
  rw [← h]
  refine Finset.sum_congr rfl fun P _ => ?_
  congr 1
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((mem_terminal_iff G t σ Y A P e).1 h1) h2
  · exact absurd ((mem_terminal_iff G t σ Y A P e).2 h2) h1
  · rfl

lemma reward_bound (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (p w y : E → ℝ) (aT : ℝ → ℝ) (c : ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hw : ∀ e, 0 ≤ w e)
    (hcore : ∀ e, c * y e ≤ probProbed G p t y aT e)
    (hterm : ∀ e, prob p y aT (fun σ Y A P => e ∈ terminalMatching G t σ Y A P) =
      p e * probProbed G p t y aT e) :
    c * lpObjective p w y ≤ algorithmReward G p t y w aT := by
  unfold lpObjective algorithmReward
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [hterm e]
  have h := mul_le_mul_of_nonneg_left (hcore e) (mul_nonneg (hw e) (hp e).1)
  calc c * (w e * p e * y e) = w e * p e * (c * y e) := by ring
    _ ≤ w e * p e * probProbed G p t y aT e := h
    _ = w e * (p e * probProbed G p t y aT e) := by ring

/-! ### C3a: Pr_σ[T all before e] = 1/(|T|+1) -/

/-- Orders in which `g` comes last among `S`. -/
def Alast (S : Finset E) (g : E) : Finset (E ≃ Fin (Fintype.card E)) :=
  Finset.univ.filter (fun σ => ∀ f ∈ S, f ≠ g → σ f < σ g)

lemma swap_mem_Alast (S : Finset E) (g h : E) (hh : h ∈ S)
    (σ : E ≃ Fin (Fintype.card E)) (hσ : σ ∈ Alast S g) :
    (Equiv.swap g h).trans σ ∈ Alast S h := by
  simp only [Alast, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.trans_apply] at hσ ⊢
  intro f hf hfh
  rw [Equiv.swap_apply_right]
  by_cases hfg : f = g
  · subst hfg
    rw [Equiv.swap_apply_left]
    exact hσ h hh (Ne.symm hfh)
  · rw [Equiv.swap_apply_of_ne_of_ne hfg hfh]
    exact hσ f hf hfg

lemma card_Alast_le (S : Finset E) (g h : E) (hh : h ∈ S) :
    (Alast S g).card ≤ (Alast S h).card := by
  refine Finset.card_le_card_of_injOn (fun σ => (Equiv.swap g h).trans σ) ?_ ?_
  · intro σ hσ
    exact swap_mem_Alast S g h hh σ hσ
  · intro σ1 _ σ2 _ H
    ext x
    have := congrArg (fun τ : E ≃ Fin (Fintype.card E) => τ (Equiv.swap g h x)) H
    simp only [Equiv.trans_apply, Equiv.swap_apply_self] at this
    rw [this]

lemma card_before (e : E) (T : Finset E) (he : e ∉ T) :
    ((Finset.univ.filter (fun σ : E ≃ Fin (Fintype.card E) => ∀ f ∈ T, σ f < σ e)).card : ℝ) *
      (T.card + 1) = ((Fintype.card E).factorial : ℝ) := by
  have hA : Finset.univ.filter (fun σ : E ≃ Fin (Fintype.card E) => ∀ f ∈ T, σ f < σ e) =
      Alast (insert e T) e := by
    ext σ
    simp only [Alast, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h f hf hfe
      rcases hf with hf | hf
      · exact absurd hf hfe
      · exact h f hf
    · intro h f hf
      exact h f (Or.inr hf) (fun hfe => he (hfe ▸ hf))
  have hcover : (Finset.univ : Finset (E ≃ Fin (Fintype.card E))) =
      (insert e T).biUnion (Alast (insert e T)) := by
    ext σ
    simp only [Finset.mem_univ, true_iff, Finset.mem_biUnion]
    obtain ⟨g, hg, hmax⟩ := Finset.exists_max_image (insert e T) (fun f => σ f)
      ⟨e, Finset.mem_insert_self e T⟩
    refine ⟨g, hg, ?_⟩
    simp only [Alast, Finset.mem_filter, Finset.mem_univ, true_and]
    intro f hf hfg
    exact lt_of_le_of_ne (hmax f hf) (fun h => hfg (σ.injective h))
  have hcard : (Finset.univ : Finset (E ≃ Fin (Fintype.card E))).card =
      (Fintype.card E).factorial := by
    rw [Finset.card_univ]
    convert Fintype.card_equiv (Fintype.equivFin E)
  have heq : ∀ g ∈ insert e T, (Alast (insert e T) g).card = (Alast (insert e T) e).card :=
    fun g hg => le_antisymm (card_Alast_le _ g e (Finset.mem_insert_self e T))
      (card_Alast_le _ e g hg)
  have hSc : (insert e T).card = T.card + 1 := by simp [he]
  have htot : (Fintype.card E).factorial = (T.card + 1) * (Alast (insert e T) e).card := by
    rw [← hcard, hcover, Finset.card_biUnion, Finset.sum_congr rfl heq, Finset.sum_const,
      smul_eq_mul, hSc]
    intro g hg h hh hgh
    show Disjoint (Alast (insert e T) g) (Alast (insert e T) h)
    rw [Finset.disjoint_left]
    intro σ h1 h2
    simp only [Alast, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact lt_asymm (h1 h hh (Ne.symm hgh)) (h2 g hg hgh)
  rw [hA, htot]
  push_cast
  ring

lemma avg_before (e : E) (T : Finset E) (he : e ∉ T) :
    (1 / ((Fintype.card E).factorial : ℝ)) *
      ∑ σ : E ≃ Fin (Fintype.card E), (if ∀ f ∈ T, σ f < σ e then (1:ℝ) else 0) =
      1 / ((T.card : ℝ) + 1) := by
  rw [Finset.sum_boole]
  have h := card_before e T he
  have hn : ((Fintype.card E).factorial : ℝ) ≠ 0 := by positivity
  have hT : ((T.card : ℝ) + 1) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff hn hT]
  linarith

/-! ### C3b: E_σ ∏_{f ∈ N, before e} (1 - q f) = ∫_0^1 ∏_{f ∈ N} (1 - x q f) -/

lemma prod_ite_expand (σ : E ≃ Fin (Fintype.card E)) (e : E) (N : Finset E) (q : E → ℝ) :
    ∏ f ∈ N, (if σ f < σ e then 1 - q f else 1) =
      ∑ T ∈ N.powerset, (∏ f ∈ T, -q f) * (if ∀ f ∈ T, σ f < σ e then (1:ℝ) else 0) := by
  have h1 : ∀ f, (if σ f < σ e then 1 - q f else (1:ℝ)) =
      (-q f) * (if σ f < σ e then (1:ℝ) else 0) + 1 := by
    intro f; split_ifs <;> ring
  rw [Finset.prod_congr rfl (fun f _ => h1 f), Finset.prod_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_boole]
  by_cases h : ∀ f ∈ T, σ f < σ e <;> simp [h]

lemma avg_prod_eq_integral (e : E) (N : Finset E) (he : e ∉ N) (q : E → ℝ) :
    (1 / ((Fintype.card E).factorial : ℝ)) *
      ∑ σ : E ≃ Fin (Fintype.card E), ∏ f ∈ N, (if σ f < σ e then 1 - q f else 1) =
      ∫ x in (0:ℝ)..1, ∏ f ∈ N, (1 - x * q f) := by
  have hL : (1 / ((Fintype.card E).factorial : ℝ)) *
      ∑ σ : E ≃ Fin (Fintype.card E), ∏ f ∈ N, (if σ f < σ e then 1 - q f else 1) =
      ∑ T ∈ N.powerset, (∏ f ∈ T, -q f) * (1 / ((T.card : ℝ) + 1)) := by
    simp only [prod_ite_expand]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [← Finset.mul_sum, ← avg_before e T (fun h => he (Finset.mem_powerset.1 hT h))]
    ring
  have hx : ∀ x : ℝ, ∏ f ∈ N, (1 - x * q f) =
      ∑ T ∈ N.powerset, (∏ f ∈ T, -q f) * x ^ T.card := by
    intro x
    have h2 : ∀ f, 1 - x * q f = x * (-q f) + 1 := fun f => by ring
    rw [Finset.prod_congr rfl (fun f _ => h2 f), Finset.prod_add]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const]
    ring
  have hR : (∫ x in (0:ℝ)..1, ∏ f ∈ N, (1 - x * q f)) =
      ∑ T ∈ N.powerset, (∏ f ∈ T, -q f) * (1 / ((T.card : ℝ) + 1)) := by
    simp only [hx]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun T _ => ?_
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp
    · intro T _
      exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
  rw [hL, hR]

end OSM8A

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OSM8A

open OfflineStochMatch.InfinitePatience OfflineStochMatchFull.InfinitePatience

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### C3c: coin factorization of the "no earlier active neighbour" event -/

open Classical in
lemma coin_prod_sum (y a p : E → ℝ) (C : E → Bool → Bool → Bool → Prop) :
    ∑ Y : E → Bool, ∑ A : E → Bool, ∑ P : E → Bool,
      coinWeight y Y * coinWeight a A * coinWeight p P *
        (if ∀ f, C f (Y f) (A f) (P f) then (1:ℝ) else 0) =
    ∏ f, ∑ b1 : Bool, ∑ b2 : Bool, ∑ b3 : Bool,
      bern (y f) b1 * bern (a f) b2 * bern (p f) b3 * (if C f b1 b2 b3 then (1:ℝ) else 0) := by
  have hpt : ∀ Y A P : E → Bool, coinWeight y Y * coinWeight a A * coinWeight p P *
      (if ∀ f, C f (Y f) (A f) (P f) then (1:ℝ) else 0) =
      ∏ f, (bern (y f) (Y f) * bern (a f) (A f) * bern (p f) (P f) *
        (if C f (Y f) (A f) (P f) then (1:ℝ) else 0)) := by
    intro Y A P
    unfold coinWeight
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_boole]
    congr 1
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (fun f _ => h1 f) h2
    · exact absurd (fun f => h2 f (Finset.mem_univ f)) h1
    · rfl
  simp only [hpt]
  rw [Fintype.prod_sum (fun f b1 => ∑ b2 : Bool, ∑ b3 : Bool,
      bern (y f) b1 * bern (a f) b2 * bern (p f) b3 * (if C f b1 b2 b3 then (1:ℝ) else 0))]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [Fintype.prod_sum (fun f b2 => ∑ b3 : Bool,
      bern (y f) (Y f) * bern (a f) b2 * bern (p f) b3 *
        (if C f (Y f) b2 b3 then (1:ℝ) else 0))]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Fintype.prod_sum (fun f b3 =>
      bern (y f) (Y f) * bern (a f) (A f) * bern (p f) b3 *
        (if C f (Y f) (A f) b3 then (1:ℝ) else 0))]

/-- Per-edge constraint of the event "e has Y,A and no earlier active-probed neighbour in N". -/
def Cev (N : Finset E) (σ : E ≃ Fin (Fintype.card E)) (e f : E) (b1 b2 b3 : Bool) : Prop :=
  if f = e then (b1 = true ∧ b2 = true)
  else if f ∈ N ∧ σ f < σ e then ¬ (b1 = true ∧ b2 = true ∧ b3 = true) else True

open Classical in
lemma prod_factor (y a p : E → ℝ) (N : Finset E) (σ : E ≃ Fin (Fintype.card E)) (e : E)
    (he : e ∉ N) :
    ∏ f, ∑ b1 : Bool, ∑ b2 : Bool, ∑ b3 : Bool,
      bern (y f) b1 * bern (a f) b2 * bern (p f) b3 *
        (if Cev N σ e f b1 b2 b3 then (1:ℝ) else 0) =
    y e * a e * ∏ f ∈ N, (if σ f < σ e then 1 - y f * a f * p f else 1) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
  congr 1
  · simp [Cev, bern]
    ring
  · have hf : ∀ f ∈ Finset.univ.erase e, (∑ b1 : Bool, ∑ b2 : Bool, ∑ b3 : Bool,
        bern (y f) b1 * bern (a f) b2 * bern (p f) b3 *
          (if Cev N σ e f b1 b2 b3 then (1:ℝ) else 0)) =
        if f ∈ N then (if σ f < σ e then 1 - y f * a f * p f else 1) else 1 := by
      intro f hf
      have hfe : f ≠ e := Finset.ne_of_mem_erase hf
      by_cases hN : f ∈ N <;> by_cases hs : σ f < σ e <;>
        simp [Cev, hfe, hN, hs, bern] <;> ring
    rw [Finset.prod_congr rfl hf, Finset.prod_ite_mem]
    congr 1
    exact Finset.inter_eq_right.2 fun f hf =>
      Finset.mem_erase.2 ⟨fun h => he (h ▸ hf), Finset.mem_univ f⟩

lemma cw_nonneg (q : E → ℝ) (hq : ∀ f, 0 ≤ q f ∧ q f ≤ 1) (P : E → Bool) :
    0 ≤ coinWeight q P :=
  Finset.prod_nonneg fun f _ => by
    unfold bern
    split_ifs <;> linarith [hq f]

open Classical in
/-- Lower bound of Pr[e probed] by the averaged neighbour product (t = ⊤). -/
lemma probProbed_ge (G : EdmondsMatching65.Polyhedron.Graph V E) (p y : E → ℝ) (aT : ℝ → ℝ)
    (e : E) (N : Finset E) (he : e ∉ N)
    (hy : ∀ f, 0 ≤ y f ∧ y f ≤ 1) (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1)
    (ha : ∀ f, 0 ≤ aT (p f * y f) ∧ aT (p f * y f) ≤ 1)
    (hB : ∀ σ Y A P, (∀ f, Cev N σ e f (Y f) (A f) (P f)) →
      IsProbed G (fun _ => ⊤) σ Y A P e) :
    y e * aT (p e * y e) * ((1 / ((Fintype.card E).factorial : ℝ)) *
      ∑ σ : E ≃ Fin (Fintype.card E),
        ∏ f ∈ N, (if σ f < σ e then 1 - y f * aT (p f * y f) * p f else 1)) ≤
      probProbed G p (fun _ => ⊤) y aT e := by
  have hσ : ∀ σ : E ≃ Fin (Fintype.card E), ∑ Y : E → Bool, ∑ A : E → Bool, ∑ P : E → Bool,
      coinWeight y Y * coinWeight (fun f => aT (p f * y f)) A * coinWeight p P *
        (if ∀ f, Cev N σ e f (Y f) (A f) (P f) then (1:ℝ) else 0) =
      y e * aT (p e * y e) *
        ∏ f ∈ N, (if σ f < σ e then 1 - y f * aT (p f * y f) * p f else 1) := by
    intro σ
    rw [coin_prod_sum]
    exact prod_factor y (fun f => aT (p f * y f)) p N σ e he
  have hle : ∀ σ : E ≃ Fin (Fintype.card E), y e * aT (p e * y e) *
      ∏ f ∈ N, (if σ f < σ e then 1 - y f * aT (p f * y f) * p f else 1) ≤
      ∑ Y : E → Bool, ∑ A : E → Bool, ∑ P : E → Bool,
        coinWeight y Y * coinWeight (fun f => aT (p f * y f)) A * coinWeight p P *
          (if IsProbed G (fun _ => ⊤) σ Y A P e then (1:ℝ) else 0) := by
    intro σ
    rw [← hσ σ]
    refine Finset.sum_le_sum fun Y _ => Finset.sum_le_sum fun A _ =>
      Finset.sum_le_sum fun P _ => ?_
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (cw_nonneg y hy Y)
      (cw_nonneg (fun f => aT (p f * y f)) ha A)) (cw_nonneg p hp P))
    split_ifs with h1 h2
    · exact le_refl _
    · exact absurd (hB σ Y A P h1) h2
    · exact zero_le_one
    · exact le_refl _
  unfold probProbed prob
  calc y e * aT (p e * y e) * ((1 / ((Fintype.card E).factorial : ℝ)) *
      ∑ σ : E ≃ Fin (Fintype.card E),
        ∏ f ∈ N, (if σ f < σ e then 1 - y f * aT (p f * y f) * p f else 1)) =
      (1 / ((Fintype.card E).factorial : ℝ)) * ∑ σ : E ≃ Fin (Fintype.card E),
        (y e * aT (p e * y e) *
          ∏ f ∈ N, (if σ f < σ e then 1 - y f * aT (p f * y f) * p f else 1)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hle σ) (by positivity)

/-- Neighbours of `e` (edges sharing an endpoint, other than `e`). -/
def Nbr (G : EdmondsMatching65.Polyhedron.Graph V E) (e : E) : Finset E :=
  Finset.univ.filter fun f => f ≠ e ∧ ∃ v, v ∈ G.ends e ∧ v ∈ G.ends f

lemma not_mem_Nbr (G : EdmondsMatching65.Polyhedron.Graph V E) (e : E) : e ∉ Nbr G e := by
  simp [Nbr]

lemma cev_spec (G : EdmondsMatching65.Polyhedron.Graph V E) (σ : E ≃ Fin (Fintype.card E))
    (Y A P : E → Bool) (e : E) (h : ∀ f, Cev (Nbr G e) σ e f (Y f) (A f) (P f)) :
    Y e = true ∧ A e = true ∧ ∀ f, σ f < σ e → (∃ v, v ∈ G.ends e ∧ v ∈ G.ends f) →
      ¬ (Y f = true ∧ A f = true ∧ P f = true) := by
  have h0 := h e
  simp only [Cev] at h0
  refine ⟨h0.1, h0.2, fun f hlt hv => ?_⟩
  have hfe : f ≠ e := fun hfe => lt_irrefl (σ e) (hfe ▸ hlt)
  have hN : f ∈ Nbr G e := by simp [Nbr, hfe, hv]
  have h1 := h f
  simp only [Cev, if_neg hfe, if_pos (And.intro hN hlt)] at h1
  exact h1

end OSM8A

set_option autoImplicit false

namespace OSM8A

lemma integral_c : (∫ x in (0:ℝ)..1, Real.exp (-2 * x)) = (1 - Real.exp (-2)) / 2 := by
  have h := intervalIntegral.integral_comp_mul_left (f := Real.exp) (a := (0:ℝ)) (b := 1)
    (show (-2:ℝ) ≠ 0 by norm_num)
  rw [h, integral_exp, smul_eq_mul]
  simp only [mul_zero, mul_one, Real.exp_zero]
  ring

lemma c_pos : 0 < (1 - Real.exp (-2)) / 2 := by
  have : Real.exp (-2) < 1 := by
    have h := Real.exp_lt_exp.mpr (show (-2:ℝ) < 0 by norm_num)
    simpa using h
  linarith

lemma c_le_one : (1 - Real.exp (-2)) / 2 ≤ 1 := by
  have : 0 < Real.exp (-2) := Real.exp_pos _
  linarith

/-- per-neighbour factor, exponential attenuation -/
lemma exp_le_fac_exp (x z : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz0 : 0 ≤ z) :
    Real.exp (-(x * z)) ≤ 1 - x * z * Real.exp (-(1 / 2 * z)) := by
  set u := x * z with hu
  have hu0 : 0 ≤ u := mul_nonneg hx0 hz0
  have huz : u ≤ z := by rw [hu]; nlinarith
  have h1 : Real.exp (-(1 / 2 * z)) ≤ Real.exp (-(u / 2)) := Real.exp_le_exp.mpr (by linarith)
  have hs : u / 2 ≤ Real.sinh (u / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  rw [Real.sinh_eq] at hs
  have e1 : Real.exp (-(u / 2)) * Real.exp (u / 2) = 1 := by rw [← Real.exp_add]; simp
  have e2 : Real.exp (-(u / 2)) * Real.exp (-(u / 2)) = Real.exp (-u) := by
    rw [← Real.exp_add]; ring_nf
  have hpos : 0 < Real.exp (-(u / 2)) := Real.exp_pos _
  have h3 : Real.exp (-(u / 2)) * ((Real.exp (u / 2) - Real.exp (-(u / 2))) / 2)
      = (1 - Real.exp (-u)) / 2 := by linear_combination (e1 - e2) / 2
  have h4 := mul_le_mul_of_nonneg_left hs hpos.le
  rw [h3] at h4
  have h5 := mul_le_mul_of_nonneg_left h1 hu0
  nlinarith

/-- per-neighbour factor, linear attenuation -/
lemma exp_le_fac_lin (x z : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz0 : 0 ≤ z) :
    Real.exp (-(x * z)) ≤ 1 - x * z * (1 - 1 / 2 * z) := by
  set u := x * z with hu
  have hu0 : 0 ≤ u := mul_nonneg hx0 hz0
  have huz : u ≤ z := by rw [hu]; nlinarith
  have hq := Real.quadratic_le_exp_of_nonneg hu0
  have hE : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (-u)
  have h1 : Real.exp (-u) * (1 + u + u ^ 2 / 2) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hq hpos.le]
  have h2 : Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
    by_contra hc
    push_neg at hc
    have hp : (0:ℝ) < 1 + u + u ^ 2 / 2 := by positivity
    have := mul_lt_mul_of_pos_right hc hp
    nlinarith [sq_nonneg (u ^ 2)]
  nlinarith [mul_le_mul_of_nonneg_left huz hu0]

/-- concavity-based key inequality, linear attenuation (s = 1 - z_e) -/
lemma lin_key (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s * (1 - Real.exp (-2)) ≤ (1 + s) / 2 * (1 - Real.exp (-2 * s)) := by
  let φ : ℝ → ℝ := fun s => (1 + s) * (1 - Real.exp (-2 * s))
  have hd : ∀ s, HasDerivAt φ (1 + (1 + 2 * s) * Real.exp (-2 * s)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 s := (hasDerivAt_id s).const_add 1
    have h2 : HasDerivAt (fun s : ℝ => -2 * s) (-2) s := by
      simpa using (hasDerivAt_id s).const_mul (-2:ℝ)
    have h4 := (h2.exp).const_sub 1
    have h5 := h1.mul h4
    exact h5.congr_deriv (by ring)
  have hderiv : deriv φ = fun s => 1 + (1 + 2 * s) * Real.exp (-2 * s) :=
    funext fun s => (hd s).deriv
  have hcont : Continuous φ := by fun_prop
  have hconc : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) φ := by
    apply AntitoneOn.concaveOn_of_deriv (convex_Icc 0 1) hcont.continuousOn
    · exact fun s _ => (hd s).differentiableAt.differentiableWithinAt
    · rw [hderiv, interior_Icc]
      intro a ha b hb hab
      simp only
      have hea : Real.exp (-2 * a) = Real.exp (-2 * b) * Real.exp (2 * (b - a)) := by
        rw [← Real.exp_add]; ring_nf
      have hge := Real.add_one_le_exp (2 * (b - a))
      have hpb := Real.exp_pos (-2 * b)
      rw [hea]
      have ha0 : 0 ≤ a := ha.1.le
      nlinarith [mul_le_mul_of_nonneg_left hge (mul_nonneg (by linarith : (0:ℝ) ≤ 1 + 2 * a) hpb.le),
        mul_nonneg (mul_nonneg ha0 (sub_nonneg.2 hab)) hpb.le]
  have := hconc.2 (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
    (sub_nonneg.2 hs1) hs0 (by ring)
  simp only [φ, smul_eq_mul, mul_zero, mul_one, zero_add, add_zero, Real.exp_zero, sub_self] at this
  nlinarith

/-- concavity-based key inequality, exponential attenuation (s = 1 - z_e) -/
lemma exp_key (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s * (1 - Real.exp (-2)) ≤ Real.exp (-(1 / 2 * (1 - s))) * (1 - Real.exp (-2 * s)) := by
  let ψ : ℝ → ℝ := fun s => Real.exp (s / 2) - Real.exp (-3 / 2 * s)
  have hd : ∀ s, HasDerivAt ψ (1 / 2 * Real.exp (s / 2) + 3 / 2 * Real.exp (-3 / 2 * s)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const 2
    have h2 : HasDerivAt (fun s : ℝ => -3 / 2 * s) (-3 / 2) s := by
      simpa using (hasDerivAt_id s).const_mul (-3 / 2 : ℝ)
    exact ((h1.exp).sub (h2.exp)).congr_deriv (by ring)
  have hderiv : deriv ψ = fun s => 1 / 2 * Real.exp (s / 2) + 3 / 2 * Real.exp (-3 / 2 * s) :=
    funext fun s => (hd s).deriv
  have hcont : Continuous ψ := by fun_prop
  have he2 : Real.exp 2 ≤ 9 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  have hconc : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) ψ := by
    apply AntitoneOn.concaveOn_of_deriv (convex_Icc 0 1) hcont.continuousOn
    · exact fun s _ => (hd s).differentiableAt.differentiableWithinAt
    · rw [hderiv, interior_Icc]
      intro a ha b hb hab
      simp only
      -- X = exp(d/2) - 1 ≥ 0 ; exp(3d/2) - 1 = X (exp d + exp(d/2) + 1) ≥ 3 X
      set d := b - a with hdd
      have hd0 : 0 ≤ d := sub_nonneg.2 hab
      set q := Real.exp (d / 2) with hq
      have hq1 : 1 ≤ q := Real.one_le_exp (by linarith)
      have hb2 : Real.exp (b / 2) = Real.exp (a / 2) * q := by rw [hq, ← Real.exp_add, hdd]; ring_nf
      have ha3 : Real.exp (-3 / 2 * a) = Real.exp (-3 / 2 * b) * q ^ 3 := by
        rw [hq, ← Real.exp_nat_mul, ← Real.exp_add, hdd]; ring_nf
      have hab9 : Real.exp (a / 2) ≤ 9 * Real.exp (-3 / 2 * b) := by
        have : Real.exp (a / 2) = Real.exp (-3 / 2 * b) * Real.exp (a / 2 + 3 / 2 * b) := by
          rw [← Real.exp_add]; ring_nf
        rw [this]
        have hle : Real.exp (a / 2 + 3 / 2 * b) ≤ 9 :=
          le_trans (Real.exp_le_exp.mpr (by linarith [ha.2, hb.2])) he2
        nlinarith [Real.exp_pos (-3 / 2 * b)]
      rw [hb2, ha3]
      have hX : 0 ≤ q - 1 := by linarith
      have hpa := Real.exp_pos (a / 2)
      have hpb := Real.exp_pos (-3 / 2 * b)
      -- goal: 1/2 e_a q + 3/2 e_b ≤ 1/2 e_a + 3/2 e_b q^3
      have hcube : 3 * (q - 1) ≤ q ^ 3 - 1 := by nlinarith [sq_nonneg (q - 1)]
      nlinarith [mul_le_mul_of_nonneg_left hab9 hX, mul_le_mul_of_nonneg_left hcube hpb.le]
  have := hconc.2 (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
    (sub_nonneg.2 hs1) hs0 (by ring)
  simp only [ψ, smul_eq_mul, mul_zero, mul_one, zero_add, add_zero, Real.exp_zero, sub_self,
    zero_div] at this
  -- relate: exp(-(1/2(1-s))) (1 - exp(-2s)) = exp(-1/2) ψ(s), 1 - exp(-2) = exp(-1/2) ψ(1)
  have hA : Real.exp (-(1 / 2 * (1 - s))) = Real.exp (-1 / 2) * Real.exp (s / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hB : Real.exp (-(1 / 2 * (1 - s))) * Real.exp (-2 * s)
      = Real.exp (-1 / 2) * Real.exp (-3 / 2 * s) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hr1 : Real.exp (-(1 / 2 * (1 - s))) * (1 - Real.exp (-2 * s))
      = Real.exp (-1 / 2) * (Real.exp (s / 2) - Real.exp (-3 / 2 * s)) := by
    linear_combination hA - hB
  have hC : Real.exp (-1 / 2) * Real.exp (1 / 2) = 1 := by rw [← Real.exp_add]; norm_num
  have hD : Real.exp (-1 / 2) * Real.exp (-3 / 2 * 1) = Real.exp (-2) := by
    rw [← Real.exp_add]; norm_num
  have hr2 : 1 - Real.exp (-2) = Real.exp (-1 / 2) * (Real.exp (1 / 2) - Real.exp (-3 / 2 * 1)) := by
    linear_combination hD - hC
  rw [hr1, hr2]
  have hp := Real.exp_pos (-1 / 2)
  nlinarith [mul_le_mul_of_nonneg_left this hp.le]

end OSM8A

namespace OSM8A

open OfflineStochMatch.InfinitePatience OfflineStochMatchFull.InfinitePatience

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma integral_exp_lin (s : ℝ) (hs : 0 < s) :
    (∫ x in (0:ℝ)..1, Real.exp (-2 * s * x)) = (1 - Real.exp (-2 * s)) / (2 * s) := by
  have h := intervalIntegral.integral_comp_mul_left (f := Real.exp) (a := (0:ℝ)) (b := 1)
    (show (-2 * s) ≠ 0 by nlinarith)
  rw [h, integral_exp, smul_eq_mul]
  simp only [mul_zero, mul_one, Real.exp_zero]
  have hs' : (2 * s) ≠ 0 := by positivity
  field_simp
  ring

lemma factor_ge (aT : ℝ → ℝ) (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) (x z : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz0 : 0 ≤ z) :
    Real.exp (-(x * z)) ≤ 1 - x * (z * aT z) := by
  rcases haT with h | h <;> subst h
  · calc _ ≤ _ := exp_le_fac_exp x z hx0 hx1 hz0
      _ = _ := by simp only [expAtt]; ring
  · calc _ ≤ _ := exp_le_fac_lin x z hx0 hx1 hz0
      _ = _ := by simp only [linAtt]; ring

lemma prod_ge (N : Finset E) (z : E → ℝ) (aT : ℝ → ℝ)
    (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) (hz : ∀ f, 0 ≤ z f)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-(x * ∑ f ∈ N, z f)) ≤ ∏ f ∈ N, (1 - x * (z f * aT (z f))) := by
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  exact Finset.prod_le_prod (fun f _ => (Real.exp_pos _).le)
    (fun f _ => factor_ge aT haT x (z f) hx0 hx1 (hz f))

lemma int_bound (N : Finset E) (z : E → ℝ) (aT : ℝ → ℝ)
    (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) (hz : ∀ f, 0 ≤ z f)
    (ze : ℝ) (hze0 : 0 ≤ ze) (hze1 : ze ≤ 1) (hsum : ∑ f ∈ N, z f ≤ 2 * (1 - ze)) :
    (1 - Real.exp (-2)) / 2 ≤ aT ze * ∫ x in (0:ℝ)..1, ∏ f ∈ N, (1 - x * (z f * aT (z f))) := by
  obtain ⟨s, rfl⟩ : ∃ s, ze = 1 - s := ⟨1 - ze, by ring⟩
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ 1 := by linarith
  have hsum' : ∑ f ∈ N, z f ≤ 2 * s := by linarith
  have hI : (∫ x in (0:ℝ)..1, Real.exp (-2 * s * x)) ≤
      ∫ x in (0:ℝ)..1, ∏ f ∈ N, (1 - x * (z f * aT (z f))) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (by fun_prop : Continuous fun x : ℝ => Real.exp (-2 * s * x)).intervalIntegrable _ _
    · exact (continuous_finset_prod N (fun f _ => by fun_prop)).intervalIntegrable _ _
    · intro x hx
      obtain ⟨hx0, hx1⟩ := hx
      refine le_trans ?_ (prod_ge N z aT haT hz x hx0 hx1)
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hsum' hx0
      nlinarith
  have haTnn : 0 ≤ aT (1 - s) := by
    rcases haT with h | h <;> subst h
    · exact (Real.exp_pos _).le
    · simp only [linAtt]; linarith
  have he2 : 0 < Real.exp (-2) := Real.exp_pos _
  rcases eq_or_lt_of_le hs0 with h0 | hpos
  · subst h0
    have hI1 : (1:ℝ) ≤ ∫ x in (0:ℝ)..1, ∏ f ∈ N, (1 - x * (z f * aT (z f))) := by
      simpa using hI
    have ha1 : 1 / 2 ≤ aT (1 - 0) := by
      rcases haT with h | h <;> subst h
      · simp only [expAtt]
        have := Real.add_one_le_exp (-(1 / 2 * (1 - 0)))
        linarith
      · simp only [linAtt]; norm_num
    calc (1 - Real.exp (-2)) / 2 ≤ aT (1 - 0) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hI1 haTnn
  · have hkey : s * (1 - Real.exp (-2)) ≤ aT (1 - s) * (1 - Real.exp (-2 * s)) := by
      rcases haT with h | h <;> subst h
      · simp only [expAtt]; exact exp_key s hs0 hs1
      · calc _ ≤ _ := lin_key s hs0 hs1
          _ = _ := by simp only [linAtt]; ring
    calc (1 - Real.exp (-2)) / 2 = s * (1 - Real.exp (-2)) / (2 * s) := by
          field_simp
      _ ≤ aT (1 - s) * (1 - Real.exp (-2 * s)) / (2 * s) := by gcongr
      _ = aT (1 - s) * ∫ x in (0:ℝ)..1, Real.exp (-2 * s * x) := by
          rw [integral_exp_lin s hpos]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hI haTnn

lemma nbr_sum_le (G : EdmondsMatching65.Polyhedron.Graph V E) (p y : E → ℝ)
    (hy : LPFeasible G p (fun _ => ⊤) y) (hp : ∀ f, 0 ≤ p f) (e : E) :
    ∑ f ∈ Nbr G e, p f * y f ≤ 2 * (1 - p e * y e) := by
  have hz : ∀ f, 0 ≤ p f * y f := fun f => mul_nonneg (hp f) (hy.1 f).1
  have hdel : ∀ u, u ∈ G.ends e → ∑ f ∈ (delta G u).erase e, p f * y f ≤ 1 - p e * y e := by
    intro u hu
    have heu : e ∈ delta G u := by simp [delta, hu]
    rw [Finset.sum_erase_eq_sub heu]
    have h1 := hy.2.1 u
    have h2 : (∑ f ∈ delta G u, p f * y f) = ∑ f ∈ delta G u, y f * p f :=
      Finset.sum_congr rfl fun f _ => mul_comm _ _
    linarith
  obtain ⟨u, v, huv⟩ : ∃ u v, G.ends e = s(u, v) :=
    Sym2.ind (f := fun z => ∃ u v, z = s(u, v)) (fun u v => ⟨u, v, rfl⟩) (G.ends e)
  have hu : u ∈ G.ends e := by rw [huv]; exact Sym2.mem_mk_left u v
  have hv : v ∈ G.ends e := by rw [huv]; exact Sym2.mem_mk_right u v
  have hsub : Nbr G e ⊆ (delta G u).erase e ∪ (delta G v).erase e := by
    intro f hf
    simp only [Nbr, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨hfe, w, hwe, hwf⟩ := hf
    rw [huv, Sym2.mem_iff] at hwe
    rcases hwe with rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hfe, by simp [delta, hwf]⟩)
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hfe, by simp [delta, hwf]⟩)
  calc ∑ f ∈ Nbr G e, p f * y f
      ≤ ∑ f ∈ (delta G u).erase e ∪ (delta G v).erase e, p f * y f :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun f _ _ => hz f
    _ ≤ ∑ f ∈ (delta G u).erase e, p f * y f + ∑ f ∈ (delta G v).erase e, p f * y f := by
        rw [← Finset.sum_union_inter]
        have : 0 ≤ ∑ f ∈ (delta G u).erase e ∩ (delta G v).erase e, p f * y f :=
          Finset.sum_nonneg fun f _ => hz f
        linarith
    _ ≤ (1 - p e * y e) + (1 - p e * y e) := add_le_add (hdel u hu) (hdel v hv)
    _ = 2 * (1 - p e * y e) := by ring

end OSM8A


namespace OSM8A

open OfflineStochMatch.InfinitePatience OfflineStochMatchFull.InfinitePatience

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### C3 glue: c * y e ≤ Pr[e probed] -/
lemma core_bound (G : EdmondsMatching65.Polyhedron.Graph V E) (p y : E → ℝ) (aT : ℝ → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2))
    (hy : LPFeasible G p (fun _ => ⊤) y) (e : E) :
    (1 - Real.exp (-2)) / 2 * y e ≤ probProbed G p (fun _ => ⊤) y aT e := by
  have hyb : ∀ f, 0 ≤ y f ∧ y f ≤ 1 := hy.1
  have hz : ∀ f, 0 ≤ p f * y f := fun f => mul_nonneg (hp f).1 (hyb f).1
  have hz1 : ∀ f, p f * y f ≤ 1 := fun f => mul_le_one₀ (hp f).2 (hyb f).1 (hyb f).2
  have ha : ∀ f, 0 ≤ aT (p f * y f) ∧ aT (p f * y f) ≤ 1 :=
    fun f => aT_range aT haT _ (hz f) (hz1 f)
  have hge := probProbed_ge G p y aT e (Nbr G e) (not_mem_Nbr G e) hyb hp ha
    (fun σ Y A P h => by
      obtain ⟨a, b, c⟩ := cev_spec G σ Y A P e h
      exact probed_of_no_active_nbr G σ Y A P e a b c)
  have hav := avg_prod_eq_integral e (Nbr G e) (not_mem_Nbr G e)
    (fun f => y f * aT (p f * y f) * p f)
  beta_reduce at hav
  rw [hav] at hge
  have hib := int_bound (Nbr G e) (fun f => p f * y f) aT haT hz (p e * y e) (hz e) (hz1 e)
    (nbr_sum_le G p y hy (fun f => (hp f).1) e)
  have heq : (∫ x in (0:ℝ)..1, ∏ f ∈ Nbr G e, (1 - x * (y f * aT (p f * y f) * p f))) =
      ∫ x in (0:ℝ)..1, ∏ f ∈ Nbr G e, (1 - x * (p f * y f * aT (p f * y f))) := by
    congr 1; ext x; exact Finset.prod_congr rfl fun f _ => by ring
  rw [heq] at hge
  calc (1 - Real.exp (-2)) / 2 * y e
      ≤ (aT (p e * y e) * ∫ x in (0:ℝ)..1, ∏ f ∈ Nbr G e, (1 - x * (p f * y f * aT (p f * y f))))
        * y e := mul_le_mul_of_nonneg_right hib (hyb e).1
    _ = y e * aT (p e * y e) *
        ∫ x in (0:ℝ)..1, ∏ f ∈ Nbr G e, (1 - x * (p f * y f * aT (p f * y f))) := by ring
    _ ≤ _ := hge

/-- Clauses for a feasible `y` (law, core bound, reward bound). -/
lemma clause_y (G : EdmondsMatching65.Polyhedron.Graph V E) (p w y : E → ℝ) (aT : ℝ → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hw : ∀ e, 0 ≤ w e)
    (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2))
    (hy : LPFeasible G p (fun _ => ⊤) y) :
    AlgorithmProbabilityLaw p y aT ∧
      (∀ e, (1 - Real.exp (-2)) / 2 * y e ≤ probProbed G p (fun _ => ⊤) y aT e) ∧
      (1 - Real.exp (-2)) / 2 * lpObjective p w y ≤ algorithmReward G p (fun _ => ⊤) y w aT := by
  have hcore := core_bound G p y aT hp haT hy
  refine ⟨law_of_feasible G p y _ aT hp haT hy, hcore, ?_⟩
  exact reward_bound G _ p w y aT _ hp hw hcore fun e =>
    prob_terminal G _ p y aT e fun σ Y A P =>
      isProbed_congrP G _ σ Y A (flipF e P) P e fun f hf => by simp [flipF, hf]

end OSM8A

namespace OSM8A

open OfflineStochMatch.InfinitePatience OfflineStochMatchFull.InfinitePatience

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### C7: the random-order CRS is Algorithm 1 with y = 1 -/

lemma probed_top_iff (G : EdmondsMatching65.Polyhedron.Graph V E)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) :
    IsProbed G (fun _ => ⊤) σ Y A P e ↔
      (∀ f, σ f < σ e → IsProbed G (fun _ => ⊤) σ Y A P f → P f = true →
        ∀ v, v ∈ G.ends e → v ∉ G.ends f) ∧ Y e = true ∧ A e = true := by
  constructor
  · rintro ⟨hfree, hY, hA⟩
    exact ⟨fun f hlt hpr hP v hv hvf =>
      (hfree v hv).1 ((matched_stateBefore G _ σ Y A P e v).2 ⟨f, hlt, hpr, hP, hvf⟩), hY, hA⟩
  · rintro ⟨h, hY, hA⟩
    refine ⟨fun v hv => ⟨fun hm => ?_, ENat.natCast_lt_top _⟩, hY, hA⟩
    obtain ⟨f, hlt, hpr, hPf, hvf⟩ := (matched_stateBefore G _ σ Y A P e v).1 hm
    exact h f hlt hpr hPf v hv hvf

open Classical in
lemma accept_iff (G : EdmondsMatching65.Polyhedron.Graph V E)
    (σ : E ≃ Fin (Fintype.card E)) (A P : E → Bool) (e : E) :
    crsAccept G (matchedPrefix G (fun _ => ⊤) σ (fun _ => true) A P (σ e).val) e (P e) (A e) = true ↔
      IsProbed G (fun _ => ⊤) σ (fun _ => true) A P e ∧ P e = true := by
  rw [probed_top_iff]
  unfold crsAccept
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨hP, hA, h⟩
    refine ⟨⟨fun f hlt hpr hPf v hv hvf => h f ?_ v hv hvf, rfl, hA⟩, hP⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt, hpr, hPf⟩
  · rintro ⟨⟨h, -, hA⟩, hP⟩
    refine ⟨hP, hA, fun f hf v hv hvf => ?_⟩
    obtain ⟨-, hlt, hpr, hPf⟩ := Finset.mem_filter.1 hf
    exact h f hlt hpr hPf v hv hvf

lemma mp_step (G : EdmondsMatching65.Polyhedron.Graph V E)
    (σ : E ≃ Fin (Fintype.card E)) (A P : E → Bool) (g : E) :
    matchedPrefix G (fun _ => ⊤) σ (fun _ => true) A P ((σ g).val + 1) =
      crsStep G (matchedPrefix G (fun _ => ⊤) σ (fun _ => true) A P (σ g).val) g (P g) (A g) := by
  have hacc := accept_iff G σ A P g
  have hM : ∀ x, x ∈ matchedPrefix G (fun _ => ⊤) σ (fun _ => true) A P (σ g).val ↔
      (σ x).val < (σ g).val ∧ IsProbed G (fun _ => ⊤) σ (fun _ => true) A P x ∧ P x = true :=
    fun x => by simp [matchedPrefix]
  ext f
  have hM1 : f ∈ matchedPrefix G (fun _ => ⊤) σ (fun _ => true) A P ((σ g).val + 1) ↔
      (σ f).val < (σ g).val + 1 ∧ IsProbed G (fun _ => ⊤) σ (fun _ => true) A P f ∧
        P f = true := by simp [matchedPrefix]
  rw [hM1]
  by_cases hfg : f = g
  · subst hfg
    have hnot : f ∉ matchedPrefix G (fun _ => ⊤) σ (fun _ => true) A P (σ f).val :=
      fun h => lt_irrefl _ ((hM f).1 h).1
    unfold crsStep
    split_ifs with hc
    · simp only [Finset.mem_insert_self, iff_true]
      exact ⟨Nat.lt_succ_self _, hacc.1 hc⟩
    · simp only [hnot, iff_false]
      rintro ⟨-, hpr, hP⟩
      exact hc (hacc.2 ⟨hpr, hP⟩)
  · have hne : (σ f).val ≠ (σ g).val := fun h => hfg (σ.injective (Fin.ext h))
    have hR : f ∈ crsStep G (matchedPrefix G (fun _ => ⊤) σ (fun _ => true) A P (σ g).val) g
        (P g) (A g) ↔ f ∈ matchedPrefix G (fun _ => ⊤) σ (fun _ => true) A P (σ g).val := by
      unfold crsStep; split_ifs <;> simp [Finset.mem_insert, hfg]
    rw [hR, hM]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

lemma crs_coupling (G : EdmondsMatching65.Polyhedron.Graph V E)
    (σ : E ≃ Fin (Fintype.card E)) (A P : E → Bool) (k : ℕ) :
    crsPrefix G σ A P k = matchedPrefix G (fun _ => ⊤) σ (fun _ => true) A P k := by
  induction k with
  | zero => ext f; simp [crsPrefix, matchedPrefix]
  | succ k ih =>
    by_cases hk : k < Fintype.card E
    · have hg : (σ (σ.symm ⟨k, hk⟩)).val = k := by simp
      have hstep : crsPrefix G σ A P (k + 1) = crsStep G (crsPrefix G σ A P k) (σ.symm ⟨k, hk⟩)
          (P (σ.symm ⟨k, hk⟩)) (A (σ.symm ⟨k, hk⟩)) := by
        unfold crsPrefix; rw [take_succ_arrival σ k hk, List.foldl_append]; rfl
      rw [hstep, ih]
      have := mp_step G σ A P (σ.symm ⟨k, hk⟩)
      rw [hg] at this
      exact this.symm
    · have h1 : (arrivalList σ).take (k + 1) = (arrivalList σ).take k := by
        rw [List.take_of_length_le, List.take_of_length_le] <;> simp [arrivalList] <;> omega
      have h2 : crsPrefix G σ A P (k + 1) = crsPrefix G σ A P k := by
        unfold crsPrefix; rw [h1]
      rw [h2, ih]
      ext f
      simp only [matchedPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
      have := (σ f).isLt
      constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨by omega, h'⟩

lemma foldl_crs_congr (G : EdmondsMatching65.Polyhedron.Graph V E) (A P A' P' : E → Bool) :
    ∀ (L : List E) (M : Finset E), (∀ e ∈ L, A e = A' e ∧ P e = P' e) →
      L.foldl (fun M e => crsStep G M e (P e) (A e)) M =
        L.foldl (fun M e => crsStep G M e (P' e) (A' e)) M
  | [], _, _ => rfl
  | e :: L, M, h => by
      simp only [List.foldl_cons]
      rw [(h e (by simp)).1, (h e (by simp)).2]
      exact foldl_crs_congr G A P A' P' L _ fun x hx => h x (List.mem_cons_of_mem _ hx)

lemma crs_operational (G : EdmondsMatching65.Polyhedron.Graph V E) : CRSOperational G := by
  obtain ⟨-, hop2, -⟩ := operational G
  refine ⟨fun σ A P k => ?_, fun σ σ' A P A' P' k hL h => ?_, fun σ A P e => ?_⟩
  · rw [crs_coupling, crs_coupling]
    obtain ⟨hm, hP, hsub⟩ := hop2 σ (fun _ => true) A P k
    refine ⟨hm, fun e he => ⟨hP e he, ?_⟩, hsub⟩
    simp only [matchedPrefix, Finset.mem_filter] at he
    exact he.2.1
  · unfold crsPrefix
    rw [hL] at h ⊢
    exact foldl_crs_congr G A P A' P' _ ∅ h
  · unfold crsOutput
    rw [crs_coupling, crs_coupling, accept_iff]
    simp [matchedPrefix]

open Classical in
lemma prob_y_one (p : E → ℝ) (aT : ℝ → ℝ)
    (ev : (E ≃ Fin (Fintype.card E)) → (E → Bool) → (E → Bool) → (E → Bool) → Prop) :
    prob p (fun _ => 1) aT ev =
      prob p (fun _ => 1) aT (fun σ _ A P => ev σ (fun _ => true) A P) := by
  have key : ∀ g : (E → Bool) → ℝ,
      ∑ Y : E → Bool, coinWeight (fun _ : E => (1:ℝ)) Y * g Y = g (fun _ => true) := by
    intro g
    rw [Finset.sum_eq_single (fun _ => true)]
    · simp [coinWeight, bern]
    · intro Y _ hY
      obtain ⟨f, hf⟩ : ∃ f, Y f = false := by
        by_contra h
        push_neg at h
        exact hY (funext fun f => by simpa using h f)
      rw [show coinWeight (fun _ : E => (1:ℝ)) Y = 0 from
        Finset.prod_eq_zero (Finset.mem_univ f) (by simp [bern, hf]), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  unfold prob
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [key, key]

lemma rcrs (G : EdmondsMatching65.Polyhedron.Graph V E) (ζ : E → ℝ) (aT : ℝ → ℝ)
    (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) (hz : DegreeRelaxation G ζ) :
    LPFeasible G ζ (fun _ => ⊤) (fun _ => 1) ∧ BalancedRCRS G ζ aT ((1 - Real.exp (-2)) / 2) := by
  have hfeas : LPFeasible G ζ (fun _ => ⊤) (fun _ => 1) :=
    ⟨fun _ => ⟨zero_le_one, le_refl _⟩, fun v => by simpa using hz.2 v,
      fun v n h => by simp at h⟩
  have hζ : ∀ e, 0 ≤ ζ e ∧ ζ e ≤ 1 := hz.1
  have hlaw := law_of_feasible G ζ (fun _ => 1) _ aT hζ haT hfeas
  refine ⟨hfeas, crs_operational G, hlaw.1, fun ev => hlaw.2.1 _, fun σ₀ => hlaw.2.2 σ₀,
    fun e => ?_, fun σ A P => crs_coupling G σ A P _⟩
  have hcore := core_bound G ζ (fun _ => 1) aT hζ haT hfeas e
  have hterm := prob_terminal G (fun _ => ⊤) ζ (fun _ => 1) aT e fun σ Y A P =>
    isProbed_congrP G (fun _ => ⊤) σ Y A (flipF e P) P e fun f hf => by simp [flipF, hf]
  have h1 : crsProb ζ aT (fun σ A P => e ∈ crsOutput G σ A P) =
      prob ζ (fun _ => 1) aT (fun σ Y A P => e ∈ terminalMatching G (fun _ => ⊤) σ Y A P) := by
    unfold crsProb
    rw [prob_y_one ζ aT (fun σ Y A P => e ∈ terminalMatching G (fun _ => ⊤) σ Y A P)]
    simp only [crsOutput, crs_coupling, terminalMatching]
  rw [h1, hterm]
  calc (1 - Real.exp (-2)) / 2 * ζ e = ζ e * ((1 - Real.exp (-2)) / 2 * 1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcore (hζ e).1

end OSM8A

namespace OSM8B

open OfflineStochMatch.InfinitePatience OfflineStochMatchFull.InfinitePatience

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### PMF averages -/

lemma pmf_sum_toReal {α : Type} [Fintype α] (q : PMF α) : ∑ a, (q a).toReal = 1 := by
  have h1 := q.tsum_coe
  rw [tsum_fintype] at h1
  rw [← ENNReal.toReal_sum (fun a _ => q.apply_ne_top a), h1, ENNReal.toReal_one]

lemma avg_le {α : Type} [Fintype α] (q : PMF α) (f : α → ℝ) (B : ℝ)
    (h : ∀ a, q a ≠ 0 → f a ≤ B) : ∑ a, (q a).toReal * f a ≤ B := by
  calc ∑ a, (q a).toReal * f a ≤ ∑ a, (q a).toReal * B := by
        apply Finset.sum_le_sum; intro a _
        by_cases ha : q a = 0
        · simp [ha]
        · exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg
    _ = B := by rw [← Finset.sum_mul, pmf_sum_toReal, one_mul]

lemma le_avg {α : Type} [Fintype α] (q : PMF α) (f : α → ℝ) (B : ℝ)
    (h : ∀ a, q a ≠ 0 → B ≤ f a) : B ≤ ∑ a, (q a).toReal * f a := by
  calc B = ∑ a, (q a).toReal * B := by rw [← Finset.sum_mul, pmf_sum_toReal, one_mul]
    _ ≤ ∑ a, (q a).toReal * f a := by
        apply Finset.sum_le_sum; intro a _
        by_cases ha : q a = 0
        · simp [ha]
        · exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg

lemma sum_sub_avg {α : Type} [Fintype α] (q : PMF α) (m : α → ℝ) (x : ℝ) :
    (∑ a, (q a).toReal * m a) - x = ∑ a, (q a).toReal * (m a - x) := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, pmf_sum_toReal, one_mul]

lemma sum_pure {α : Type} [Fintype α] [DecidableEq α] (a : α) (f : α → ℝ) :
    ∑ x, ((PMF.pure a) x).toReal * f x = f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; rw [PMF.pure_apply_of_ne _ _ hb]; simp
  · simp

/-! ### Generic bounds on policy evaluation at legal histories -/

lemma eval_le (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (p : E → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (π : ProbingPolicy G t) (T : ProbeHistory E → ℝ)
    (F : ℕ → ProbeHistory E → ℝ)
    (h0 : ∀ h, LegalHistory G t h → T h ≤ F 0 h)
    (hstop : ∀ n h, LegalHistory G t h → T h ≤ F (n + 1) h)
    (hstep : ∀ n h e, LegalHistory G t h → LegalNext G t h e →
      (1 - p e) * F n (h ++ [(e, false)]) + p e * F n (h ++ [(e, true)]) ≤ F (n + 1) h) :
    ∀ n h, LegalHistory G t h → policyEvalFrom G t p π T n h ≤ F n h := by
  intro n
  induction n with
  | zero => intro h hh; exact h0 h hh
  | succ n ih =>
    intro h hh
    simp only [policyEvalFrom]
    apply avg_le
    intro act hact
    cases act with
    | none => exact hstop n h hh
    | some e =>
      have hl : LegalNext G t h e := by
        by_contra hn; exact hact (π.legal h hh e hn)
      have h1p : 0 ≤ 1 - p e := by linarith [(hp e).2]
      refine le_trans ?_ (hstep n h e hh hl)
      exact add_le_add (mul_le_mul_of_nonneg_left (ih _ (LegalHistory.snoc hh hl)) h1p)
        (mul_le_mul_of_nonneg_left (ih _ (LegalHistory.snoc hh hl)) (hp e).1)

lemma le_eval (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (p : E → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (π : ProbingPolicy G t) (T : ProbeHistory E → ℝ)
    (F : ℕ → ProbeHistory E → ℝ)
    (h0 : ∀ h, LegalHistory G t h → F 0 h ≤ T h)
    (hstop : ∀ n h, LegalHistory G t h → F (n + 1) h ≤ T h)
    (hstep : ∀ n h e, LegalHistory G t h → LegalNext G t h e →
      F (n + 1) h ≤ (1 - p e) * F n (h ++ [(e, false)]) + p e * F n (h ++ [(e, true)])) :
    ∀ n h, LegalHistory G t h → F n h ≤ policyEvalFrom G t p π T n h := by
  intro n
  induction n with
  | zero => intro h hh; exact h0 h hh
  | succ n ih =>
    intro h hh
    simp only [policyEvalFrom]
    apply le_avg
    intro act hact
    cases act with
    | none => exact hstop n h hh
    | some e =>
      have hl : LegalNext G t h e := by
        by_contra hn; exact hact (π.legal h hh e hn)
      have h1p : 0 ≤ 1 - p e := by linarith [(hp e).2]
      refine le_trans (hstep n h e hh hl) ?_
      exact add_le_add (mul_le_mul_of_nonneg_left (ih _ (LegalHistory.snoc hh hl)) h1p)
        (mul_le_mul_of_nonneg_left (ih _ (LegalHistory.snoc hh hl)) (hp e).1)

lemma eval_bounds (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (p : E → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (π : ProbingPolicy G t) (T : ProbeHistory E → ℝ)
    (lo hi : ℝ) (hT : ∀ h, LegalHistory G t h → lo ≤ T h ∧ T h ≤ hi) :
    ∀ n h, LegalHistory G t h →
      lo ≤ policyEvalFrom G t p π T n h ∧ policyEvalFrom G t p π T n h ≤ hi := by
  intro n h hh
  refine ⟨le_eval G t p hp π T (fun _ _ => lo) (fun h hh => (hT h hh).1)
      (fun _ h hh => (hT h hh).1)
      (fun _ _ e _ _ => by
        show lo ≤ (1 - p e) * lo + p e * lo
        exact le_of_eq (by ring)) n h hh,
    eval_le G t p hp π T (fun _ _ => hi) (fun h hh => (hT h hh).2)
      (fun _ h hh => (hT h hh).2)
      (fun _ _ e _ _ => by
        show (1 - p e) * hi + p e * hi ≤ hi
        exact le_of_eq (by ring)) n h hh⟩

/-! ### Linearity in the terminal reward -/

lemma eval_sum (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (p : E → ℝ)
    (π : ProbingPolicy G t) {ι : Type} (s : Finset ι) (c : ι → ℝ)
    (T : ι → ProbeHistory E → ℝ) :
    ∀ n h, policyEvalFrom G t p π (fun h => ∑ i ∈ s, c i * T i h) n h
      = ∑ i ∈ s, c i * policyEvalFrom G t p π (T i) n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    simp only [policyEvalFrom]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun act _ => ?_
    cases act with
    | none =>
      dsimp only
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    | some e =>
      dsimp only
      rw [ih, ih, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Indicators: committed edge, probed edge -/

noncomputable def indA (e0 : E) (h : ProbeHistory E) : ℝ := if (e0, true) ∈ h then 1 else 0

noncomputable def indB (e0 : E) (h : ProbeHistory E) : ℝ :=
  if e0 ∈ h.map Prod.fst then 1 else 0

lemma indA_snoc (f e : E) (b : Bool) (h : ProbeHistory E) :
    indA f (h ++ [(e, b)]) = if f = e ∧ b = true then 1 else indA f h := by
  unfold indA
  by_cases hfe : f = e ∧ b = true
  · obtain ⟨rfl, rfl⟩ := hfe; simp
  · rw [if_neg hfe]
    have : (f, true) ∈ h ++ [(e, b)] ↔ (f, true) ∈ h := by
      simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro (h1 | ⟨h1, h2⟩)
        · exact h1
        · exact absurd ⟨h1, h2.symm⟩ hfe
      · exact Or.inl
    simp only [this]

lemma indB_snoc (f e : E) (b : Bool) (h : ProbeHistory E) :
    indB f (h ++ [(e, b)]) = if f = e then 1 else indB f h := by
  unfold indB
  by_cases hfe : f = e
  · subst hfe; simp
  · rw [if_neg hfe]; simp [hfe]

lemma mem_hm (h : ProbeHistory E) (e : E) : e ∈ historyMatching h ↔ (e, true) ∈ h := by
  simp only [historyMatching, List.mem_toFinset, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨hm, hb⟩, rfl⟩
    simp at hb
    subst hb
    exact hm
  · intro hm
    exact ⟨(e, true), ⟨hm, rfl⟩, rfl⟩

/-- Pr[e committed] = p_e Pr[e probed], as an identity of evaluations at legal histories. -/
lemma diff_id (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (p : E → ℝ)
    (π : ProbingPolicy G t) (e0 : E) :
    ∀ n h, LegalHistory G t h →
      policyEvalFrom G t p π (indA e0) n h - indA e0 h =
        p e0 * (policyEvalFrom G t p π (indB e0) n h - indB e0 h) := by
  intro n
  induction n with
  | zero => intro h _; simp [policyEvalFrom]
  | succ n ih =>
    intro h hh
    simp only [policyEvalFrom]
    rw [sum_sub_avg, sum_sub_avg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun act _ => ?_
    by_cases hz : π.choose h act = 0
    · simp [hz]
    cases act with
    | none => simp
    | some f =>
      have hl : LegalNext G t h f := by
        by_contra hn; exact hz (π.legal h hh f hn)
      have hf : f ∉ h.map Prod.fst := hl.1
      have i0 := ih _ (LegalHistory.snoc (b := false) hh hl)
      have i1 := ih _ (LegalHistory.snoc (b := true) hh hl)
      rw [indA_snoc, indB_snoc] at i0 i1
      dsimp only
      by_cases hfe : f = e0
      · have hf' : e0 ∉ h.map Prod.fst := hfe ▸ hf
        have a0 : indA e0 h = 0 := by
          unfold indA; rw [if_neg]; intro hm; exact hf' (List.mem_map.2 ⟨_, hm, rfl⟩)
        have b0 : indB e0 h = 0 := by unfold indB; rw [if_neg hf']
        rw [if_neg (by simp), if_pos hfe.symm, a0] at i0
        rw [if_pos ⟨hfe.symm, rfl⟩, if_pos hfe.symm] at i1
        have hpe : p f = p e0 := by rw [hfe]
        rw [a0, b0]
        linear_combination (π.choose h (some f)).toReal * ((1 - p f) * i0 + p f * i1)
          + (π.choose h (some f)).toReal * hpe
      · rw [if_neg (fun hc => hfe hc.1.symm), if_neg (fun hc => hfe hc.symm)] at i0 i1
        linear_combination (π.choose h (some f)).toReal * ((1 - p f) * i0 + p f * i1)

/-- In a legal history at most one committed edge meets each vertex. -/
lemma legal_sum_le (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (v : V) :
    ∀ h, LegalHistory G t h → ∑ f ∈ delta G v, indA f h ≤ 1 := by
  intro h hh
  induction hh with
  | nil => simp [indA]
  | @snoc h e b hh hl ih =>
    rw [Finset.sum_congr rfl fun f _ => indA_snoc f e b h]
    by_cases hc : b = true ∧ v ∈ G.ends e
    · have h0 : ∀ f ∈ delta G v, indA f h = 0 := by
        intro f hf
        have hv := (hl.2 v hc.2).1
        simp only [historyState, Finset.mem_filter, Finset.mem_univ, true_and, not_exists,
          not_and] at hv
        have hfv : v ∈ G.ends f := by simpa [delta] using hf
        unfold indA; rw [if_neg]; intro hm; exact hv f ((mem_hm h f).2 hm) hfv
      calc ∑ f ∈ delta G v, (if f = e ∧ b = true then (1 : ℝ) else indA f h)
          = ∑ f ∈ delta G v, (if f = e then (1 : ℝ) else 0) :=
            Finset.sum_congr rfl fun f hf => by
              by_cases hfe : f = e
              · simp [hfe, hc.1]
              · simp [hfe, h0 f hf]
        _ ≤ 1 := by rw [Finset.sum_ite_eq']; split_ifs <;> norm_num
    · calc ∑ f ∈ delta G v, (if f = e ∧ b = true then (1 : ℝ) else indA f h)
          = ∑ f ∈ delta G v, indA f h :=
            Finset.sum_congr rfl fun f hf => by
              rw [if_neg]; rintro ⟨rfl, hb⟩; exact hc ⟨hb, by simpa [delta] using hf⟩
        _ ≤ 1 := ih

/-! ### Policy reward as an LP objective -/

lemma reward_eq (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (p w : E → ℝ)
    (π : ProbingPolicy G t) :
    policyReward G p t w π =
      lpObjective p w (fun e => policyEvalFrom G t p π (indB e) (Fintype.card E) []) := by
  unfold policyReward lpObjective
  have hT : (fun h : ProbeHistory E => ∑ e ∈ historyMatching h, w e) =
      fun h => ∑ e ∈ Finset.univ, w e * indA e h := by
    funext h
    have : historyMatching h = Finset.univ.filter (fun e => (e, true) ∈ h) := by
      ext e; simp [mem_hm]
    rw [this, Finset.sum_filter]
    simp only [indA, mul_ite, mul_one, mul_zero]
  rw [hT, eval_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hd := diff_id G t p π e (Fintype.card E) [] LegalHistory.nil
  have hA0 : indA e ([] : ProbeHistory E) = 0 := by simp [indA]
  have hB0 : indB e ([] : ProbeHistory E) = 0 := by simp [indB]
  rw [hA0, hB0] at hd
  linear_combination w e * hd

lemma lpfeas_top (G : EdmondsMatching65.Polyhedron.Graph V E) (p y : E → ℝ) :
    LPFeasible G p (fun _ => ⊤) y ↔
      (∀ f, 0 ≤ y f ∧ y f ≤ 1) ∧ ∀ v, ∑ f ∈ delta G v, y f * p f ≤ 1 := by
  unfold LPFeasible
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · intro h
    exact ⟨h.1, h.2, fun v n hn => by simp at hn⟩

lemma X_feas (G : EdmondsMatching65.Polyhedron.Graph V E) (p : E → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (π : ProbingPolicy G (fun _ => ⊤)) :
    LPFeasible G p (fun _ => ⊤)
      (fun e => policyEvalFrom G (fun _ => ⊤) p π (indB e) (Fintype.card E) []) := by
  rw [lpfeas_top]
  refine ⟨fun f => eval_bounds G _ p hp π (indB f) 0 1 (fun h _ => by
      unfold indB; split_ifs <;> norm_num) _ [] LegalHistory.nil, fun v => ?_⟩
  calc ∑ f ∈ delta G v, policyEvalFrom G (fun _ => ⊤) p π (indB f) (Fintype.card E) [] * p f
      = ∑ f ∈ delta G v, 1 * policyEvalFrom G (fun _ => ⊤) p π (indA f) (Fintype.card E) [] :=
        Finset.sum_congr rfl fun f _ => by
          have hd := diff_id G _ p π f (Fintype.card E) [] LegalHistory.nil
          have hA0 : indA f ([] : ProbeHistory E) = 0 := by simp [indA]
          have hB0 : indB f ([] : ProbeHistory E) = 0 := by simp [indB]
          rw [hA0, hB0] at hd
          linear_combination -hd
    _ = policyEvalFrom G (fun _ => ⊤) p π (fun h => ∑ f ∈ delta G v, 1 * indA f h)
          (Fintype.card E) [] := (eval_sum G _ p π (delta G v) (fun _ => 1) indA _ []).symm
    _ ≤ 1 := (eval_bounds G _ p hp π _ 0 1 (fun h hh => ⟨Finset.sum_nonneg fun f _ => by
            unfold indA; split_ifs <;> norm_num, by
            simpa using legal_sum_le G _ v h hh⟩) _ [] LegalHistory.nil).2

/-! ### Dynamic programming: an optimal policy exists -/

open Classical in
noncomputable def legalSet (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (h : ProbeHistory E) : Finset (Option E) :=
  Finset.univ.filter (fun a => ∀ e, a = some e → LegalNext G t h e)

lemma none_mem_legalSet (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (h : ProbeHistory E) : none ∈ legalSet G t h := by
  simp [legalSet]

lemma some_mem_legalSet (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (h : ProbeHistory E) (e : E) (hl : LegalNext G t h e) : some e ∈ legalSet G t h := by
  simp [legalSet, hl]

noncomputable def gAct (p : E → ℝ) (T W : ProbeHistory E → ℝ) (h : ProbeHistory E) :
    Option E → ℝ
  | none => T h
  | some e => (1 - p e) * W (h ++ [(e, false)]) + p e * W (h ++ [(e, true)])

noncomputable def Vdp (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (p : E → ℝ)
    (T : ProbeHistory E → ℝ) : ℕ → ProbeHistory E → ℝ
  | 0, h => T h
  | n + 1, h => (legalSet G t h).sup' ⟨none, none_mem_legalSet G t h⟩ (gAct p T (Vdp G t p T n) h)

lemma Vdp_succ (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (p : E → ℝ)
    (T : ProbeHistory E → ℝ) (n : ℕ) (h : ProbeHistory E) :
    Vdp G t p T (n + 1) h =
      (legalSet G t h).sup' ⟨none, none_mem_legalSet G t h⟩ (gAct p T (Vdp G t p T n) h) := rfl

noncomputable def bestAct (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (p : E → ℝ) (T : ProbeHistory E → ℝ) (n : ℕ) (h : ProbeHistory E) : Option E :=
  Classical.choose (Finset.exists_max_image (legalSet G t h) (gAct p T (Vdp G t p T n) h)
    ⟨none, none_mem_legalSet G t h⟩)

lemma bestAct_spec (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (p : E → ℝ) (T : ProbeHistory E → ℝ) (n : ℕ) (h : ProbeHistory E) :
    bestAct G t p T n h ∈ legalSet G t h ∧
      ∀ x ∈ legalSet G t h, gAct p T (Vdp G t p T n) h x ≤
        gAct p T (Vdp G t p T n) h (bestAct G t p T n h) :=
  Classical.choose_spec (Finset.exists_max_image (legalSet G t h) (gAct p T (Vdp G t p T n) h)
    ⟨none, none_mem_legalSet G t h⟩)

lemma Vdp_succ_eq (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (p : E → ℝ) (T : ProbeHistory E → ℝ) (n : ℕ) (h : ProbeHistory E) :
    Vdp G t p T (n + 1) h = gAct p T (Vdp G t p T n) h (bestAct G t p T n h) := by
  rw [Vdp_succ]
  exact le_antisymm (Finset.sup'_le _ _ (bestAct_spec G t p T n h).2)
    (Finset.le_sup' _ (bestAct_spec G t p T n h).1)

open Classical in
lemma bestAct_legal (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (p : E → ℝ) (T : ProbeHistory E → ℝ) (n : ℕ) (h : ProbeHistory E) (e : E)
    (hs : bestAct G t p T n h = some e) : LegalNext G t h e :=
  (Finset.mem_filter.1 (bestAct_spec G t p T n h).1).2 e hs

noncomputable def dpPolicy (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (p : E → ℝ) (T : ProbeHistory E → ℝ) : ProbingPolicy G t where
  choose h := PMF.pure (bestAct G t p T (Fintype.card E - h.length - 1) h)
  legal := by
    intro h _ e hn
    exact PMF.pure_apply_of_ne _ _ (fun heq => hn (bestAct_legal G t p T _ h e heq.symm))

lemma eval_dp (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (p : E → ℝ) (T : ProbeHistory E → ℝ) :
    ∀ n h, h.length + n = Fintype.card E →
      policyEvalFrom G t p (dpPolicy G t p T) T n h = Vdp G t p T n h := by
  intro n
  induction n with
  | zero => intro h _; rfl
  | succ n ih =>
    intro h hlen
    simp only [policyEvalFrom]
    have hn : Fintype.card E - h.length - 1 = n := by omega
    have hc : (dpPolicy G t p T).choose h = PMF.pure (bestAct G t p T n h) := by
      show PMF.pure (bestAct G t p T (Fintype.card E - h.length - 1) h) = _
      rw [hn]
    rw [hc, sum_pure, Vdp_succ_eq]
    rcases bestAct G t p T n h with _ | e
    · rfl
    · dsimp only [gAct]
      rw [ih _ (by simp; omega), ih _ (by simp; omega)]

lemma eval_le_Vdp (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (T : ProbeHistory E → ℝ)
    (π : ProbingPolicy G t) :
    ∀ n h, LegalHistory G t h → policyEvalFrom G t p π T n h ≤ Vdp G t p T n h :=
  eval_le G t p hp π T (Vdp G t p T) (fun h _ => le_refl _)
    (fun n h _ => by
      rw [Vdp_succ]
      exact Finset.le_sup' (gAct p T (Vdp G t p T n) h) (none_mem_legalSet G t h))
    (fun n h e _ hl => by
      rw [Vdp_succ]
      exact Finset.le_sup' (gAct p T (Vdp G t p T n) h) (some_mem_legalSet G t h e hl))

lemma opt_attained (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (w : E → ℝ) :
    ∃ π : ProbingPolicy G t, policyReward G p t w π = OPT G p t w := by
  let T : ProbeHistory E → ℝ := fun h => ∑ e ∈ historyMatching h, w e
  refine ⟨dpPolicy G t p T, ?_⟩
  have hval : policyReward G p t w (dpPolicy G t p T) = Vdp G t p T (Fintype.card E) [] :=
    eval_dp G t p T _ [] (by simp)
  have hg : IsGreatest (policyRewards G p t w) (policyReward G p t w (dpPolicy G t p T)) :=
    ⟨⟨_, rfl⟩, by
      rintro _ ⟨π', rfl⟩
      rw [hval]
      exact eval_le_Vdp G t p hp T π' _ [] LegalHistory.nil⟩
  exact hg.csSup_eq.symm

/-! ### LP maximizer by compactness -/

lemma exists_max (G : EdmondsMatching65.Polyhedron.Graph V E) (p w : E → ℝ) :
    ∃ y, IsLPMaximizer G p (fun _ => ⊤) w y := by
  have hS : {y : E → ℝ | LPFeasible G p (fun _ => ⊤) y} =
      (⋂ f, {y : E → ℝ | 0 ≤ y f} ∩ {y | y f ≤ 1}) ∩
        ⋂ v, {y : E → ℝ | ∑ f ∈ delta G v, y f * p f ≤ 1} := by
    ext y
    simp only [Set.mem_setOf_eq, lpfeas_top, Set.mem_inter_iff, Set.mem_iInter]
  have hcl : IsClosed {y : E → ℝ | LPFeasible G p (fun _ => ⊤) y} := by
    rw [hS]
    exact (isClosed_iInter fun f => (isClosed_le continuous_const (continuous_apply f)).inter
      (isClosed_le (continuous_apply f) continuous_const)).inter
      (isClosed_iInter fun v => isClosed_le (continuous_finsetSum _ fun f _ =>
        (continuous_apply f).mul continuous_const) continuous_const)
  have hK : IsCompact {y : E → ℝ | LPFeasible G p (fun _ => ⊤) y} :=
    (isCompact_Icc (a := (0 : E → ℝ)) (b := 1)).of_isClosed_subset hcl (fun y hy => by
      have h' := ((lpfeas_top G p y).1 hy).1
      exact ⟨fun e => (h' e).1, fun e => (h' e).2⟩)
  have hne : {y : E → ℝ | LPFeasible G p (fun _ => ⊤) y}.Nonempty :=
    ⟨0, by rw [Set.mem_setOf_eq, lpfeas_top]; simp⟩
  have hc : Continuous (lpObjective p w) := by unfold lpObjective; fun_prop
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne hc.continuousOn
  refine ⟨y, hy, ?_⟩
  have hg : IsGreatest (lpRewards G p (fun _ => ⊤) w) (lpObjective p w y) :=
    ⟨⟨y, hy, rfl⟩, by rintro _ ⟨z, hz, rfl⟩; exact isMaxOn_iff.1 hmax z hz⟩
  exact hg.csSup_eq.symm

/-! ### Package: clauses 5, 7 and the OPT/policy bound of clause 8 -/

theorem optima_pack (G : EdmondsMatching65.Polyhedron.Graph V E) (p w : E → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hw : ∀ e, 0 ≤ w e) :
    OptimaAttained G p (fun _ => ⊤) w ∧ (∃ y, IsLPMaximizer G p (fun _ => ⊤) w y) ∧
    (∀ π : ProbingPolicy G (fun _ => ⊤),
      policyReward G p (fun _ => ⊤) w π ≤ lpValue G p (fun _ => ⊤) w) ∧
    OPT G p (fun _ => ⊤) w ≤ lpValue G p (fun _ => ⊤) w := by
  have hobj : ∀ y, LPFeasible G p (fun _ => ⊤) y →
      0 ≤ lpObjective p w y ∧ lpObjective p w y ≤ ∑ e, w e := by
    intro y hy
    have h' := ((lpfeas_top G p y).1 hy).1
    unfold lpObjective
    refine ⟨Finset.sum_nonneg fun e _ => mul_nonneg (mul_nonneg (hw e) (hp e).1) (h' e).1,
      Finset.sum_le_sum fun e _ => ?_⟩
    rw [mul_assoc]
    exact mul_le_of_le_one_right (hw e) (mul_le_one₀ (hp e).2 (h' e).1 (h' e).2)
  have hrew : ∀ π : ProbingPolicy G (fun _ => ⊤),
      0 ≤ policyReward G p (fun _ => ⊤) w π ∧ policyReward G p (fun _ => ⊤) w π ≤ ∑ e, w e :=
    fun π => eval_bounds G _ p hp π (fun h => ∑ e ∈ historyMatching h, w e) 0 (∑ e, w e)
      (fun h _ => ⟨Finset.sum_nonneg fun e _ => hw e,
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun e _ _ => hw e)⟩) _ [] LegalHistory.nil
  have hbddLP : BddAbove (lpRewards G p (fun _ => ⊤) w) :=
    ⟨∑ e, w e, by rintro _ ⟨y, hy, rfl⟩; exact (hobj y hy).2⟩
  have hπlp : ∀ π : ProbingPolicy G (fun _ => ⊤),
      policyReward G p (fun _ => ⊤) w π ≤ lpValue G p (fun _ => ⊤) w := by
    intro π
    rw [reward_eq]
    exact le_csSup hbddLP ⟨_, X_feas G p hp π, rfl⟩
  obtain ⟨πs, hπs⟩ := opt_attained G (fun _ => ⊤) p hp w
  have hmax := exists_max G p w
  refine ⟨⟨⟨_, fun _ => 0, by rw [lpfeas_top]; simp, rfl⟩, hbddLP,
      ⟨_, stopPolicy G (fun _ => ⊤), rfl⟩,
      ⟨∑ e, w e, by rintro _ ⟨π, rfl⟩; exact (hrew π).2⟩, hmax, ⟨πs, hπs⟩, hrew, hobj⟩,
    hmax, hπlp, ?_⟩
  rw [← hπs]
  exact hπlp πs

end OSM8B

open OfflineStochMatchFull.InfinitePatience OfflineStochMatch.InfinitePatience in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (p w : E → ℝ) (aT : ℝ → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hw : ∀ e, 0 ≤ w e)
    (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) :
    let t : V → ℕ∞ := fun _ => ⊤
    let c : ℝ := (1 - Real.exp (-2)) / 2
    (∫ x in (0 : ℝ)..1, Real.exp (-2 * x)) = c ∧
    0 < c ∧ c ≤ 1 ∧
    AlgorithmOperational G t ∧ OptimaAttained G p t w ∧
    (∀ y : E → ℝ, LPFeasible G p t y →
      AlgorithmProbabilityLaw p y aT ∧
      (∀ e, c * y e ≤ probProbed G p t y aT e) ∧
      c * lpObjective p w y ≤ algorithmReward G p t y w aT) ∧
    (∃ yStar : E → ℝ, IsLPMaximizer G p t w yStar) ∧
    (∀ yStar : E → ℝ, IsLPMaximizer G p t w yStar →
      (∀ π : ProbingPolicy G t,
        c * policyReward G p t w π ≤ algorithmReward G p t yStar w aT) ∧
      c * OPT G p t w ≤ algorithmReward G p t yStar w aT) ∧
    (∀ ζ : E → ℝ, DegreeRelaxation G ζ →
      LPFeasible G ζ t (fun _ => 1) ∧ BalancedRCRS G ζ aT c) := by
  intro t c
  obtain ⟨hopt, hmax, hπlp, hOPT⟩ := OSM8B.optima_pack G p w hp hw
  refine ⟨OSM8A.integral_c, OSM8A.c_pos, OSM8A.c_le_one, OSM8A.operational G, hopt,
    fun y hy => OSM8A.clause_y G p w y aT hp hw haT hy, hmax, ?_,
    fun ζ hz => OSM8A.rcrs G ζ aT haT hz⟩
  intro yStar hys
  have hc := OSM8A.clause_y G p w yStar aT hp hw haT hys.1
  have hval : lpObjective p w yStar = lpValue G p t w := hys.2
  have c0 : 0 ≤ c := OSM8A.c_pos.le
  refine ⟨fun π => ?_, ?_⟩
  · calc c * policyReward G p t w π ≤ c * lpObjective p w yStar := by
          rw [hval]; exact mul_le_mul_of_nonneg_left (hπlp π) c0
      _ ≤ _ := hc.2.2
  · calc c * OPT G p t w ≤ c * lpObjective p w yStar := by
          rw [hval]; exact mul_le_mul_of_nonneg_left hOPT c0
      _ ≤ _ := hc.2.2
