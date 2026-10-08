-- Prove2me | solution 1 for OnlineRandomization.Simulation.corollary_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:43:57.546629+00:00
-- url     : https://prove2.me/submissions/33b9667c-00f3-4468-8fa5-5fc833a04e41

import Definitions.Def_OnlineRandomization_Simulation_Winning
import Definitions.Def_OnlineRandomization_Simulation_Model

open MeasureTheory

namespace OnlineRandomization.Simulation

section Comb
variable {R A : Type*} [Fintype A] [Nonempty A]

lemma sim_ww_mono (F : Game R A) (α : ℝ → ℝ) : ∀ (k k' : ℕ) (r : List R) (a : List A),
    k ≤ k' → WinsWithin F α k r a → WinsWithin F α k' r a
  | 0, 0, r, a, _, h => h
  | 0, k'+1, r, a, _, h => Or.inl h
  | k+1, 0, r, a, hk, _ => absurd hk (by omega)
  | k+1, k'+1, r, a, hk, h => by
      rcases h with h | ⟨x, hx⟩
      · exact Or.inl h
      · exact Or.inr ⟨x, fun y => sim_ww_mono F α k k' _ _ (by omega) (hx y)⟩

lemma sim_playAux_congr (G G' : DetAlg R A) (Q : OfflineAdv R A) : ∀ (m : ℕ) (r : List R) (a : List A),
    (∀ s : List R, r.length < s.length → G s = G' s) → playAux G Q m r a = playAux G' Q m r a
  | 0, r, a, _ => rfl
  | m+1, r, a, h => by
      simp only [playAux]
      cases hq : Q.next a with
      | none => rfl
      | some x =>
        simp only
        rw [h (r ++ [x]) (by simp)]
        exact sim_playAux_congr G G' Q m _ _ (fun s hs => h s (by simp at hs; omega))

lemma sim_win_of_all (F : Game R A) (α : ℝ → ℝ) (Q : OfflineAdv R A) : ∀ (m : ℕ) (r : List R) (a : List A),
    (∀ G : DetAlg R A, α (F.opt (playAux G Q m r a).1) <
      F.cost (playAux G Q m r a).1 (playAux G Q m r a).2) →
    WinsWithin F α m r a
  | 0, r, a, h => by
      have := h (fun _ => Classical.arbitrary A)
      exact this
  | m+1, r, a, h => by
      classical
      cases hq : Q.next a with
      | none =>
        have := h (fun _ => Classical.arbitrary A)
        simp only [playAux, hq] at this
        exact Or.inl this
      | some x =>
        refine Or.inr ⟨x, fun y => sim_win_of_all F α Q m _ _ (fun G' => ?_)⟩
        have := h (Function.update G' (r ++ [x]) y)
        simp only [playAux, hq, Function.update_self] at this
        rwa [sim_playAux_congr (Function.update G' (r ++ [x]) y) G' Q m _ _ (fun s hs => by
          rw [Function.update_of_ne]; rintro rfl; simp at hs)] at this

open Classical in
noncomputable def simPick (F : Game R A) (α : ℝ → ℝ) (N : ℕ) (r : List R) (a : List A) :
    Option R :=
  if α (F.opt r) < F.cost r a then none else
  if h : ∃ x : R, ∀ y : A, WinsWithin F α (N - a.length - 1) (r ++ [x]) (a ++ [y])
  then some h.choose else none

noncomputable def simROfRev (F : Game R A) (α : ℝ → ℝ) (N : ℕ) : List A → List R
  | [] => []
  | _ :: l => match simPick F α N (simROfRev F α N l) l.reverse with
     | none => simROfRev F α N l
     | some x => simROfRev F α N l ++ [x]

noncomputable def simROf (F : Game R A) (α : ℝ → ℝ) (N : ℕ) (a : List A) : List R :=
  simROfRev F α N a.reverse

lemma simROf_snoc (F : Game R A) (α : ℝ → ℝ) (N : ℕ) (a : List A) (y : A) (x : R)
    (h : simPick F α N (simROf F α N a) a = some x) :
    simROf F α N (a ++ [y]) = simROf F α N a ++ [x] := by
  unfold simROf at *
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, simROfRev, List.reverse_reverse]
  rw [h]

noncomputable def simWinQ (F : Game R A) (α : ℝ → ℝ) (N : ℕ) : OfflineAdv R A where
  next := fun a => if a.length < N then simPick F α N (simROf F α N a) a else none
  depth := N
  stop_of_le := by intro a h; simp [not_lt.2 h]

lemma sim_fwd (F : Game R A) (α : ℝ → ℝ) (N : ℕ) (G : DetAlg R A) : ∀ (m : ℕ) (r : List R) (a : List A),
    r = simROf F α N a → a.length + m = N → WinsWithin F α m r a →
    α (F.opt (playAux G (simWinQ F α N) m r a).1) <
      F.cost (playAux G (simWinQ F α N) m r a).1 (playAux G (simWinQ F α N) m r a).2
  | 0, r, a, _, _, h => h
  | m+1, r, a, hr, hl, h => by
      have hn : (simWinQ F α N).next a = simPick F α N r a := by
        simp [simWinQ, hr]; omega
      by_cases himm : α (F.opt r) < F.cost r a
      · have : simPick F α N r a = none := by unfold simPick; simp [himm]
        simp only [playAux, hn, this]; exact himm
      · rcases h with h | hex
        · exact absurd h himm
        · have hm : N - a.length - 1 = m := by omega
          have hex' : ∃ x : R, ∀ y : A, WinsWithin F α (N - a.length - 1) (r ++ [x]) (a ++ [y]) := by
            rw [hm]; exact hex
          have hp : simPick F α N r a = some hex'.choose := by
            unfold simPick; simp [himm, hex']
          obtain ⟨x, hpx, hxs⟩ : ∃ x, simPick F α N r a = some x ∧
              ∀ y, WinsWithin F α m (r ++ [x]) (a ++ [y]) :=
            ⟨hex'.choose, hp, by rw [← hm]; exact hex'.choose_spec⟩
          simp only [playAux, hn, hpx]
          apply sim_fwd F α N G m
          · rw [simROf_snoc F α N a _ x (hr ▸ hpx), hr]
          · simp; omega
          · exact hxs _

theorem initial_position_iff_core {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ) :
    IsWinning F α [] [] ↔
      ∃ Q : OfflineAdv R A, ∀ G : DetAlg R A,
        α (F.opt (play G Q).1) < F.cost (play G Q).1 (play G Q).2 := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨simWinQ F α k, fun G => ?_⟩
    exact sim_fwd F α k G k [] [] (by simp [simROf, simROfRev]) (by simp) hk
  · rintro ⟨Q, hQ⟩
    exact ⟨Q.depth, sim_win_of_all F α Q Q.depth [] [] hQ⟩

end Comb

section NW
variable {R A : Type*} [Fintype A] [Nonempty A]

lemma sim_nw_step (F : Game R A) (α : ℝ → ℝ) (r : List R) (a : List A)
    (h : ¬ IsWinning F α r a) (x : R) : ∃ y : A, ¬ IsWinning F α (r ++ [x]) (a ++ [y]) := by
  classical
  by_contra hc
  push_neg at hc
  choose k hk using hc
  apply h
  refine ⟨Finset.univ.sup k + 1, Or.inr ⟨x, fun y => ?_⟩⟩
  exact sim_ww_mono F α (k y) _ _ _ (Finset.le_sup (Finset.mem_univ y)) (hk y)

open Classical in
noncomputable def simCy (F : Game R A) (α : ℝ → ℝ) (r : List R) (a : List A) (x : R) : A :=
  if h : ∃ y : A, ¬ IsWinning F α (r ++ [x]) (a ++ [y]) then h.choose else Classical.arbitrary A

noncomputable def simAOfRev (F : Game R A) (α : ℝ → ℝ) : List R → List A
  | [] => []
  | x :: l => simAOfRev F α l ++ [simCy F α l.reverse (simAOfRev F α l) x]

noncomputable def simAOf (F : Game R A) (α : ℝ → ℝ) (r : List R) : List A :=
  simAOfRev F α r.reverse

lemma simAOf_snoc (F : Game R A) (α : ℝ → ℝ) (r : List R) (x : R) :
    simAOf F α (r ++ [x]) = simAOf F α r ++ [simCy F α r (simAOf F α r) x] := by
  simp [simAOf, simAOfRev]

noncomputable def simD (F : Game R A) (α : ℝ → ℝ) : DetAlg R A :=
  fun s => (simAOf F α s).getLastD (Classical.arbitrary A)

lemma sim_answers_snoc (G : DetAlg R A) (r : List R) (x : R) :
    G.answers (r ++ [x]) = G.answers r ++ [G (r ++ [x])] := by
  unfold DetAlg.answers
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [List.take_append_of_le_length (by omega)]
  · simp only [List.map_cons, List.map_nil]
    rw [List.take_of_length_le (by simp)]

lemma simD_answers (F : Game R A) (α : ℝ → ℝ) (r : List R) :
    (simD F α).answers r = simAOf F α r := by
  induction r using List.reverseRecOn with
  | nil => simp [DetAlg.answers, simAOf, simAOfRev]
  | append_singleton r x ih =>
    rw [sim_answers_snoc, ih, simAOf_snoc]
    simp [simD, simAOf_snoc]

lemma simAOf_nw (F : Game R A) (α : ℝ → ℝ) (h : ¬ IsWinning F α [] []) (r : List R) :
    ¬ IsWinning F α r (simAOf F α r) := by
  induction r using List.reverseRecOn with
  | nil => simpa [simAOf, simAOfRev] using h
  | append_singleton r x ih =>
    rw [simAOf_snoc]
    have hex := sim_nw_step F α r _ ih x
    unfold simCy
    rw [dif_pos hex]
    exact hex.choose_spec

theorem not_winning_deterministic_core {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ)
    (h : ¬ IsWinning F α [] []) :
    ∃ D : DetAlg R A, IsCompetitive F α D := by
  refine ⟨simD F α, fun r => ?_⟩
  unfold DetAlg.costOn
  rw [simD_answers]
  have := simAOf_nw F α h r
  by_contra hc
  exact this ⟨0, lt_of_not_ge hc⟩

end NW


section Meas

def SimFinMeas {Ω X : Type*} [MeasurableSpace Ω] (f : Ω → X) : Prop :=
  ∃ S : Finset X, (∀ ω, f ω ∈ S) ∧ ∀ x, MeasurableSet (f ⁻¹' {x})

lemma simFinMeas_const {Ω X : Type*} [MeasurableSpace Ω] (x : X) :
    SimFinMeas (fun _ : Ω => x) := by
  classical
  refine ⟨{x}, fun _ => Finset.mem_singleton_self x, fun y => ?_⟩
  rw [Set.preimage_const]
  split_ifs
  · exact MeasurableSet.univ
  · exact MeasurableSet.empty

lemma simFinMeas_comp {Ω X Y : Type*} [MeasurableSpace Ω] {f : Ω → X}
    (hf : SimFinMeas f) (h : X → Y) : SimFinMeas (fun ω => h (f ω)) := by
  classical
  obtain ⟨S, hS, hm⟩ := hf
  refine ⟨S.image h, fun ω => Finset.mem_image_of_mem h (hS ω), fun y => ?_⟩
  have : (fun ω => h (f ω)) ⁻¹' {y} = ⋃ x ∈ S.filter (fun x => h x = y), f ⁻¹' {x} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Finset.mem_filter,
      exists_prop]
    constructor
    · intro hy; exact ⟨f ω, ⟨hS ω, hy⟩, rfl⟩
    · rintro ⟨x, ⟨_, hx⟩, rfl⟩; exact hx
  rw [this]
  exact Finset.measurableSet_biUnion _ (fun x _ => hm x)

lemma simFinMeas_dep {Ω X Y : Type*} [MeasurableSpace Ω] [Fintype Y] {c : Ω → Y}
    (hc : ∀ y, MeasurableSet (c ⁻¹' {y})) (g : Y → Ω → X) (hg : ∀ y, SimFinMeas (g y)) :
    SimFinMeas (fun ω => g (c ω) ω) := by
  classical
  choose S hS hm using hg
  refine ⟨Finset.univ.biUnion S, fun ω => Finset.mem_biUnion.2 ⟨c ω, Finset.mem_univ _, hS _ ω⟩,
    fun x => ?_⟩
  have : (fun ω => g (c ω) ω) ⁻¹' {x} = ⋃ y, (c ⁻¹' {y} ∩ (g y) ⁻¹' {x}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨c ω, rfl, h⟩
    · rintro ⟨y, rfl, h⟩; exact h
  rw [this]
  exact MeasurableSet.iUnion (fun y => (hc y).inter (hm y x))

lemma sim_int_fin {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → X} (S : Finset X) (hS : ∀ ω, f ω ∈ S) (hm : ∀ x, MeasurableSet (f ⁻¹' {x}))
    (g : X → ℝ) :
    Integrable (fun ω => g (f ω)) μ ∧
      ∫ ω, g (f ω) ∂μ = ∑ x ∈ S, μ.real (f ⁻¹' {x}) * g x := by
  have hpt : (fun ω => g (f ω)) = fun ω => ∑ x ∈ S, (f ⁻¹' {x}).indicator (fun _ => g x) ω := by
    funext ω
    rw [Finset.sum_eq_single (f ω)]
    · rw [Set.indicator_of_mem (by simp)]
    · intro x _ hx
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact fun h => hx h.symm
    · intro h; exact absurd (hS ω) h
  rw [hpt]
  refine ⟨integrable_finset_sum _ (fun x _ => (integrable_const (g x)).indicator (hm x)), ?_⟩
  rw [integral_finset_sum _ (fun x _ => (integrable_const (g x)).indicator (hm x))]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [integral_indicator_const _ (hm x), smul_eq_mul]

variable {R A Ω : Type*} [Fintype A] [MeasurableSpace Ω]

lemma sim_play_finMeas (H : RandAlg R A Ω) (Q : OfflineAdv R A) : ∀ (m : ℕ) (r : List R) (a : List A),
    SimFinMeas (fun ω => playAux (H.alg ω) Q m r a)
  | 0, r, a => simFinMeas_const (r, a)
  | m+1, r, a => by
      cases hq : Q.next a with
      | none =>
        have : (fun ω => playAux (H.alg ω) Q (m+1) r a) = fun _ => (r, a) := by
          funext ω; simp [playAux, hq]
        rw [this]; exact simFinMeas_const _
      | some x =>
        have : (fun ω => playAux (H.alg ω) Q (m+1) r a) =
            fun ω => (fun y ω => playAux (H.alg ω) Q m (r ++ [x]) (a ++ [y]))
              (H.alg ω (r ++ [x])) ω := by
          funext ω; simp [playAux, hq]
        rw [this]
        exact simFinMeas_dep (c := fun ω => H.alg ω (r ++ [x])) (fun y => H.meas _ y)
          (fun y ω => playAux (H.alg ω) Q m (r ++ [x]) (a ++ [y]))
          (fun y => sim_play_finMeas H Q m (r ++ [x]) (a ++ [y]))

lemma sim_listmap_finMeas (H : RandAlg R A Ω) : ∀ L : List (List R),
    SimFinMeas (fun ω => L.map (fun s => H.alg ω s))
  | [] => by simpa using simFinMeas_const ([] : List A)
  | s :: L => by
      have : (fun ω => (s :: L).map (fun s => H.alg ω s)) =
          fun ω => (fun y ω => y :: L.map (fun s => H.alg ω s)) (H.alg ω s) ω := by
        funext ω; simp
      rw [this]
      exact simFinMeas_dep (fun y => H.meas _ y) _
        (fun y => simFinMeas_comp (sim_listmap_finMeas H L) (fun l => y :: l))

lemma sim_answers_finMeas (H : RandAlg R A Ω) (r : List R) :
    SimFinMeas (fun ω => (H.alg ω).answers r) := by
  have : (fun ω => (H.alg ω).answers r) =
      fun ω => ((List.range r.length).map (fun i => r.take (i+1))).map (fun s => H.alg ω s) := by
    funext ω; simp [DetAlg.answers, List.map_map, Function.comp_def]
  rw [this]; exact sim_listmap_finMeas H _


theorem winning_defeats_randomized_core {R A Ω : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] (F : Game R A) (α : ℝ → ℝ)
    (Q : OfflineAdv R A)
    (hQ : ∀ G : DetAlg R A,
      α (F.opt (play G Q).1) < F.cost (play G Q).1 (play G Q).2)
    (H : RandAlg R A Ω) :
    (∫ ω, α (F.opt (play (H.alg ω) Q).1) ∂H.μ) <
      (∫ ω, F.cost (play (H.alg ω) Q).1 (play (H.alg ω) Q).2 ∂H.μ) := by
  haveI := H.isProb
  obtain ⟨S, hS, hm⟩ : SimFinMeas (fun ω => play (H.alg ω) Q) :=
    sim_play_finMeas H Q Q.depth [] []
  have h1 := (sim_int_fin H.μ S hS hm (fun p => α (F.opt p.1))).1
  have h2 := (sim_int_fin H.μ S hS hm (fun p => F.cost p.1 p.2)).1
  have h3 := (sim_int_fin H.μ S hS hm (fun p => F.cost p.1 p.2 - α (F.opt p.1))).1
  have hpos : 0 < ∫ ω, (F.cost (play (H.alg ω) Q).1 (play (H.alg ω) Q).2 -
      α (F.opt (play (H.alg ω) Q).1)) ∂H.μ := by
    rw [integral_pos_iff_support_of_nonneg (fun ω => by
      have := hQ (H.alg ω); simp only [Pi.zero_apply]; linarith) h3]
    have : Function.support (fun ω => F.cost (play (H.alg ω) Q).1 (play (H.alg ω) Q).2 -
        α (F.opt (play (H.alg ω) Q).1)) = Set.univ := by
      ext ω
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      have := hQ (H.alg ω); linarith
    rw [this, measure_univ]; exact zero_lt_one
  rw [integral_sub h2 h1] at hpos
  linarith

end Meas


section Sim
variable {R A : Type*}

noncomputable def simReqs (Q : OfflineAdv R A) (a : List A) : List R :=
  (List.range (a.length + 1)).filterMap (fun j => Q.next (a.take j))

noncomputable def simAdv (Q : OfflineAdv R A) (D : DetAlg R A) : OnlineAdv R A :=
  { toOfflineAdv := Q, ans := fun a => D (simReqs Q a) }

def SimInv (Q : OfflineAdv R A) (p : List R × List A) : Prop :=
  p.1.length = p.2.length ∧
    ∀ i ≤ p.2.length, (List.range i).filterMap (fun j => Q.next (p.2.take j)) = p.1.take i

lemma simInv_playAux (G : DetAlg R A) (Q : OfflineAdv R A) : ∀ (m : ℕ) (r : List R) (a : List A),
    SimInv Q (r, a) → SimInv Q (playAux G Q m r a)
  | 0, r, a, h => h
  | m+1, r, a, h => by
      cases hq : Q.next a with
      | none => simpa [playAux, hq] using h
      | some x =>
        simp only [playAux, hq]
        apply simInv_playAux G Q m
        obtain ⟨hl, hi⟩ := h
        simp only at hl hi
        refine ⟨by simp [hl], fun i hi' => ?_⟩
        simp only [List.length_append, List.length_singleton] at hi' ⊢
        rcases Nat.lt_or_ge i (a.length + 1) with h1 | h1
        · have e1 : (List.range i).filterMap (fun j => Q.next ((a ++ [G (r ++ [x])]).take j)) =
              (List.range i).filterMap (fun j => Q.next (a.take j)) := by
            apply List.filterMap_congr
            intro j hj
            rw [List.mem_range] at hj
            rw [List.take_append_of_le_length (by omega)]
          rw [e1, hi i (by omega), List.take_append_of_le_length (by omega)]
        · have hi2 : i = a.length + 1 := by omega
          subst hi2
          rw [List.range_succ, List.filterMap_append]
          have e1 : (List.range a.length).filterMap (fun j => Q.next ((a ++ [G (r ++ [x])]).take j)) =
              (List.range a.length).filterMap (fun j => Q.next (a.take j)) := by
            apply List.filterMap_congr
            intro j hj
            rw [List.mem_range] at hj
            rw [List.take_append_of_le_length (by omega)]
          rw [e1, hi a.length le_rfl, List.take_of_length_le (by omega),
            List.take_of_length_le (by simp; omega)]
          simp [hq]

lemma sim_onlineAnswers (G D : DetAlg R A) (Q : OfflineAdv R A) :
    onlineAnswers G (simAdv Q D) = D.answers (play G Q).1 := by
  have hinv : SimInv Q (play G Q) :=
    simInv_playAux G Q _ _ _ ⟨rfl, fun i hi => by simp at hi; subst hi; simp⟩
  obtain ⟨hl, hi⟩ := hinv
  unfold onlineAnswers DetAlg.answers
  simp only [simAdv]
  rw [hl]
  apply List.map_congr_left
  intro i hi'
  rw [List.mem_range] at hi'
  congr 1
  unfold simReqs
  rw [List.length_take, min_eq_left hi'.le]
  rw [← hi (i+1) (by omega)]
  apply List.filterMap_congr
  intro j hj
  rw [List.mem_range] at hj
  rw [List.take_take, min_eq_left (by omega)]

end Sim

theorem theorem_2_1_core {R A Ω : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] (F : Game R A) (α : ℝ → ℝ)
    (H : RandAlg R A Ω)
    (hH : IsCompetitiveOffline F α H) :
    ∃ D : DetAlg R A, IsCompetitive F α D := by
  by_cases hw : IsWinning F α [] []
  · obtain ⟨Q, hQ⟩ := (initial_position_iff_core F α).1 hw
    have := winning_defeats_randomized_core F α Q hQ H
    have := hH Q
    linarith
  · exact not_winning_deterministic_core F α hw

theorem theorem_2_2_core {R A Ω Ω' : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (F : Game R A) (α β : ℝ → ℝ)
    (hα : IsLinear α) (hαmono : Monotone α)
    (G : RandAlg R A Ω) (H : RandAlg R A Ω')
    (hG : IsCompetitiveOnline F α G)
    (hH : IsCompetitiveObl F β H) :
    IsCompetitiveOffline F (α ∘ β) G := by
  intro Q
  obtain ⟨c, d, hcd⟩ := hα
  haveI := G.isProb
  haveI := H.isProb
  obtain ⟨S, hS, hm⟩ : SimFinMeas (fun ω => play (G.alg ω) Q) :=
    sim_play_finMeas G Q Q.depth [] []
  set w : List R × List A → ℝ := fun p => G.μ.real ((fun ω => play (G.alg ω) Q) ⁻¹' {p}) with hw
  have hw0 : ∀ p, 0 ≤ w p := fun p => by simp [hw]
  -- K p ω'
  have hK : ∀ p : List R × List A, Integrable (fun ω' => (H.alg ω').costOn F p.1) H.μ := by
    intro p
    obtain ⟨T, hT, hmT⟩ := sim_answers_finMeas H p.1
    exact (sim_int_fin H.μ T hT hmT (fun l => F.cost p.1 l)).1
  have step1 : ∀ ω', (∫ ω, F.cost (play (G.alg ω) Q).1 (play (G.alg ω) Q).2 ∂G.μ) ≤
      ∑ p ∈ S, w p * α ((H.alg ω').costOn F p.1) := by
    intro ω'
    have h1 := hG (simAdv Q (H.alg ω'))
    have e : ∀ ω, onlineAnswers (G.alg ω) (simAdv Q (H.alg ω')) =
        (H.alg ω').answers (play (G.alg ω) Q).1 := fun ω => sim_onlineAnswers _ _ _
    simp only [e] at h1
    have h2 := (sim_int_fin G.μ S hS hm (fun p => α ((H.alg ω').costOn F p.1))).2
    simp only [DetAlg.costOn] at h2
    exact h1.trans_eq h2
  have hint : Integrable (fun ω' => ∑ p ∈ S, w p * α ((H.alg ω').costOn F p.1)) H.μ := by
    refine integrable_finset_sum _ (fun p _ => ?_)
    simp only [hcd]
    exact (((hK p).const_mul c).add (integrable_const d)).const_mul (w p)
  have step2 : (∫ ω, F.cost (play (G.alg ω) Q).1 (play (G.alg ω) Q).2 ∂G.μ) ≤
      ∑ p ∈ S, w p * α (∫ ω', (H.alg ω').costOn F p.1 ∂H.μ) := by
    have := integral_mono (integrable_const _) hint step1
    simp only [integral_const, probReal_univ, one_smul] at this
    refine this.trans_eq ?_
    rw [integral_finset_sum _ (fun p _ => by
      simp only [hcd]; exact (((hK p).const_mul c).add (integrable_const d)).const_mul (w p))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [hcd]
    rw [integral_const_mul, integral_add ((hK p).const_mul c) (integrable_const d),
      integral_const_mul, integral_const, probReal_univ, one_smul]
  have step3 : ∑ p ∈ S, w p * α (∫ ω', (H.alg ω').costOn F p.1 ∂H.μ) ≤
      ∑ p ∈ S, w p * α (β (F.opt p.1)) :=
    Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (hαmono (hH p.1)) (hw0 p))
  have h4 := (sim_int_fin G.μ S hS hm (fun p => α (β (F.opt p.1)))).2
  simp only [Function.comp_apply]
  rw [h4]
  exact step2.trans step3

theorem corollary_2_1_core {R A Ω Ω' : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (F : Game R A) (α β : ℝ → ℝ)
    (hα : IsLinear α) (hαmono : Monotone α)
    (G : RandAlg R A Ω) (H : RandAlg R A Ω')
    (hG : IsCompetitiveOnline F α G)
    (hH : IsCompetitiveObl F β H) :
    ∃ D : DetAlg R A, IsCompetitive F (α ∘ β) D :=
  theorem_2_1_core F (α ∘ β) G (theorem_2_2_core F α β hα hαmono G H hG hH)

end OnlineRandomization.Simulation

open OnlineRandomization.Simulation


theorem solution {R A Ω Ω' : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (F : Game R A) (α β : ℝ → ℝ)
    (hα : IsLinear α) (hαmono : Monotone α) (hβ : IsLinear β)
    (G : RandAlg R A Ω) (H : RandAlg R A Ω')
    (hG : IsCompetitiveOnline F α G)
    (hH : IsCompetitiveObl F β H) :
    ∃ D : DetAlg R A, IsCompetitive F (α ∘ β) D := by
  exact corollary_2_1_core F α β hα hαmono G H hG hH
