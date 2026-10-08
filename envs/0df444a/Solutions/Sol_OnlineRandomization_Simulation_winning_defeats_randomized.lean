-- Prove2me | solution 1 for OnlineRandomization.Simulation.winning_defeats_randomized
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:41:26.928986+00:00
-- url     : https://prove2.me/submissions/b6682b9c-bf0a-4291-9110-0f8737244723

import Definitions.Def_OnlineRandomization_Simulation_Winning

open MeasureTheory

namespace OnlineRandomization.Simulation

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

end OnlineRandomization.Simulation

open OnlineRandomization.Simulation


theorem solution {R A Ω : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] (F : Game R A) (α : ℝ → ℝ)
    (Q : OfflineAdv R A)
    (hQ : ∀ G : DetAlg R A,
      α (F.opt (play G Q).1) < F.cost (play G Q).1 (play G Q).2)
    (H : RandAlg R A Ω) :
    (∫ ω, α (F.opt (play (H.alg ω) Q).1) ∂H.μ) <
      (∫ ω, F.cost (play (H.alg ω) Q).1 (play (H.alg ω) Q).2 ∂H.μ) := by
  exact winning_defeats_randomized_core F α Q hQ H
