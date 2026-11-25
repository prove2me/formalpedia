-- Prove2me | solution 1 for PandoraKnapsack.Skipping.machine_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:14:58.557548+00:00
-- url     : https://prove2.me/submissions/6877917c-4fdb-4987-b50f-a2f1b5195b70

import Definitions.Def_PandoraKnapsack_Skipping_Machine

open MeasureTheory SmaleNinth
open scoped Classical

namespace PandoraKnapsack.Skipping

private lemma measurable_fibers {X Y K : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace K] [Countable K] [MeasurableSingletonClass K]
    {f : X → Y} (g : X → K) (hg : Measurable g)
    (h : ∀ k : K, Measurable fun a : {x : X // g x = k} => f a.1) : Measurable f := by
  intro u hu
  have hm (k : K) : MeasurableSet {x | g x = k} := hg (measurableSet_singleton k)
  let S (k : K) := Subtype.val '' ((fun a : {x : X // g x = k} => f a.1) ⁻¹' u)
  have hs (k : K) : MeasurableSet (S k) := (hm k).subtype_image (h k hu)
  have he : f ⁻¹' u = ⋃ k, S k := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro hx
      exact ⟨g x, ⟨x,rfl⟩,hx,rfl⟩
    · rintro ⟨_, a, ha, rfl⟩
      exact ha
  rw [he]
  exact MeasurableSet.iUnion hs

private def ramFields (s : RAMConfig) := (s.pc,s.regs,s.ptrs,s.mem)
local instance : MeasurableSpace RAMConfig := MeasurableSpace.comap ramFields inferInstance

private lemma measurable_ramFields : Measurable ramFields := Measurable.of_comap_le le_rfl

@[local fun_prop] private lemma meas_pc : Measurable RAMConfig.pc := measurable_ramFields.fst
@[local fun_prop] private lemma meas_regs : Measurable RAMConfig.regs := measurable_ramFields.snd.fst
@[local fun_prop] private lemma meas_ptrs : Measurable RAMConfig.ptrs := measurable_ramFields.snd.snd.fst
@[local fun_prop] private lemma meas_mem : Measurable RAMConfig.mem := measurable_ramFields.snd.snd.snd

variable {X : Type*} [MeasurableSpace X]

@[local fun_prop] private lemma meas_mk_ram {p : X → ℕ} {r : X → ℕ → ℝ}
    {q : X → ℕ → ℤ} {m : X → ℤ → ℝ}
    (hp : Measurable p) (hr : Measurable r) (hq : Measurable q) (hm : Measurable m) :
    Measurable fun x => RAMConfig.mk (p x) (r x) (q x) (m x) :=
  measurable_comap_iff.mpr (hp.prodMk (hr.prodMk (hq.prodMk hm)))

private def stateFields (s : State) := (s.core,s.draws)
local instance : MeasurableSpace State := MeasurableSpace.comap stateFields inferInstance
private lemma measurable_stateFields : Measurable stateFields := Measurable.of_comap_le le_rfl
@[local fun_prop] private lemma meas_core : Measurable State.core := measurable_stateFields.fst
@[local fun_prop] private lemma meas_draws : Measurable State.draws := measurable_stateFields.snd
@[local fun_prop] private lemma meas_mk_state {c : X → RAMConfig} {d : X → ℕ}
    (hc : Measurable c) (hd : Measurable d) : Measurable fun x => State.mk (c x) (d x) :=
  measurable_comap_iff.mpr (hc.prodMk hd)

private lemma meas_address {K V : Type*} [MeasurableSpace K]
    [Countable K] [MeasurableSingletonClass K] [MeasurableSpace V]
    {f : X → K → V} {a : X → K} (hf : Measurable f) (ha : Measurable a) :
    Measurable fun x => f x (a x) := by
  have h : Measurable fun p : X × K => f p.1 p.2 :=
    measurable_from_prod_countable_left fun _ => hf.eval
  exact h.comp (measurable_id.prodMk ha)

@[local fun_prop] private lemma meas_write {K V : Type*} [MeasurableSpace K]
    [Countable K] [MeasurableSingletonClass K] [DecidableEq K] [MeasurableSpace V]
    {f : X → K → V} {a : X → K} {v : X → V}
    (hf : Measurable f) (ha : Measurable a) (hv : Measurable v) :
    Measurable fun x => Function.update (f x) (a x) (v x) := by
  apply measurable_pi_lambda
  intro k
  simp only [Function.update_apply]
  exact Measurable.ite (measurableSet_eq_fun measurable_const ha) hv hf.eval

@[local fun_prop] private lemma meas_mem_at {s : X → RAMConfig} {a : X → ℤ}
    (hs : Measurable s) (ha : Measurable a) : Measurable fun x => (s x).mem (a x) :=
  meas_address (meas_mem.comp hs) ha

@[local fun_prop] private lemma meas_ram_step (R : RAMProgram) : Measurable (RAMStep R) := by
  classical
  apply measurable_fibers RAMConfig.pc meas_pc
  intro k
  have hk (a : {s : RAMConfig // s.pc = k}) : a.1.pc = k := a.2
  simp only [RAMStep, hk]
  cases he : R[k]? with
  | none => exact measurable_subtype_coe
  | some ins =>
    cases ins <;> dsimp only <;> first | fun_prop |
      apply Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) <;> fun_prop



private lemma meas_select {K Y : Type*} [MeasurableSpace K] [Countable K]
    [MeasurableSingletonClass K] [MeasurableSpace Y] (a : X → K) (ha : Measurable a)
    (F : K → X → Y) (hF : ∀ k, Measurable (F k)) : Measurable fun x => F (a x) x := by
  have h : Measurable fun p : X × K => F p.2 p.1 := measurable_from_prod_countable_left hF
  exact h.comp (measurable_id.prodMk ha)

variable {n m T B : ℕ}

/-- Measurability of a coefficient query with both item and choice selected at run time. -/
private def lookup (F : Fin n → Fin m → ℝ → ℝ) (p q : ℤ) (r : ℝ) : ℝ :=
  match ptrIndex n p, ptrIndex m q with
  | some i, some j => F i j r
  | _, _ => 0

@[local fun_prop] private lemma meas_lookup {F : Fin n → Fin m → ℝ → ℝ} {p q : X → ℤ} {r : X → ℝ}
    (hF : ∀ i j, Measurable (F i j)) (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) :
    Measurable fun x => lookup F (p x) (q x) (r x) := by
  apply meas_select (fun x => (p x,q x)) (hp.prodMk hq) (fun z x => lookup F z.1 z.2 (r x))
  rintro ⟨u,v⟩
  unfold lookup
  cases ptrIndex n u <;> cases ptrIndex m v <;> first | exact measurable_const | exact (hF _ _).comp hr

private lemma meas_cdf (I : Instance n m T) (i j) : Measurable (cdf I i j) := by
  unfold cdf
  apply Finset.measurable_fun_sum
  intro s _
  exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const

private lemma meas_truncMean (I : Instance n m T) (i j) : Measurable (truncMean I i j) := by
  unfold truncMean
  fun_prop

private lemma meas_draw_coord (k : ℕ) : Measurable (fun ω : Fin B → unitInterval => extendDraws ω k) := by
  unfold extendDraws
  split_ifs <;> fun_prop

@[local fun_prop] private lemma meas_dynamic_draw {ω : X → Fin B → unitInterval} {k : X → ℕ}
    (hω : Measurable ω) (hk : Measurable k) : Measurable fun x => extendDraws (ω x) (k x) :=
  meas_select k hk _ (fun j => (meas_draw_coord j).comp hω)

private lemma meas_indicator_value (I : Instance n m T) {p : X → ℤ} (hp : Measurable p) :
    Measurable fun x => (match ptrIndex n (p x) with | some i => I.value i | none => 0) := by
  let F : ℤ → ℝ := fun z => match ptrIndex n z with | some i => I.value i | none => 0
  exact (measurable_of_countable F).comp hp

private lemma meas_step (I : Instance n m T) (P : Program) {s : X → State} {ω : X → Fin B → unitInterval}
    (hs : Measurable s) (hω : Measurable ω) : Measurable fun x => step I (extendDraws (ω x)) P (s x) := by
  classical
  apply measurable_fibers (fun x => (s x).core.pc) (by fun_prop)
  intro k
  have hk (a : {x : X // (s x).core.pc = k}) : (s a.1).core.pc = k := a.2
  simp only [step,hk]
  cases he : P[k]? with
  | none => fun_prop
  | some ins =>
    cases ins with
    | core instr => dsimp only; fun_prop
    | uniform d => dsimp only; fun_prop
    | ptrReal d q =>
      dsimp only
      apply meas_mk_state _ (by fun_prop)
      apply meas_mk_ram (by fun_prop) _ (by fun_prop) (by fun_prop)
      apply meas_write (by fun_prop) (by fun_prop)
      exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp (by fun_prop)
    | value d q =>
      dsimp only
      apply meas_mk_state _ (by fun_prop)
      apply meas_mk_ram (by fun_prop) _ (by fun_prop) (by fun_prop)
      apply meas_write (by fun_prop) (by fun_prop)
      exact meas_indicator_value I (by fun_prop)
    | cost d q q' =>
      dsimp only
      apply meas_mk_state _ (by fun_prop)
      apply meas_mk_ram (by fun_prop) _ (by fun_prop) (by fun_prop)
      apply meas_write (by fun_prop) (by fun_prop)
      apply meas_lookup (F := fun i j _ => I.cost i j) (r := fun _ => 0) (fun _ _ => measurable_const) <;> fun_prop
    | cdf d q q' src =>
      dsimp only
      apply meas_mk_state _ (by fun_prop)
      apply meas_mk_ram (by fun_prop) _ (by fun_prop) (by fun_prop)
      apply meas_write (by fun_prop) (by fun_prop)
      apply meas_lookup (meas_cdf I) <;> fun_prop
    | truncMean d q q' src =>
      dsimp only
      apply meas_mk_state _ (by fun_prop)
      apply meas_mk_ram (by fun_prop) _ (by fun_prop) (by fun_prop)
      apply meas_write (by fun_prop) (by fun_prop)
      apply meas_lookup (meas_truncMean I) <;> fun_prop

private lemma meas_run (I : Instance n m T) (P : Program) (t : ℕ) :
    Measurable fun ω : Fin B → unitInterval => run I (extendDraws ω) P t := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    simp only [run,Function.iterate_succ_apply']
    exact meas_step I P ih measurable_id

local instance {α : Type*} : MeasurableSpace (Option α) := ⊤
local instance {α : Type*} : MeasurableSpace (List α) := ⊤

private lemma meas_readNat : Measurable readNat := by
  apply (measurable_const (a := (none : Option ℕ))).measurable_of_countable_ne
  apply (Set.countable_range (fun k : ℕ => (k : ℝ))).mono
  intro x hx
  by_contra! hh
  have he : ¬ ∃ k : ℕ, (k : ℝ) = x := hh
  exact hx (by simp [readNat,he])

private lemma meas_decode_entry (n m : ℕ) {mem : X → ℤ → ℝ} (hm : Measurable mem) (r : ℕ) :
    Measurable fun x => decodeEntry n m (mem x) r := by
  let F : Option ℕ × Option ℕ × Option ℕ → Option (Fin n × Fin m × ℕ)
    | (some i,some j,some θ) => if h : i < n ∧ j < m then some (⟨i,h.1⟩,⟨j,h.2⟩,θ) else none
    | _ => none
  let a (z : ℤ) (x : X) := readNat (mem x z)
  have h (z : ℤ) : Measurable (a z) := meas_readNat.comp hm.eval
  have hF := (measurable_of_countable F).comp ((h (1+3*(r:ℤ))).prodMk
    ((h (2+3*(r:ℤ))).prodMk (h (3+3*(r:ℤ)))))
  convert hF using 1
  funext x
  unfold decodeEntry
  dsimp [Function.comp_def, a]
  cases readNat (mem x (1+3*(r:ℤ))) <;> cases readNat (mem x (2+3*(r:ℤ))) <;>
    cases readNat (mem x (3+3*(r:ℤ))) <;> rfl

private lemma meas_decode_list (n m : ℕ) {mem : X → ℤ → ℝ} (hm : Measurable mem) (l : List ℕ) :
    Measurable fun x => l.mapM (decodeEntry n m (mem x)) := by
  induction l with
  | nil => exact measurable_const
  | cons r l ih =>
    let F : Option (Fin n × Fin m × ℕ) × Option (SkipList n m) → Option (SkipList n m) :=
      fun z => do let e ← z.1; let t ← z.2; pure (e :: t)
    simp only [List.mapM_cons]
    exact (measurable_of_countable F).comp ((meas_decode_entry n m hm r).prodMk ih)

private lemma meas_output (I : Instance n m T) (P : Program) (B : ℕ) :
    Measurable (outputPolicy I P B) := by
  let mem := fun ω : Fin B → unitInterval => (run I (extendDraws ω) P B).core.mem
  have hm : Measurable mem := meas_mem.comp (meas_core.comp (meas_run I P B))
  let F : Option ℕ → (Fin B → unitInterval) → Option (SkipList n m)
    | none, _ => none
    | some l, ω => (List.range l).mapM (decodeEntry n m (mem ω))
  have hF (l : Option ℕ) : Measurable (F l) := by
    cases l with
    | none => exact measurable_const
    | some l => exact meas_decode_list n m hm (List.range l)
  have hd := meas_select (fun ω => readNat (mem ω 0)) (meas_readNat.comp hm.eval) F hF
  have he : (fun x => F (readNat (mem x 0)) x) = (fun x => decodeOutput n m (mem x)) := by
    funext x
    unfold decodeOutput
    cases readNat (mem x 0) <;> rfl
  rw [he] at hd
  exact (measurable_of_countable (fun o : Option (SkipList n m) => o.getD [])).comp hd

private lemma finite_skip_policies (n m T : ℕ) : {σ : SkipList n m | IsSkippingPolicy T σ}.Finite := by
  let A := Fin n × Fin m × Fin (T+1)
  let erase (e : A) : Fin n × Fin m × ℕ := (e.1,e.2.1,e.2.2.val)
  apply ((List.finite_length_le A n).image (List.map erase)).subset
  intro σ hσ
  change (σ.map (fun e => e.1)).Nodup ∧ ∀ e ∈ σ, e.2.2 ≤ T at hσ
  let tagged : List A := σ.pmap (fun e (h : e.2.2 ≤ T) => (e.1,e.2.1,⟨e.2.2,by omega⟩)) hσ.2
  refine ⟨tagged, ?_, ?_⟩
  · simpa [tagged] using hσ.1.length_le_card
  · dsimp [tagged]
    rw [List.map_pmap]
    change List.pmap (fun (a : Fin n × Fin m × ℕ) (_ : a.2.2 ≤ T) => a) σ hσ.2 = σ
    rw [List.pmap_eq_map]; simp

end PandoraKnapsack.Skipping

open PandoraKnapsack.Skipping

theorem solution {n m T : ℕ} (I : Instance n m T) (P : Program) (B : ℕ)
    (hv : ∀ ω : Fin B → unitInterval, IsSkippingPolicy T (outputPolicy I P B ω)) :
    Integrable (fun ω => skipValue I (outputPolicy I P B ω)) (drawLaw B) := by
  let : MeasurableSpace (SkipList n m) := ⊤
  obtain ⟨C,hC⟩ := ((finite_skip_policies n m T).image (fun σ => ‖skipValue I σ‖)).bddAbove
  have hm := (measurable_of_countable (skipValue I)).comp (meas_output I P B)
  let : IsFiniteMeasure (drawLaw B) := by unfold drawLaw; infer_instance
  apply Integrable.of_bound hm.aestronglyMeasurable C
  exact Filter.Eventually.of_forall fun ω => hC ⟨_,hv ω,rfl⟩
