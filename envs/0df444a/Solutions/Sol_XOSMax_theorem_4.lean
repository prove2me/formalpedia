-- Prove2me | solution 1 for XOSMax.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-11-04T15:02:17.010122+00:00
-- url     : https://prove2.me/submissions/3c4799e8-ca4c-47cf-a253-49fbe2212311

import Definitions.Def_XOSMax_IsKXOS
import Definitions.Def_XOSMax_IsMaximizerApprox
import Definitions.Def_XOSMax_xosMax

namespace XOSMax
open OracleProg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace XT
variable {E : Type} [DecidableEq E]

theorem run_tick_bind {α : Type} (f : Finset E → ℝ) (g : Unit → OracleProg E α) :
    run f (OracleProg.bind tick g) = ((run f (g ())).1, (run f (g ())).2 + 1) := by
  simp [tick, OracleProg.bind, run]

theorem run_ask_bind {α : Type} (f : Finset E → ℝ) (X : Finset E) (g : ℝ → OracleProg E α) :
    run f (OracleProg.bind (ask X) g) = ((run f (g (f X))).1, (run f (g (f X))).2 + 1) := by
  simp [ask, OracleProg.bind, run]

theorem run_ticks_bind {α : Type} (f : Finset E → ℝ) (n : ℕ) (g : Unit → OracleProg E α) :
    run f (OracleProg.bind (ticks n) g) = ((run f (g ())).1, (run f (g ())).2 + n) := by
  induction n with
  | zero => simp [ticks, OracleProg.bind]
  | succ n ih => simp only [ticks, OracleProg.bind, run] at *; rw [ih]; ext <;> simp; omega

theorem run_foldlM_fst {σ α : Type} (f : Finset E → ℝ) (g : σ → α → OracleProg E σ) :
    ∀ (l : List α) (s : σ), (run f (l.foldlM g s)).1 = l.foldl (fun s a => (run f (g s a)).1) s := by
  intro l; induction l with
  | nil => intro s; simp [List.foldlM]
  | cons a l ih => intro s; simp only [List.foldlM_cons, List.foldl_cons]; erw [run_bind]; simp [ih]

theorem run_foldlM_cost {σ α : Type} (f : Finset E → ℝ) (g : σ → α → OracleProg E σ) (Φ : σ → ℕ) (c : ℕ) :
    ∀ (l : List α) (s : σ), (∀ s a, a ∈ l → (run f (g s a)).2 + Φ s ≤ c + Φ (run f (g s a)).1) →
      (run f (l.foldlM g s)).2 + Φ s ≤ c * l.length + Φ (run f (l.foldlM g s)).1 := by
  intro l; induction l with
  | nil => intro s _; simp [List.foldlM]
  | cons a l ih =>
    intro s h
    simp only [List.foldlM_cons]; erw [run_bind]
    have h1 := h s a (by simp)
    have h2 := ih (run f (g s a)).1 (fun s' a' ha' => h s' a' (by simp [ha']))
    simp only [List.length_cons]
    nlinarith


@[simp] theorem run_tick (f : Finset E → ℝ) : run f (tick : OracleProg E Unit) = ((), 1) := rfl
@[simp] theorem run_ask (f : Finset E → ℝ) (X : Finset E) : run f (ask X) = (f X, 1) := rfl

@[simp] theorem run_ticks (f : Finset E → ℝ) (n : ℕ) : run f (ticks n : OracleProg E Unit) = ((), n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ticks, run, ih]

theorem run_filterStep (f : Finset E → ℝ) (acc : List E) (v : E) :
    run f (filterStep acc v) = (if 0 < f {v} then acc ++ [v] else acc, 3) := by
  simp only [filterStep, bind_eq_bind, run_tick_bind, run_ask_bind]
  split_ifs <;> simp

theorem run_growStep' (f : Finset E → ℝ) (v : E) (V' : Finset E) (u : E) :
    (run f (growStep v V' u)).1 = (if u = v then V' else if f (insert u V') = f V' + f {u} then insert u V' else V') ∧
    (run f (growStep v V' u)).2 ≤ 7 := by
  simp only [growStep, bind_eq_bind]
  split_ifs <;> simp [*]

theorem run_buildYStep (f : Finset E → ℝ) (V' : Finset E) (b : ℝ) (Y' : Finset E) (v : E) :
    (run f (buildYStep V' b Y' v)).1 = (if v ∈ V' then Y' else if b < f (insert v V') then insert v Y' else Y') ∧
    (run f (buildYStep V' b Y' v)).2 ≤ 5 := by
  simp only [buildYStep, bind_eq_bind]
  split_ifs <;> simp [*]

noncomputable def CS (f : Finset E → ℝ) (inc : Option (Finset E × ℝ)) (X : Finset E) : Option (Finset E × ℝ) :=
  match inc with
  | none => some (X, f X)
  | some (B, b) => if b < f X then some (X, f X) else some (B, b)

theorem run_consider (f : Finset E → ℝ) (inc : Option (Finset E × ℝ)) (X : Finset E) :
    run f (consider inc X) = (CS f inc X, 3) := by
  simp only [consider, bind_eq_bind, run_tick_bind, run_ask_bind]
  rcases inc with _ | ⟨B, b⟩
  · simp [CS]
  · simp only [CS]; split_ifs <;> simp


theorem run_filter (f : Finset E → ℝ) (L : List E) :
    (run f (L.foldlM filterStep [])).1 = L.filter (fun v => 0 < f {v}) ∧
    (run f (L.foldlM filterStep [])).2 ≤ 3 * L.length := by
  constructor
  · rw [run_foldlM_fst]
    have hfun : (fun s a => (run f (filterStep s a)).1) = fun (s : List E) a => if 0 < f {a} then s ++ [a] else s := by
      funext s a; simp [run_filterStep]
    rw [hfun]
    have : ∀ (l acc : List E), l.foldl (fun (s : List E) a => if 0 < f {a} then s ++ [a] else s) acc
        = acc ++ l.filter (fun v => 0 < f {v}) := by
      intro l; induction l with
      | nil => simp
      | cons a l ih => intro acc; rw [List.foldl_cons, ih]; split_ifs with h <;> simp [List.filter_cons, h]
    simpa using this L []
  · have := run_foldlM_cost f filterStep (fun _ => 0) 3 L [] (fun s a _ => by simp [run_filterStep])
    simpa [mul_comm] using this

noncomputable def GG (f : Finset E → ℝ) (v : E) (V' : Finset E) (u : E) : Finset E :=
  if u = v then V' else if f (insert u V') = f V' + f {u} then insert u V' else V'

noncomputable def GC (f : Finset E → ℝ) (L : List E) (v : E) : Finset E := L.foldl (GG f v) {v}

theorem run_growClique (f : Finset E → ℝ) (L : List E) (v : E) :
    (run f (growClique L v)).1 = GC f L v ∧ (run f (growClique L v)).2 ≤ 1 + 7 * L.length := by
  simp only [growClique, bind_eq_bind, run_bind, run_tick]
  constructor
  · rw [run_foldlM_fst]; unfold GC; congr 1; funext s a; rw [(run_growStep' f v s a).1]; rfl
  · have := run_foldlM_cost f (growStep v) (fun _ => 0) 7 L {v} (fun s a _ => by simp [(run_growStep' f v s a).2])
    simp at this; simp; omega

noncomputable def CG (f : Finset E → ℝ) (L : List E) (st : Finset E × List (Finset E)) (v : E) :
    Finset E × List (Finset E) :=
  if v ∈ st.1 then st else (st.1 ∪ GC f L v, st.2 ++ [GC f L v])

theorem run_cliqueStep (f : Finset E → ℝ) (L : List E) (st : Finset E × List (Finset E)) (v : E) :
    (run f (cliqueStep L st v)).1 = CG f L st v ∧
    (run f (cliqueStep L st v)).2 + (8 * L.length + 2) * st.2.length ≤
      1 + (8 * L.length + 2) * (CG f L st v).2.length := by
  simp only [cliqueStep, bind_eq_bind, CG]
  split_ifs with h
  · simp [h]
  · have := run_growClique f L v
    simp only [run_bind, run_tick, run_ticks_bind, this.1]
    simp
    nlinarith [this.2]

theorem run_cliquePhase (f : Finset E → ℝ) (L : List E) :
    (run f (cliquePhase L)).1 = (L.foldl (CG f L) (∅, [])).2 ∧
    (run f (cliquePhase L)).2 ≤ L.length + (8 * L.length + 2) * (L.foldl (CG f L) (∅, [])).2.length := by
  simp only [cliquePhase, bind_eq_bind, run_bind, run_ret]
  have hf : (run f (L.foldlM (cliqueStep L) (∅, []))).1 = L.foldl (CG f L) (∅, []) := by
    rw [run_foldlM_fst]; congr 1; funext s a; exact (run_cliqueStep f L s a).1
  have := run_foldlM_cost f (cliqueStep L) (fun st => (8 * L.length + 2) * st.2.length) 1 L (∅, [])
    (fun s a _ => by rw [(run_cliqueStep f L s a).1]; exact (run_cliqueStep f L s a).2)
  rw [hf] at this ⊢
  simp at this ⊢; omega


noncomputable def BYS (f : Finset E → ℝ) (V' : Finset E) (b : ℝ) (Y : Finset E) (v : E) : Finset E :=
  if v ∈ V' then Y else if b < f (insert v V') then insert v Y else Y

noncomputable def BY (f : Finset E → ℝ) (L : List E) (V' : Finset E) : Finset E :=
  L.foldl (BYS f V' (f V')) V'

theorem run_buildY (f : Finset E → ℝ) (L : List E) (V' : Finset E) :
    (run f (buildY L V')).1 = BY f L V' ∧ (run f (buildY L V')).2 ≤ 6 * L.length + 1 := by
  simp only [buildY, bind_eq_bind, run_bind, run_ticks, run_ask]
  constructor
  · rw [run_foldlM_fst]; unfold BY; congr 1; funext s a; rw [(run_buildYStep f V' _ s a).1]; rfl
  · have := run_foldlM_cost f (buildYStep V' (f V')) (fun _ => 0) 5 L V' (fun s a _ => by simp [(run_buildYStep f V' _ s a).2])
    simp at this; simp; omega

noncomputable def SP (f : Finset E → ℝ) (L : List E) (V' : Finset E) (inc : Option (Finset E × ℝ)) (W : Finset E) :
    Option (Finset E × ℝ) := L.foldl (fun inc' v => CS f inc' (insert v (V' ∪ W))) inc

theorem run_scanPair (f : Finset E → ℝ) (L : List E) (V' : Finset E) (inc : Option (Finset E × ℝ)) (W : Finset E) :
    (run f (scanPair L V' inc W)).1 = SP f L V' inc W ∧ (run f (scanPair L V' inc W)).2 ≤ 4 * L.length := by
  simp only [scanPair, bind_eq_bind, run_bind, run_ticks]
  constructor
  · rw [run_foldlM_fst]; unfold SP; congr 1; funext s a; rw [run_consider]
  · have := run_foldlM_cost f (fun inc' v => consider inc' (insert v (V' ∪ W))) (fun _ => 0) 3 L inc
      (fun s a _ => by simp [run_consider])
    simp at this; simp; omega

noncomputable def SPS (f : Finset E → ℝ) (L : List E) : List (Finset E) → Option (Finset E × ℝ) → Option (Finset E × ℝ)
  | [], inc => inc
  | V' :: rest, inc => SPS f L rest (rest.foldl (SP f L V') inc)

theorem run_scanPairs (f : Finset E → ℝ) (L : List E) : ∀ (Vs : List (Finset E)) (inc : Option (Finset E × ℝ)),
    (run f (scanPairs L Vs inc)).1 = SPS f L Vs inc ∧
    (run f (scanPairs L Vs inc)).2 ≤ Vs.length * (1 + 4 * L.length * Vs.length) := by
  intro Vs; induction Vs with
  | nil => intro inc; simp [scanPairs, SPS]
  | cons V' rest ih =>
    intro inc
    simp only [scanPairs, SPS, bind_eq_bind, run_bind, run_tick]
    have hf : (run f (rest.foldlM (scanPair L V') inc)).1 = rest.foldl (SP f L V') inc := by
      rw [run_foldlM_fst]; congr 1; funext s a; exact (run_scanPair f L V' s a).1
    have hc := run_foldlM_cost f (scanPair L V') (fun _ => 0) (4 * L.length) rest inc
      (fun s a _ => by simpa using (run_scanPair f L V' s a).2)
    rw [hf]
    refine ⟨(ih _).1, ?_⟩
    have h2 := (ih (rest.foldl (SP f L V') inc)).2
    simp at hc ⊢
    nlinarith


theorem run_considers (f : Finset E → ℝ) (l : List (Finset E)) (inc : Option (Finset E × ℝ)) :
    (run f (l.foldlM consider inc)).1 = l.foldl (CS f) inc ∧ (run f (l.foldlM consider inc)).2 ≤ 3 * l.length := by
  constructor
  · rw [run_foldlM_fst]; congr 1; funext s a; rw [run_consider]
  · have := run_foldlM_cost f consider (fun _ => 0) 3 l inc (fun s a _ => by simp [run_consider])
    simp at this; omega

theorem run_Ys (f : Finset E → ℝ) (L : List E) (Vs : List (Finset E)) :
    (run f (List.foldlM (fun acc V' => (buildY L V').bind fun Y => pure (acc ++ [Y])) [] Vs)).1 = Vs.map (BY f L) ∧
    (run f (List.foldlM (fun acc V' => (buildY L V').bind fun Y => pure (acc ++ [Y])) [] Vs)).2
      ≤ Vs.length * (6 * L.length + 1) := by
  constructor
  · rw [run_foldlM_fst]
    have hfun : (fun s a => (run f ((fun (acc : List (Finset E)) V' => (buildY L V').bind fun Y => pure (acc ++ [Y])) s a)).1)
        = fun s a => s ++ [BY f L a] := by
      funext s a; simp [(run_buildY f L a).1]
    rw [hfun]
    have : ∀ (l acc : List (Finset E)), l.foldl (fun s a => s ++ [BY f L a]) acc = acc ++ l.map (BY f L) := by
      intro l; induction l with
      | nil => simp
      | cons a l ih => intro acc; rw [List.foldl_cons, ih]; simp
    simpa using this Vs []
  · have := run_foldlM_cost f (fun (acc : List (Finset E)) V' => (buildY L V').bind fun Y => pure (acc ++ [Y]))
      (fun _ => 0) (6 * L.length + 1) Vs [] (fun s a _ => by simpa using (run_buildY f L a).2)
    simp at this ⊢; linarith

noncomputable def outOf (inc : Option (Finset E × ℝ)) : Finset E :=
  match inc with
  | none => ∅
  | some (B, _) => B

theorem run_alg4 (f : Finset E → ℝ) (L : List E) :
    let Vs := (L.foldl (CG f L) (∅, [])).2
    (run f (alg4 L)).1 = outOf (SPS f L Vs ((Vs.map (BY f L)).foldl (CS f) (Vs.foldl (CS f) none))) ∧
    (run f (alg4 L)).2 ≤ L.length + (8 * L.length + 2) * Vs.length + Vs.length * (6 * L.length + 1)
      + 3 * Vs.length + 3 * Vs.length + Vs.length * (1 + 4 * L.length * Vs.length) + L.length := by
  intro Vs
  simp only [alg4, bind_eq_bind, run_bind]
  obtain ⟨h1, h2⟩ := run_cliquePhase f L
  rw [h1]
  obtain ⟨h3, h4⟩ := run_Ys f L Vs
  obtain ⟨h5, h6⟩ := run_considers f Vs none
  rw [h3, h5]
  obtain ⟨h7, h8⟩ := run_considers f (Vs.map (BY f L)) (Vs.foldl (CS f) none)
  rw [h7]
  obtain ⟨h9, h10⟩ := run_scanPairs f L Vs ((Vs.map (BY f L)).foldl (CS f) (Vs.foldl (CS f) none))
  rw [h9]
  simp only [run_ticks, List.length_map] at h8 ⊢
  have hV : (List.foldl (CG f L) (∅, []) L).2 = Vs := rfl
  rw [hV] at h2 ⊢
  generalize SPS f L Vs (List.foldl (CS f) (List.foldl (CS f) none Vs) (List.map (BY f L) Vs)) = inc at h10 ⊢
  rcases inc with _ | ⟨B, b⟩
  all_goals
    simp only [pure_eq_ret] at h4
    simp only [outOf, pure_eq_ret, run_ret]
    constructor
    · first | trivial | rfl
    · omega


theorem run_xosMax (f : Finset E → ℝ) (L : List E) :
    (run f (xosMax L)).1 = (run f (alg4 (L.filter (fun v => 0 < f {v})))).1 ∧
    (run f (xosMax L)).2 ≤ 3 * L.length + (run f (alg4 (L.filter (fun v => 0 < f {v})))).2 := by
  simp only [xosMax, bind_eq_bind, run_bind]
  obtain ⟨h1, h2⟩ := run_filter f L
  rw [h1]; exact ⟨rfl, by omega⟩


section Math
variable [Fintype E] {k : ℕ} {w : Fin k → E → ℝ} {f : Finset E → ℝ}

def gS (f : Finset E → ℝ) (S : Finset E) : ℝ := ∑ x ∈ S, f {x}

noncomputable def Cl (w : Fin k → E → ℝ) (f : Finset E → ℝ) (S : Finset E) : Finset (Fin k) :=
  Finset.univ.filter (fun i => ∀ x ∈ S, w i x = f {x})

theorem mem_Cl {S : Finset E} {i : Fin k} : i ∈ Cl w f S ↔ ∀ x ∈ S, w i x = f {x} := by
  simp [Cl]

theorem Cl_anti {S T : Finset E} (h : S ⊆ T) : Cl w f T ⊆ Cl w f S := by
  intro i hi; rw [mem_Cl] at *; exact fun x hx => hi x (h hx)

theorem le_f (hw : Represents w f) (S : Finset E) (i : Fin k) : ∑ x ∈ S, w i x ≤ f S :=
  (hw S).2 ⟨i, rfl⟩

theorem ex_f (hw : Represents w f) (S : Finset E) : ∃ i, ∑ x ∈ S, w i x = f S := by
  obtain ⟨i, hi⟩ := (hw S).1; exact ⟨i, hi⟩

theorem w_le (hw : Represents w f) (i : Fin k) (x : E) : w i x ≤ f {x} := by
  simpa using le_f hw {x} i

theorem f_le_g (hw : Represents w f) (S : Finset E) : f S ≤ gS f S := by
  obtain ⟨i, hi⟩ := ex_f hw S
  rw [← hi]; exact Finset.sum_le_sum (fun x _ => w_le hw i x)

theorem sum_eq_g_of_mem (S : Finset E) {i : Fin k} (hi : i ∈ Cl w f S) : ∑ x ∈ S, w i x = gS f S := by
  rw [mem_Cl] at hi; exact Finset.sum_congr rfl hi

theorem f_eq_g_of_mem (hw : Represents w f) (S : Finset E) {i : Fin k} (hi : i ∈ Cl w f S) : f S = gS f S :=
  le_antisymm (f_le_g hw S) (by rw [← sum_eq_g_of_mem S hi]; exact le_f hw S i)

theorem Cl_ne_of_eq (hw : Represents w f) (S : Finset E) (h : f S = gS f S) : (Cl w f S).Nonempty := by
  obtain ⟨i, hi⟩ := ex_f hw S
  refine ⟨i, ?_⟩
  rw [mem_Cl]
  have h0 : ∑ x ∈ S, (f {x} - w i x) = 0 := by
    rw [Finset.sum_sub_distrib, hi]; unfold gS at h; linarith
  intro x hx
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sub_nonneg.mpr (w_le hw i y))).mp h0 x hx
  linarith

theorem f_empty (hw : Represents w f) : f ∅ = 0 := by
  obtain ⟨i, hi⟩ := ex_f hw ∅; simpa using hi.symm


def Inv0 (w : Fin k → E → ℝ) (f : Finset E → ℝ) (L : List E) (v : E) (V' : Finset E) : Prop :=
  v ∈ V' ∧ (∀ x ∈ V', x ∈ L) ∧ (Cl w f V').Nonempty

theorem GG_step (hw : Represents w f) (L : List E) (v : E) (V' : Finset E) (u : E) (hu : u ∈ L)
    (h : Inv0 w f L v V') :
    Inv0 w f L v (GG f v V' u) ∧ V' ⊆ GG f v V' u ∧
      (u ∉ GG f v V' u → ∀ i ∈ Cl w f (GG f v V' u), w i u ≠ f {u}) := by
  obtain ⟨hv, hL, i0, hi0⟩ := h
  have hg : f V' = gS f V' := f_eq_g_of_mem hw V' hi0
  unfold GG
  split_ifs with h1 h2
  · subst h1; exact ⟨⟨hv, hL, i0, hi0⟩, subset_rfl, fun h => absurd hv h⟩
  · refine ⟨⟨Finset.mem_insert_of_mem hv, ?_, ?_⟩, Finset.subset_insert _ _, fun h => absurd (Finset.mem_insert_self _ _) h⟩
    · intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx; exacts [hu, hL x hx]
    · by_cases huV : u ∈ V'
      · rw [Finset.insert_eq_of_mem huV]; exact ⟨i0, hi0⟩
      · apply Cl_ne_of_eq hw
        rw [h2, hg]; unfold gS; rw [Finset.sum_insert huV]; ring
  · refine ⟨⟨hv, hL, i0, hi0⟩, subset_rfl, ?_⟩
    intro huV i hi hwi
    apply h2
    have hi' : i ∈ Cl w f (insert u V') := by
      rw [mem_Cl] at hi ⊢
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx; exacts [hwi, hi x hx]
    rw [f_eq_g_of_mem hw _ hi', hg]; unfold gS; rw [Finset.sum_insert huV]; ring

theorem GG_fold (hw : Represents w f) (L : List E) (v : E) : ∀ (l : List E), (∀ u ∈ l, u ∈ L) →
    ∀ V', Inv0 w f L v V' → Inv0 w f L v (l.foldl (GG f v) V') ∧ V' ⊆ l.foldl (GG f v) V' ∧
      ∀ u ∈ l, u ∉ l.foldl (GG f v) V' → ∀ i ∈ Cl w f (l.foldl (GG f v) V'), w i u ≠ f {u} := by
  intro l; induction l with
  | nil => intro _ V' h; simpa using h
  | cons a l ih =>
    intro hl V' h
    obtain ⟨s1, s2, s3⟩ := GG_step hw L v V' a (hl a (by simp)) h
    obtain ⟨t1, t2, t3⟩ := ih (fun u hu => hl u (by simp [hu])) _ s1
    simp only [List.foldl_cons]
    refine ⟨t1, s2.trans t2, ?_⟩
    intro u hu hnot i hi
    rcases List.mem_cons.mp hu with rfl | hu
    · exact s3 (fun hm => hnot (t2 hm)) i (Cl_anti t2 hi)
    · exact t3 u hu hnot i hi

theorem GC_spec (hw : Represents w f) (L : List E) (v : E) (hv : v ∈ L) :
    Inv0 w f L v (GC f L v) ∧ ∀ u ∈ L, u ∉ GC f L v → ∀ i ∈ Cl w f (GC f L v), w i u ≠ f {u} := by
  have h0 : Inv0 w f L v {v} := by
    refine ⟨Finset.mem_singleton_self _, fun x hx => by rw [Finset.mem_singleton.mp hx]; exact hv, ?_⟩
    exact Cl_ne_of_eq hw _ (by simp [gS])
  obtain ⟨t1, -, t3⟩ := GG_fold hw L v L (fun u hu => hu) {v} h0
  exact ⟨t1, t3⟩


def GoodV (w : Fin k → E → ℝ) (f : Finset E → ℝ) (L : List E) (V : Finset E) : Prop :=
  (∀ x ∈ V, x ∈ L) ∧ (Cl w f V).Nonempty ∧ ∀ u ∈ L, u ∉ V → ∀ i ∈ Cl w f V, w i u ≠ f {u}

def JS (w : Fin k → E → ℝ) (f : Finset E → ℝ) (L : List E) (st : Finset E × List (Finset E)) : Prop :=
  (∀ x, x ∈ st.1 ↔ ∃ V ∈ st.2, x ∈ V) ∧ (∀ V ∈ st.2, GoodV w f L V) ∧
    st.2.Pairwise (fun A B => Disjoint (Cl w f A) (Cl w f B))

theorem CG_step (hw : Represents w f) (L : List E) (st : Finset E × List (Finset E)) (v : E) (hv : v ∈ L)
    (h : JS w f L st) : JS w f L (CG f L st v) ∧ (∀ x ∈ st.1, x ∈ (CG f L st v).1) ∧ v ∈ (CG f L st v).1 := by
  unfold CG
  split_ifs with h1
  · exact ⟨h, fun x hx => hx, h1⟩
  · obtain ⟨hR, hG, hP⟩ := h
    obtain ⟨⟨g1, g2, g3⟩, g4⟩ := GC_spec hw L v hv
    refine ⟨⟨?_, ?_, ?_⟩, fun x hx => Finset.mem_union_left _ hx, Finset.mem_union_right _ g1⟩
    · intro x; simp only [Finset.mem_union, hR, List.mem_append, List.mem_singleton]
      constructor
      · rintro (⟨V, hV, hx⟩ | hx); exacts [⟨V, Or.inl hV, hx⟩, ⟨_, Or.inr rfl, hx⟩]
      · rintro ⟨V, hV | rfl, hx⟩; exacts [Or.inl ⟨V, hV, hx⟩, Or.inr hx]
    · intro V hV
      rcases List.mem_append.mp hV with hV | hV
      · exact hG V hV
      · rw [List.mem_singleton.mp hV]; exact ⟨g2, g3, g4⟩
    · rw [List.pairwise_append]
      refine ⟨hP, List.pairwise_singleton _ _, ?_⟩
      intro A hA B hB
      rw [List.mem_singleton.mp hB]
      rw [Finset.disjoint_left]
      intro i hiA hiB
      have hvA : v ∉ A := fun hvA => h1 ((hR v).mpr ⟨A, hA, hvA⟩)
      exact (hG A hA).2.2 v hv hvA i hiA ((mem_Cl.mp hiB) v g1)

theorem CG_fold (hw : Represents w f) (L : List E) : ∀ (l : List E), (∀ u ∈ l, u ∈ L) →
    ∀ st, JS w f L st → JS w f L (l.foldl (CG f L) st) ∧ ∀ u ∈ l, u ∈ (l.foldl (CG f L) st).1 := by
  intro l; induction l with
  | nil => intro _ st h; simpa using h
  | cons a l ih =>
    intro hl st h
    obtain ⟨s1, -, s3⟩ := CG_step hw L st a (hl a (by simp)) h
    simp only [List.foldl_cons]
    have : ∀ st', JS w f L st' → ∀ x ∈ st'.1, x ∈ (l.foldl (CG f L) st').1 := by
      clear ih s1 s3 h st
      induction l with
      | nil => intro st' _ x hx; exact hx
      | cons b l ih2 =>
        intro st' h' x hx
        obtain ⟨u1, u2, -⟩ := CG_step hw L st' b (hl b (by simp)) h'
        exact ih2 (fun u hu => hl u (by simp at hu ⊢; tauto)) _ u1 x (u2 x hx)
    obtain ⟨t1, t2⟩ := ih (fun u hu => hl u (by simp [hu])) _ s1
    refine ⟨t1, ?_⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact this _ s1 u s3
    · exact t2 u hu

theorem cliques_spec (hw : Represents w f) (L : List E) :
    let Vs := (L.foldl (CG f L) (∅, [])).2
    (∀ V ∈ Vs, GoodV w f L V) ∧ (∀ u ∈ L, ∃ V ∈ Vs, u ∈ V) ∧
      Vs.Pairwise (fun A B => Disjoint (Cl w f A) (Cl w f B)) := by
  intro Vs
  have h0 : JS w f L (∅, []) := ⟨by simp, by simp, List.Pairwise.nil⟩
  obtain ⟨⟨hR, hG, hP⟩, hc⟩ := CG_fold hw L L (fun u hu => hu) (∅, []) h0
  exact ⟨hG, fun u hu => (hR u).mp (hc u hu), hP⟩


theorem pw_forall {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b}, a ∈ l → b ∈ l → a ≠ b → R a b := by
  intro l; induction l with
  | nil => intro _ a b ha; simp at ha
  | cons x l ih =>
    intro h a b ha hb hab
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · exact absurd (ha'.trans hb'.symm) hab
    · rw [ha']; exact h.1 b hb'
    · rw [hb']; exact hs _ _ (h.1 a ha')
    · exact ih h.2 ha' hb' hab

theorem count_spec (Vs : List (Finset E)) (hne : ∀ V ∈ Vs, (Cl w f V).Nonempty)
    (hP : Vs.Pairwise (fun A B => Disjoint (Cl w f A) (Cl w f B))) :
    Vs.Nodup ∧ Vs.toFinset.card = Vs.length ∧ Vs.length ≤ k ∧
      (Vs.length = k → (∀ j : Fin k, ∃ V ∈ Vs, j ∈ Cl w f V) ∧ ∀ V ∈ Vs, (Cl w f V).card ≤ 1) := by
  have hnd : Vs.Nodup := by
    refine List.Pairwise.imp_of_mem ?_ hP
    intro A B hA _ hd hAB
    subst hAB
    obtain ⟨i, hi⟩ := hne A hA
    exact Finset.disjoint_left.mp hd hi hi
  have hcard : Vs.toFinset.card = Vs.length := List.toFinset_card_of_nodup hnd
  have hpd : (Vs.toFinset : Set (Finset E)).PairwiseDisjoint (Cl w f) := by
    intro A hA B hB hAB
    simp only [List.coe_toFinset, Set.mem_ofPred_eq] at hA hB
    exact pw_forall (fun a b h => Disjoint.symm h) hP hA hB hAB
  have hsum : ∑ V ∈ Vs.toFinset, (Cl w f V).card = (Vs.toFinset.biUnion (Cl w f)).card :=
    (Finset.card_biUnion hpd).symm
  have hle : (Vs.toFinset.biUnion (Cl w f)).card ≤ k := by
    simpa using Finset.card_le_univ (Vs.toFinset.biUnion (Cl w f))
  have hge : Vs.toFinset.card ≤ ∑ V ∈ Vs.toFinset, (Cl w f V).card := by
    have := Finset.card_nsmul_le_sum Vs.toFinset (fun V => (Cl w f V).card) 1
      (fun V hV => Finset.Nonempty.card_pos (hne V (List.mem_toFinset.mp hV)))
    simpa using this
  refine ⟨hnd, hcard, by omega, fun hk => ⟨?_, ?_⟩⟩
  · have hu : Vs.toFinset.biUnion (Cl w f) = Finset.univ := by
      apply Finset.eq_univ_of_card; simp; omega
    intro j
    have : j ∈ Vs.toFinset.biUnion (Cl w f) := hu ▸ Finset.mem_univ j
    obtain ⟨V, hV, hj⟩ := Finset.mem_biUnion.mp this
    exact ⟨V, List.mem_toFinset.mp hV, hj⟩
  · intro V hV
    have hV' : V ∈ Vs.toFinset := List.mem_toFinset.mpr hV
    have h1 := Finset.add_sum_erase Vs.toFinset (fun V => (Cl w f V).card) hV'
    have h2 := Finset.card_nsmul_le_sum (Vs.toFinset.erase V) (fun V => (Cl w f V).card) 1
      (fun V' hV'' => Finset.Nonempty.card_pos (hne V' (List.mem_toFinset.mp (Finset.mem_of_mem_erase hV''))))
    rw [Finset.card_erase_of_mem hV'] at h2
    simp at h2 h1
    omega


theorem mem_BYfold (f : Finset E → ℝ) (V : Finset E) (b : ℝ) (y : E) : ∀ (l : List E) (Y0 : Finset E),
    y ∈ l.foldl (BYS f V b) Y0 ↔ y ∈ Y0 ∨ (y ∈ l ∧ y ∉ V ∧ b < f (insert y V)) := by
  intro l; induction l with
  | nil => intro Y0; simp
  | cons a l ih =>
    intro Y0
    rw [List.foldl_cons, ih]
    unfold BYS
    by_cases hya : y = a
    · subst hya; by_cases h1 : y ∈ V <;> by_cases h2 : b < f (insert y V) <;> simp [h1, h2]
    · split_ifs with h1 h2 <;> simp [hya]

theorem mem_BY (f : Finset E → ℝ) (L : List E) (V : Finset E) (y : E) :
    y ∈ BY f L V ↔ y ∈ V ∨ (y ∈ L ∧ y ∉ V ∧ f V < f (insert y V)) := by
  unfold BY; rw [mem_BYfold]

def Val (f : Finset E → ℝ) (inc : Option (Finset E × ℝ)) : Prop := inc = none ∨ ∃ B, inc = some (B, f B)
def Dom (f : Finset E → ℝ) (inc : Option (Finset E × ℝ)) (t : ℝ) : Prop := ∃ B, inc = some (B, f B) ∧ t ≤ f B

theorem Dom.val {f : Finset E → ℝ} {inc} {t : ℝ} (h : Dom f inc t) : Val f inc := by
  obtain ⟨B, h, -⟩ := h; exact Or.inr ⟨B, h⟩

theorem CS_val {f : Finset E → ℝ} {inc} (X : Finset E) (h : Val f inc) : Val f (CS f inc X) ∧ Dom f (CS f inc X) (f X) := by
  rcases h with rfl | ⟨B, rfl⟩
  · exact ⟨Or.inr ⟨X, rfl⟩, X, rfl, le_rfl⟩
  · simp only [CS]; split_ifs with h
    · exact ⟨Or.inr ⟨X, rfl⟩, X, rfl, le_rfl⟩
    · exact ⟨Or.inr ⟨B, rfl⟩, B, rfl, le_of_not_gt h⟩

theorem CS_dom {f : Finset E → ℝ} {inc} {t : ℝ} (X : Finset E) (h : Dom f inc t) : Dom f (CS f inc X) t := by
  obtain ⟨B, rfl, ht⟩ := h
  simp only [CS]; split_ifs with h
  · exact ⟨X, rfl, by linarith⟩
  · exact ⟨B, rfl, ht⟩

theorem fold_val {α : Type} {f : Finset E → ℝ} {F : Option (Finset E × ℝ) → α → Option (Finset E × ℝ)}
    (hF : ∀ inc a, Val f inc → Val f (F inc a)) : ∀ (l : List α) inc, Val f inc → Val f (l.foldl F inc) := by
  intro l; induction l with
  | nil => intro inc h; exact h
  | cons a l ih => intro inc h; exact ih _ (hF inc a h)

theorem fold_dom {α : Type} {f : Finset E → ℝ} {F : Option (Finset E × ℝ) → α → Option (Finset E × ℝ)}
    (hF : ∀ inc a t, Dom f inc t → Dom f (F inc a) t) : ∀ (l : List α) inc t, Dom f inc t → Dom f (l.foldl F inc) t := by
  intro l; induction l with
  | nil => intro inc t h; exact h
  | cons a l ih => intro inc t h; exact ih _ _ (hF inc a t h)

theorem fold_dom_mem {α : Type} {f : Finset E → ℝ} {F : Option (Finset E × ℝ) → α → Option (Finset E × ℝ)}
    (hV : ∀ inc a, Val f inc → Val f (F inc a)) (hF : ∀ inc a t, Dom f inc t → Dom f (F inc a) t)
    {t : ℝ} : ∀ (l : List α) inc a, a ∈ l → (∀ inc, Val f inc → Dom f (F inc a) t) → Val f inc →
      Dom f (l.foldl F inc) t := by
  intro l; induction l with
  | nil => intro inc a ha; simp at ha
  | cons b l ih =>
    intro inc a ha hT h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact fold_dom hF l _ _ (hT inc h)
    · exact ih _ a ha hT (hV inc b h)

theorem SP_val (f : Finset E → ℝ) (L : List E) (V : Finset E) : ∀ inc W, Val f inc → Val f (SP f L V inc W) :=
  fun inc W h => fold_val (fun inc a h => (CS_val _ h).1) L inc h

theorem SP_dom (f : Finset E → ℝ) (L : List E) (V : Finset E) : ∀ inc W t, Dom f inc t → Dom f (SP f L V inc W) t :=
  fun inc W t h => fold_dom (fun inc a t h => CS_dom _ h) L inc t h

theorem SP_mem (f : Finset E → ℝ) (L : List E) (V : Finset E) (W : Finset E) (v : E) (hv : v ∈ L) :
    ∀ inc, Val f inc → Dom f (SP f L V inc W) (f (insert v (V ∪ W))) :=
  fun inc h => fold_dom_mem (fun inc a h => (CS_val _ h).1) (fun inc a t h => CS_dom _ h) L inc v hv
    (fun inc h => (CS_val _ h).2) h

theorem SPS_val (f : Finset E → ℝ) (L : List E) : ∀ (Vs : List (Finset E)) inc, Val f inc → Val f (SPS f L Vs inc) := by
  intro Vs; induction Vs with
  | nil => intro inc h; exact h
  | cons V rest ih => intro inc h; exact ih _ (fold_val (SP_val f L V) rest inc h)

theorem SPS_dom (f : Finset E → ℝ) (L : List E) : ∀ (Vs : List (Finset E)) inc t, Dom f inc t → Dom f (SPS f L Vs inc) t := by
  intro Vs; induction Vs with
  | nil => intro inc t h; exact h
  | cons V rest ih => intro inc t h; exact ih _ _ (fold_dom (SP_dom f L V) rest inc t h)

theorem SPS_pairs (f : Finset E → ℝ) (L : List E) : ∀ (Vs : List (Finset E)) inc, Val f inc →
    Vs.Pairwise (fun A B => ∀ v ∈ L, Dom f (SPS f L Vs inc) (f (insert v (A ∪ B)))) := by
  intro Vs; induction Vs with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons V rest ih =>
    intro inc h
    rw [List.pairwise_cons]
    refine ⟨?_, ih _ (fold_val (SP_val f L V) rest inc h)⟩
    intro B hB v hv
    exact SPS_dom f L rest _ _ (fold_dom_mem (SP_val f L V) (SP_dom f L V) rest inc B hB
      (fun inc h => SP_mem f L V B v hv inc h) h)

theorem Dom.le_out {f : Finset E → ℝ} {inc} {t : ℝ} (h : Dom f inc t) : t ≤ f (outOf inc) := by
  obtain ⟨B, rfl, ht⟩ := h; exact ht


theorem cover_sum (φ ψ : E → ℝ) : ∀ (J : Finset (Finset E)) (S : Finset E), (∀ u ∈ S, ∃ V ∈ J, u ∈ V) →
    (∀ V ∈ J, ∀ x ∈ V, 0 ≤ ψ x) → (∀ u ∈ S, φ u ≤ ψ u) → ∑ u ∈ S, φ u ≤ ∑ V ∈ J, ∑ x ∈ V, ψ x := by
  intro J
  induction J using Finset.induction_on with
  | empty =>
    intro S hS _ _
    have : S = ∅ := Finset.eq_empty_of_forall_notMem (fun u hu => by obtain ⟨V, hV, -⟩ := hS u hu; simp at hV)
    simp [this]
  | insert V J hVJ ih =>
    intro S hS hψ hφ
    rw [Finset.sum_insert hVJ, ← Finset.sum_filter_add_sum_filter_not S (· ∈ V)]
    have h1 : ∑ u ∈ S.filter (· ∈ V), φ u ≤ ∑ x ∈ V, ψ x :=
      le_trans (Finset.sum_le_sum (fun u hu => hφ u (Finset.mem_filter.mp hu).1))
        (Finset.sum_le_sum_of_subset_of_nonneg (fun u hu => (Finset.mem_filter.mp hu).2)
          (fun x hx _ => hψ V (Finset.mem_insert_self _ _) x hx))
    have h2 : ∑ u ∈ S.filter (fun u => ¬ u ∈ V), φ u ≤ ∑ V ∈ J, ∑ x ∈ V, ψ x := by
      apply ih
      · intro u hu
        obtain ⟨hu1, hu2⟩ := Finset.mem_filter.mp hu
        obtain ⟨V', hV', huV'⟩ := hS u hu1
        rcases Finset.mem_insert.mp hV' with rfl | hV'
        · exact absurd huV' hu2
        · exact ⟨V', hV', huV'⟩
      · exact fun V' hV' => hψ V' (Finset.mem_insert_of_mem hV')
      · exact fun u hu => hφ u (Finset.mem_filter.mp hu).1
    linarith

theorem core (hk : 2 ≤ k) (hw : Represents w f) (L : List E) (hL : ∀ u, u ∈ L ↔ 0 < f {u})
    (Vs : List (Finset E)) (hG : ∀ V ∈ Vs, GoodV w f L V) (hcov : ∀ u ∈ L, ∃ V ∈ Vs, u ∈ V)
    (hP : Vs.Pairwise (fun A B => Disjoint (Cl w f A) (Cl w f B))) (b : ℝ) (hb0 : 0 ≤ b)
    (c1 : ∀ V ∈ Vs, f V ≤ b) (c2 : ∀ V ∈ Vs, f (BY f L V) ≤ b)
    (c3 : ∀ A ∈ Vs, ∀ B ∈ Vs, A ≠ B → ∀ v ∈ L, f (insert v (A ∪ B)) ≤ b) :
    ∀ X, f X ≤ ((k : ℝ) - 1) * b := by
  intro X
  obtain ⟨i, hi⟩ := ex_f hw X
  set P := Finset.univ.filter (fun u => 0 < w i u) with hPdef
  have hPL : ∀ u ∈ P, u ∈ L := fun u hu =>
    (hL u).mpr (lt_of_lt_of_le (Finset.mem_filter.mp hu).2 (w_le hw i u))
  have hpos : ∀ u ∈ L, 0 < f {u} := fun u hu => (hL u).mp hu
  have hVpos : ∀ V ∈ Vs, ∀ x ∈ V, 0 ≤ f {x} := fun V hV x hx => le_of_lt (hpos x ((hG V hV).1 x hx))
  have hOPT : f X ≤ ∑ u ∈ P, w i u := by
    rw [← hi, ← Finset.sum_filter_add_sum_filter_not X (fun u => 0 < w i u)]
    have h1 : ∑ u ∈ X.filter (fun u => ¬ 0 < w i u), w i u ≤ 0 :=
      Finset.sum_nonpos (fun u hu => le_of_not_gt (Finset.mem_filter.mp hu).2)
    have h2 : ∑ u ∈ X.filter (fun u => 0 < w i u), w i u ≤ ∑ u ∈ P, w i u :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun u hu => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩)
        (fun u hu _ => le_of_lt (Finset.mem_filter.mp hu).2)
    linarith
  obtain ⟨hnd, hcard, hlen, hk_eq⟩ := count_spec Vs (fun V hV => (hG V hV).2.1) hP
  set T := Vs.toFinset with hTdef
  have hsumb : ∀ J ⊆ T, ∑ V ∈ J, ∑ x ∈ V, f {x} ≤ J.card * b := by
    intro J hJ
    have := Finset.sum_le_card_nsmul J (fun V => ∑ x ∈ V, f {x}) b (fun V hV => by
      have hV' : V ∈ Vs := List.mem_toFinset.mp (hJ hV)
      obtain ⟨j, hj⟩ := (hG V hV').2.1
      have h1 := f_eq_g_of_mem hw V hj
      have h2 := c1 V hV'
      unfold gS at h1; linarith)
    simpa using this
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  by_cases hlt : Vs.length < k
  · have h1 : ∑ u ∈ P, w i u ≤ ∑ V ∈ T, ∑ x ∈ V, f {x} :=
      cover_sum (fun u => w i u) (fun x => f {x}) T P
        (fun u hu => by obtain ⟨V, hV, huV⟩ := hcov u (hPL u hu); exact ⟨V, List.mem_toFinset.mpr hV, huV⟩)
        (fun V hV => hVpos V (List.mem_toFinset.mp hV)) (fun u _ => w_le hw i u)
    have h2 := hsumb T subset_rfl
    have h3 : ((T.card : ℕ) : ℝ) ≤ (k : ℝ) - 1 := by
      have : T.card + 1 ≤ k := by omega
      have : ((T.card + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast this
      push_cast at this; linarith
    have h4 : (T.card : ℝ) * b ≤ ((k : ℝ) - 1) * b := mul_le_mul_of_nonneg_right h3 hb0
    linarith
  · have hlk : Vs.length = k := by omega
    obtain ⟨hall, hone⟩ := hk_eq hlk
    obtain ⟨A, hA, hiA⟩ := hall i
    have hAg := f_eq_g_of_mem hw A hiA
    have hAs := sum_eq_g_of_mem A hiA
    have hAP : A ⊆ P := by
      intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [(mem_Cl.mp hiA) x hx]; exact hpos x ((hG A hA).1 x hx)
    have hPY : P ⊆ BY f L A := by
      intro u hu
      rw [mem_BY]
      by_cases huA : u ∈ A
      · exact Or.inl huA
      · refine Or.inr ⟨hPL u hu, huA, ?_⟩
        have h1 := le_f hw (insert u A) i
        rw [Finset.sum_insert huA, hAs, ← hAg] at h1
        have h2 : 0 < w i u := (Finset.mem_filter.mp hu).2
        linarith
    have hk1 : ((k : ℝ) - 1) * b = ((k : ℝ) - 2) * b + b := by ring
    have hk2 : 0 ≤ ((k : ℝ) - 2) * b := mul_nonneg (by linarith) hb0
    by_cases hYP : BY f L A ⊆ P
    · have hYe : BY f L A = P := Finset.Subset.antisymm hYP hPY
      have h1 := le_f hw P i
      have h2 := c2 A hA
      rw [hYe] at h2
      linarith
    · obtain ⟨y, hyY, hyP⟩ := Finset.not_subset.mp hYP
      have hyA : y ∉ A := fun h => hyP (hAP h)
      obtain ⟨hyL, -, hlt'⟩ := ((mem_BY f L A y).mp hyY).resolve_left hyA
      have hwy : w i y ≤ 0 := by
        by_contra hc
        exact hyP (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hc⟩)
      obtain ⟨j, hj⟩ := ex_f hw (insert y A)
      have hji : j ≠ i := by
        rintro rfl
        rw [Finset.sum_insert hyA, hAs, ← hAg] at hj
        linarith
      obtain ⟨B, hB, hjB⟩ := hall j
      have hAB : A ≠ B := by
        rintro rfl
        have h1 := hone A hA
        have h2 : 1 < (Cl w f A).card := Finset.one_lt_card.mpr ⟨i, hiA, j, hjB, hji.symm⟩
        omega
      have hZ := c3 A hA B hB hAB y hyL
      have hZeq : insert y (A ∪ B) = insert y A ∪ (B \ insert y A) := by
        ext x; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff]; tauto
      have hfZ : f (insert y A) + ∑ x ∈ B \ insert y A, f {x} ≤ f (insert y (A ∪ B)) := by
        have h1 := le_f hw (insert y (A ∪ B)) j
        rw [hZeq, Finset.sum_union Finset.disjoint_sdiff, hj] at h1
        have hB' : ∑ x ∈ B \ insert y A, w j x = ∑ x ∈ B \ insert y A, f {x} :=
          Finset.sum_congr rfl (fun x hx => (mem_Cl.mp hjB) x (Finset.mem_sdiff.mp hx).1)
        rw [← hZeq] at h1
        linarith
      have hsplit : ∑ u ∈ P, w i u = ∑ u ∈ A, w i u + ∑ u ∈ (P \ A).filter (· ∈ B), w i u
          + ∑ u ∈ (P \ A).filter (fun u => ¬ u ∈ B), w i u := by
        rw [← Finset.sum_sdiff hAP, ← Finset.sum_filter_add_sum_filter_not (P \ A) (· ∈ B)]; ring
      have hmid : ∑ u ∈ (P \ A).filter (· ∈ B), w i u ≤ ∑ x ∈ B \ insert y A, f {x} := by
        refine le_trans (Finset.sum_le_sum (fun x _ => w_le hw i x)) (Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun x hx _ => hVpos B hB x (Finset.mem_sdiff.mp hx).1))
        intro x hx
        obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
        obtain ⟨hxP, hxA⟩ := Finset.mem_sdiff.mp hx1
        refine Finset.mem_sdiff.mpr ⟨hx2, ?_⟩
        rw [Finset.mem_insert]; rintro (rfl | h)
        · exact hyP hxP
        · exact hxA h
      have hBT : B ∈ T.erase A := Finset.mem_erase.mpr ⟨hAB.symm, List.mem_toFinset.mpr hB⟩
      have hrest : ∑ u ∈ (P \ A).filter (fun u => ¬ u ∈ B), w i u ≤ ∑ V ∈ (T.erase A).erase B, ∑ x ∈ V, f {x} := by
        refine cover_sum (fun u => w i u) (fun x => f {x}) _ _ ?_ ?_ (fun u _ => w_le hw i u)
        · intro u hu
          obtain ⟨hu1, hu2⟩ := Finset.mem_filter.mp hu
          obtain ⟨huP, huA⟩ := Finset.mem_sdiff.mp hu1
          obtain ⟨V, hV, huV⟩ := hcov u (hPL u huP)
          refine ⟨V, Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, List.mem_toFinset.mpr hV⟩⟩, huV⟩
          · rintro rfl; exact hu2 huV
          · rintro rfl; exact huA huV
        · intro V hV
          exact hVpos V (List.mem_toFinset.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hV)))
      have hrest2 := hsumb ((T.erase A).erase B) (fun V hV => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hV))
      have hc : ((T.erase A).erase B).card + 2 = k := by
        rw [Finset.card_erase_of_mem hBT, Finset.card_erase_of_mem (List.mem_toFinset.mpr hA)]
        rw [← hTdef, hcard]; omega
      have hcR : (((T.erase A).erase B).card : ℝ) = (k : ℝ) - 2 := by
        have := congrArg (fun n : ℕ => (n : ℝ)) hc
        push_cast at this; linarith
      rw [hcR] at hrest2
      rw [hAs, ← hAg] at hsplit
      linarith


theorem cost_arith (n m l k : ℕ) (hm : m ≤ n) (hl : l ≤ k) (hn : 1 ≤ n) (hk : 2 ≤ k) :
    3 * n + (m + (8 * m + 2) * l + l * (6 * m + 1) + 3 * l + 3 * l + l * (1 + 4 * m * l) + m)
      ≤ 33 * (n * k ^ 2) := by
  have h1 : m * l ≤ n * k := Nat.mul_le_mul hm hl
  have h2 : m * l * l ≤ n * k * k := Nat.mul_le_mul h1 hl
  have h3 : n * k ≤ n * k * k := Nat.le_mul_of_pos_right _ (by omega)
  have h4 : n ≤ n * k := Nat.le_mul_of_pos_right _ (by omega)
  have h5 : k ≤ n * k := Nat.le_mul_of_pos_left _ (by omega)
  have e : n * k ^ 2 = n * k * k := by ring
  have e2 : l * (1 + 4 * m * l) = l + 4 * (m * l * l) := by ring
  have e3 : (8 * m + 2) * l = 8 * (m * l) + 2 * l := by ring
  have e4 : l * (6 * m + 1) = 6 * (m * l) + l := by ring
  rw [e, e2, e3, e4]
  omega

end Math

theorem main : ∃ C : ℕ, ∀ (E : Type) [Fintype E] [DecidableEq E] [Nonempty E] (L : List E),
    L.Nodup → (∀ v, v ∈ L) → ∀ (k : ℕ), 2 ≤ k → ∀ f : Finset E → ℝ, IsKXOS k f →
      IsMaximizerApprox Finset.univ ((k : ℝ) - 1) f (run f (xosMax L)).1 ∧
      (run f (xosMax L)).2 ≤ C * k ^ 2 * Fintype.card E ∧
      (k = 2 → (∀ X, f X ≤ f (run f (xosMax L)).1) ∧
        (run f (xosMax L)).2 ≤ C * Fintype.card E) := by
  refine ⟨200, ?_⟩
  intro E _ _ _ L hnd hall k hk f hf
  obtain ⟨w, hw⟩ := hf
  set L' := L.filter (fun v => 0 < f {v}) with hL'def
  have hL' : ∀ u, u ∈ L' ↔ 0 < f {u} := by intro u; simp [hL'def, hall u]
  set Vs := (L'.foldl (CG f L') (∅, [])).2 with hVs
  set inc1 := Vs.foldl (CS f) none with hinc1
  set inc2 := (Vs.map (BY f L')).foldl (CS f) inc1 with hinc2
  set inc3 := SPS f L' Vs inc2 with hinc3
  obtain ⟨hx1, hx2⟩ := run_xosMax f L
  obtain ⟨ha1, ha2⟩ := run_alg4 f L'
  have hout : (run f (xosMax L)).1 = outOf inc3 := by rw [hx1, ha1]
  obtain ⟨hG, hcov, hP⟩ := cliques_spec hw L'
  obtain ⟨-, -, hlen, -⟩ := count_spec Vs (fun V hV => (hG V hV).2.1) hP
  -- domination facts
  have hCSv : ∀ inc (a : Finset E), Val f inc → Val f (CS f inc a) := fun inc a h => (CS_val a h).1
  have hCSd : ∀ inc (a : Finset E) t, Dom f inc t → Dom f (CS f inc a) t := fun inc a t h => CS_dom a h
  have hv1 : Val f inc1 := fold_val hCSv Vs none (Or.inl rfl)
  have hv2 : Val f inc2 := fold_val hCSv _ inc1 hv1
  have d1 : ∀ V ∈ Vs, Dom f inc3 (f V) := fun V hV =>
    SPS_dom f L' Vs _ _ (fold_dom hCSd _ _ _ (fold_dom_mem hCSv hCSd Vs none V hV (fun inc h => (CS_val V h).2) (Or.inl rfl)))
  have d2 : ∀ V ∈ Vs, Dom f inc3 (f (BY f L' V)) := fun V hV =>
    SPS_dom f L' Vs _ _ (fold_dom_mem hCSv hCSd _ inc1 (BY f L' V) (List.mem_map_of_mem hV)
      (fun inc h => (CS_val _ h).2) hv1)
  have d3 : ∀ A ∈ Vs, ∀ B ∈ Vs, A ≠ B → ∀ v ∈ L', Dom f inc3 (f (insert v (A ∪ B))) := by
    intro A hA B hB hAB
    exact pw_forall (fun a b h v hv => by rw [Finset.union_comm]; exact h v hv) (SPS_pairs f L' Vs inc2 hv2) hA hB hAB
  set b := f (outOf inc3) with hb
  have hb0 : 0 ≤ b := by
    by_cases hVe : Vs = []
    · have : inc3 = none := by simp [hinc3, hinc2, hinc1, hVe, SPS]
      rw [hb, this]; simp [outOf, f_empty hw]
    · obtain ⟨V, hV⟩ := List.exists_mem_of_ne_nil Vs hVe
      have h1 := (d1 V hV).le_out
      obtain ⟨j, hj⟩ := (hG V hV).2.1
      rw [f_eq_g_of_mem hw V hj] at h1
      have : 0 ≤ gS f V := Finset.sum_nonneg (fun x hx => le_of_lt ((hL' x).mp ((hG V hV).1 x hx)))
      linarith
  have happ : ∀ X, f X ≤ ((k : ℝ) - 1) * b :=
    core hk hw L' hL' Vs hG hcov hP b hb0 (fun V hV => (d1 V hV).le_out) (fun V hV => (d2 V hV).le_out)
      (fun A hA B hB hAB v hv => (d3 A hA B hB hAB v hv).le_out)
  -- cost
  have hn : Fintype.card E = L.length := by
    have : L.toFinset = Finset.univ := Finset.eq_univ_iff_forall.mpr (fun x => List.mem_toFinset.mpr (hall x))
    rw [← List.toFinset_card_of_nodup hnd, this, Finset.card_univ]
  have hn1 : 1 ≤ L.length := by rw [← hn]; exact Fintype.card_pos
  have hm : L'.length ≤ L.length := List.length_filter_le _ _
  have hcost : (run f (xosMax L)).2 ≤ 33 * (L.length * k ^ 2) :=
    le_trans hx2 (le_trans (Nat.add_le_add_left ha2 _) (cost_arith _ _ _ _ hm hlen hn1 hk))
  rw [hout]
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨⟨Finset.subset_univ _, fun X _ => ?_⟩, ?_, ?_⟩
  · have h1 := happ X
    rw [one_div, inv_mul_le_iff₀ (by linarith)]
    exact h1
  · rw [hn]; nlinarith [hcost]
  · intro hk2
    subst hk2
    refine ⟨fun X => by have := happ X; norm_num at this; linarith, ?_⟩
    rw [hn]; nlinarith [hcost]

end XT

theorem theorem_4 : ∃ C : ℕ, ∀ (E : Type) [Fintype E] [DecidableEq E] [Nonempty E] (L : List E),
    L.Nodup → (∀ v, v ∈ L) → ∀ (k : ℕ), 2 ≤ k → ∀ f : Finset E → ℝ, IsKXOS k f →
      IsMaximizerApprox Finset.univ ((k : ℝ) - 1) f (run f (xosMax L)).1 ∧
      (run f (xosMax L)).2 ≤ C * k ^ 2 * Fintype.card E ∧
      (k = 2 → (∀ X, f X ≤ f (run f (xosMax L)).1) ∧
        (run f (xosMax L)).2 ≤ C * Fintype.card E) := XT.main

end XOSMax


-- Platform entry point: restates the target verbatim.
namespace XOSMax

open OracleProg

/-- **Theorem 4**: "There exists a deterministic algorithm to find a (k − 1)-maximizer of a given
k-XOS function in O(k²n) time for any k ≥ 2 (even if k is unknown). In particular, when k = 2, it
finds an exact maximizer in O(n) time" (Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3,
Theorem 4, p.2).

**Formalization Note** The algorithm is the program `xosMax L` for an arbitrary enumeration `L` of the
ground set, which implies the existence claim. It is deterministic and does not know `k` because it is
a value of the program type built from `L` alone, and the same program serves every `k`. `O(·)` is one
constant `C`, chosen before the ground set, `L`, `k` and `f`. The cost counts value oracle calls and
charged elementary steps. There is no hypothesis on the sign of `f` or of the clauses: the §2
preprocessing inside `xosMax` discharges `f(v) > 0`. -/
theorem _root_.solution : ∃ C : ℕ, ∀ (E : Type) [Fintype E] [DecidableEq E] [Nonempty E] (L : List E),
    L.Nodup → (∀ v, v ∈ L) → ∀ (k : ℕ), 2 ≤ k → ∀ f : Finset E → ℝ, IsKXOS k f →
      IsMaximizerApprox Finset.univ ((k : ℝ) - 1) f (run f (xosMax L)).1 ∧
      (run f (xosMax L)).2 ≤ C * k ^ 2 * Fintype.card E ∧
      (k = 2 → (∀ X, f X ≤ f (run f (xosMax L)).1) ∧
        (run f (xosMax L)).2 ≤ C * Fintype.card E) := by
  apply @XOSMax.theorem_4 <;> assumption

end XOSMax
