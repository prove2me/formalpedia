-- Prove2me | solution 1 for QueryMachines.Tower.towerRuns
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:34:27.019592+00:00
-- url     : https://prove2.me/submissions/4c69ba59-3271-4af1-b4ea-3c1253271ca5

import Definitions.Def_Tower_Chain
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_Runs
import Definitions.Def_Tower_TowerRuns
import Theorems.Thm_QueryMachines_stWithinRules
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_Tower_chain_facts
import Theorems.Thm_QueryMachines_Tower_up_ok

set_option autoImplicit false

open QueryMachines QueryMachines.Tower
open Groundwork

namespace QueryMachines.Tower

variable {Q A α β : Type} {M : QueryMachine Q A α β} {O : Q → Option A} {w : Q → ℕ}
  {s : M.σ} {b : β} {S S' T T' : ℕ}

private theorem wfMono (h : M.WithinFrom O w s T S b) (hT : T ≤ T') (hS : S ≤ S') :
    M.WithinFrom O w s T' S' b := QueryMachine.WithinFrom.mono h hT hS

private theorem wfHalt (h1 : M.out s = some b) (h2 : size s ≤ S) :
    M.WithinFrom O w s T S b := (stWithinRules Q A α β M O w s T S b).1 h1 h2

private theorem wfStep (h1 : M.out s = none) (h2 : M.ask s = none) (h3 : size s ≤ S)
    (h : M.WithinFrom O w (M.step s) T S b) : M.WithinFrom O w s (T + 1) S b :=
  (stWithinRules Q A α β M O w s T S b).2.1 h1 h2 h3 h

private theorem wfQuery {x : Q} {v : A} (h1 : M.out s = none) (h2 : M.ask s = some x)
    (h3 : O x = some v) (h4 : size s ≤ S)
    (h : M.WithinFrom O w (M.resume s v) T S b) :
    M.WithinFrom O w s (T + w x) S b :=
  (stWithinRules Q A α β M O w s T S b).2.2 x v h1 h2 h3 h4 h

variable (M : QueryMachine (Q ⊕ α) (A ⊕ β) α β)

private theorem rout_none {s : M.σ} (K : List M.σ) (h : M.out s = none) :
    rout M (s :: K) = none := by
  cases K
  · exact h
  · rfl

private theorem rask_halted {s : M.σ} {b : β} (K : List M.σ) (h : M.out s = some b) :
    rask M (s :: K) = none := by simp [rask, h]

private theorem rask_none {s : M.σ} (K : List M.σ) (h1 : M.out s = none)
    (h2 : M.ask s = none) : rask M (s :: K) = none := by simp [rask, h1, h2]

private theorem rask_call {s : M.σ} {a' : α} (K : List M.σ) (h1 : M.out s = none)
    (h2 : M.ask s = some (Sum.inr a')) : rask M (s :: K) = none := by
  simp [rask, h1, h2]

private theorem rask_query {s : M.σ} {x : Q} (K : List M.σ) (h1 : M.out s = none)
    (h2 : M.ask s = some (Sum.inl x)) : rask M (s :: K) = some x := by
  simp [rask, h1, h2]

private theorem rstep_step {s : M.σ} (K : List M.σ) (h1 : M.out s = none)
    (h2 : M.ask s = none) : rstep M (s :: K) = M.step s :: K := by
  simp [rstep, h1, h2]

private theorem rstep_call {s : M.σ} {a' : α} (K : List M.σ) (h1 : M.out s = none)
    (h2 : M.ask s = some (Sum.inr a')) :
    rstep M (s :: K) = M.init a' :: s :: K := by simp [rstep, h1, h2]

private theorem rstep_pop {s s' : M.σ} {b : β} (K : List M.σ) (h : M.out s = some b) :
    rstep M (s :: s' :: K) = M.resume s' (Sum.inr b) :: K := by simp [rstep, h]

private theorem size_stack (s : M.σ) (K : List M.σ) :
    size (s :: K) = size s + 1 + size K := by
  simp only [size_list, List.map_cons, List.sum_cons]
  omega

private theorem selfCall_from (O : Q → Option A) (w : Q → ℕ) (Good : α → Prop)
    (val : α → β) (dep T : α → ℕ) (S : ℕ)
    (H : ∀ a, Good a → M.Within (callOracle O Good val dep a)
      (Sum.elim w fun a' => T a' + 2) a (T a) S (val a)) :
    ∀ (n : ℕ) (a : α), dep a = n → Good a → ∀ (s : M.σ) (own : ℕ) (L : List (Q ⊕ α)),
      M.Reaches (callOracle O Good val dep a) S (val a) s own L →
      ∀ (K : List M.σ) (S' tk : ℕ) (b : β), size K + (dep a + 1) * (S + 1) ≤ S' →
      (∀ sh : M.σ, M.out sh = some (val a) → size sh ≤ S →
        (selfCall M).WithinFrom O w (sh :: K : List M.σ) tk S' b) →
      (selfCall M).WithinFrom O w (s :: K : List M.σ)
        (own + (L.map (Sum.elim w fun a' => T a' + 2)).sum + tk) S' b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro a hn hG s own L hr K S' tk b hS hc
  have hmul : (dep a + 1) * (S + 1) = dep a * (S + 1) + (S + 1) := Nat.succ_mul _ _
  have hsz : ∀ s : M.σ, size s ≤ S → size (s :: K : List M.σ) ≤ S' := fun s hs => by
    rw [size_stack]
    omega
  induction hr with
  | halt h1 h2 => exact wfMono (hc _ h1 h2) (by omega) le_rfl
  | @step s own L h1 h2 h3 _ ih =>
    have h := wfStep (M := selfCall M) (s := (s :: K : List M.σ)) (O := O) (w := w)
      (rout_none M K h1) (rask_none M K h1 h2) (hsz _ h3)
      (by
        rw [show (selfCall M).step (s :: K : List M.σ) = (M.step s :: K : List M.σ) from
          rstep_step M K h1 h2]
        exact ih)
    exact wfMono h (by omega) le_rfl
  | @query s own L x v h1 h2 h3 h4 _ ih =>
    rcases x with q | a'
    · obtain ⟨v0, hv0, rfl⟩ : ∃ v0, O q = some v0 ∧ Sum.inl v0 = v := by
        simpa [callOracle] using h3
      have h := wfQuery (M := selfCall M) (s := (s :: K : List M.σ)) (O := O) (w := w)
        (rout_none M K h1) (rask_query M K h1 h2) hv0 (hsz _ h4) ih
      refine wfMono h ?_ le_rfl
      simp only [List.map_cons, List.sum_cons, Sum.elim_inl]
      omega
    · obtain ⟨⟨hG', hd⟩, rfl⟩ : (Good a' ∧ dep a' < dep a) ∧ Sum.inr (val a') = v := by
        simpa [callOracle] using h3
      obtain ⟨own', L', hr', hc'⟩ := H a' hG'
      have hle : (dep a' + 1) * (S + 1) ≤ dep a * (S + 1) := Nat.mul_le_mul_right _ hd
      have hsz2 : ∀ sh : M.σ, size sh ≤ S → size (sh :: s :: K : List M.σ) ≤ S' := fun sh hs => by
        have : S + 1 ≤ (dep a' + 1) * (S + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
        rw [size_stack, size_stack]
        omega
      have hcall := IH (dep a') (hn ▸ hd) a' rfl hG' _ own' L' hr' (s :: K) S'
        (own + (L.map (Sum.elim w fun a' => T a' + 2)).sum + tk + 1) b
        (by rw [size_stack]; omega)
        (fun sh g1 g2 => wfStep (M := selfCall M) (s := (sh :: s :: K : List M.σ)) rfl
          (rask_halted M (s :: K) g1) (hsz2 _ g2)
          (by
            rw [show (selfCall M).step (sh :: s :: K : List M.σ) =
              (M.resume s (Sum.inr (val a')) :: K : List M.σ) from rstep_pop M K g1]
            exact ih))
      have h := wfStep (M := selfCall M) (s := (s :: K : List M.σ)) (O := O) (w := w)
        (rout_none M K h1) (rask_call M K h1 h2) (hsz _ h4)
        (by
          rw [show (selfCall M).step (s :: K : List M.σ) =
            (M.init a' :: s :: K : List M.σ) from rstep_call M K h1 h2]
          exact hcall)
      refine wfMono h ?_ le_rfl
      simp only [List.map_cons, List.sum_cons, Sum.elim_inr]
      omega

private theorem selfCallRuns_aux : SelfCallRuns := by
  intro Q A α β M O w Good val dep T S H a hG
  obtain ⟨own, L, hr, hc⟩ := H a hG
  have h1 : S + 1 ≤ (dep a + 1) * (S + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have h := selfCall_from M O w Good val dep T S H (dep a) a rfl hG _ own L hr []
    ((dep a + 1) * (S + 1) + 1) 0 (val a)
    (by simp only [size_list, List.map_nil, List.sum_nil]; omega)
    (fun sh g1 g2 => wfHalt (M := selfCall M) (s := ([sh] : List M.σ)) g1
      (by
        show size ([sh] : List M.σ) ≤ _
        rw [size_stack]
        simp only [size_list, List.map_nil, List.sum_nil]
        omega))
  obtain ⟨own', L', hr', hc'⟩ := h
  exact ⟨own', L', hr', by omega⟩

variable {Ctx G : Type} [HasSize Ctx] {P : Spec Ctx Q A} {gl : G → Option A} {wg : G → ℕ}
  {Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A}
  {Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A}
  {TS : ℕ → ℕ → ℕ → ℕ} {TI : ℕ → ℕ → ℕ} {SS SI SC : ℕ}
  {c0 : Ctx} {f0 : Q → Option A} {tq : ℕ}

private theorem cost_eq (TS : ℕ → ℕ → ℕ → ℕ) (TI : ℕ → ℕ → ℕ) (l t : ℕ) :
    cost TS TI l t = TS l (callCost TS TI l t) t := by cases l <;> rfl

private theorem callOracle_call {Q A α β : Type} (O : Q → Option A) {Good : α → Prop}
    (val : α → β) {dep : α → ℕ} {a a' : α} (h : Good a' ∧ dep a' < dep a) :
    callOracle O Good val dep a (Sum.inr a') = some (Sum.inr (val a')) := if_pos h

private theorem sol_sim_aux (hM : P.Meets gl wg Sol Inn TS TI SS SI SC) (hG : P.Good c0 f0)
    (env : List Ctx) (hC : Chain P c0 f0 env) {b : A} {s : Sol.σ} {own : ℕ}
    {L : List (Ctx ⊕ (Q ⊕ G))}
    (hr : Sol.Reaches (P.oracle gl (parent c0 env) (tabs P f0 env)) SS b s own L) :
    (nest Sol Inn).WithinFrom
      (callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P)
        (Sum.inl (env, parent c0 env)))
      (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2)
      (Sum.inl (env, s) : NSt Sol Inn)
      (own + (L.map (Sum.elim
        (fun _ => callCost TS TI (P.lev (parent c0 env)) (price P TI tq env))
        (Sum.elim (fun _ => price P TI tq env) wg))).sum)
      (P.lev c0 * (SC + 1) + SS + SI + 2) b := by
  obtain ⟨hGd, hlev, hsize⟩ := chain_facts hM hG env hC
  have hsz : ∀ s : Sol.σ, size s ≤ SS →
      size (Sum.inl (env, s) : NSt Sol Inn) ≤ P.lev c0 * (SC + 1) + SS + SI + 2 := fun s hs => by
    have : env.length * (SC + 1) ≤ P.lev c0 * (SC + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [size_inl, size_prod]
    dsimp only
    omega
  induction hr with
  | halt h1 h2 => exact wfHalt (M := nest Sol Inn) h1 (hsz _ h2)
  | @step s own L h1 h2 h3 _ ih =>
    have ha : (nest Sol Inn).ask (Sum.inl (env, s) : NSt Sol Inn) = none := by simp [nest, h2]
    exact wfMono (wfStep (M := nest Sol Inn) (s := (Sum.inl (env, s) : NSt Sol Inn))
      h1 ha (hsz _ h3) ih) (by omega) le_rfl
  | @query s own L z v h1 h2 h3 h4 _ ih =>
    rcases z with c' | y
    · obtain ⟨hch, rfl⟩ : P.Child (parent c0 env) (tabs P f0 env) c' ∧
          P.val c' (P.tab c' (tabs P f0 env)) = v := by simpa [Spec.oracle] using h3
      have hl := hM.child_lev _ _ c' hGd hch
      have ha : (nest Sol Inn).ask (Sum.inl (env, s) : NSt Sol Inn) =
          some (Sum.inr (Sum.inl (c' :: env, c'))) := by simp [nest, h2]
      have ho : callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P)
          (Sum.inl (env, parent c0 env)) (Sum.inr (Sum.inl (c' :: env, c'))) =
          some (Sum.inr (P.val c' (P.tab c' (tabs P f0 env)))) :=
        callOracle_call _ _ ⟨⟨⟨hC, hch⟩, rfl⟩,
          by show 2 * P.lev c' + (env.length + 1) + 1 <
            2 * P.lev (parent c0 env) + env.length + 1; omega⟩
      have hw : (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2)
          (Sum.inr (Sum.inl (c' :: env, c'))) =
          callCost TS TI (P.lev (parent c0 env)) (price P TI tq env) := by rw [← hl]; rfl
      refine wfMono (wfQuery (M := nest Sol Inn) (s := (Sum.inl (env, s) : NSt Sol Inn))
        (w := (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2))
        h1 ha ho (hsz _ h4) ih) ?_ le_rfl
      rw [hw]
      simp only [List.map_cons, List.sum_cons, Sum.elim_inl]
      omega
    · obtain ⟨r, ho, rfl, hw⟩ := up_ok tq gl wg TS env hC y v (by cases y <;> exact h3)
        (Sum.inl (env, parent c0 env))
        (by show env.length ≤ 2 * P.lev (parent c0 env) + env.length + 1; omega)
      have ha : (nest Sol Inn).ask (Sum.inl (env, s) : NSt Sol Inn) = some (upQuery env y) := by
        simp [nest, h2]
      refine wfMono (wfQuery (M := nest Sol Inn) (s := (Sum.inl (env, s) : NSt Sol Inn))
        (w := (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2))
        h1 ha ho (hsz _ h4) ih) ?_ le_rfl
      rw [hw]
      simp only [List.map_cons, List.sum_cons, Sum.elim_inr]
      omega

private theorem inn_sim_aux (hM : P.Meets gl wg Sol Inn TS TI SS SI SC) (hG : P.Good c0 f0)
    (env : List Ctx) (hC : Chain P c0 f0 env) (c : Ctx) (q : Q) {b : A} {i : Inn.σ}
    {own : ℕ} {L : List (Q ⊕ G)}
    (hr : Inn.Reaches (Sum.elim (tabs P f0 env) gl) SI b i own L) :
    (nest Sol Inn).WithinFrom
      (callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P)
        (Sum.inr (c, env, q)))
      (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2)
      (Sum.inr (env, i) : NSt Sol Inn)
      (own + (L.map (Sum.elim (fun _ => price P TI tq env) wg)).sum)
      (P.lev c0 * (SC + 1) + SS + SI + 2) b := by
  obtain ⟨hGd, hlev, hsize⟩ := chain_facts hM hG env hC
  have hsz : ∀ i : Inn.σ, size i ≤ SI →
      size (Sum.inr (env, i) : NSt Sol Inn) ≤ P.lev c0 * (SC + 1) + SS + SI + 2 := fun i hi => by
    have : env.length * (SC + 1) ≤ P.lev c0 * (SC + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [size_inr, size_prod]
    dsimp only
    omega
  induction hr with
  | halt h1 h2 => exact wfHalt (M := nest Sol Inn) h1 (hsz _ h2)
  | @step i own L h1 h2 h3 _ ih =>
    have ha : (nest Sol Inn).ask (Sum.inr (env, i) : NSt Sol Inn) = none := by simp [nest, h2]
    exact wfMono (wfStep (M := nest Sol Inn) (s := (Sum.inr (env, i) : NSt Sol Inn))
      h1 ha (hsz _ h3) ih) (by omega) le_rfl
  | @query i own L y v h1 h2 h3 h4 _ ih =>
    obtain ⟨r, ho, rfl, hw⟩ := up_ok tq gl wg TS env hC y v h3 (Sum.inr (c, env, q))
      (le_refl env.length)
    have ha : (nest Sol Inn).ask (Sum.inr (env, i) : NSt Sol Inn) = some (upQuery env y) := by
      simp [nest, h2]
    refine wfMono (wfQuery (M := nest Sol Inn) (s := (Sum.inr (env, i) : NSt Sol Inn))
      (w := (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2))
      h1 ha ho (hsz _ h4) ih) ?_ le_rfl
    rw [hw]
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem nest_within_aux (hM : P.Meets gl wg Sol Inn TS TI SS SI SC)
    (hG : P.Good c0 f0) (x : NIn Ctx Q) (hx : nGood P c0 f0 x) :
    (nest Sol Inn).Within
      (callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P) x)
      (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2)
      x (nT P TS TI tq x) (P.lev c0 * (SC + 1) + SS + SI + 2) (nval P c0 f0 x) := by
  rcases x with ⟨env, c⟩ | ⟨c, env, q⟩
  · obtain ⟨hC, rfl⟩ := hx
    obtain ⟨own, L, hr, hc⟩ := hM.sol _ _ (chain_facts hM hG env hC).1
      (callCost TS TI (P.lev (parent c0 env)) (price P TI tq env)) (price P TI tq env)
    obtain ⟨own', L', hr', hc'⟩ := sol_sim_aux (tq := tq) hM hG env hC hr
    exact ⟨own', L', hr', hc'.trans (hc.trans (le_of_eq (cost_eq TS TI _ _).symm))⟩
  · obtain ⟨hC, hs⟩ := hx
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨own, L, hr, hc⟩ := hM.inn _ _ c (chain_facts hM hG env hC.1).1 hC.2 q a ha
      (price P TI tq env)
    obtain ⟨own', L', hr', hc'⟩ := inn_sim_aux (tq := tq) hM hG env hC.1 c q hr
    have hv : nval P c0 f0 (Sum.inr (c, env, q)) = a := by
      show (P.tab c (tabs P f0 env) q).getD _ = a
      rw [ha]
      rfl
    rw [hv]
    exact ⟨own', L', hr', hc'.trans hc⟩

private theorem tower_reaches_aux {O : Q ⊕ G → Option A} {S : ℕ} {b : A}
    {s : (selfCall (nest Sol Inn)).σ} {own : ℕ} {L : List (Q ⊕ G)}
    (h : (selfCall (nest Sol Inn)).Reaches O S b s own L) :
    (tower Sol Inn).Reaches O S b s own L := by
  induction h with
  | halt h1 h2 => exact .halt h1 h2
  | step h1 h2 h3 _ ih => exact .step h1 h2 h3 ih
  | query h1 h2 h3 h4 _ ih => exact .query h1 h2 h3 h4 ih

end QueryMachines.Tower

theorem solution : TowerRuns := by
  intro Ctx Q G A _ P gl wg Sol Inn TS TI SS SI SC hM c f hG tq
  obtain ⟨own, L, hr, hc⟩ := QueryMachines.Tower.selfCallRuns_aux _ _ _ _ (nest Sol Inn)
    (Sum.elim f gl) (Sum.elim (fun _ => tq) wg) (nGood P c f) (nval P c f) (ndep P)
    (nT P TS TI tq) (P.lev c * (SC + 1) + SS + SI + 2)
    (fun x hx => QueryMachines.Tower.nest_within_aux hM hG x hx)
    (Sum.inl ([], c)) ⟨trivial, rfl⟩
  exact ⟨own, L, QueryMachines.Tower.tower_reaches_aux hr, hc⟩
