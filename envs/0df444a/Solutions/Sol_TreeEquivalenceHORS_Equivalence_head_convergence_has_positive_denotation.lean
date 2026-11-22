-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.head_convergence_has_positive_denotation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T19:23:45.666581+00:00
-- url     : https://prove2.me/submissions/e2eaa548-1115-45e8-a1e0-cc6c233e5a35

import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics

namespace TreeEquivalenceHORS.Equivalence

theorem ofArgs_args (τ : Ty) : Ty.ofArgs τ.args = τ := by
  induction τ with
  | o => rfl
  | arr σ τ _ ih => simp [Ty.args, Ty.ofArgs, ih]

theorem args_ofArgs (l : List Ty) : (Ty.ofArgs l).args = l := by
  induction l <;> simp [Ty.ofArgs, Ty.args, *]

private theorem app_typed_inv {G : HORS} {ctx : List Ty} {t u : Tm} {τ : Ty}
    (h : G.typeOf ctx (t.app u) = some τ) :
    ∃ σ, G.typeOf ctx t = some (.arr σ τ) ∧ G.typeOf ctx u = some σ := by
  unfold HORS.typeOf at h
  split at h <;> simp_all

theorem spine_typed {G : HORS} {ctx : List Ty} (t : Tm) {τ : Ty}
    (h : G.typeOf ctx t = some τ) :
    ∃ tys, G.typeOf ctx t.spine.1 = some (Ty.ofArgs (tys ++ τ.args)) ∧
      t.spine.2.map (G.typeOf ctx) = tys.map some := by
  induction t generalizing τ with
  | var i | nt i | tm i => exact ⟨[], by simpa [ofArgs_args, Tm.spine] using h, rfl⟩
  | app t u ih _ =>
    obtain ⟨σ, ht, hu⟩ := app_typed_inv h
    obtain ⟨tys, hhead, hargs⟩ := ih ht
    exact ⟨tys ++ [σ], by simpa [Tm.spine, Ty.args] using hhead,
      by simp [Tm.spine, hargs, hu]⟩

theorem subst_typed {G : HORS} {ctx : List Ty} {args : List Tm}
    (htys : args.map (G.typeOf []) = ctx.map some) (t : Tm) {τ : Ty}
    (h : G.typeOf ctx t = some τ) : G.typeOf [] (t.subst args) = some τ := by
  induction t generalizing τ with
  | var i =>
    have hh := congrArg (fun l : List (Option Ty) => l[i]?) htys
    change ctx[i]? = some τ at h
    simp only [List.getElem?_map, h, Option.map_some] at hh
    cases ha : args[i]? with
    | none => simp [ha] at hh
    | some u => simpa [Tm.subst, List.getD_eq_getElem?_getD, ha] using Option.some.inj (by simpa [ha] using hh : some (G.typeOf [] u) = some (some τ))
  | nt i | tm i => exact h
  | app t u ih₁ ih₂ =>
    obtain ⟨σ, ht, hu⟩ := app_typed_inv h
    simp [Tm.subst, HORS.typeOf, ih₁ ht, ih₂ hu]

theorem step_typed {G : HORS} (hG : G.Valid) {t u : Tm}
    (ht : G.typeOf [] t = some .o) (hs : G.HeadStep t u) : G.typeOf [] u = some .o := by
  obtain ⟨tys, hhead, hargs⟩ := spine_typed t ht
  unfold HORS.HeadStep HORS.headStep at hs
  split at hs <;> try contradiction
  rename_i F args sp
  simp only [sp, HORS.typeOf, Ty.args, List.append_nil] at hhead
  simp only [sp] at hargs
  rw [hhead] at hs
  cases hr : G.rules[F]? with
  | none => simp [hr] at hs
  | some body =>
    simp only [hr, args_ofArgs] at hs
    split at hs <;> try contradiction
    obtain rfl := Option.some.inj hs
    apply subst_typed hargs
    have hi : F < G.nts.length := by simpa using (Option.isSome_iff_exists.mpr ⟨_, hhead⟩)
    simp only [HORS.Valid, HORS.valid, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hG
    simpa [HORS.ruleOK, hhead, hr, args_ofArgs] using hG.2 F hi

theorem headConv_typed {G : HORS} (hG : G.Valid) {t : Tm} (ht : G.typeOf [] t = some .o)
    {c : ℕ} {us : List Tm} (hc : G.HeadConv t c us) :
    G.alphabet[c]? = some us.length ∧ ∀ u ∈ us, G.typeOf [] u = some .o := by
  obtain ⟨v, hv, hsp⟩ := hc
  have htv : G.typeOf [] v = some .o := by
    clear hsp
    induction hv with
    | refl => exact ht
    | tail _ hs ih => exact step_typed hG ih hs
  obtain ⟨tys, hh, hu⟩ := spine_typed v htv
  simp only [hsp, HORS.typeOf, Ty.args, List.append_nil] at hh
  simp only [hsp] at hu
  cases he : G.alphabet[c]? with
  | none => simp [he] at hh
  | some r =>
    simp only [he, Option.map_some, Option.some.injEq] at hh
    have ha := congrArg Ty.args hh
    simp only [termTy, args_ofArgs] at ha
    subst tys
    have len := congrArg List.length hu
    simp only [List.length_map, List.length_replicate] at len
    refine ⟨by rw [len], fun u hm => ?_⟩
    have mem : G.typeOf [] u ∈ us.map (G.typeOf []) := List.mem_map_of_mem hm
    rw [hu] at mem
    simpa using (List.eq_of_mem_replicate (by simpa only [List.map_replicate] using mem))

namespace FiniteModel

def Below (σ : Ty) (x y : SVal) := leT σ x y = true
def Member (σ : Ty) (x : SVal) := x ∈ enum σ

theorem below_tabs (σ τ : Ty) (s t : List SVal) :
    Below (.arr σ τ) (.tab s) (.tab t) ↔ List.Forall₂ (Below τ) s t := by
  rw [List.forall₂_iff_zip]
  simp [Below,leT,List.all_eq_true,Prod.forall]

theorem below_antisymm (σ : Ty) {x y : SVal} (h : Below σ x y) (k : Below σ y x) : x = y := by
  induction σ generalizing x y with
  | o => cases x <;> cases y <;> simp_all [Below,leT]; rename_i x y; cases x <;> cases y <;> simp_all
  | arr σ τ _ ih =>
    cases x <;> cases y <;> try contradiction
    rename_i s t
    rw [below_tabs,List.forall₂_iff_get] at h k
    apply congrArg SVal.tab
    apply List.ext_get h.1
    intro i hi hj
    exact ih (h.2 i hi hj) (k.2 i hj hi)

theorem below_trans (σ : Ty) {x y z : SVal} (h : Below σ x y) (k : Below σ y z) : Below σ x z := by
  induction σ generalizing x y z with
  | o => cases x <;> cases y <;> cases z <;> try contradiction
         rename_i a b c; cases a <;> cases b <;> cases c <;> simp_all [Below,leT]
  | arr σ τ _ ih =>
    cases x <;> cases y <;> cases z <;> try contradiction
    rw [below_tabs,List.forall₂_iff_get] at h k ⊢
    refine ⟨h.1.trans k.1, fun i hi hj => ?_⟩
    have hm := h.1 ▸ hi
    exact ih (h.2 i hi hm) (k.2 i hm hj)

theorem mem_tuples {α : Type} (k : ℕ) (xs : List α) (ys : List α) :
    ys ∈ tuples k xs ↔ ys.length = k ∧ ∀ x ∈ ys, x ∈ xs := by
  induction k generalizing ys with
  | zero => cases ys <;> simp [tuples]
  | succ k ih =>
    cases ys with
    | nil => simp [tuples]
    | cons y ys =>
      simp [tuples,ih,and_assoc,and_left_comm,and_comm]

def TableOK (σ τ : Ty) (l : List SVal) : Prop :=
  l.length = (enum σ).length ∧ (∀ v ∈ l, Member τ v) ∧
    ∀ i < (enum σ).length, ∀ j < (enum σ).length,
      Below σ ((enum σ).getD i default) ((enum σ).getD j default) →
        Below τ (l.getD i default) (l.getD j default)

theorem mem_tab (σ τ : Ty) (l : List SVal) : Member (.arr σ τ) (.tab l) ↔ TableOK σ τ l := by
  have bit (a b : Bool) : (a = false ∨ b = true) ↔ (a = true → b = true) := by cases a <;> simp
  simp [Member,enum,TableOK,mem_tuples,Below,List.all_eq_true, Bool.or_eq_true, and_assoc,bit]

theorem below_refl (σ : Ty) {v : SVal} (hv : Member σ v) : Below σ v v := by
  induction σ generalizing v with
  | o =>
    simp [Member,enum] at hv
    rcases hv with rfl | rfl <;> rfl
  | arr σ τ _ ih =>
    cases v with
    | bit b => simp [Member,enum] at hv
    | tab l =>
      obtain ⟨_,mem,_⟩ := (mem_tab _ _ _).mp hv
      apply (below_tabs _ _ _ _).mpr
      apply List.forall₂_iff_get.mpr
      exact ⟨rfl, fun i h _ => ih (mem _ (List.get_mem _ _))⟩

def index (σ : Ty) (x : SVal) : ℕ :=
  (enum σ).findIdx fun y => leT σ x y && leT σ y x

theorem index_lt {σ : Ty} {x : SVal} (hx : Member σ x) : index σ x < (enum σ).length :=
  List.findIdx_lt_length_of_exists ⟨x,hx,by simp only [Bool.and_self]; exact below_refl σ hx⟩

theorem at_index {σ : Ty} {x : SVal} (hx : Member σ x) : (enum σ).getD (index σ x) default = x := by
  have ok := @List.findIdx_getElem _ (fun y => leT σ x y && leT σ y x) (enum σ) (index_lt hx)
  simp only [Bool.and_eq_true] at ok
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (index_lt hx), Option.getD_some]
  exact below_antisymm σ ok.2 ok.1

theorem mem_getD {σ : Ty} {i : ℕ} (h : i < (enum σ).length) : Member σ ((enum σ).getD i default) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]
  exact List.getElem_mem h

def tabulate (σ : Ty) (f : SVal → SVal) : SVal := .tab ((enum σ).map f)

private theorem map_get {l : List SVal} (f : SVal → SVal) (i : ℕ) (hi : i < l.length) :
    (l.map f).getD i default = f (l.getD i default) := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]

theorem tabulate_lookup {σ : Ty} (f : SVal → SVal) {x : SVal} (hx : Member σ x) :
    appT σ (tabulate σ f) x = f x := by
  change ((enum σ).map f).getD (index σ x) default = _
  rw [map_get _ _ (index_lt hx),at_index hx]

theorem tabulate_mem (σ τ : Ty) (f : SVal → SVal)
    (typed : ∀ x, Member σ x → Member τ (f x))
    (mono : ∀ x y, Member σ x → Member σ y → Below σ x y → Below τ (f x) (f y)) :
    Member (.arr σ τ) (tabulate σ f) := by
  apply (mem_tab _ _ _).mpr
  refine ⟨by simp, ?_, ?_⟩
  · intro v hv
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    exact typed x hx
  · intro i hi j hj ord
    rw [map_get _ _ hi,map_get _ _ hj]
    exact mono _ _ (mem_getD hi) (mem_getD hj) ord

theorem tabulate_below (σ τ : Ty) {f g : SVal → SVal} (h : ∀ x, Member σ x → Below τ (f x) (g x)) :
    Below (.arr σ τ) (tabulate σ f) (tabulate σ g) := by
  apply (below_tabs _ _ _ _).mpr
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp,fun i hi _ => ?_⟩
  simpa using h ((enum σ)[i]'(by simpa using hi)) (List.getElem_mem _)

theorem app_mem {σ τ : Ty} {f x : SVal} (hf : Member (.arr σ τ) f) (hx : Member σ x) :
    Member τ (appT σ f x) := by
  cases f with
  | bit b => simp [Member,enum] at hf
  | tab l =>
    obtain ⟨len,hm,_⟩ := (mem_tab _ _ _).mp hf
    have hi : index σ x < l.length := len ▸ index_lt hx
    change Member τ (l.getD (index σ x) default)
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
    exact hm _ (List.getElem_mem _)

theorem app_below {σ τ : Ty} {f g x y : SVal}
    (hf : Member (.arr σ τ) f) (hg : Member (.arr σ τ) g) (hx : Member σ x) (hy : Member σ y)
    (hfg : Below (.arr σ τ) f g) (hxy : Below σ x y) :
    Below τ (appT σ f x) (appT σ g y) := by
  cases f with
  | bit b => simp [Member,enum] at hf
  | tab l =>
    cases g with
    | bit b => simp [Member,enum] at hg
    | tab r =>
      obtain ⟨lr,_,mono⟩ := (mem_tab _ _ _).mp hg
      obtain ⟨ll,_⟩ := (mem_tab _ _ _).mp hf
      have h₁ := index_lt hx
      have h₂ := index_lt hy
      have z := mono _ h₁ _ h₂ (by simpa only [at_index hx,at_index hy] using hxy)
      apply below_trans τ _ z
      have ij := (List.forall₂_iff_get.mp ((below_tabs _ _ _ _).mp hfg)).2 (index σ x) (ll ▸ h₁) (lr ▸ h₁)
      change Below τ (l.getD (index σ x) default) (r.getD (index σ x) default)
      simpa only [List.get_eq_getElem, List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (ll ▸ h₁),
        List.getElem?_eq_getElem (lr ▸ h₁),Option.getD_some] using ij

theorem bot_mem (σ : Ty) : Member σ (botV σ) := by
  induction σ with
  | o => simp [Member,botV,enum]
  | arr σ τ _ h =>
    simpa [botV,tabulate] using tabulate_mem σ τ (fun _ => botV τ) (fun _ _ => h)
      (fun _ _ _ _ _ => below_refl τ h)

theorem one_mem (σ : Ty) : Member σ (oneV σ) := by
  induction σ with
  | o => simp [Member,oneV,enum]
  | arr σ τ _ h =>
    simpa [oneV,tabulate] using tabulate_mem σ τ (fun _ => oneV τ) (fun _ _ => h)
      (fun _ _ _ _ _ => below_refl τ h)

theorem bot_below (σ : Ty) {x : SVal} (hx : Member σ x) : Below σ (botV σ) x := by
  induction σ generalizing x with
  | o => simp [Member,enum] at hx; rcases hx with rfl | rfl <;> rfl
  | arr σ τ _ ih =>
    cases x with
    | bit b => simp [Member,enum] at hx
    | tab l =>
      obtain ⟨len,mem,_⟩ := (mem_tab _ _ _).mp hx
      apply (below_tabs _ _ _ _).mpr
      apply List.forall₂_iff_get.mpr
      refine ⟨by simp [len],fun i hi hj => ?_⟩
      simpa using ih (mem l[i] (List.getElem_mem hj))

end FiniteModel

namespace FiniteModel

def Related (σ : Ty) (v w : SVal) := Member σ v ∧ Member σ w ∧ Below σ v w

structure Matches {α β : Type} [Inhabited α] [Inhabited β] (rel : Ty → α → β → Prop)
    (ts : List Ty) (a : List α) (b : List β) : Prop where
  left : a.length = ts.length
  right : b.length = ts.length
  atIdx : ∀ i σ, ts[i]? = some σ → rel σ (a.getD i default) (b.getD i default)

theorem matches_nil {α β : Type} [Inhabited α] [Inhabited β] (r : Ty → α → β → Prop) :
    Matches r [] [] [] := ⟨rfl,rfl,by simp⟩

theorem matches_snoc {α β : Type} [Inhabited α] [Inhabited β] {r : Ty → α → β → Prop}
    {ts : List Ty} {a : List α} {b : List β} {σ x y}
    (h : Matches r ts a b) (hr : r σ x y) : Matches r (ts ++ [σ]) (a ++ [x]) (b ++ [y]) := by
  refine ⟨by simp [h.left],by simp [h.right],?_⟩
  intro i τ ht
  by_cases hi : i < ts.length
  · rw [List.getElem?_append_left hi] at ht
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left (h.left ▸ hi),
      List.getElem?_append_left (h.right ▸ hi)] using h.atIdx i τ ht
  · have j : ts.length ≤ i := by omega
    rw [List.getElem?_append_right j] at ht
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (h.left ▸ j),
      List.getElem?_append_right (h.right ▸ j),h.left,h.right]
    cases hh : i-ts.length with
    | zero => simp [hh] at ht; subst τ; exact hr
    | succ k => simp [hh] at ht

abbrev Env := Matches Related

theorem Env.refl_left {ts a b} (h : Env ts a b) : Env ts a a :=
  ⟨h.left,h.left,fun i σ ht => by
    have v := (h.atIdx i σ ht).1
    exact ⟨v,v,below_refl σ v⟩⟩

theorem Env.refl_right {ts a b} (h : Env ts a b) : Env ts b b :=
  ⟨h.right,h.right,fun i σ ht => by
    have v := (h.atIdx i σ ht).2.1
    exact ⟨v,v,below_refl σ v⟩⟩

private theorem inv_app {G : HORS} {ctx : List Ty} {t u : Tm} {τ : Ty}
    (h : G.typeOf ctx (.app t u) = some τ) :
    ∃ σ, G.typeOf ctx t = some (.arr σ τ) ∧ G.typeOf ctx u = some σ := by
  simp only [HORS.typeOf] at h
  split at h <;> simp_all

theorem den_related {G : HORS} {ctx : List Ty} {η₁ η₂ ρ₁ ρ₂ : List SVal}
    (he : Env G.nts η₁ η₂) (hr : Env ctx ρ₁ ρ₂) (t : Tm) {τ : Ty}
    (ht : G.typeOf ctx t = some τ) :
    Related τ (G.den ctx η₁ ρ₁ t) (G.den ctx η₂ ρ₂ t) := by
  induction t generalizing τ with
  | var i => exact hr.atIdx i τ ht
  | nt i => exact he.atIdx i τ ht
  | tm c =>
    cases hc : G.alphabet[c]? with
    | none => simp [HORS.typeOf,hc] at ht
    | some r =>
      obtain rfl := (by simpa [HORS.typeOf,hc] using ht : termTy r = τ)
      simpa [HORS.den,hc] using (show Related (termTy r) (oneV (termTy r)) (oneV (termTy r)) from
        ⟨one_mem _,one_mem _,below_refl _ (one_mem _)⟩)
  | app t u it iu =>
    obtain ⟨σ,ht,hu⟩ := inv_app ht
    obtain ⟨l,r,lr⟩ := it ht
    obtain ⟨a,b,ab⟩ := iu hu
    simp only [HORS.den,hu]
    exact ⟨app_mem l a,app_mem r b,app_below l r a b lr ab⟩

theorem rule_related {G : HORS} {ctx : List Ty} {η₁ η₂ : List SVal} {body : Tm}
    (ht : G.typeOf ctx body = some .o) (he : Env G.nts η₁ η₂)
    (τ : Ty) (pre : List Ty) (hctx : ctx = pre ++ τ.args) {ρ₁ ρ₂ : List SVal}
    (hr : Env pre ρ₁ ρ₂) :
    Related τ (G.ruleTab ctx η₁ body τ ρ₁) (G.ruleTab ctx η₂ body τ ρ₂) := by
  induction τ generalizing pre η₁ η₂ ρ₁ ρ₂ with
  | o =>
    simp only [Ty.args,List.append_nil] at hctx
    subst ctx
    exact den_related he hr body ht
  | arr σ τ _ ih =>
    let left (x : SVal) := G.ruleTab ctx η₁ body τ (ρ₁ ++ [x])
    let right (x : SVal) := G.ruleTab ctx η₂ body τ (ρ₂ ++ [x])
    have ctx' : ctx = (pre ++ [σ]) ++ τ.args := by simpa [List.append_assoc,Ty.args] using hctx
    have cross {α β a b : List SVal} (e : Env G.nts α β) (r : Env pre a b) {x y : SVal} (xy : Related σ x y) :
        Related τ (G.ruleTab ctx α body τ (a ++ [x])) (G.ruleTab ctx β body τ (b ++ [y])) :=
      ih e _ ctx' (matches_snoc r xy)
    have self (x : SVal) (vx : Member σ x) : Related σ x x := ⟨vx,vx,below_refl σ vx⟩
    change Related (.arr σ τ) (tabulate σ left) (tabulate σ right)
    exact ⟨tabulate_mem σ τ left (fun x vx => (cross he hr (self x vx)).1)
      (fun _ _ vx vy xy => (cross he.refl_left hr.refl_left ⟨vx,vy,xy⟩).2.2),
      tabulate_mem σ τ right (fun x vx => (cross he hr (self x vx)).2.1)
      (fun _ _ vx vy xy => (cross he.refl_right hr.refl_right ⟨vx,vy,xy⟩).2.2),
      tabulate_below σ τ (fun x vx => (cross he hr (self x vx)).2.2)⟩

theorem rule_type {G : HORS} (v : G.Valid) (i : ℕ) (σ : Ty) (hi : G.nts[i]? = some σ) :
    G.typeOf σ.args (G.rules.getD i (.tm 0)) = some .o := by
  obtain ⟨hlt,_⟩ := List.getElem?_eq_some_iff.mp hi
  simp only [HORS.Valid,HORS.valid,Bool.and_eq_true,List.all_eq_true] at v
  have ok := v.2 i (List.mem_range.mpr hlt)
  cases hb : G.rules[i]? with
  | none => simp [HORS.ruleOK,hi,hb] at ok
  | some b => simpa [HORS.ruleOK,hi,hb,List.getD_eq_getElem?_getD] using ok

theorem phi_related {G : HORS} (v : G.Valid) {a b : List SVal} (h : Env G.nts a b) :
    Env G.nts (G.Phi a) (G.Phi b) := by
  refine ⟨by simp [HORS.Phi],by simp [HORS.Phi],?_⟩
  intro i σ hi
  obtain ⟨lt,eq⟩ := List.getElem?_eq_some_iff.mp hi
  have tab := rule_related (rule_type v i σ hi) h σ [] (by simp) (matches_nil Related)
  simpa [HORS.Phi,List.getD_eq_getElem?_getD,lt,hi,eq] using tab

theorem env_trans {ts a b c} (h : Env ts a b) (k : Env ts b c) : Env ts a c := by
  refine ⟨h.left,k.right,fun i σ hi => ?_⟩
  obtain ⟨va,_,le₁⟩ := h.atIdx i σ hi
  obtain ⟨_,vc,le₂⟩ := k.atIdx i σ hi
  exact ⟨va,vc,below_trans σ le₁ le₂⟩

theorem env_antisymm {ts a b} (h : Env ts a b) (k : Env ts b a) : a = b := by
  apply List.ext_get (h.left.trans h.right.symm)
  intro i ha hb
  have ht := h.left ▸ ha
  have hi := List.getElem?_eq_getElem ht
  have e := below_antisymm _ (h.atIdx i _ hi).2.2 (k.atIdx i _ hi).2.2
  simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ha,List.getElem?_eq_getElem hb] using e

theorem initial_related (G : HORS) : Env G.nts G.eta0 G.eta0 := by
  refine ⟨by simp [HORS.eta0],by simp [HORS.eta0],fun i σ hi => ?_⟩
  simp [HORS.eta0,List.getD_eq_getElem?_getD,hi,Related,bot_mem,bot_below]

theorem initial_le {G : HORS} {a : List SVal} (h : Env G.nts a a) : Env G.nts G.eta0 a := by
  refine ⟨by simp [HORS.eta0],h.left,fun i σ hi => ?_⟩
  have hv := (h.atIdx i σ hi).1
  simpa [HORS.eta0,List.getD_eq_getElem?_getD,hi] using
    (show Related σ (botV σ) (a.getD i default) from ⟨bot_mem σ,hv,bot_below σ hv⟩)

def envs : List Ty → List (List SVal)
  | [] => [[]]
  | σ :: ts => (enum σ).flatMap fun x => (envs ts).map (x :: ·)

theorem envs_length (ts : List Ty) : (envs ts).length = (ts.map fun τ => (enum τ).length).prod := by
  induction ts with
  | nil => rfl
  | cons σ ts ih =>
    simp [envs, List.length_flatMap,ih]

theorem env_mem {ts e} (h : Env ts e e) : e ∈ envs ts := by
  induction ts generalizing e with
  | nil => have z := h.left; simp at z; simp [z,envs]
  | cons σ ts ih =>
    cases e with
    | nil => have z := h.left; simp at z
    | cons a e =>
      have head := (h.atIdx 0 σ (by simp)).1
      have tail : Env ts e e :=
        ⟨Nat.succ.inj h.left,Nat.succ.inj h.right,fun i τ hi => h.atIdx (i+1) τ hi⟩
      exact List.mem_flatMap.mpr ⟨a,head,List.mem_map.mpr ⟨e,ih tail,rfl⟩⟩

def stage (G : HORS) (n : ℕ) := G.Phi^[n] G.eta0

theorem stage_next (G : HORS) (n : ℕ) : stage G (n+1) = G.Phi (stage G n) := Function.iterate_succ_apply' _ _ _

theorem stage_related {G : HORS} (v : G.Valid) (n : ℕ) : Env G.nts (stage G n) (stage G (n+1)) := by
  induction n with
  | zero => exact initial_le (phi_related v (initial_related G))
  | succ n ih => simpa only [←stage_next] using phi_related v ih

theorem stage_mono {G : HORS} (v : G.Valid) {i j : ℕ} (h : i ≤ j) :
    Env G.nts (stage G i) (stage G j) := by
  induction h with
  | refl => exact (stage_related v i).refl_left
  | step h ih => exact env_trans ih (stage_related v _)

theorem stage_fixed {G : HORS} (v : G.Valid) : G.Phi G.etaStar = G.etaStar := by
  let B := G.envCard
  change G.Phi (stage G B) = stage G B
  by_contra bad
  have strict (i j : ℕ) (hi : i < j) (hj : j ≤ B) : stage G i ≠ stage G j := by
    intro eq
    have rev : Env G.nts (stage G (i+1)) (stage G i) := eq ▸ stage_mono v (show i+1 ≤ j by omega)
    have fix := (stage_next G i).symm.trans (env_antisymm rev (stage_related v i))
    have later (n : ℕ) : stage G (i+n) = stage G i := by
      induction n with
      | zero => rfl
      | succ n ih => rw [←Nat.add_assoc,stage_next,ih,fix]
    have atB := later (B-i)
    rw [show i+(B-i)=B by omega] at atB
    exact bad (by rw [atB,fix])
  let xs := (List.range (B+1)).map (stage G)
  have nodup : xs.Nodup := by
    apply List.Nodup.map_on _ List.nodup_range
    intro i hi j hj eq
    simp only [List.mem_range] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact (strict i j h (by omega) eq).elim
    · exact h
    · exact (strict j i h (by omega) eq.symm).elim
  have sub : xs ⊆ envs G.nts := by
    intro e he
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
    exact env_mem (stage_related v i).refl_left
  have count := nodup.length_le_of_subset sub
  simp [xs,envs_length,B,HORS.envCard] at count


local instance : Inhabited Tm := ⟨.tm 0⟩

def Supports (G : HORS) : Ty → SVal → Tm → Prop
  | .o, v, t => v = .bit true → ∃ c us, G.HeadConv t c us
  | .arr σ τ, f, t => ∀ x u, Member σ x → Supports G σ x u → Supports G τ (appT σ f x) (.app t u)

private theorem supports_bot (G : HORS) (τ : Ty) (t : Tm) : Supports G τ (botV τ) t := by
  induction τ generalizing t with
  | o => simp [Supports,botV]
  | arr σ τ _ ih =>
    intro x u hx _
    have eq := tabulate_lookup (fun _ => botV τ) hx
    simp [tabulate] at eq
    simpa only [botV,eq] using ih (.app t u)

private theorem supports_terminal_aux (G : HORS) (τ : Ty) {t : Tm} {c : ℕ} {us : List Tm}
    (sp : t.spine = (.tm c,us)) : Supports G τ (oneV τ) t := by
  induction τ generalizing t us with
  | o => exact fun _ => ⟨c,us,t,.refl,sp⟩
  | arr σ τ _ ih =>
    intro x u hx _
    have eq := tabulate_lookup (fun _ => oneV τ) hx
    simp [tabulate] at eq
    simp only [oneV,eq]
    exact ih (show (Tm.app t u).spine = (.tm c,us ++ [u]) by simp [Tm.spine,sp])

private def realized (G : HORS) (τ : Ty) (v : SVal) (t : Tm) :=
  Member τ v ∧ Supports G τ v t

private theorem real_env {G : HORS} {ctx ρ args} (h : Matches (realized G) ctx ρ args) : Env ctx ρ ρ :=
  ⟨h.left,h.left,fun i σ hi => by
    have hv := (h.atIdx i σ hi).1
    exact ⟨hv,hv,below_refl _ hv⟩⟩

private theorem subst_supported {G : HORS} {ctx η ρ args}
    (ge : Env G.nts η η) (le' : Matches (realized G) ctx ρ args)
    (global : ∀ j τ, G.nts[j]? = some τ → Supports G τ (η.getD j default) (.nt j))
    (t : Tm) {τ : Ty} (ht : G.typeOf ctx t = some τ) :
    Supports G τ (G.den ctx η ρ t) (t.subst args) := by
  induction t generalizing τ with
  | var i =>
    have hi : i < args.length := le'.right ▸ (List.getElem?_eq_some_iff.mp ht).choose
    simpa [Tm.subst,HORS.den,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi] using (le'.atIdx i τ ht).2
  | nt i => exact global i τ ht
  | tm c =>
    cases hc : G.alphabet[c]? with
    | none => simp [HORS.typeOf,hc] at ht
    | some r =>
      obtain rfl := (by simpa [HORS.typeOf,hc] using ht : termTy r = τ)
      simpa [Tm.subst,HORS.den,hc] using supports_terminal_aux G (termTy r) (t := .tm c) (us := []) rfl
  | app t u it iu =>
    obtain ⟨σ,ht,hu⟩ := (by unfold HORS.typeOf at ht; split at ht <;> simp_all :
      ∃ σ, G.typeOf ctx t = some (.arr σ τ) ∧ G.typeOf ctx u = some σ)
    have member := (den_related ge (real_env le') u hu).1
    simpa [HORS.den,hu,Tm.subst] using (it ht _ _ member (iu hu))

theorem spine_apps {h : Tm} (l : List Tm) :
    (Tm.apps h l).spine = (h.spine.1,h.spine.2 ++ l) := by
  induction l generalizing h with
  | nil => simp [Tm.apps]
  | cons t l ih => simpa [Tm.apps,List.foldl_cons,Tm.spine,List.append_assoc] using ih (h := h.app t)

theorem apps_snoc (h : Tm) (a : List Tm) (t : Tm) : Tm.apps h (a ++ [t]) = .app (Tm.apps h a) t := by
  simp [Tm.apps,List.foldl_append]

private theorem rule_support {G : HORS} {F : ℕ} {τF : Ty} {η : List SVal} {body : Tm}
    (hn : G.nts[F]? = some τF) (hb : G.rules[F]? = some body) (ht : G.typeOf τF.args body = some .o)
    (ge : Env G.nts η η) (global : ∀ j τ, G.nts[j]? = some τ → Supports G τ (η.getD j default) (.nt j))
    (τ : Ty) (pre : List Ty) (hctx : τF.args = pre ++ τ.args) {ρ : List SVal} {args : List Tm}
    (local' : Matches (realized G) pre ρ args) :
    Supports G τ (G.ruleTab τF.args η body τ ρ) (Tm.apps (.nt F) args) := by
  induction τ generalizing pre args ρ with
  | o =>
    simp only [Ty.args,List.append_nil] at hctx
    subst pre
    have step : G.HeadStep (Tm.apps (.nt F) args) (body.subst args) := by
      simp [HORS.HeadStep,HORS.headStep,spine_apps,Tm.spine,hn,hb,local'.right]
    intro positive
    obtain ⟨c,us,t,run,head⟩ := subst_supported ge local' global body ht positive
    exact ⟨c,us,t,run.head step,head⟩
  | arr σ τ _ ih =>
    intro x u hx hu
    change Supports G τ (appT σ (tabulate σ fun v => G.ruleTab τF.args η body τ (ρ ++ [v])) x) _
    rw [tabulate_lookup _ hx,←apps_snoc]
    exact ih _ (by simpa [Ty.args,List.append_assoc] using hctx) (matches_snoc local' ⟨hx,hu⟩)

private theorem stage_support (G : HORS) (vg : G.Valid) (n : ℕ) : ∀ F τ, G.nts[F]? = some τ →
    Supports G τ ((stage G n).getD F default) (.nt F) := by
  induction n with
  | zero =>
    intro F τ ht
    simpa [stage,HORS.eta0,List.getD_eq_getElem?_getD,ht] using supports_bot G τ (.nt F)
  | succ n ih =>
    intro F τ ht
    obtain ⟨hlt,hval⟩ := List.getElem?_eq_some_iff.mp ht
    have len : G.rules.length = G.nts.length := by
      simp only [HORS.Valid,HORS.valid,Bool.and_eq_true,beq_iff_eq] at vg
      exact vg.1.1
    have hr := List.getElem?_eq_getElem (len ▸ hlt)
    have bodyTy := rule_type vg F τ ht
    have b := rule_support ht hr (by simpa only [List.getD_eq_getElem?_getD,hr,Option.getD_some] using bodyTy)
      (stage_related vg n).refl_left ih τ [] (by simp) (matches_nil _)
    simpa [stage_next,HORS.Phi,List.getD_eq_getElem?_getD,hlt,hval,ht,hr,Tm.apps] using b

theorem positive_implies_converges (G : HORS) (vg : G.Valid) (t : Tm) (ht : G.typeOf [] t = some .o)
    (h : G.den [] G.etaStar [] t = .bit true) : ∃ c us, G.HeadConv t c us := by
  have sp := subst_supported (stage_related vg G.envCard).refl_left (matches_nil _)
    (stage_support G vg G.envCard) t ht h
  have e : t.subst [] = t := by clear sp h ht; induction t <;> simp [Tm.subst,List.getD_eq_getElem?_getD, *]
  exact e ▸ sp



private def applyList (G : HORS) (η : List SVal) (v : SVal) : List Tm → SVal
  | [] => v
  | u :: us => applyList G η (appT ((G.typeOf [] u).getD .o) v (G.den [] η [] u)) us

private theorem den_apps (G : HORS) (η : List SVal) (h : Tm) (us : List Tm)
    (all' : ∀ u ∈ us, ∃ σ, G.typeOf [] u = some σ) :
    G.den [] η [] (Tm.apps h us) = applyList G η (G.den [] η [] h) us := by
  induction us generalizing h with
  | nil => rfl
  | cons u us ih =>
    obtain ⟨σ,hu⟩ := all' u (by simp)
    change G.den [] η [] (Tm.apps (.app h u) us) = _
    rw [ih _ (fun u hu => all' u (.tail _ hu))]
    simp [applyList,HORS.den,hu]

private theorem reconstruct (t : Tm) : Tm.apps t.spine.1 t.spine.2 = t := by
  induction t with
  | var | nt | tm => rfl
  | app t u ih _ => simp [Tm.spine,apps_snoc,ih]

private theorem components_typed {G : HORS} {tys : List Ty} {us : List Tm}
    (h : us.map (G.typeOf []) = tys.map some) : ∀ u ∈ us, ∃ σ, G.typeOf [] u = some σ := by
  intro u hu
  obtain ⟨σ,_,hs⟩ := List.mem_map.mp (h ▸ List.mem_map_of_mem (f := G.typeOf []) hu)
  exact ⟨σ,hs.symm⟩

private theorem den_subst {G : HORS} {η : List SVal} {ctx : List Ty} {args : List Tm}
    (ha : args.map (G.typeOf []) = ctx.map some) (t : Tm) {τ : Ty} (ht : G.typeOf ctx t = some τ) :
    G.den [] η [] (t.subst args) = G.den ctx η (args.map (G.den [] η [])) t := by
  induction t generalizing τ with
  | nt | tm => rfl
  | var i =>
    have hs := congrArg (fun l => l[i]?) ha
    change ctx[i]? = some τ at ht
    simp only [List.getElem?_map,ht] at hs
    cases eq : args[i]? with
    | none => simp [eq,ht] at hs
    | some u => simp [Tm.subst,HORS.den,List.getD_eq_getElem?_getD,eq]
  | app t u it iu =>
    obtain ⟨σ,ht',hu⟩ := (by unfold HORS.typeOf at ht; split at ht <;> simp_all :
      ∃ σ, G.typeOf ctx t = some (.arr σ τ) ∧ G.typeOf ctx u = some σ)
    simp [Tm.subst,HORS.den,subst_typed ha _ hu,hu,it ht',iu hu]

private theorem apply_rule (G : HORS) (η : List SVal) (ge : Env G.nts η η) (ctx : List Ty) (body : Tm)
    (τ : Ty) (ρ : List SVal) (us : List Tm) (ha : us.map (G.typeOf []) = τ.args.map some) :
    applyList G η (G.ruleTab ctx η body τ ρ) us =
      G.den ctx η (ρ ++ us.map (G.den [] η [])) body := by
  induction τ generalizing ρ us with
  | o =>
    have e : us = [] := by simpa [Ty.args] using ha
    subst us; simp [applyList,HORS.ruleTab]
  | arr σ τ _ ih =>
    cases us with
    | nil => simp [Ty.args] at ha
    | cons u us =>
      obtain ⟨hu,rest⟩ := (by simpa [Ty.args] using ha : G.typeOf [] u = some σ ∧ _)
      have hv := (den_related ge (matches_nil _) u hu).1
      change applyList G η (appT ((G.typeOf [] u).getD .o) (tabulate σ _) (G.den [] η [] u)) us = _
      simp only [hu,Option.getD_some,tabulate_lookup _ hv]
      simpa [List.append_assoc] using ih (ρ ++ [G.den [] η [] u]) us rest

private theorem apply_one (G : HORS) (η : List SVal) (ge : Env G.nts η η)
    (τ : Ty) (us : List Tm) (ha : us.map (G.typeOf []) = τ.args.map some) :
    applyList G η (oneV τ) us = .bit true := by
  induction τ generalizing us with
  | o =>
    have e : us = [] := by simpa [Ty.args] using ha
    subst us; rfl
  | arr σ τ _ ih =>
    cases us with
    | nil => simp [Ty.args] at ha
    | cons u us =>
      obtain ⟨hu,rest⟩ := (by simpa [Ty.args] using ha : G.typeOf [] u = some σ ∧ _)
      have hv := (den_related ge (matches_nil _) u hu).1
      have eq := tabulate_lookup (fun _ => oneV τ) hv
      simp [tabulate] at eq
      simpa [applyList,oneV,hu,eq] using ih us rest

private theorem head_preserves {G : HORS} (v : G.Valid) {t u : Tm} (ht : G.typeOf [] t = some .o)
    (step : G.HeadStep t u) : G.den [] G.etaStar [] t = G.den [] G.etaStar [] u := by
  have ge := (stage_related v G.envCard).refl_left
  obtain ⟨tys,hh,ha⟩ := spine_typed t ht
  unfold HORS.HeadStep HORS.headStep at step
  split at step <;> try contradiction
  rename_i F us sp
  simp only [sp,HORS.typeOf,Ty.args,List.append_nil] at hh
  simp only [sp] at ha
  have r := reconstruct t
  rw [sp] at r
  rw [←r,den_apps _ _ _ _ (components_typed ha)]
  rw [hh] at step
  cases hb : G.rules[F]? with
  | none => simp [hb] at step
  | some body =>
    simp only [hb,args_ofArgs] at step
    split at step <;> try contradiction
    obtain rfl := Option.some.inj step
    have argTy : us.map (G.typeOf []) = (Ty.ofArgs tys).args.map some := by simpa [args_ofArgs] using ha
    have bty := rule_type v F (Ty.ofArgs tys) hh
    simp only [List.getD_eq_getElem?_getD,hb,Option.getD_some] at bty
    have hfix := congrArg (fun s : List SVal => s.getD F default) (stage_fixed v)
    obtain ⟨hi,eq⟩ := List.getElem?_eq_some_iff.mp hh
    have entry : G.etaStar.getD F default = G.ruleTab (Ty.ofArgs tys).args G.etaStar body (Ty.ofArgs tys) [] := by
      simpa [HORS.Phi,List.getD_eq_getElem?_getD,hh,hb,hi,eq] using hfix.symm
    simp only [HORS.den,entry,apply_rule G G.etaStar ge _ _ _ _ _ argTy,List.nil_append,den_subst argTy body bty]

private theorem terminal_value {G : HORS} (v : G.Valid) {t : Tm} (ht : G.typeOf [] t = some .o)
    {c us} (sp : t.spine = (.tm c,us)) : G.den [] G.etaStar [] t = .bit true := by
  obtain ⟨tys,hh,ha⟩ := spine_typed t ht
  simp only [sp,HORS.typeOf,Ty.args,List.append_nil] at hh
  simp only [sp] at ha
  cases hc : G.alphabet[c]? with
  | none => simp [hc] at hh
  | some ar =>
    obtain eq : termTy ar = Ty.ofArgs tys := by simpa [hc] using hh
    have sy : us.map (G.typeOf []) = (termTy ar).args.map some := by simpa [eq,args_ofArgs] using ha
    have r := reconstruct t
    rw [sp] at r
    rw [←r,den_apps _ _ _ _ (components_typed ha)]
    simpa [HORS.den,hc] using apply_one G G.etaStar (stage_related v G.envCard).refl_left (termTy ar) us sy

theorem convergence_positive (G : HORS) (vg : G.Valid) (t : Tm) (ht : G.typeOf [] t = some .o)
    (h : ∃ c us, G.HeadConv t c us) : G.den [] G.etaStar [] t = .bit true := by
  obtain ⟨c,us,u,reach,head⟩ := h
  have run : G.typeOf [] u = some .o ∧ G.den [] G.etaStar [] t = G.den [] G.etaStar [] u := by
    clear head
    induction reach with
    | refl => exact ⟨ht,rfl⟩
    | tail _ hs ih => exact ⟨step_typed vg ih.1 hs,ih.2.trans (head_preserves vg ih.1 hs)⟩
  exact run.2.trans (terminal_value vg run.1 head)


end FiniteModel

private theorem proved_here (G : HORS) (vg : G.Valid) (t : Tm) (ht : G.typeOf [] t = some .o)
    (h : ∃ c us, G.HeadConv t c us) : G.den [] G.etaStar [] t = .bit true := by
  exact FiniteModel.convergence_positive G vg t ht h


end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution (G : HORS) (vg : G.Valid) (t : Tm) (ht : G.typeOf [] t = some .o)
    (h : ∃ c us, G.HeadConv t c us) : G.den [] G.etaStar [] t = .bit true := proved_here G vg t ht h
