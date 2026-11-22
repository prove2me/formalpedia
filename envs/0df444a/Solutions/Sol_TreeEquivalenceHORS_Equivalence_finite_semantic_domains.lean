-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.finite_semantic_domains
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T19:15:24.293248+00:00
-- url     : https://prove2.me/submissions/0972e49a-e4e2-46f9-9345-8ad523fb7b02

import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics

namespace TreeEquivalenceHORS.Equivalence

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

/-- The enumerated finite domains have least elements, and table application is monotone in both arguments. -/

private theorem proved_here :
    (∀ σ : Ty, botV σ ∈ enum σ ∧ (∀ x ∈ enum σ, leT σ (botV σ) x = true)) ∧
    (∀ (σ τ : Ty) (f x : SVal), f ∈ enum (.arr σ τ) → x ∈ enum σ → appT σ f x ∈ enum τ) ∧
    ∀ (σ τ : Ty) (f g x y : SVal), f ∈ enum (.arr σ τ) → g ∈ enum (.arr σ τ) →
      x ∈ enum σ → y ∈ enum σ → leT (.arr σ τ) f g = true → leT σ x y = true →
      leT τ (appT σ f x) (appT σ g y) = true := by
  exact ⟨fun σ => ⟨FiniteModel.bot_mem σ,fun _ hx => FiniteModel.bot_below σ hx⟩,
    fun _ _ _ _ hf hx => FiniteModel.app_mem hf hx,fun _ _ _ _ _ _ => FiniteModel.app_below⟩

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution :
    (∀ σ : Ty, botV σ ∈ enum σ ∧ (∀ x ∈ enum σ, leT σ (botV σ) x = true)) ∧
    (∀ (σ τ : Ty) (f x : SVal), f ∈ enum (.arr σ τ) → x ∈ enum σ → appT σ f x ∈ enum τ) ∧
    ∀ (σ τ : Ty) (f g x y : SVal), f ∈ enum (.arr σ τ) → g ∈ enum (.arr σ τ) →
      x ∈ enum σ → y ∈ enum σ → leT (.arr σ τ) f g = true → leT σ x y = true →
      leT τ (appT σ f x) (appT σ g y) = true := proved_here
