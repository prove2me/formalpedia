-- Prove2me | solution 1 for OAI.VariableWL.general_hard
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T02:01:30.925504+00:00
-- url     : https://prove2.me/submissions/99a97445-d13a-4f06-b951-ff6fc12a892f

import Mathlib
import Definitions.Def_VariableWL
import Definitions.Def_OAIQ6Wl002

section
-- module Solutions.OAIQ6_WL.VariableWL_Affine
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.Blocks.valuationFintype _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.Markers

open scoped CharTwo

variable {V : Type uVariable5} {G : SimpleGraph V}

theorem walkSum_of_potential (ω : V → V → Bit) (s : V → Bit)
    (hs : ∀ u v, G.Adj u v → s u + s v = ω u v) {u v : V} (p : G.Walk u v) :
    walkSum ω p = s u + s v := by
  induction p with
  | nil => simp [walkSum]
  | @cons u v w h p ih =>
    rw [walkSum_cons, ih, ← hs u v h]
    simp [add_assoc]

end VariableWL.Markers

namespace VariableWL.Affine
open scoped CharTwo

theorem gauge_horizontal {d : ℕ} (x y h h' : Vec d) (s t δ : Bit)
    (hmark : s + t = δ) :
    (x + s • (h' + h)) + (y + t • (h' + h)) + δ • h' = x + y + δ • h := by
  ext i
  change x i + s * (h' i + h i) + (y i + t * (h' i + h i)) + δ * h' i =
    x i + y i + δ * h i
  rw [← hmark]
  have htwo : (2 : Bit) = 0 := by decide
  linear_combination (h' i * (s + t)) * htwo

theorem gauge_vertical {d e : ℕ} (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit)
    (x : Vec d) (y : Vec e) (h h' : Vec d) (j j' : Vec e) (s t : Bit)
    (hs : s = t) (hdiff : L (h' + h) = R (j' + j)) :
    L (x + s • (h' + h)) + R (y + t • (j' + j)) = L x + R y := by
  subst t
  simp only [map_add, map_smul, smul_eq_mul]
  have hd : L h' + L h = R j' + R j := by simpa using hdiff
  rw [hd]
  simp [add_comm, add_left_comm]

theorem shift_difference {d e : ℕ} (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit)
    (h h' : Vec d) (j j' : Vec e) (b : Bit)
    (hh : L h + R j = b) (hh' : L h' + R j' = b) :
    L (h' + h) = R (j' + j) := by
  simp only [map_add]
  have htwo : (2 : Bit) = 0 := by decide
  linear_combination hh' + hh - (R j' + R j - b) * htwo

end VariableWL.Affine

namespace VariableWL.ScalarImages

open scoped CharTwo

theorem zero_buffer_unique {B : Set Pair} (hB : B.Nonempty)
    (h₀ : Prod.fst '' B = {0}) (h₁ : Prod.snd '' B = {0}) : B = {(0, 0)} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  have hall : ∀ x ∈ B, x = (0, 0) := by
    intro x hx
    have hx₀ : x.1 ∈ ({0} : Set Bit) := h₀ ▸ Set.mem_image_of_mem Prod.fst hx
    have hx₁ : x.2 ∈ ({0} : Set Bit) := h₁ ▸ Set.mem_image_of_mem Prod.snd hx
    exact Prod.ext (Set.mem_singleton_iff.mp hx₀) (Set.mem_singleton_iff.mp hx₁)
  rcases hB with ⟨x, hx⟩
  exact ⟨hall x hx ▸ hx, hall⟩

theorem zero_propagates {B : Set Pair} {D : Set Bit} (hB : B.Nonempty)
    (h₀ : Prod.fst '' B = {0}) (h₁ : Prod.snd '' B = {0})
    (hD : sum '' B = D) : D = {0} := by
  rw [← hD, zero_buffer_unique hB h₀ h₁]
  simp [sum]

end VariableWL.ScalarImages

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Refinement
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL

private theorem map_univ_comp_equiv {A : Type uVariable1} {B : Type uVariable2} {C : Type uVariable3} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → C) :
    Finset.univ.val.map f = Finset.univ.val.map (fun a => f (e a)) := by
  rw [← Multiset.map_univ_val_equiv e, Multiset.map_map]
  rfl

theorem color_iso {G H : Graph} (e : G.graph ≃g H.graph) (k : ℕ) :
    ∀ s (v : Tuple G k), color H k s (e ∘ v) = color G k s v := by
  classical
  intro s
  induction s with
  | zero =>
    intro v
    funext i j
    simp [color, e.injective.eq_iff, e.map_rel_iff]
  | succ s ih =>
    intro v
    apply Prod.ext (ih v)
    change Finset.univ.val.map (fun z => fun i =>
      color H k s (Function.update (e ∘ v) i z)) =
      Finset.univ.val.map (fun z => fun i => color G k s (Function.update v i z))
    rw [map_univ_comp_equiv e.toEquiv]
    apply Multiset.map_congr rfl
    intro z _
    funext i
    simpa only [Function.comp_update, RelIso.coe_fn_toEquiv] using ih (Function.update v i z)

theorem histogram_iso {G H : Graph} (e : G.graph ≃g H.graph) (k s : ℕ) :
    histogram H k s = histogram G k s := by
  unfold histogram
  rw [map_univ_comp_equiv (tupleEquiv e k)]
  apply Multiset.map_congr rfl
  intro v _
  exact color_iso e k s v

theorem color_zero_eq_iff {G H : Graph} {k : ℕ} (v : Tuple G k) (w : Tuple H k) :
    color G k 0 v = color H k 0 w ↔
      (∀ i j, v i = v j ↔ w i = w j) ∧
      (∀ i j, G.graph.Adj (v i) (v j) ↔ H.graph.Adj (w i) (w j)) := by
  classical
  constructor
  · intro h
    have hi : ∀ i j, (v i = v j ↔ w i = w j) ∧
        (G.graph.Adj (v i) (v j) ↔ H.graph.Adj (w i) (w j)) := by
      intro i j
      have hc := congrFun (congrFun h i) j
      change (decide (v i = v j), decide (G.graph.Adj (v i) (v j))) =
        (decide (w i = w j), decide (H.graph.Adj (w i) (w j))) at hc
      simpa only [Prod.mk.injEq, decide_eq_decide] using hc
    exact ⟨fun i j => (hi i j).1, fun i j => (hi i j).2⟩
  · rintro ⟨he, ha⟩
    funext i j
    apply Prod.ext
    · exact decide_eq_decide.mpr (he i j)
    · exact decide_eq_decide.mpr (ha i j)

theorem exists_color_match {G H : Graph} {k s : ℕ}
    (h : histogram G k s = histogram H k s) (v : Tuple G k) :
    ∃ w : Tuple H k, color H k s w = color G k s v := by
  have hm : color G k s v ∈ histogram G k s :=
    Multiset.mem_map.mpr ⟨v, Finset.mem_univ_val v, rfl⟩
  rw [h] at hm
  rcases Multiset.mem_map.mp hm with ⟨w, _, hw⟩
  exact ⟨w, hw⟩

end VariableWL

namespace VariableWL

theorem color_factor_succ {G : Graph} {k s t : ℕ} (f : Color k s → Color k t)
    (hf : ∀ v : Tuple G k, color G k t v = f (color G k s v)) (v : Tuple G k) :
    color G k (t+1) v = liftColor f (color G k (s+1) v) := by
  apply Prod.ext (hf v)
  change Finset.univ.val.map (fun z => fun i => color G k t (Function.update v i z)) =
    (Finset.univ.val.map (fun z => fun i => color G k s (Function.update v i z))).map
      (fun a => f ∘ a)
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro z _
  funext i
  exact hf (Function.update v i z)

theorem tagColor_factor_succ {G H : Graph} {k s t : ℕ} (f : Color k s → Color k t)
    (hf : ∀ v, tagColor G H k t v = f (tagColor G H k s v)) (v : TaggedTuple G H k) :
    tagColor G H k (t+1) v = liftColor f (tagColor G H k (s+1) v) := by
  cases v with
  | inl v => exact color_factor_succ f (fun a => hf (.inl a)) v
  | inr v => exact color_factor_succ f (fun a => hf (.inr a)) v

theorem tagColor_eq_previous {G H : Graph} {k s : ℕ} {v w : TaggedTuple G H k}
    (h : tagColor G H k (s+1) v = tagColor G H k (s+1) w) :
    tagColor G H k s v = tagColor G H k s w := by
  have hp := congrArg Prod.fst h
  cases v <;> cases w <;> exact hp

private theorem samePairs_next_subset (G H : Graph) (k s : ℕ) :
    samePairs G H k (s+1) ⊆ samePairs G H k s := by
  classical
  intro p hp
  simp only [samePairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact tagColor_eq_previous hp

private theorem exists_nat_plateau (a : ℕ → ℕ) (hmono : ∀ n, a (n+1) ≤ a n) :
    ∃ n ≤ a 0, a (n+1) = a n := by
  by_contra! h
  have hstrict : ∀ n ≤ a 0, a (n+1) < a n := by
    intro n hn
    exact lt_of_le_of_ne (hmono n) (h n hn)
  have hbound : ∀ n ≤ a 0 + 1, a n + n ≤ a 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hstep := hstrict n (by omega)
      omega
  have := hbound (a 0 + 1) le_rfl
  omega

theorem exists_stable_round (G H : Graph) (k : ℕ) :
    ∃ s ≤ (G.order ^ k + H.order ^ k) ^ 2, StableAt G H k s := by
  classical
  obtain ⟨s, hs, heq⟩ := exists_nat_plateau
    (fun n => (samePairs G H k n).card)
    (fun n => Finset.card_le_card (samePairs_next_subset G H k n))
  have hsets : samePairs G H k (s+1) = samePairs G H k s :=
    Finset.eq_of_subset_of_card_le (samePairs_next_subset G H k s) heq.ge
  refine ⟨s, ?_, ?_⟩
  · refine hs.trans ?_
    calc
      (samePairs G H k 0).card ≤ Fintype.card (TaggedTuple G H k × TaggedTuple G H k) :=
        Finset.card_le_univ _
      _ = (G.order ^ k + H.order ^ k) ^ 2 := by
        simp [TaggedTuple, Tuple, pow_two]
  · intro v w hvw
    have hm : (v, w) ∈ samePairs G H k s := by
      simp [samePairs, hvw]
    rw [← hsets] at hm
    simpa only [samePairs, Finset.mem_filter, Finset.mem_univ, true_and] using hm

theorem stable_later_factor {G H : Graph} {k s : ℕ} (hs : StableAt G H k s) :
    ∀ t, ∃ f : Color k s → Color k (s+t),
      ∀ v, tagColor G H k (s+t) v = f (tagColor G H k s v) := by
  obtain ⟨f₀, hf₀⟩ := (Function.factorsThrough_iff (tagColor G H k (s+1))).mp hs
  have hbase : ∀ v, tagColor G H k (s+1) v = f₀ (tagColor G H k s v) :=
    fun v => congrFun hf₀ v
  intro t
  induction t with
  | zero => exact ⟨id, fun _ => rfl⟩
  | succ t ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨liftColor f ∘ f₀, ?_⟩
    intro v
    calc
      tagColor G H k (s+(t+1)) v = liftColor f (tagColor G H k (s+1) v) :=
        tagColor_factor_succ f hf v
      _ = (liftColor f ∘ f₀) (tagColor G H k s v) := by rw [hbase]; rfl

end VariableWL

namespace VariableWL

theorem exists_equiv_of_map_univ_eq {α : Type uVariable4} {β : Type uVariable5} {γ : Type uVariable6} [Fintype α] [Fintype β]
    (f : α → γ) (g : β → γ)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ e : α ≃ β, ∀ a, f a = g (e a) := by
  classical
  have hc (c : γ) : Fintype.card {a // f a = c} = Fintype.card {b // g b = c} := by
    have hh := congrArg (Multiset.count c) h
    simpa only [Multiset.count_map, ← Finset.filter_val, ← Finset.card_def,
      Fintype.card_subtype, eq_comm (a := c)] using hh
  let e (c : γ) : {a // f a = c} ≃ {b // g b = c} := Fintype.equivOfCardEq (hc c)
  exact ⟨Equiv.ofFiberEquiv e, fun a => (Equiv.ofFiberEquiv_map e a).symm⟩

theorem color_reindex (G : Graph) (k s : ℕ) (e : Equiv.Perm (Fin k)) (v : Tuple G k) :
    color G k s (v ∘ e) = permColor e s (color G k s v) := by
  classical
  induction s generalizing v with
  | zero => rfl
  | succ s ih =>
    change (color G k s (v ∘ e), _) = (permColor e s (color G k s v), _)
    apply Prod.ext (ih v)
    change (Finset.univ.val.map (fun z i => color G k s (Function.update (v ∘ e) i z))) =
      (Finset.univ.val.map (fun z i => color G k s (Function.update v i z))).map
        (fun p i => permColor e s (p (e i)))
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro z _
    funext i
    rw [← Function.update_comp_eq_of_injective v e.injective]
    exact ih _

theorem StableEq.reindex {G H : Graph} {k : ℕ} {v : Tuple G k} {w : Tuple H k}
    (h : StableEq v w) (e : Equiv.Perm (Fin k)) : StableEq (v ∘ e) (w ∘ e) := by
  intro s
  rw [color_reindex, color_reindex, h s]

theorem color_eq_previous {G H : Graph} {k s : ℕ} {v : Tuple G k} {w : Tuple H k}
    (h : color G k (s+1) v = color H k (s+1) w) :
    color G k s v = color H k s w := congrArg Prod.fst h

theorem color_eq_of_le {G H : Graph} {k s t : ℕ} {v : Tuple G k} {w : Tuple H k}
    (hle : s ≤ t) (h : color G k t v = color H k t w) :
    color G k s v = color H k s w := by
  induction t generalizing s with
  | zero => have : s = 0 := Nat.eq_zero_of_le_zero hle; subst s; exact h
  | succ t ih =>
    by_cases he : s = t+1
    · subst s; exact h
    · exact ih (by omega) (color_eq_previous h)

theorem stableEq_of_color_eq {G H : Graph} {k s : ℕ} (hs : StableAt G H k s)
    {v : Tuple G k} {w : Tuple H k} (h : color G k s v = color H k s w) :
    StableEq v w := by
  intro t
  by_cases ht : t ≤ s
  · exact color_eq_of_le ht h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_ge ht))
    obtain ⟨f, hf⟩ := stable_later_factor hs d
    exact (hf (.inl v)).trans ((congrArg f h).trans (hf (.inr w)).symm)

theorem StableEq.exists_bijection {G H : Graph} {k : ℕ}
    {v : Tuple G k} {w : Tuple H k} (h : StableEq v w) :
    ∃ e : Fin G.order ≃ Fin H.order, ∀ z i,
      StableEq (Function.update v i z) (Function.update w i (e z)) := by
  classical
  obtain ⟨s, _, hs⟩ := exists_stable_round G H k
  have hprof : Finset.univ.val.map (fun z i => color G k s (Function.update v i z)) =
      Finset.univ.val.map (fun z i => color H k s (Function.update w i z)) :=
    congrArg Prod.snd (h (s+1))
  obtain ⟨e, he⟩ := exists_equiv_of_map_univ_eq _ _ hprof
  exact ⟨e, fun z i => stableEq_of_color_eq hs (congrFun (he z) i)⟩

end VariableWL

universe uGame1 uGame2 uGame3 uGame4 uGame5 uGame6 uGame7

namespace VariableWL.Game

theorem Winning.color_eq {G H : Graph} {k : ℕ} {p : Position G H (k+1)}
    (hp : Winning p) (σ : Fin k → Fin (k+1)) (hσ : Function.Injective σ)
    (v : Tuple G k) (w : Tuple H k) (hr : Realizes p σ v w) (s : ℕ) :
    color G k s v = color H k s w := by
  classical
  induction s generalizing p σ v w with
  | zero =>
    apply (color_zero_eq_iff v w).mpr
    have h := hp.partialIso
    exact ⟨fun i j => (h (σ i) (σ j) _ _ (hr i) (hr j)).1,
      fun i j => (h (σ i) (σ j) _ _ (hr i) (hr j)).2⟩
  | succ s ih =>
    apply Prod.ext (ih hp σ hσ v w hr)
    obtain ⟨j, hj⟩ := exists_fresh σ
    let p₀ := Function.update p j none
    have hp₀ : Winning p₀ := hp.discard (clear_subposition p j)
    obtain ⟨e, he⟩ := hp₀.move j (by simp [p₀])
    change Finset.univ.val.map (fun z i => color G k s (Function.update v i z)) =
      Finset.univ.val.map (fun z i => color H k s (Function.update w i z))
    rw [map_univ_comp_equiv e]
    apply Multiset.map_congr rfl
    intro z _
    funext i
    apply ih (he z) (Function.update σ i j) (update_injective_of_fresh hσ i j hj)
    intro a
    by_cases ha : a = i
    · subst a; simp
    · simp only [Function.update_of_ne ha, Function.update_of_ne (hj a)]
      simpa [p₀, Function.update_of_ne (hj a)] using hr a

end VariableWL.Game

namespace VariableWL.Game

theorem equivalent_of_winning {G H : Graph} {k : ℕ}
    (h : Winning (fun _ : Fin (k+1) => (none : Option (Fin G.order × Fin H.order)))) :
    Equivalent G H k := by
  obtain ⟨E, hE⟩ := h.fill k Fin.castSucc (Fin.castSucc_injective k) (fun _ => rfl)
  intro s
  unfold histogram
  rw [map_univ_comp_equiv E]
  apply Multiset.map_congr rfl
  intro v _
  obtain ⟨p, hp, _, hr⟩ := hE v
  exact hp.color_eq Fin.castSucc (Fin.castSucc_injective k) v (E v) hr s

end VariableWL.Game

namespace VariableWL.Game

theorem reindex_embeddings {α : Type uGame7} {k : ℕ} (f g : Fin k → α)
    (hg : Function.Injective g) (hr : ∀ i, ∃ j, f j = g i) :
    ∃ e : Equiv.Perm (Fin k), g = f ∘ e := by
  classical
  choose a ha using hr
  have hinj : Function.Injective a := by
    intro i j hij
    apply hg
    rw [← ha i, ← ha j, hij]
  let e := Equiv.ofBijective a
    ((Fintype.bijective_iff_injective_and_card a).mpr ⟨hinj, rfl⟩)
  exact ⟨e, funext fun i => (ha i).symm⟩

theorem fullStable_update {G H : Graph} {k : ℕ}
    (v : Fin (k+1) → Fin G.order) (w : Fin (k+1) → Fin H.order)
    (j : Fin (k+1)) (z : Fin G.order) (t : Fin H.order)
    (hbase : StableEq (v ∘ j.succAbove) (w ∘ j.succAbove))
    (hrep : ∀ a, StableEq (Function.update (v ∘ j.succAbove) a z)
      (Function.update (w ∘ j.succAbove) a t)) :
    FullStable (Function.update v j z) (Function.update w j t) := by
  classical
  intro τ
  obtain ⟨m, hm⟩ := exists_fresh τ
  by_cases hmj : m = j
  · subst m
    obtain ⟨e, he⟩ := reindex_embeddings j.succAbove τ τ.injective
      (fun b => Fin.exists_succAbove_eq (hm b))
    have hG : Function.update v j z ∘ τ = (v ∘ j.succAbove) ∘ e := by
      funext b
      simp only [Function.comp_apply, Function.update_of_ne (hm b)]
      exact congrArg v (congrFun he b)
    have hH : Function.update w j t ∘ τ = (w ∘ j.succAbove) ∘ e := by
      funext b
      simp only [Function.comp_apply, Function.update_of_ne (hm b)]
      exact congrArg w (congrFun he b)
    rw [hG, hH]
    exact hbase.reindex e
  · obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hmj
    let σ' := Function.update j.succAbove a j
    have hr : ∀ b, ∃ c, σ' c = τ b := by
      intro b
      by_cases hb : τ b = j
      · exact ⟨a, by simp [σ', hb]⟩
      · obtain ⟨c, hc⟩ := Fin.exists_succAbove_eq hb
        have hca : c ≠ a := by
          intro hca
          exact hm b (hc.symm.trans (hca ▸ ha))
        exact ⟨c, by simpa [σ', Function.update_of_ne hca] using hc⟩
    obtain ⟨e, he⟩ := reindex_embeddings σ' τ τ.injective hr
    have hcomp {A : Type} (u : Fin (k+1) → A) (x : A) :
        Function.update u j x ∘ σ' = Function.update (u ∘ j.succAbove) a x := by
      funext b
      by_cases hb : b = a
      · subst b; simp [σ']
      · simp [σ', Function.update_of_ne hb, Function.comp_apply, Fin.succAbove_ne]
    rw [he, ← Function.comp_assoc, hcomp, ← Function.comp_assoc, hcomp]
    exact (hrep a).reindex e

theorem FullStable.atomic {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    {v : Fin (k+1) → Fin G.order} {w : Fin (k+1) → Fin H.order}
    (h : FullStable v w) (i j : Fin (k+1)) :
    (v i = v j ↔ w i = w j) ∧ (G.graph.Adj (v i) (v j) ↔ H.graph.Adj (w i) (w j)) := by
  obtain ⟨m, hmi, hmj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hmi.symm
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hmj.symm
  have hc := (color_zero_eq_iff _ _).mp (h m.succAboveEmb 0)
  have h₁ := hc.1 a b
  have h₂ := hc.2 a b
  simp only [Function.comp_apply, Fin.coe_succAboveEmb, ha, hb] at h₁ h₂
  exact ⟨h₁, h₂⟩

end VariableWL.Game

namespace VariableWL.Game

theorem ghostFamily_winning (G H : Graph) (k : ℕ) (hk : 2 ≤ k) :
    WinningFamily (GhostFamily G H k) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rintro p ⟨v, w, hs, hf⟩ i j a b hia hjb
    obtain ⟨hvi, hwi⟩ := hf i a hia
    obtain ⟨hvj, hwj⟩ := hf j b hjb
    simpa only [hvi, hwi, hvj, hwj] using hs.atomic hk i j
  · rintro p ⟨v, w, hs, hf⟩ p' hsub
    exact ⟨v, w, hs, fun i a ha => hf i a (hsub i a ha)⟩
  · rintro p ⟨v, w, hs, hf⟩ j _
    have hbase := hs j.succAboveEmb
    obtain ⟨e, he⟩ := hbase.exists_bijection
    refine ⟨e, fun z => ?_⟩
    refine ⟨Function.update v j z, Function.update w j (e z),
      fullStable_update v w j z (e z) hbase (he z), ?_⟩
    intro i a ha
    by_cases hij : i = j
    · subst i
      simp only [Function.update_self, Option.some.injEq] at ha
      subst a
      simp
    · simp only [Function.update_of_ne hij] at ha ⊢
      exact hf i a ha

theorem exists_fullStable {G H : Graph} {k : ℕ} (hG : 0 < G.order)
    (h : Equivalent G H k) :
    ∃ v : Fin (k+1) → Fin G.order, ∃ w : Fin (k+1) → Fin H.order, FullStable v w := by
  classical
  let z : Fin G.order := ⟨0, hG⟩
  let v : Tuple G k := fun _ => z
  obtain ⟨s, _, hs⟩ := exists_stable_round G H k
  obtain ⟨w, hw⟩ := exists_color_match (h s) v
  have hb : StableEq v w := stableEq_of_color_eq hs hw.symm
  obtain ⟨e, he⟩ := hb.exists_bijection
  let j := Fin.last k
  let V : Fin (k+1) → Fin G.order := Fin.insertNth j z v
  let W : Fin (k+1) → Fin H.order := Fin.insertNth j (e z) w
  have hv : V ∘ j.succAbove = v := Fin.insertNth_comp_succAbove j z v
  have hw' : W ∘ j.succAbove = w := Fin.insertNth_comp_succAbove j (e z) w
  refine ⟨Function.update V j z, Function.update W j (e z), ?_⟩
  apply fullStable_update V W j z (e z)
  · simpa only [hv, hw'] using hb
  · simpa only [hv, hw'] using he z

theorem winning_of_equivalent {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    (hG : 0 < G.order) (h : Equivalent G H k) :
    Winning (fun _ : Fin (k+1) => (none : Option (Fin G.order × Fin H.order))) := by
  obtain ⟨v, w, hvw⟩ := exists_fullStable hG h
  refine ⟨GhostFamily G H k, ⟨v, w, hvw, ?_⟩, ghostFamily_winning G H k hk⟩
  intro i a ha
  contradiction

theorem equivalent_iff_winning {G H : Graph} {k : ℕ} (hk : 2 ≤ k) (hG : 0 < G.order) :
    Equivalent G H k ↔
      Winning (fun _ : Fin (k+1) => (none : Option (Fin G.order × Fin H.order))) :=
  ⟨winning_of_equivalent hk hG, equivalent_of_winning⟩

end VariableWL.Game

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Subdivision
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.Subdivision

variable {P : Type uVariable1} {E : Type uVariable2} {n : ℕ}

theorem exists_unused_cut [DecidableEq E] (S : Finset (Link E n))
    (hS : S.card < n+1) : ∃ cut : E → Fin (n+1), ∀ e, (e, cut e) ∉ S := by
  classical
  have hx (e : E) : ∃ i : Fin (n+1), (e,i) ∉ S := by
    by_contra h
    have hall : ∀ i : Fin (n+1), (e,i) ∈ S := by simpa using h
    have hsub : Finset.univ.image (fun i : Fin (n+1) => (e,i)) ⊆ S := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hall i
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (fun _ _ h => Prod.mk.inj h |>.2),
      Finset.card_univ, Fintype.card_fin] at hc
    omega
  exact ⟨fun e => (hx e).choose, fun e => (hx e).choose_spec⟩

theorem owner_link (src dst : E → P) (cut : E → Fin (n+1))
    (l : Link E n) (hcut : l.2 ≠ cut l.1) :
    owner src dst cut (left src l) = owner src dst cut (right dst l) := by
  have hv : l.2.val ≠ (cut l.1).val := fun h => hcut (Fin.ext h)
  unfold left right
  split_ifs with h₀ h₁ h₁
  · omega
  · simp only [owner]
    rw [ite_eq_left (by omega)]
  · simp only [owner]
    rw [ite_eq_right (by omega)]
  · simp only [owner]
    have hi : l.2.val - 1 < (cut l.1).val ↔ l.2.val < (cut l.1).val := by omega
    simp only [hi]

theorem owner_adj (hn : 0 < n) (src dst : E → P) (S : Set (Link E n))
    (cut : E → Fin (n+1)) (hc : ∀ l ∈ S, l.2 ≠ cut l.1)
    {v w : Vertex P E n} (h : (supportGraph hn src dst S).Adj v w) :
    owner src dst cut v = owner src dst cut w := by
  obtain ⟨l, hl, h⟩ := h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact owner_link src dst cut l (hc l hl)
  · exact (owner_link src dst cut l (hc l hl)).symm

theorem owner_walk (hn : 0 < n) (src dst : E → P) (S : Set (Link E n))
    (cut : E → Fin (n+1)) (hc : ∀ l ∈ S, l.2 ≠ cut l.1)
    {v w : Vertex P E n} (p : (supportGraph hn src dst S).Walk v w) :
    owner src dst cut v = owner src dst cut w := by
  induction p with
  | nil => rfl
  | cons h p ih => exact (owner_adj hn src dst S cut hc h).trans ih

theorem at_most_one_real [DecidableEq E] (hn : 0 < n) (src dst : E → P)
    (S : Finset (Link E n)) (hS : S.card < n+1) {p q : P}
    (h : (supportGraph hn src dst S).Reachable (.inl p) (.inl q)) : p = q := by
  obtain ⟨cut, hc⟩ := exists_unused_cut S hS
  apply owner_walk hn src dst S cut (fun l hl h => ?_) h.some
  change l ∈ S at hl
  exact hc l.1 (by simpa only [← h, Prod.eta] using hl)

end VariableWL.Subdivision

namespace VariableWL.Subdivision
variable {P : Type uVariable6} {E : Type uVariable7} {n : ℕ}

theorem internal_adj_wire (hn : 0 < n) (src dst : E → P) (S : Set (Link E n))
    {e f : E} {i j : Fin n}
    (h : (supportGraph hn src dst S).Adj (.inr (e,i)) (.inr (f,j))) : e = f := by
  obtain ⟨l, _, h⟩ := h
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  all_goals
    simp only [left, right] at h₁ h₂
    split_ifs at h₁ h₂
    all_goals simp_all

end VariableWL.Subdivision

namespace VariableWL.Markers
open scoped CharTwo
variable {V : Type uVariable9} {G : SimpleGraph V}

theorem walkSum_congr {ω ω' : V → V → Bit}
    (h : ∀ u v, G.Adj u v → ω u v = ω' u v) {u v : V} (p : G.Walk u v) :
    walkSum ω p = walkSum ω' p := by
  induction p with
  | nil => rfl
  | cons h' p ih => rw [walkSum_cons, walkSum_cons, h _ _ h', ih]

theorem walkSum_add (ω ω' : V → V → Bit) {u v : V} (p : G.Walk u v) :
    walkSum (fun x y => ω x y + ω' x y) p = walkSum ω p + walkSum ω' p := by
  induction p with
  | nil => simp [walkSum]
  | cons _ _ ih => simp only [walkSum_cons, ih]; ring

theorem walkSum_mul (ω : V → V → Bit) (c : Bit) {u v : V} (p : G.Walk u v) :
    walkSum (fun x y => ω x y * c) p = walkSum ω p * c := by
  induction p with
  | nil => simp [walkSum]
  | cons _ _ ih => simp only [walkSum_cons, ih]; ring

end VariableWL.Markers

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Wrapping
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11

namespace VariableWL.Wrapping
open scoped CharTwo
open Markers

variable {I : Type uVariable1} {V : Type uVariable2} [DecidableEq I] {G : SimpleGraph V}

namespace RowDiagram

variable {next : Equiv.Perm I} (D : RowDiagram G next)

theorem boundary_incidence (i : I) {u v : V} (h : G.Adj u v) :
    (if D.boundary u = i then (1 : Bit) else 0) +
      (if D.boundary v = i then 1 else 0) =
    D.rowWeight i u v + D.rowWeight (next.symm i) u v := by
  have hs := D.shape u v h
  cases hh : D.horizontal u v with
  | none =>
    simp only [hh] at hs
    simp [rowWeight, hh, hs]
  | some j =>
    simp only [hh] at hs
    rcases hs with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · simp [rowWeight, hh, hu, hv, ← next.eq_symm_apply]
    · simp [rowWeight, hh, hu, hv, ← next.eq_symm_apply, add_comm]

theorem row_parity_next {v : V} (p : G.Walk v v) (i : I) :
    walkSum (D.rowWeight (next i)) p = walkSum (D.rowWeight i) p := by
  classical
  let s (v : V) : Bit := if D.boundary v = next i then 1 else 0
  have ht := walkSum_of_potential
    (fun u v => D.rowWeight (next i) u v + D.rowWeight i u v) s
    (fun u v h => by simpa [s] using D.boundary_incidence (next i) h) p
  rw [walkSum_add] at ht
  have hh := congrArg (fun x => x + walkSum (D.rowWeight i) p) ht
  simpa [add_assoc] using hh

theorem row_parity_all
    (horbit : ∀ i j : I, ∃ m : ℕ, next^[m] i = j)
    {v : V} (p : G.Walk v v) (i j : I) :
    walkSum (D.rowWeight i) p = walkSum (D.rowWeight j) p := by
  obtain ⟨m, rfl⟩ := horbit i j
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', D.row_parity_next]
    exact ih

theorem finRotate_orbit {r : ℕ} [NeZero r] (i j : Fin r) :
    ∃ m : ℕ, (finRotate r)^[m] i = j := by
  refine ⟨(j-i).val, ?_⟩
  rw [← finCycle_eq_finRotate_iterate]
  simp

theorem covers_rows {B : Type uVariable3} [DecidableEq B] (U : Finset B) (row : B → I)
    (hcover : ∀ u v, G.Adj u v → ∀ i, D.horizontal u v = some i → i ∈ U.image row)
    (horbit : ∀ i j : I, ∃ m : ℕ, next^[m] i = j)
    {marked : I} (hw : D.Wraps marked) : ∀ i, i ∈ U.image row := by
  classical
  obtain ⟨v, p, hp⟩ := hw
  intro i
  by_contra hi
  have hz : walkSum (D.rowWeight i) p = 0 := by
    rw [walkSum_congr (ω' := fun _ _ => 0) (fun u v h => ?_), walkSum_zero]
    simp only [rowWeight, ite_eq_right_iff, one_ne_zero, imp_false]
    exact fun hh => hi (hcover u v h i hh)
  have he := D.row_parity_all horbit p i marked
  rw [hz, hp] at he
  exact zero_ne_one he

theorem blocks_card_ge [Fintype I] {B : Type uVariable4} [DecidableEq B]
    (U : Finset B) (row : B → I)
    (hcover : ∀ u v, G.Adj u v → ∀ i, D.horizontal u v = some i → i ∈ U.image row)
    (horbit : ∀ i j : I, ∃ m : ℕ, next^[m] i = j)
    {marked : I} (hw : D.Wraps marked) : Fintype.card I ≤ U.card := by
  have he : U.image row = Finset.univ := Finset.eq_univ_of_forall
    (D.covers_rows U row hcover horbit hw)
  calc
    Fintype.card I = (U.image row).card := by rw [he, Finset.card_univ]
    _ ≤ U.card := Finset.card_image_le

theorem row_injective [Fintype I] {B : Type uVariable5} [DecidableEq B]
    (U : Finset B) (row : B → I)
    (hcover : ∀ u v, G.Adj u v → ∀ i, D.horizontal u v = some i → i ∈ U.image row)
    (horbit : ∀ i j : I, ∃ m : ℕ, next^[m] i = j)
    {marked : I} (hw : D.Wraps marked) (hc : U.card = Fintype.card I) :
    Set.InjOn row (↑U : Set B) := by
  apply Finset.card_image_iff.mp
  have he : U.image row = Finset.univ := Finset.eq_univ_of_forall
    (D.covers_rows U row hcover horbit hw)
  rw [he, Finset.card_univ, hc]

end RowDiagram

end VariableWL.Wrapping

namespace VariableWL.Wrapping.RowDiagram
open scoped CharTwo
open Markers
variable {I : Type uVariable6} {V : Type uVariable7} {L : Type uVariable8} [DecidableEq I] [DecidableEq L]
    {G : SimpleGraph V} {next : Equiv.Perm I} (D : RowDiagram G next)

theorem label_incidence (label : V → L) (first last : I → L)
    (hl : D.Labeled label first last) (i : I) (x : L) {u v : V} (h : G.Adj u v) :
    (if (D.boundary u, label u) = (i,x) then (1 : Bit) else 0) +
      (if (D.boundary v, label v) = (i,x) then 1 else 0) =
    D.rowWeight i u v * (if first i = x then 1 else 0) +
      D.rowWeight (next.symm i) u v * (if last (next.symm i) = x then 1 else 0) := by
  have hs := hl u v h
  cases hh : D.horizontal u v with
  | none =>
    simp only [hh] at hs
    rw [hs]
    simp [rowWeight, hh]
  | some j =>
    simp only [hh] at hs
    rcases hs with ⟨hu, hv⟩ | ⟨hv, hu⟩
    all_goals
      rw [hu, hv]
      by_cases hji : j = i <;> by_cases hjp : j = next.symm i <;>
        simp_all [rowWeight, ← next.eq_symm_apply, add_comm]

theorem label_coherence (label : V → L) (first last : I → L)
    (hl : D.Labeled label first last)
    (horbit : ∀ i j : I, ∃ m : ℕ, next^[m] i = j)
    {marked : I} (hw : D.Wraps marked) : ∀ i, last i = first (next i) := by
  obtain ⟨v, p, hp⟩ := hw
  have hpar (i : I) : walkSum (D.rowWeight i) p = 1 :=
    (D.row_parity_all horbit p i marked).trans hp
  have hc (i : I) : last (next.symm i) = first i := by
    let s (v : V) : Bit := if (D.boundary v, label v) = (i,first i) then 1 else 0
    have ht := walkSum_of_potential
      (fun u v => D.rowWeight i u v * (if first i = first i then 1 else 0) +
        D.rowWeight (next.symm i) u v * (if last (next.symm i) = first i then 1 else 0)) s
      (fun u v h => D.label_incidence label first last hl i (first i) h) p
    rw [walkSum_add, walkSum_mul, walkSum_mul, hpar, hpar] at ht
    by_contra he
    simp [he] at ht
  intro i
  simpa using hc (next i)

end VariableWL.Wrapping.RowDiagram

namespace VariableWL.Wrapping
variable {I : Type uVariable9} {B : Type uVariable10} {L : Type uVariable11} [Fintype I] [DecidableEq I] [DecidableEq B]

theorem overlap_compl_card_le_one (U A B' : Finset B) (row : B → I)
    (hA : A ⊆ U) (hB : B' ⊆ U) (hU : U.card ≤ Fintype.card I + 1)
    (hcA : A.card = Fintype.card I) (hcB : B'.card = Fintype.card I)
    (hi : Set.InjOn row (↑A : Set B)) :
    ((A ∩ B').image row)ᶜ.card ≤ 1 := by
  have hsub : A ∪ B' ⊆ U := Finset.union_subset hA hB
  have hle := Finset.card_le_card hsub
  have hcard := Finset.card_union_add_card_inter A B'
  have hinj : Set.InjOn row (↑(A ∩ B') : Set B) := hi.mono (by
    intro x hx; exact (Finset.mem_inter.mp hx).1)
  rw [Finset.card_compl, Finset.card_image_iff.mpr hinj]
  omega

theorem adjacent_cover (next : Equiv.Perm I) (hnofix : ∀ i, next i ≠ i)
    (S : Finset I) (hS : Sᶜ.card ≤ 1) (i : I) : i ∈ S ∨ next.symm i ∈ S := by
  by_contra h
  push Not at h
  have hi : next.symm i ≠ i := by
    intro he
    have hh := congrArg next he
    exact hnofix i (by simpa using hh.symm)
  have hsub : {i, next.symm i} ⊆ Sᶜ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_compl.mpr h.1
    · exact Finset.mem_compl.mpr h.2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair hi.symm] at hc
  omega

theorem overlap_address_unique (next : Equiv.Perm I) (hnofix : ∀ i, next i ≠ i)
    (U A B' : Finset B) (row : B → I)
    (hA : A ⊆ U) (hB : B' ⊆ U) (hU : U.card ≤ Fintype.card I + 1)
    (hcA : A.card = Fintype.card I) (hcB : B'.card = Fintype.card I)
    (hi : Set.InjOn row (↑A : Set B)) (a a' : I → L)
    (hlabel : ∀ b ∈ A ∩ B', a (row b) = a' (row b) ∧
      a (next (row b)) = a' (next (row b))) : a = a' := by
  funext i
  have hc := overlap_compl_card_le_one U A B' row hA hB hU hcA hcB hi
  rcases adjacent_cover next hnofix _ hc i with h | h
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
    exact (hlabel b hb).1
  · obtain ⟨b, hb, hbi⟩ := Finset.mem_image.mp h
    have hh := (hlabel b hb).2
    simpa only [hbi, Equiv.apply_symm_apply] using hh

end VariableWL.Wrapping

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_ProductImages
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.BlockCoordinates.coordinateFintype _root_.OAI.VariableWL.BlockCoordinates.defaultProperNumberings _root_.OAI.VariableWL.Blocks.blockFintype _root_.OAI.VariableWL.Blocks.rawValueAddCommGroup _root_.OAI.VariableWL.Blocks.rawValueFintype _root_.OAI.VariableWL.Blocks.readoutValueAddCommGroup _root_.OAI.VariableWL.Blocks.readoutValueFintype _root_.OAI.VariableWL.Blocks.valuationFintype _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.ProductImages
open scoped CharTwo
open VariableWL.Affine

variable (r : ℕ) (P : Type uVariable1) (E : Type uVariable2)

namespace Instance
variable {r : ℕ} {P : Type uVariable3} {E : Type uVariable4} (J : Instance r P E)

namespace Witness
variable {J} (Q : J.Witness)

theorem wireValues_nonempty (e : E) (a : Address r) :
    (Q.wireValues e a).Nonempty := (Q.nonempty _ _).image _

theorem right_image (e : E) (a : Address r) (ha : J.Allowed e a) :
    J.rightForm e '' Q.values (J.target e) (J.mapAddress e a) =
      Q.wireValues e a := (Q.images e a ha).symm

theorem lift_left (e : E) (a : Address r) {b : Bit} (hb : b ∈ Q.wireValues e a) :
    ∃ v ∈ Q.values (J.source e) a, J.leftForm e v = b := hb

theorem lift_right (e : E) (a : Address r) (ha : J.Allowed e a)
    {b : Bit} (hb : b ∈ Q.wireValues e a) :
    ∃ v ∈ Q.values (J.target e) (J.mapAddress e a), J.rightForm e v = b := by
  rw [← Q.right_image e a ha] at hb
  exact hb

end Witness

theorem ambient_on_domain (e : E) (i : Fin r) (a : Bool) (ha : a ∈ J.domain e i) :
    J.ambient e i a = J.map e i a := (J.exists_ambient e i).choose_spec a ha

open Subdivision
variable {n : ℕ}

theorem alignment_match (hn : 0 < n) (cut : E → Fin (n+1))
    (l : Link E n) (hc : l.2 ≠ cut l.1) (i : Fin r)
    {a b : Bool} (h : J.Matches l i a b) :
    J.alignment cut (left J.source l) i a =
      J.alignment cut (right J.target l) i b := by
  have hv : l.2.val ≠ (cut l.1).val := fun hh => hc (Fin.ext hh)
  have hl := l.2.isLt
  have hk := (cut l.1).isLt
  unfold left right
  split_ifs with h₀ h₁ h₁
  · omega
  · simp only [alignment]
    rw [ite_eq_left (by omega)]
    simp only [Equiv.refl_apply]
    exact (h.2.trans (ite_eq_right h₁)).symm
  · simp only [alignment]
    rw [ite_eq_right (by omega), Equiv.refl_apply]
    rw [J.ambient_on_domain _ _ _ h.1, h.2, ite_eq_left h₁]
  · simp only [alignment]
    have hi : l.2.val - 1 < (cut l.1).val ↔ l.2.val < (cut l.1).val := by omega
    rw [h.2, ite_eq_right h₁]
    simp only [hi]

end Instance
end VariableWL.ProductImages

namespace VariableWL.ProductImages.Instance
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} (J : ProductImages.Instance r P E)

theorem cutShifts_equation (hn : 0 < n) (cut : E → Fin (n+1))
    (v : ∀ p, Vec (J.dimension p)) (l : Link E n) (hc : l.2 ≠ cut l.1) :
    J.shiftLeft (J.cutShifts cut v) l = J.shiftRight (J.cutShifts cut v) l := by
  have hv : l.2.val ≠ (cut l.1).val := fun h => hc (Fin.ext h)
  have hl := l.2.isLt
  have hk := (cut l.1).isLt
  unfold shiftLeft shiftRight
  split_ifs with h₀ h₁ h₁
  · omega
  · simp only [cutShifts]
    rw [ite_eq_left (by omega)]
  · simp only [cutShifts]
    rw [ite_eq_right (by omega)]
  · simp only [cutShifts]
    have hi : l.2.val - 1 < (cut l.1).val ↔ l.2.val < (cut l.1).val := by omega
    simp only [hi]

end VariableWL.ProductImages.Instance

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Blocks
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.BlockCoordinates.coordinateFintype _root_.OAI.VariableWL.BlockCoordinates.defaultProperNumberings _root_.OAI.VariableWL.Blocks.blockFintype _root_.OAI.VariableWL.Blocks.horizontalFintype _root_.OAI.VariableWL.Blocks.rawValueAddCommGroup _root_.OAI.VariableWL.Blocks.rawValueFintype _root_.OAI.VariableWL.Blocks.readoutValueAddCommGroup _root_.OAI.VariableWL.Blocks.readoutValueFintype _root_.OAI.VariableWL.Blocks.squareFintype _root_.OAI.VariableWL.Blocks.valuationFintype _root_.OAI.VariableWL.Blocks.verticalFintype _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12 uVariable13 uVariable14 uVariable15 uVariable16 uVariable17 uVariable18

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable13} {E : Type uVariable14} (J : ProductImages.Instance r P E)

theorem supportLinks_card (U : Finset (Block (n := n) J)) :
    (supportLinks J U).card ≤ U.card := by
  classical
  calc
    _ ≤ ∑ b ∈ U, (linksOf b.val).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ U, 1 := Finset.sum_le_sum fun b _ => by
      cases b.val <;> simp [linksOf]
    _ = U.card := by simp

theorem hasReadout_horizontal_row {b : RawBlock r n P E} {h : Horizontal r n P E}
    (hh : HasReadout J b (.inl h)) : h.row = row b := by
  classical
  cases b with
  | inl h' => cases hh; rfl
  | inr s =>
    rcases hh with hh | hh | hh | hh
    · cases hh; rfl
    · cases hh; rfl
    · cases hh
    · cases hh

theorem hasReadout_vertical_link {b : RawBlock r n P E} {v : Vertical r n E}
    (hh : HasReadout J b (.inr v)) : v.link ∈ linksOf b := by
  classical
  cases b with
  | inl h => cases hh
  | inr s =>
    rcases hh with hh | hh | hh | hh
    · cases hh
    · cases hh
    · cases hh; simp [linksOf, squareBottom]
    · cases hh; simp [linksOf, squareTop]

theorem projection_adj (hr : 2 ≤ r) (hn : 0 < n) (U : Finset (Block (n := n) J))
    {v w : Corner r n P E} (h : (diagram J hr hn U).Adj v w) :
    v.2.1 = w.2.1 ∨ (supportGraph hn J.source J.target (supportLinks J U)).Adj v.2.1 w.2.1 := by
  classical
  obtain ⟨b,hb,a,ha,h⟩ := h
  have hv {a : Vertical r n E} (ha : HasReadout J b.val (.inr a)) :
      a.link ∈ supportLinks J U := Finset.mem_biUnion.mpr
        ⟨b,hb,hasReadout_vertical_link J ha⟩
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> cases a with
  | inl h => exact Or.inl rfl
  | inr v =>
    apply Or.inr
    first
    | exact ⟨v.link, hv ha, Or.inl ⟨rfl,rfl⟩⟩
    | exact ⟨v.link, hv ha, Or.inr ⟨rfl,rfl⟩⟩

theorem projection_reachable (hr : 2 ≤ r) (hn : 0 < n) (U : Finset (Block (n := n) J))
    {v w : Corner r n P E} (h : (diagram J hr hn U).Reachable v w) :
    (supportGraph hn J.source J.target (supportLinks J U)).Reachable v.2.1 w.2.1 := by
  classical
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h p ih =>
    rcases projection_adj J hr hn U h with h | h
    · exact h ▸ ih
    · exact h.reachable.trans ih

theorem row_cover (hr : 3 ≤ r) (hn : 0 < n) (U : Finset (Block (n := n) J))
    {v w : Corner r n P E} (h : (diagram J (by omega) hn U).Adj v w)
    {i : Fin r} (hi : (rowDiagram J hr hn U).horizontal v w = some i) :
    i ∈ U.image (fun b => row b.val) := by
  classical
  obtain ⟨b,hb,a,ha,h⟩ := h
  have he : (Sum.elim (fun h => some h.row) (fun _ => none) a) = some i := by
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have ht := (horizontalTag_readout J hr a).1.symm.trans hi
      cases a <;> exact ht
    · have ht := (horizontalTag_readout J hr a).2.symm.trans hi
      cases a <;> exact ht
  cases a with
  | inr v => cases he
  | inl h =>
    have he' := Option.some.inj he
    exact Finset.mem_image.mpr ⟨b,hb,(hasReadout_horizontal_row J ha).symm.trans he'⟩

theorem wrapping_card_ge (hr : 3 ≤ r) (hn : 0 < n) (U : Finset (Block (n := n) J))
    {marked : Fin r} (hw : (rowDiagram J hr hn U).Wraps marked) : r ≤ U.card := by
  classical
  have : NeZero r := ⟨by omega⟩
  simpa only [Fintype.card_fin] using (rowDiagram J hr hn U).blocks_card_ge U
    (fun b => row b.val) (fun _ _ h _ hi => row_cover J hr hn U h hi)
    Wrapping.RowDiagram.finRotate_orbit hw

theorem wrapping_row_injective (hr : 3 ≤ r) (hn : 0 < n) (U : Finset (Block (n := n) J))
    {marked : Fin r} (hw : (rowDiagram J hr hn U).Wraps marked) (hc : U.card = r) :
    Set.InjOn (fun b : Block (n := n) J => row b.val) (↑U : Set (Block (n := n) J)) := by
  classical
  have : NeZero r := ⟨by omega⟩
  exact (rowDiagram J hr hn U).row_injective U (fun b => row b.val)
    (fun _ _ h _ hi => row_cover J hr hn U h hi)
    Wrapping.RowDiagram.finRotate_orbit hw (by simpa only [Fintype.card_fin] using hc)

theorem square_alignment (hn : 0 < n) (cut : E → Fin (n+1))
    (s : Square r n E) (hs : ValidSquare J s) (hc : s.link.2 ≠ cut s.link.1) :
    aligned J cut (end0 J (.inl (squareRight J s))) = firstLabel J cut (.inr s) ∧
    aligned J cut (end1 J (.inl (squareRight J s))) = lastLabel J cut (.inr s) := by
  classical
  constructor
  · exact (J.alignment_match hn cut s.link hc s.row ⟨hs.1,rfl⟩).symm
  · exact (J.alignment_match hn cut s.link hc (finRotate r s.row) ⟨hs.2,rfl⟩).symm

theorem horizontal_labels (hn : 0 < n) (cut : E → Fin (n+1))
    (b : Block (n := n) J) (hc : ∀ l ∈ linksOf b.val, l.2 ≠ cut l.1)
    {h : Horizontal r n P E} (hh : HasReadout J b.val (.inl h)) :
    aligned J cut (end0 J (.inl h)) = firstLabel J cut b.val ∧
    aligned J cut (end1 J (.inl h)) = lastLabel J cut b.val := by
  classical
  obtain ⟨b,hb⟩ := b
  cases b with
  | inl h' => cases hh; exact ⟨rfl,rfl⟩
  | inr s =>
    rcases hh with hh | hh | hh | hh
    · cases hh; exact ⟨rfl,rfl⟩
    · cases hh; exact square_alignment J hn cut s hb (hc s.link (by simp [linksOf]))
    · cases hh
    · cases hh

theorem vertical_labels (hn : 0 < n) (cut : E → Fin (n+1))
    (b : Block (n := n) J) (hc : ∀ l ∈ linksOf b.val, l.2 ≠ cut l.1)
    {v : Vertical r n E} (hv : HasReadout J b.val (.inr v)) :
    aligned J cut (end0 J (.inr v)) = aligned J cut (end1 J (.inr v)) := by
  classical
  obtain ⟨b,hb⟩ := b
  cases b with
  | inl h => cases hv
  | inr s =>
    have hcut := hc s.link (by simp [linksOf])
    rcases hv with hv | hv | hv | hv
    · cases hv
    · cases hv
    · cases hv; exact J.alignment_match hn cut s.link hcut s.row ⟨hb.1,rfl⟩
    · cases hv; exact J.alignment_match hn cut s.link hcut (finRotate r s.row) ⟨hb.2,rfl⟩

end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable15} {E : Type uVariable16} (J : ProductImages.Instance r P E)

theorem recovered_address (hr : 3 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (cut : E → Fin (n+1))
    (hcut : ∀ l ∈ supportLinks J U, l.2 ≠ cut l.1)
    {marked : Fin r} (hw : (rowDiagram J hr hn U).Wraps marked) (hc : U.card = r) :
    ∃ a : Fin r → Bool, ∀ b ∈ U,
      firstLabel J cut b.val = a (row b.val) ∧
        lastLabel J cut b.val = a (finRotate r (row b.val)) := by
  classical
  have : NeZero r := ⟨by omega⟩
  have hrows := (rowDiagram J hr hn U).covers_rows U (fun b => row b.val)
    (fun _ _ h _ hi => row_cover J hr hn U h hi)
    Wrapping.RowDiagram.finRotate_orbit hw
  have hi := wrapping_row_injective J hr hn U hw hc
  choose chosen hat using fun i => Finset.mem_image.mp (hrows i)
  have hatmem (i) : chosen i ∈ U := (hat i).1
  have hatrow (i) : row (chosen i).val = i := (hat i).2
  have hateq (b : Block (n := n) J) (hb : b ∈ U) : chosen (row b.val) = b :=
    hi (hatmem _) hb (hatrow _)
  let first := fun i => firstLabel J cut (chosen i).val
  let last := fun i => lastLabel J cut (chosen i).val
  have hl : (rowDiagram J hr hn U).Labeled (aligned J cut) first last := by
    rintro v w ⟨b,hb,c,hc,h⟩
    have hc' : ∀ l ∈ linksOf b.val, l.2 ≠ cut l.1 := fun l hl =>
      hcut l (Finset.mem_biUnion.mpr ⟨b,hb,hl⟩)
    have hfirst : first (row b.val) = firstLabel J cut b.val := by
      dsimp only [first]; rw [hateq b hb]
    have hlast : last (row b.val) = lastLabel J cut b.val := by
      dsimp only [last]; rw [hateq b hb]
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · dsimp only [rowDiagram]
      rw [(horizontalTag_readout J hr c).1]
      cases c with
      | inl h =>
        have hrow := hasReadout_horizontal_row J hc
        obtain ⟨hf,hl⟩ := horizontal_labels J hn cut b hc' hc
        rw [← hrow] at hfirst hlast
        exact Or.inl ⟨Prod.ext rfl (hf.trans hfirst.symm),
          Prod.ext rfl (hl.trans hlast.symm)⟩
      | inr v => exact Prod.ext rfl (vertical_labels J hn cut b hc' hc)
    · dsimp only [rowDiagram]
      rw [(horizontalTag_readout J hr c).2]
      cases c with
      | inl h =>
        have hrow := hasReadout_horizontal_row J hc
        obtain ⟨hf,hl⟩ := horizontal_labels J hn cut b hc' hc
        rw [← hrow] at hfirst hlast
        exact Or.inr ⟨Prod.ext rfl (hf.trans hfirst.symm),
          Prod.ext rfl (hl.trans hlast.symm)⟩
      | inr v => exact Prod.ext rfl (vertical_labels J hn cut b hc' hc).symm
  have hcoherent := (rowDiagram J hr hn U).label_coherence (aligned J cut) first last
    hl Wrapping.RowDiagram.finRotate_orbit hw
  refine ⟨first, fun b hb => ⟨?_, ?_⟩⟩
  · dsimp only [first]; rw [hateq b hb]
  · rw [← hcoherent (row b.val)]
    dsimp only [last]; rw [hateq b hb]

end VariableWL.Blocks

namespace VariableWL.ProductImages.Instance
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable17} {E : Type uVariable18} (J : ProductImages.Instance r P E)

theorem shiftLeft_agree {h g : J.Shifts n} (l : Link E n)
    (ha : J.AgreeAt h g (left J.source l)) : J.shiftLeft h l = J.shiftLeft g l := by
  unfold left at ha
  unfold shiftLeft
  split_ifs at ha ⊢ with hl
  · exact congrArg (J.leftForm l.1) ha
  · exact ha

theorem shiftRight_agree {h g : J.Shifts n} (l : Link E n)
    (ha : J.AgreeAt h g (right J.target l)) : J.shiftRight h l = J.shiftRight g l := by
  unfold right at ha
  unfold shiftRight
  split_ifs at ha ⊢ with hr
  · exact congrArg (J.rightForm l.1) ha
  · exact ha

theorem shiftLeft_eq_internal (h : J.Shifts n) (l : Link E n) {q : E × Fin n}
    (hq : left J.source l = .inr q) : J.shiftLeft h l = h.2 q := by
  unfold left at hq
  split at hq
  · cases hq
  · rename_i hl
    simp only [shiftLeft, dite_eq_right hl, Sum.inr.inj hq]

theorem shiftRight_eq_internal (h : J.Shifts n) (l : Link E n) {q : E × Fin n}
    (hq : right J.target l = .inr q) : J.shiftRight h l = h.2 q := by
  unfold right at hq
  split at hq
  · cases hq
  · rename_i hr
    simp only [shiftRight, dite_eq_right hr, Sum.inr.inj hq]

theorem agree_adj (hn : 0 < n) (S : Set (Link E n)) {h g : J.Shifts n}
    (hh : J.ShiftSystem S h) (hg : J.ShiftSystem S g)
    {v w : Vertex P E n} (he : (supportGraph hn J.source J.target S).Adj v w)
    (hv : J.AgreeAt h g v) (hw : ∀ p, w = .inl p → h.1 p = g.1 p) :
    J.AgreeAt h g w := by
  cases w with
  | inl p => exact hw p rfl
  | inr q =>
    obtain ⟨l,hl,(⟨hvl,hwr⟩ | ⟨hvr,hwl⟩)⟩ := he
    · have ha := J.shiftLeft_agree l (hvl ▸ hv)
      have hb := (hh l hl).symm.trans (ha.trans (hg l hl))
      rw [J.shiftRight_eq_internal h l hwr.symm,
        J.shiftRight_eq_internal g l hwr.symm] at hb
      exact hb
    · have ha := J.shiftRight_agree l (hvr ▸ hv)
      have hb := (hh l hl).trans (ha.trans (hg l hl).symm)
      rw [J.shiftLeft_eq_internal h l hwl.symm,
        J.shiftLeft_eq_internal g l hwl.symm] at hb
      exact hb

theorem agree_reachable (hn : 0 < n) (S : Set (Link E n)) {h g : J.Shifts n}
    (hh : J.ShiftSystem S h) (hg : J.ShiftSystem S g) (root : Vertex P E n)
    (hroot : J.AgreeAt h g root)
    (hreals : ∀ p, (supportGraph hn J.source J.target S).Reachable root (.inl p) →
      h.1 p = g.1 p) {w : Vertex P E n}
    (hw : (supportGraph hn J.source J.target S).Reachable root w) : J.AgreeAt h g w := by
  obtain ⟨path⟩ := hw
  have walk_prop {v w : Vertex P E n} (p : (supportGraph hn J.source J.target S).Walk v w)
      (hv : J.AgreeAt h g v)
      (hr : (supportGraph hn J.source J.target S).Reachable root v) : J.AgreeAt h g w := by
    induction p with
    | nil => exact hv
    | @cons v u w h p ih =>
      have hu := hr.trans h.reachable
      exact ih (J.agree_adj hn S hh hg h hv (fun p he => hreals p (he ▸ hu))) hu
  exact walk_prop path hroot (.refl _)

end VariableWL.ProductImages.Instance

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BlockImages
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.BlockCoordinates.coordinateFintype _root_.OAI.VariableWL.BlockCoordinates.defaultProperNumberings _root_.OAI.VariableWL.Blocks.blockFintype _root_.OAI.VariableWL.Blocks.horizontalFintype _root_.OAI.VariableWL.Blocks.rawValueAddCommGroup _root_.OAI.VariableWL.Blocks.rawValueFintype _root_.OAI.VariableWL.Blocks.readoutValueAddCommGroup _root_.OAI.VariableWL.Blocks.readoutValueFintype _root_.OAI.VariableWL.Blocks.valuationFintype _root_.OAI.VariableWL.Blocks.verticalFintype _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12

namespace VariableWL.Blocks
open scoped CharTwo
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E)

theorem gauge_horizontal_readout (marked : Fin r) (h g : J.Shifts n)
    (M : Potentials (n := n) J) (s : Corner r n P E → Bit) (x : Horizontal r n P E)
    (hs : s (end0 J (.inl x)) + s (end1 J (.inl x)) = marker marked x.row) :
    potentialValues J marked g (gaugePotentials J h g M s) (.inl x) =
      potentialValues J marked h M (.inl x) := by
  exact Affine.gauge_horizontal _ _ _ _ _ _ _ hs

theorem gauge_vertical_readout (marked : Fin r) (h g : J.Shifts n)
    (M : Potentials (n := n) J) (s : Corner r n P E → Bit) (y : Vertical r n E)
    (hs : s (end0 J (.inr y)) = s (end1 J (.inr y)))
    (hh : J.shiftLeft h y.link = J.shiftRight h y.link)
    (hg : J.shiftLeft g y.link = J.shiftRight g y.link) :
    potentialValues J marked g (gaugePotentials J h g M s) (.inr y) =
      potentialValues J marked h M (.inr y) := by
  exact Affine.gauge_vertical _ _ _ _ _ _ _ _ _ _ hs
    (Affine.shift_difference _ _ _ _ _ _ _
      ((link_equation_iff J h y.link).mpr hh) ((link_equation_iff J g y.link).mpr hg))

end VariableWL.Blocks

namespace VariableWL.Markers
open scoped CharTwo
variable {V : Type uVariable4} {G : SimpleGraph V}

theorem exists_potential_all (ω : V → V → Bit)
    (hsym : ∀ u v, G.Adj u v → ω u v = ω v u)
    (hzero : ∀ u (p : G.Walk u u), walkSum ω p = 0) :
    ∃ s : V → Bit, ∀ u v, G.Adj u v → s u + s v = ω u v := by
  classical
  let root (v : V) : V := (G.connectedComponentMk v).out
  have hr (v : V) : G.Reachable (root v) v :=
    SimpleGraph.ConnectedComponent.exact (G.connectedComponentMk v).out_eq
  let p (v : V) : G.Walk (root v) v := (hr v).some
  refine ⟨fun v => walkSum ω (p v), ?_⟩
  intro u v huv
  have he : root v = root u := congrArg (fun c : G.ConnectedComponent => c.out)
    (SimpleGraph.ConnectedComponent.sound huv.reachable).symm
  have hc := hzero (root u)
    (((p u).append huv.toWalk).append ((p v).copy he rfl).reverse)
  simp only [walkSum_append, walkSum_reverse ω hsym, walkSum_copy,
    SimpleGraph.Adj.toWalk, walkSum_cons, walkSum_nil, add_zero] at hc
  calc
    walkSum ω (p u) + walkSum ω (p v) =
        (walkSum ω (p u) + ω u v + walkSum ω (p v)) + ω u v := by
      simp [add_comm, add_assoc]
    _ = ω u v := by rw [hc, zero_add]
end VariableWL.Markers

namespace VariableWL.Wrapping.RowDiagram
open scoped CharTwo
open VariableWL.Markers
variable {I : Type uVariable5} {V : Type uVariable6} [DecidableEq I] {G : SimpleGraph V}
    {next : Equiv.Perm I} (D : VariableWL.Wrapping.RowDiagram G next)

theorem nonwrapping_potential (marked : I) (hn : ¬ D.Wraps marked) :
    ∃ s : V → Bit, ∀ u v, G.Adj u v → s u + s v = D.rowWeight marked u v := by
  apply Markers.exists_potential_all
  · intro u v h
    simp only [rowWeight, D.symmetric u v h]
  · intro u p
    have hx : ∀ x : Bit, x = 0 ∨ x = 1 := by decide
    rcases hx (walkSum (D.rowWeight marked) p) with h | h
    · exact h
    · exact (hn ⟨u,p,h⟩).elim
end VariableWL.Wrapping.RowDiagram

namespace VariableWL.Blocks
open scoped CharTwo
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable7} {E : Type uVariable8} (J : ProductImages.Instance r P E)

theorem readout_adj (hr : 2 ≤ r) (hn : 0 < n) (U : Set (Block (n := n) J))
    {b : Block (n := n) J} (hb : b ∈ U) {a : Readout r n P E}
    (ha : HasReadout J b.val a) : (diagram J hr hn U).Adj (end0 J a) (end1 J a) :=
  ⟨b,hb,a,ha,Or.inl ⟨rfl,rfl⟩⟩

theorem gauge_nonwrapping (hr : 3 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (marked : Fin r)
    (h g : J.Shifts n) (M : Potentials (n := n) J)
    (hh : J.ShiftSystem (supportLinks J U) h)
    (hg : J.ShiftSystem (supportLinks J U) g)
    (hnw : ¬ (rowDiagram J hr hn U).Wraps marked) :
    ∃ M' : Potentials (n := n) J, ∀ b ∈ U, ∀ a, HasReadout J b.val a →
      potentialValues J marked g M' a = potentialValues J marked h M a := by
  classical
  obtain ⟨s,hs⟩ := (rowDiagram J hr hn U).nonwrapping_potential marked hnw
  refine ⟨gaugePotentials J h g M s, ?_⟩
  intro b hb a ha
  have hed := readout_adj J (by omega) hn U hb ha
  have he := hs (end0 J a) (end1 J a) hed
  dsimp only [rowDiagram] at he
  unfold Wrapping.RowDiagram.rowWeight at he
  dsimp only at he
  simp only [(horizontalTag_readout J hr a).1] at he
  cases a with
  | inl x =>
    apply gauge_horizontal_readout J marked h g M s x
    simpa [marker] using he
  | inr y =>
    apply gauge_vertical_readout J marked h g M s y
    · simp only [reduceCtorEq, ite_false] at he
      have he' := congrArg (fun z => z + s (end1 J (.inr y))) he
      simpa [add_assoc] using he'
    · exact hh y.link (Finset.mem_biUnion.mpr
        ⟨b,hb,hasReadout_vertical_link J ha⟩)
    · exact hg y.link (Finset.mem_biUnion.mpr
        ⟨b,hb,hasReadout_vertical_link J ha⟩)
end VariableWL.Blocks

namespace VariableWL.ProductImages.Instance
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable9} {E : Type uVariable10} (J : ProductImages.Instance r P E)

theorem replaceInternal_agree_outside (hn : 0 < n) (S : Set (Link E n))
    (root : Vertex P E n) (a : Bit) (h : J.Shifts n) {v : Vertex P E n}
    (hv : ¬ (supportGraph hn J.source J.target S).Reachable root v) :
    J.AgreeAt (J.replaceInternal hn S root a h) h v := by
  classical
  cases v with
  | inl p => rfl
  | inr q => exact ite_eq_right hv

theorem replaceInternal_system (hn : 0 < n) (S : Set (Link E n))
    (root : Vertex P E n) (a : Bit) (h : J.Shifts n) (hh : J.ShiftSystem S h)
    (hnr : ∀ p, ¬ (supportGraph hn J.source J.target S).Reachable root (.inl p)) :
    J.ShiftSystem S (J.replaceInternal hn S root a h) := by
  classical
  intro l hl
  have hadj : (supportGraph hn J.source J.target S).Adj
      (left J.source l) (right J.target l) := ⟨l,hl,Or.inl ⟨rfl,rfl⟩⟩
  by_cases hr : (supportGraph hn J.source J.target S).Reachable root (left J.source l)
  · have hr' := hr.trans hadj.reachable
    obtain ⟨q,hq⟩ : ∃ q, left J.source l = .inr q := by
      cases he : left J.source l with
      | inl p => exact (hnr p (he ▸ hr)).elim
      | inr q => exact ⟨q,rfl⟩
    obtain ⟨q',hq'⟩ : ∃ q', right J.target l = .inr q' := by
      cases he : right J.target l with
      | inl p => exact (hnr p (he ▸ hr')).elim
      | inr q => exact ⟨q,rfl⟩
    rw [J.shiftLeft_eq_internal _ l hq, J.shiftRight_eq_internal _ l hq']
    simp only [replaceInternal, ite_eq_left (hq ▸ hr), ite_eq_left (hq' ▸ hr')]
  · have hr' : ¬ (supportGraph hn J.source J.target S).Reachable root (right J.target l) :=
      fun hw => hr (hw.trans hadj.symm.reachable)
    rw [J.shiftLeft_agree l (J.replaceInternal_agree_outside hn S root a h hr),
      J.shiftRight_agree l (J.replaceInternal_agree_outside hn S root a h hr')]
    exact hh l hl

theorem exists_scalar_shift (hn : 0 < n) (S : Set (Link E n))
    (root : Vertex P E n) (a : Bit) (h : J.Shifts n) (hh : J.ShiftSystem S h)
    (hnr : ∀ p, ¬ (supportGraph hn J.source J.target S).Reachable root (.inl p)) :
    ∃ g : J.Shifts n, J.ShiftSystem S g ∧ ∀ q,
      (supportGraph hn J.source J.target S).Reachable root (.inr q) → g.2 q = a := by
  classical
  refine ⟨J.replaceInternal hn S root a h,
    J.replaceInternal_system hn S root a h hh hnr, ?_⟩
  intro q hq
  exact ite_eq_left hq

theorem internal_adj_values (hn : 0 < n) (S : Set (Link E n))
    (h : J.Shifts n) (hh : J.ShiftSystem S h) {q q' : E × Fin n}
    (ha : (supportGraph hn J.source J.target S).Adj (.inr q) (.inr q')) :
    h.2 q = h.2 q' := by
  obtain ⟨l,hl,⟨he,he'⟩ | ⟨he,he'⟩⟩ := ha
  · exact (J.shiftLeft_eq_internal h l he.symm).symm.trans
      ((hh l hl).trans (J.shiftRight_eq_internal h l he'.symm))
  · exact (J.shiftRight_eq_internal h l he.symm).symm.trans
      ((hh l hl).symm.trans (J.shiftLeft_eq_internal h l he'.symm))

theorem scalar_constant (hn : 0 < n) (S : Set (Link E n))
    (h : J.Shifts n) (hh : J.ShiftSystem S h) (q : E × Fin n)
    (hnr : ∀ p, ¬ (supportGraph hn J.source J.target S).Reachable (.inr q) (.inl p))
    {q' : E × Fin n}
    (hr : (supportGraph hn J.source J.target S).Reachable (.inr q) (.inr q')) :
    h.2 q = h.2 q' := by
  have walk_prop {v w : Vertex P E n}
      (p : (supportGraph hn J.source J.target S).Walk v w)
      (hv : ∃ qv, v = .inr qv ∧ h.2 q = h.2 qv)
      (hreach : (supportGraph hn J.source J.target S).Reachable (.inr q) v) :
      ∃ qw, w = .inr qw ∧ h.2 q = h.2 qw := by
    induction p with
    | nil => exact hv
    | @cons v u w hadj p ih =>
      obtain ⟨qv,rfl,hv⟩ := hv
      have hu := hreach.trans hadj.reachable
      obtain ⟨qu,rfl⟩ : ∃ qu, u = .inr qu := by
        cases u with
        | inl real => exact (hnr real hu).elim
        | inr qu => exact ⟨qu,rfl⟩
      exact ih ⟨qu,rfl,hv.trans (J.internal_adj_values hn S h hh hadj)⟩ hu
  obtain ⟨qw,he,hh'⟩ := walk_prop hr.some ⟨q,rfl,rfl⟩ (.refl _)
  cases Sum.inr.inj he
  exact hh'
end VariableWL.ProductImages.Instance

namespace VariableWL.ProductImages.Instance
open Subdivision
variable {r n : ℕ} {P : Type uVariable11} {E : Type uVariable12} (J : ProductImages.Instance r P E)

theorem bool_perm_eq_of_apply {f g : Equiv.Perm Bool} {a : Bool}
    (h : f a = g a) : f = g := by
  ext b
  by_cases hb : b = a
  · simpa only [hb] using h
  · have hf : f b ≠ f a := f.injective.ne hb
    have hg : g b ≠ g a := g.injective.ne hb
    rw [h] at hf
    exact (show ∀ x y z : Bool, x ≠ z → y ≠ z → x = y by decide) _ _ _ hf hg

theorem alignment_link (hn : 0 < n) (cut : E → Fin (n+1))
    (l : Link E n) (hc : l.2 ≠ cut l.1) (i : Fin r) :
    J.alignment cut (left J.source l) i =
      J.alignment cut (right J.target l) i * J.transport l i := by
  obtain ⟨a,ha⟩ := J.domain_nonempty l.1 i
  apply bool_perm_eq_of_apply (a := a)
  have he := J.alignment_match hn cut l hc i
    (a := a) (b := if l.2.val = n then J.map l.1 i a else a) ⟨ha,rfl⟩
  by_cases hl : l.2.val = n
  · simpa only [transport, ite_eq_left hl, Equiv.Perm.coe_mul, Function.comp_apply,
      J.ambient_on_domain _ _ _ ha] using he
  · simpa only [transport, ite_eq_right hl, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.refl_apply] using he

theorem relativeAlignment_link (hn : 0 < n) (cut cut' : E → Fin (n+1))
    (l : Link E n) (hc : l.2 ≠ cut l.1) (hc' : l.2 ≠ cut' l.1) (i : Fin r) :
    J.relativeAlignment cut cut' (left J.source l) i =
      J.relativeAlignment cut cut' (right J.target l) i := by
  unfold relativeAlignment
  rw [J.alignment_link hn cut l hc i, J.alignment_link hn cut' l hc' i]
  simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left]

theorem relativeAlignment_reachable (hn : 0 < n) (S : Set (Link E n))
    (cut cut' : E → Fin (n+1))
    (hc : ∀ l ∈ S, l.2 ≠ cut l.1) (hc' : ∀ l ∈ S, l.2 ≠ cut' l.1)
    {v w : Vertex P E n} (h : (supportGraph hn J.source J.target S).Reachable v w)
    (i : Fin r) : J.relativeAlignment cut cut' v i = J.relativeAlignment cut cut' w i := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons ha _ ih =>
    apply Eq.trans _ ih
    obtain ⟨l,hl,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := ha
    · exact J.relativeAlignment_link hn cut cut' l (hc l hl) (hc' l hl) i
    · exact (J.relativeAlignment_link hn cut cut' l (hc l hl) (hc' l hl) i).symm
end VariableWL.ProductImages.Instance

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BlockCoordinates
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.BlockCoordinates.coordinateFintype _root_.OAI.VariableWL.BlockCoordinates.defaultProperNumberings _root_.OAI.VariableWL.Blocks.blockFintype _root_.OAI.VariableWL.Blocks.horizontalFintype _root_.OAI.VariableWL.Blocks.rawValueAddCommGroup _root_.OAI.VariableWL.Blocks.rawValueFintype _root_.OAI.VariableWL.Blocks.readoutValueAddCommGroup _root_.OAI.VariableWL.Blocks.readoutValueFintype _root_.OAI.VariableWL.Blocks.squareFintype _root_.OAI.VariableWL.Blocks.valuationFintype _root_.OAI.VariableWL.Blocks.verticalFintype _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12 uVariable13 uVariable14 uVariable15 uVariable16 uVariable17 uVariable18 uVariable19 uVariable20 uVariable21

namespace VariableWL.Subdivision
variable {P : Type uVariable1} {E : Type uVariable2} {n : ℕ}

theorem realFree_reachable_wire (hn : 0 < n) (src dst : E → P)
    (S : Set (Link E n)) (q : E × Fin n)
    (hnr : ∀ p, ¬ (supportGraph hn src dst S).Reachable (.inr q) (.inl p))
    {v : Vertex P E n} (hr : (supportGraph hn src dst S).Reachable (.inr q) v) :
    ∃ j, v = .inr (q.1,j) := by
  have aux {u v : Vertex P E n} (p : (supportGraph hn src dst S).Walk u v)
      (hu : ∃ j, u = .inr (q.1,j))
      (hreach : (supportGraph hn src dst S).Reachable (.inr q) u) :
      ∃ j, v = .inr (q.1,j) := by
    induction p with
    | nil => exact hu
    | @cons u v w ha p ih =>
      obtain ⟨i,rfl⟩ := hu
      have hv := hreach.trans ha.reachable
      obtain ⟨q',rfl⟩ : ∃ q', v = .inr q' := by
        cases v with
        | inl real => exact (hnr real hv).elim
        | inr q' => exact ⟨q',rfl⟩
      have hw := internal_adj_wire hn src dst S ha
      exact ih ⟨q'.2, by rw [hw]⟩ hv
  exact aux hr.some ⟨q.2,rfl⟩ (.refl _)
end VariableWL.Subdivision

namespace VariableWL.Markers
open scoped CharTwo
variable {V : Type uVariable3} {G H : SimpleGraph V}

theorem exists_nonzero_edge (ω : V → V → Bit) {u v : V} (p : G.Walk u v)
    (hp : walkSum ω p ≠ 0) :
    ∃ x y, G.Reachable u x ∧ G.Adj x y ∧ ω x y ≠ 0 := by
  induction p with
  | nil => exact (hp rfl).elim
  | @cons u v w ha p ih =>
    by_cases he : ω u v = 0
    · obtain ⟨x,y,hx,hy,hh⟩ := ih (by simpa only [walkSum_cons, he, zero_add] using hp)
      exact ⟨x,y,ha.reachable.trans hx,hy,hh⟩
    · exact ⟨u,v,.refl _,ha,he⟩
end VariableWL.Markers

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable4} {E : Type uVariable5} (J : ProductImages.Instance r P E)

theorem readout_reachable (hr : 2 ≤ r) (hn : 0 < n) (U : Set (Block (n := n) J))
    {b : Block (n := n) J} (hb : b ∈ U) {a : Readout r n P E}
    (ha : HasReadout J b.val a) :
    (diagram J hr hn U).Reachable (anchor J b.val) (end0 J a) ∧
      (diagram J hr hn U).Reachable (anchor J b.val) (end1 J a) := by
  obtain ⟨b,hb'⟩ := b
  cases b with
  | inl h =>
    cases ha
    exact ⟨.refl _, (readout_adj J hr hn U hb rfl).reachable⟩
  | inr s =>
    have hL := (readout_adj J hr hn U hb (Or.inl rfl)).reachable
    have hR := (readout_adj J hr hn U hb (Or.inr (Or.inl rfl))).reachable
    have hB := (readout_adj J hr hn U hb (Or.inr (Or.inr (Or.inl rfl)))).reachable
    have hT := (readout_adj J hr hn U hb (Or.inr (Or.inr (Or.inr rfl)))).reachable
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨.refl _,hL⟩
    · exact ⟨hB,hB.trans hR⟩
    · exact ⟨.refl _,hB⟩
    · exact ⟨hL,hL.trans hT⟩

theorem wrapping_connected (hr : 3 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) {marked : Fin r}
    (hw : (rowDiagram J hr hn U).Wraps marked) (hc : U.card = r) :
    ∃ root : Corner r n P E, ∀ b ∈ U,
      (diagram J (by omega) hn U).Reachable root (anchor J b.val) := by
  classical
  have : NeZero r := ⟨by omega⟩
  have hi := wrapping_row_injective J hr hn U hw hc
  obtain ⟨root,p,hp⟩ := hw
  refine ⟨root, ?_⟩
  intro b hb
  have hpar := (rowDiagram J hr hn U).row_parity_all
    Wrapping.RowDiagram.finRotate_orbit p (row b.val) marked
  obtain ⟨u,v,hu,hv,he⟩ := Markers.exists_nonzero_edge _ p
    (show Markers.walkSum ((rowDiagram J hr hn U).rowWeight (row b.val)) p ≠ 0 by
      rw [hpar,hp]; exact one_ne_zero)
  have htag : horizontalTag u v = some (row b.val) := by
    by_contra hh
    exact he (ite_eq_right hh)
  obtain ⟨b',hb',a,ha,heq⟩ := hv
  have haRow : row b'.val = row b.val := by
    have ht : Sum.elim (fun h => some h.row) (fun _ => none) a = some (row b.val) := by
      rcases heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · have hh := (horizontalTag_readout J hr a).1.symm.trans htag
        cases a <;> exact hh
      · have hh := (horizontalTag_readout J hr a).2.symm.trans htag
        cases a <;> exact hh
    cases a with
    | inr a => cases ht
    | inl a => exact (hasReadout_horizontal_row J ha).symm.trans (Option.some.inj ht)
  have hbb : b' = b := hi hb' hb haRow
  subst b'
  obtain ⟨h0,h1⟩ := readout_reachable J (by omega) hn U hb ha
  rcases heq with ⟨rfl,_⟩ | ⟨rfl,_⟩
  · exact hu.trans h0.symm
  · exact hu.trans h1.symm
end VariableWL.Blocks

namespace VariableWL.ProductImages.Instance
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable6} {E : Type uVariable7} (J : ProductImages.Instance r P E)

theorem lift_scalar_to_cut (hn : 0 < n) (Q : J.Witness)
    (S : Set (Link E n)) (cut : E → Fin (n+1))
    (hc : ∀ l ∈ S, l.2 ≠ cut l.1) (q : E × Fin n)
    (a : Address r) (ha : J.Allowed q.1 a) {b : Bit}
    (hb : b ∈ Q.wireValues q.1 a) :
    ∃ g : J.Shifts n, J.ShiftSystem S g ∧ g.2 q = b ∧
      ∀ p, (supportGraph hn J.source J.target S).Reachable (.inr q) (.inl p) →
        g.1 p ∈ Q.values p (fun i => J.alignment cut (.inr q) i (a i)) := by
  classical
  by_cases hj : q.2.val < (cut q.1).val
  · obtain ⟨v,hv,hvb⟩ := Q.lift_left q.1 a hb
    let values : ∀ p, Vec (J.dimension p) := Function.update (fun _ => 0) (J.source q.1) v
    have hval : values (J.source q.1) = v := Function.update_self _ _ _
    refine ⟨J.cutShifts cut values, fun l hl => J.cutShifts_equation hn cut values l (hc l hl), ?_, ?_⟩
    · simpa only [cutShifts, ite_eq_left hj, hval] using hvb
    · intro p hp
      have ho := owner_walk hn J.source J.target S cut hc hp.some
      have he : J.source q.1 = p := by simpa only [owner, ite_eq_left hj] using ho
      subst p
      simpa only [cutShifts, hval, alignment, ite_eq_left hj, Equiv.refl_apply] using hv
  · obtain ⟨v,hv,hvb⟩ := Q.lift_right q.1 a ha hb
    let values : ∀ p, Vec (J.dimension p) := Function.update (fun _ => 0) (J.target q.1) v
    have hval : values (J.target q.1) = v := Function.update_self _ _ _
    refine ⟨J.cutShifts cut values, fun l hl => J.cutShifts_equation hn cut values l (hc l hl), ?_, ?_⟩
    · simpa only [cutShifts, ite_eq_right hj, hval] using hvb
    · intro p hp
      have ho := owner_walk hn J.source J.target S cut hc hp.some
      have he : J.target q.1 = p := by simpa only [owner, ite_eq_right hj] using ho
      subst p
      have had : (fun i => J.alignment cut (.inr q) i (a i)) = J.mapAddress q.1 a := by
        funext i
        simp only [alignment, ite_eq_right hj, mapAddress, J.ambient_on_domain _ _ _ (ha i)]
      simpa only [cutShifts, hval, had] using hv

theorem agree_from_real [DecidableEq E] (hn : 0 < n)
    (S : Finset (Link E n)) (hS : S.card < n+1) {h g : J.Shifts n}
    (hh : J.ShiftSystem S h) (hg : J.ShiftSystem S g) (p : P)
    (he : h.1 p = g.1 p) {v : Vertex P E n}
    (hv : (supportGraph hn J.source J.target S).Reachable (.inl p) v) :
    J.AgreeAt h g v := by
  apply J.agree_reachable hn S hh hg (.inl p) he _ hv
  intro p' hp'
  have hpp := at_most_one_real hn J.source J.target S hS hp'
  subst p'
  exact he

theorem agree_from_internal (hn : 0 < n) (S : Set (Link E n))
    {h g : J.Shifts n} (hh : J.ShiftSystem S h) (hg : J.ShiftSystem S g)
    (q : E × Fin n) (he : h.2 q = g.2 q)
    (hnr : ∀ p, ¬ (supportGraph hn J.source J.target S).Reachable (.inr q) (.inl p))
    {v : Vertex P E n} (hv : (supportGraph hn J.source J.target S).Reachable (.inr q) v) :
    J.AgreeAt h g v :=
  J.agree_reachable hn S hh hg (.inr q) he (fun p hp => (hnr p hp).elim) hv
end VariableWL.ProductImages.Instance

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable8} {E : Type uVariable9} (J : ProductImages.Instance r P E)

theorem componentBlocks_subset (hr : 2 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (c : (diagram J hr hn U).ConnectedComponent) :
    componentBlocks J hr hn U c ⊆ U := by
  intro b hb
  exact ((mem_componentBlocks J hr hn U c b).mp hb).1

theorem readout_component (hr : 2 ≤ r) (hn : 0 < n) (U : Set (Block (n := n) J))
    {b : Block (n := n) J} (hb : b ∈ U) {a : Readout r n P E}
    (ha : HasReadout J b.val a) :
    (diagram J hr hn U).connectedComponentMk (anchor J b.val) =
      (diagram J hr hn U).connectedComponentMk (end0 J a) ∧
    (diagram J hr hn U).connectedComponentMk (anchor J b.val) =
      (diagram J hr hn U).connectedComponentMk (end1 J a) := by
  obtain ⟨h0,h1⟩ := readout_reachable J hr hn U hb ha
  exact ⟨SimpleGraph.ConnectedComponent.sound h0, SimpleGraph.ConnectedComponent.sound h1⟩

theorem component_adj (hr : 2 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (c : (diagram J hr hn U).ConnectedComponent)
    {v w : Corner r n P E} (hv : (diagram J hr hn U).connectedComponentMk v = c)
    (ha : (diagram J hr hn U).Adj v w) :
    (diagram J hr hn (componentBlocks J hr hn U c)).Adj v w := by
  obtain ⟨b,hb,a,hb',he⟩ := ha
  have hc : (diagram J hr hn U).connectedComponentMk (anchor J b.val) = c := by
    obtain ⟨h0,h1⟩ := readout_component J hr hn U hb hb'
    rcases he with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact h0.trans hv
    · exact h1.trans hv
  exact ⟨b, (mem_componentBlocks J hr hn U c b).mpr ⟨hb,hc⟩,a,hb',he⟩

theorem component_reachable (hr : 2 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (c : (diagram J hr hn U).ConnectedComponent)
    {v w : Corner r n P E} (hv : (diagram J hr hn U).connectedComponentMk v = c)
    (hw : (diagram J hr hn U).Reachable v w) :
    (diagram J hr hn (componentBlocks J hr hn U c)).Reachable v w := by
  obtain ⟨p⟩ := hw
  induction p with
  | nil => exact .refl _
  | cons ha p ih =>
    have hv' := (SimpleGraph.ConnectedComponent.sound ha.reachable).symm.trans hv
    exact (component_adj J hr hn U c hv ha).reachable.trans (ih hv')

theorem component_anchors_connected (hr : 2 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (c : (diagram J hr hn U).ConnectedComponent)
    {b b' : Block (n := n) J} (hb : b ∈ componentBlocks J hr hn U c)
    (hb' : b' ∈ componentBlocks J hr hn U c) :
    (diagram J hr hn (componentBlocks J hr hn U c)).Reachable
      (anchor J b.val) (anchor J b'.val) := by
  have hb0 := ((mem_componentBlocks J hr hn U c b).mp hb).2
  have hb1 := ((mem_componentBlocks J hr hn U c b').mp hb').2
  exact component_reachable J hr hn U c hb0 (SimpleGraph.ConnectedComponent.exact (hb0.trans hb1.symm))

end VariableWL.Blocks

namespace VariableWL.Subdivision
variable {P : Type uVariable10} {E : Type uVariable11} {A : Type uVariable12} {n : ℕ}

theorem internal_reachable_invariant (hn : 0 < n) (src dst : E → P)
    (S : Set (Link E n)) (F : E × Fin n → A)
    (hF : ∀ q q', (supportGraph hn src dst S).Adj (.inr q) (.inr q') → F q = F q')
    (q : E × Fin n)
    (hnr : ∀ p, ¬ (supportGraph hn src dst S).Reachable (.inr q) (.inl p))
    {q' : E × Fin n} (hr : (supportGraph hn src dst S).Reachable (.inr q) (.inr q')) :
    F q = F q' := by
  have aux {u v : Vertex P E n} (p : (supportGraph hn src dst S).Walk u v)
      (hu : ∃ qu, u = .inr qu ∧ F q = F qu)
      (hreach : (supportGraph hn src dst S).Reachable (.inr q) u) :
      ∃ qv, v = .inr qv ∧ F q = F qv := by
    induction p with
    | nil => exact hu
    | @cons u v w ha p ih =>
      obtain ⟨qu,rfl,hu⟩ := hu
      have hv := hreach.trans ha.reachable
      obtain ⟨qv,rfl⟩ : ∃ qv, v = .inr qv := by
        cases v with
        | inl real => exact (hnr real hv).elim
        | inr qv => exact ⟨qv,rfl⟩
      exact ih ⟨qv,rfl,hu.trans (hF qu qv ha)⟩ hv
  obtain ⟨qv,he,hh⟩ := aux hr.some ⟨q,rfl,rfl⟩ (.refl _)
  cases Sum.inr.inj he
  exact hh
end VariableWL.Subdivision

namespace VariableWL.ProductImages.Instance
open Subdivision
variable {r n : ℕ} {P : Type uVariable13} {E : Type uVariable14} (J : ProductImages.Instance r P E)

theorem alignment_internal_adj (hn : 0 < n) (S : Set (Link E n))
    (cut : E → Fin (n+1)) (hc : ∀ l ∈ S, l.2 ≠ cut l.1)
    {q q' : E × Fin n} (ha : (supportGraph hn J.source J.target S).Adj (.inr q) (.inr q'))
    (i : Fin r) : J.alignment cut (.inr q) i = J.alignment cut (.inr q') i := by
  obtain ⟨l,hl,⟨he,he'⟩ | ⟨he,he'⟩⟩ := ha
  · have hlast : l.2.val ≠ n := by
      intro h; simp only [right, dite_eq_left h] at he'; cases he'
    have h := J.alignment_link hn cut l (hc l hl) i
    simpa only [← he, ← he', transport, ite_eq_right hlast,
      show Equiv.refl Bool = (1 : Equiv.Perm Bool) from rfl, mul_one] using h
  · have hlast : l.2.val ≠ n := by
      intro h; simp only [right, dite_eq_left h] at he; cases he
    have h := J.alignment_link hn cut l (hc l hl) i
    simpa only [← he, ← he', transport, ite_eq_right hlast,
      show Equiv.refl Bool = (1 : Equiv.Perm Bool) from rfl, mul_one] using h.symm

theorem alignment_internal_reachable (hn : 0 < n) (S : Set (Link E n))
    (cut : E → Fin (n+1)) (hc : ∀ l ∈ S, l.2 ≠ cut l.1) (q : E × Fin n)
    (hnr : ∀ p, ¬ (supportGraph hn J.source J.target S).Reachable (.inr q) (.inl p))
    {q' : E × Fin n} (hr : (supportGraph hn J.source J.target S).Reachable (.inr q) (.inr q'))
    (i : Fin r) : J.alignment cut (.inr q) i = J.alignment cut (.inr q') i :=
  internal_reachable_invariant hn J.source J.target S (fun q => J.alignment cut (.inr q) i)
    (fun _ _ h => J.alignment_internal_adj hn S cut hc h i) q hnr hr
end VariableWL.ProductImages.Instance

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable15} {E : Type uVariable16} (J : ProductImages.Instance r P E)

theorem type_has_horizontal (b : RawBlock r n P E) {t : Vertex P E n}
    (ht : t ∈ typesOf J b) : ∃ h : Horizontal r n P E,
      HasReadout J b (.inl h) ∧ h.type = t := by
  classical
  cases b with
  | inl h =>
    have he : t = h.type := by simpa only [typesOf, Finset.mem_singleton] using ht
    exact ⟨h,rfl,he.symm⟩
  | inr s =>
    simp only [typesOf, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact ⟨squareLeft J s,Or.inl rfl,rfl⟩
    · exact ⟨squareRight J s,Or.inr (Or.inl rfl),rfl⟩

theorem anchor_mem_types (b : RawBlock r n P E) : (anchor J b).2.1 ∈ typesOf J b := by
  classical
  cases b <;> simp [anchor, typesOf, end0, squareLeft]

theorem supportLinks_endpoints (U : Finset (Block (n := n) J)) {l : Link E n}
    (hl : l ∈ supportLinks J U) :
    left J.source l ∈ supportTypes J U ∧ right J.target l ∈ supportTypes J U := by
  classical
  obtain ⟨b,hb,hl⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨b,hvalid⟩ := b
  cases b with
  | inl h => simp [linksOf] at hl
  | inr s =>
    have he : l = s.link := by simpa only [linksOf, Finset.mem_singleton] using hl
    subst l
    constructor <;> apply Finset.mem_biUnion.mpr ⟨⟨.inr s,hvalid⟩,hb,?_⟩ <;> simp [typesOf]

theorem support_reachable_mem (hn : 0 < n) (U : Finset (Block (n := n) J))
    {v w : Vertex P E n} (hv : v ∈ supportTypes J U)
    (hw : (supportGraph hn J.source J.target (supportLinks J U)).Reachable v w) :
    w ∈ supportTypes J U := by
  obtain ⟨p⟩ := hw
  induction p with
  | nil => exact hv
  | cons ha p ih =>
    apply ih
    obtain ⟨l,hl,⟨_,rfl⟩ | ⟨_,rfl⟩⟩ := ha
    · exact (supportLinks_endpoints J U hl).2
    · exact (supportLinks_endpoints J U hl).1

theorem support_types_connected (hr : 2 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J))
    (hconn : ∀ b ∈ U, ∀ b' ∈ U, (diagram J hr hn U).Reachable (anchor J b.val) (anchor J b'.val))
    {v w : Vertex P E n} (hv : v ∈ supportTypes J U) (hw : w ∈ supportTypes J U) :
    (supportGraph hn J.source J.target (supportLinks J U)).Reachable v w := by
  classical
  obtain ⟨b,hb,hv⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨b',hb',hw⟩ := Finset.mem_biUnion.mp hw
  obtain ⟨h,hh,rfl⟩ := type_has_horizontal J b.val hv
  obtain ⟨h',hh',rfl⟩ := type_has_horizontal J b'.val hw
  have h0 := (readout_reachable J hr hn U hb hh).1
  have h1 := (readout_reachable J hr hn U hb' hh').1
  exact projection_reachable J hr hn U ((h0.symm.trans (hconn b hb b' hb')).trans h1)

theorem anchor_label_allowed (b : Block (n := n) J) :
    (anchor J b.val).2.2 ∈ J.labels (anchor J b.val).2.1 (row b.val) := by
  obtain ⟨b,hb⟩ := b
  cases b with
  | inl h => exact hb.1
  | inr s => exact J.matches_left s.link s.row ⟨hb.1,rfl⟩

theorem firstLabel_anchor (cut : E → Fin (n+1)) (b : RawBlock r n P E) :
    firstLabel J cut b = J.alignment cut (anchor J b).2.1 (row b) (anchor J b).2.2 := by
  cases b <;> rfl

end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision
variable {r n : ℕ} {P : Type uVariable17} {E : Type uVariable18} (J : ProductImages.Instance r P E)

theorem wrapping_address_allowed (hr : 3 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (cut : E → Fin (n+1))
    (hc : ∀ l ∈ supportLinks J U, l.2 ≠ cut l.1)
    {marked : Fin r} (hw : (rowDiagram J hr hn U).Wraps marked) (hcard : U.card = r)
    (q : E × Fin n) (hq : (.inr q : Vertex P E n) ∈ supportTypes J U)
    (hnr : ∀ p, (.inl p : Vertex P E n) ∉ supportTypes J U)
    {a : Fin r → Bool} (ha : Recovers J cut U a) :
    J.Allowed q.1 (addressAt J cut a (.inr q)) := by
  classical
  have : NeZero r := ⟨by omega⟩
  obtain ⟨root,hroot⟩ := wrapping_connected J hr hn U hw hcard
  have hconn : ∀ b ∈ U, ∀ b' ∈ U,
      (diagram J (by omega) hn U).Reachable (anchor J b.val) (anchor J b'.val) :=
    fun b hb b' hb' => (hroot b hb).symm.trans (hroot b' hb')
  have hnr' : ∀ p, ¬ (supportGraph hn J.source J.target (supportLinks J U)).Reachable
      (.inr q) (.inl p) := fun p hp => hnr p (support_reachable_mem J hn U hq hp)
  intro i
  obtain ⟨b,hb,hi⟩ := Finset.mem_image.mp ((rowDiagram J hr hn U).covers_rows U
    (fun b => row b.val) (fun _ _ h _ hi => row_cover J hr hn U h hi)
    Wrapping.RowDiagram.finRotate_orbit hw i)
  have ht : (anchor J b.val).2.1 ∈ supportTypes J U :=
    Finset.mem_biUnion.mpr ⟨b,hb,anchor_mem_types J b.val⟩
  have hreach := support_types_connected J (by omega) hn U hconn hq ht
  obtain ⟨j,he⟩ := realFree_reachable_wire hn J.source J.target (supportLinks J U) q hnr' hreach
  have hal := J.alignment_internal_reachable hn (supportLinks J U) cut hc q hnr'
    (he ▸ hreach) i
  have hal' : J.alignment cut (.inr q) i = J.alignment cut (anchor J b.val).2.1 i := by
    simpa only [he] using hal
  have hlabel := anchor_label_allowed J b
  rw [hi, he] at hlabel
  change (J.alignment cut (.inr q) i).symm (a i) ∈ J.domain q.1 i
  rw [hal', ← hi, ← (ha b hb).1, firstLabel_anchor, Equiv.symm_apply_apply]
  simpa only [hi, ProductImages.Instance.labels] using hlabel

theorem permutation_coordinates {A : Type uVariable19} (f g f' g' : Equiv.Perm A)
    (h : f * g⁻¹ = f' * g'⁻¹) (x : A) : f.symm (f' x) = g.symm (g' x) := by
  have he := congrArg (fun p : Equiv.Perm A => f⁻¹ * p * g') h
  have hfg : g⁻¹ * g' = f⁻¹ * f' := by simpa only [mul_assoc, inv_mul_cancel_left,
    inv_mul_cancel, mul_one] using he
  exact congrArg (fun e : Equiv.Perm A => e x) hfg.symm

theorem recovered_overlap (hr : 3 ≤ r) (hn : 0 < n)
    (U W W' : Finset (Block (n := n) J)) (cut : E → Fin (n+1))
    (hW : W ⊆ U) (hW' : W' ⊆ U) (hU : U.card ≤ r+1)
    (hcW : W.card = r) (hcW' : W'.card = r)
    {marked : Fin r} (hw : (rowDiagram J hr hn W).Wraps marked)
    {a a' : Fin r → Bool} (ha : Recovers J cut W a) (ha' : Recovers J cut W' a') : a = a' := by
  classical
  apply Wrapping.overlap_address_unique (finRotate r) (Wrapping.finRotate_no_fixed (by omega))
    U W W' (fun b => row b.val) hW hW' (by simpa using hU)
    (by simpa using hcW) (by simpa using hcW')
    (wrapping_row_injective J hr hn W hw hcW) a a'
  intro b hb
  obtain ⟨hb,hb'⟩ := Finset.mem_inter.mp hb
  exact ⟨(ha b hb).1.symm.trans (ha' b hb').1, (ha b hb).2.symm.trans (ha' b hb').2⟩
end VariableWL.Blocks

namespace VariableWL.ProductImages.Instance
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable20} {E : Type uVariable21} (J : ProductImages.Instance r P E)

theorem scalar_image_of_real (hn : 0 < n) (Q : J.Witness)
    (S : Finset (Link E n)) (hS : S.card < n+1) (cut : E → Fin (n+1))
    (hc : ∀ l ∈ S, l.2 ≠ cut l.1) (h : J.Shifts n) (hh : J.ShiftSystem S h)
    (q : E × Fin n) (p : P)
    (hp : (supportGraph hn J.source J.target S).Reachable (.inr q) (.inl p))
    (a : Address r) (ha : J.Allowed q.1 a)
    (hreal : h.1 p ∈ Q.values p (fun i => J.alignment cut (.inr q) i (a i))) :
    h.2 q ∈ Q.wireValues q.1 a := by
  classical
  have hg : J.ShiftSystem S (J.cutShifts cut h.1) := fun l hl =>
    J.cutShifts_equation hn cut h.1 l (hc l hl)
  have he := J.agree_from_real hn S hS hh hg p rfl hp.symm
  change h.2 q = (J.cutShifts cut h.1).2 q at he
  rw [he]
  have ho := owner_walk hn J.source J.target S cut hc hp.some
  by_cases hj : q.2.val < (cut q.1).val
  · have hpe : J.source q.1 = p := by simpa only [owner, ite_eq_left hj] using ho
    subst p
    have hmem : h.1 (J.source q.1) ∈ Q.values (J.source q.1) a := by
      simpa only [alignment, ite_eq_left hj, Equiv.refl_apply] using hreal
    exact ⟨h.1 (J.source q.1),hmem, by simp only [cutShifts, ite_eq_left hj]⟩
  · have hpe : J.target q.1 = p := by simpa only [owner, ite_eq_right hj] using ho
    subst p
    have had : (fun i => J.alignment cut (.inr q) i (a i)) = J.mapAddress q.1 a := by
      funext i
      simp only [alignment, ite_eq_right hj, mapAddress, J.ambient_on_domain _ _ _ (ha i)]
    rw [had] at hreal
    rw [← Q.right_image q.1 a ha]
    exact ⟨h.1 (J.target q.1),hreal, by simp only [cutShifts, ite_eq_right hj]⟩
end VariableWL.ProductImages.Instance

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BlockExtensions
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.BlockCoordinates.coordinateFintype _root_.OAI.VariableWL.BlockCoordinates.defaultProperNumberings _root_.OAI.VariableWL.Blocks.blockFintype _root_.OAI.VariableWL.Blocks.horizontalFintype _root_.OAI.VariableWL.Blocks.rawValueAddCommGroup _root_.OAI.VariableWL.Blocks.rawValueFintype _root_.OAI.VariableWL.Blocks.readoutValueAddCommGroup _root_.OAI.VariableWL.Blocks.readoutValueFintype _root_.OAI.VariableWL.Blocks.squareFintype _root_.OAI.VariableWL.Blocks.valuationFintype _root_.OAI.VariableWL.Blocks.verticalFintype _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E)

theorem supportLinks_mono {C D : Finset (Block (n := n) J)} (h : C ⊆ D) :
    supportLinks J C ⊆ supportLinks J D := by
  classical
  exact Finset.biUnion_subset_biUnion_of_subset_left _ h

theorem supportTypes_mono {C D : Finset (Block (n := n) J)} (h : C ⊆ D) :
    supportTypes J C ⊆ supportTypes J D := by
  classical
  exact Finset.biUnion_subset_biUnion_of_subset_left _ h

theorem avoids_mono {C D : Finset (Block (n := n) J)} (h : C ⊆ D)
    {cut : E → Fin (n+1)} (ha : Avoids J cut D) : Avoids J cut C :=
  fun l hl => ha l (supportLinks_mono J h hl)

theorem supportTypes_nonempty {C : Finset (Block (n := n) J)} (hC : C.Nonempty) :
    (supportTypes J C).Nonempty := by
  classical
  obtain ⟨b,hb⟩ := hC
  exact ⟨(anchor J b.val).2.1, Finset.mem_biUnion.mpr ⟨b,hb,anchor_mem_types J b.val⟩⟩

theorem support_noReal_reach (hn : 0 < n) (C : Finset (Block (n := n) J))
    (hnr : NoReal J C) {t : Vertex P E n} (ht : t ∈ supportTypes J C) :
    ∀ p, ¬ (supportGraph hn J.source J.target (supportLinks J C)).Reachable t (.inl p) :=
  fun p hp => hnr p (support_reachable_mem J hn C ht hp)

theorem component_support_connected (hr : 2 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (c : (diagram J hr hn U).ConnectedComponent) :
    SupportConnected J hn (componentBlocks J hr hn U c) := by
  intro t ht u hu
  exact support_types_connected J hr hn _
    (fun _ hb _ hb' => component_anchors_connected J hr hn U c hb hb') ht hu

theorem internal_same_address (hn : 0 < n) (C : Finset (Block (n := n) J))
    (hC : SupportConnected J hn C) (hnr : NoReal J C)
    (cut : E → Fin (n+1)) (hc : Avoids J cut C) (a : Address r)
    {q q' : E × Fin n} (hq : Sum.inr q ∈ supportTypes J C)
    (hq' : Sum.inr q' ∈ supportTypes J C) :
    q.1 = q'.1 ∧ addressAt J cut a (.inr q) = addressAt J cut a (.inr q') := by
  have hp := hC _ hq _ hq'
  have hnq := support_noReal_reach J hn C hnr hq
  obtain ⟨j,he⟩ := realFree_reachable_wire hn J.source J.target (supportLinks J C) q hnq hp
  have heP : q' = (q.1,j) := Sum.inr.inj he
  have hqq := congrArg Prod.fst heP
  refine ⟨hqq.symm, ?_⟩
  funext i
  have hh := J.alignment_internal_reachable hn (supportLinks J C) cut hc q hnq
    (he ▸ hp) i
  have hh' : J.alignment cut (.inr q) i = J.alignment cut (.inr q') i := by
    simpa only [he] using hh
  simp only [addressAt, hh']

theorem wrapping_address_allowed_superset (hr : 3 ≤ r) (hn : 0 < n)
    (C W : Finset (Block (n := n) J)) (hW : W ⊆ C)
    (hC : SupportConnected J hn C) (hnr : NoReal J C)
    (cut : E → Fin (n+1)) (hc : Avoids J cut C)
    {marked : Fin r} (hw : (rowDiagram J hr hn W).Wraps marked) (hcard : W.card = r)
    {a : Address r} (ha : Recovers J cut W a) {q : E × Fin n}
    (hq : Sum.inr q ∈ supportTypes J C) : J.Allowed q.1 (addressAt J cut a (.inr q)) := by
  have hne : W.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨t,ht⟩ := supportTypes_nonempty J hne
  obtain ⟨q',rfl⟩ : ∃ q', t = Sum.inr q' := by
    cases t with
    | inl p => exact (hnr p (supportTypes_mono J hW ht)).elim
    | inr q' => exact ⟨q',rfl⟩
  have had := wrapping_address_allowed J hr hn W cut (avoids_mono J hW hc)
    hw hcard q' ht (fun p hp => hnr p (supportTypes_mono J hW hp)) ha
  obtain ⟨he,he'⟩ := internal_same_address J hn C hC hnr cut hc a hq
    (supportTypes_mono J hW ht)
  rw [he,he']
  exact had

theorem admissible_of_one (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (cut : E → Fin (n+1)) (C W : Finset (Block (n := n) J)) (hC : C.card ≤ r+1)
    (hW : W ⊆ C) (hcard : W.card = r) (hw : (rowDiagram J hr hn W).Wraps marked)
    (a : Address r) (ha : Recovers J cut W a) (h : J.Shifts n)
    (hs : J.ShiftSystem (supportLinks J C) h) (had : AddressCondition J Q cut C a h) :
    Admissible J hr hn marked Q cut C h := by
  refine ⟨hs, ?_⟩
  intro W' hW' hcW' hw' a' ha'
  have he := recovered_overlap J hr hn C W W' cut hW hW' hC hcard hcW' hw ha ha'
  subst a'
  exact had

theorem addressCondition_exists (hn : 0 < n) (Q : J.Witness)
    (C : Finset (Block (n := n) J)) (hC : SupportConnected J hn C)
    (cut : E → Fin (n+1)) (hc : Avoids J cut C) (a : Address r) :
    ∃ h : J.Shifts n, J.ShiftSystem (supportLinks J C) h ∧ AddressCondition J Q cut C a h := by
  classical
  choose v hv using Q.nonempty
  let h := J.cutShifts cut (fun p => v p a)
  have hh : J.ShiftSystem (supportLinks J C) h :=
    fun l hl => J.cutShifts_equation hn cut _ l (hc l hl)
  by_cases hnr : NoReal J C
  · by_cases he : (supportTypes J C).Nonempty
    · obtain ⟨t,ht⟩ := he
      obtain ⟨q,rfl⟩ : ∃ q, t = Sum.inr q := by
        cases t with
        | inl p => exact (hnr p ht).elim
        | inr q => exact ⟨q,rfl⟩
      obtain ⟨b,hb⟩ := Q.wireValues_nonempty q.1 (addressAt J cut a (.inr q))
      obtain ⟨g,hg,hgb⟩ := J.exists_scalar_shift hn (supportLinks J C) (.inr q) b h hh
        (support_noReal_reach J hn C hnr ht)
      refine ⟨g,hg,⟨fun p hp => (hnr p hp).elim, fun _ q' hq' => ?_⟩⟩
      rw [hgb q' (hC _ ht _ hq')]
      obtain ⟨he,ha⟩ := internal_same_address J hn C hC hnr cut hc a ht hq'
      simpa only [he,ha] using hb
    · refine ⟨h,hh,⟨?_, fun _ q hq => (he ⟨.inr q,hq⟩).elim⟩⟩
      intro p hp
      exact (he ⟨.inl p,hp⟩).elim
  · refine ⟨h,hh,⟨?_,fun hh => (hnr hh).elim⟩⟩
    intro p _
    exact hv p a

theorem admissible_exists (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (C : Finset (Block (n := n) J)) (hC : SupportConnected J hn C) (hcard : C.card ≤ r+1)
    (cut : E → Fin (n+1)) (hc : Avoids J cut C) :
    ∃ h : J.Shifts n, Admissible J hr hn marked Q cut C h := by
  classical
  by_cases hw : ∃ W ⊆ C, W.card = r ∧ (rowDiagram J hr hn W).Wraps marked
  · obtain ⟨W,hW,hcW,hw⟩ := hw
    obtain ⟨a,ha⟩ := recovered_address J hr hn W cut (avoids_mono J hW hc) hw hcW
    obtain ⟨h,hs,had⟩ := addressCondition_exists J hn Q C hC cut hc a
    exact ⟨h, admissible_of_one J hr hn marked Q cut C W hcard hW hcW hw a ha h hs had⟩
  · refine ⟨J.cutShifts cut (fun _ => 0), ⟨?_,?_⟩⟩
    · exact fun l hl => J.cutShifts_equation hn cut _ l (hc l hl)
    · intro W hW hcW hwW
      exact (hw ⟨W,hW,hcW,hwW⟩).elim
end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} (J : ProductImages.Instance r P E)

theorem addressAt_cut_independent_superset (hr : 3 ≤ r) (hn : 0 < n)
    (C W : Finset (Block (n := n) J)) (hW : W ⊆ C) (hC : SupportConnected J hn C)
    (cut cut' : E → Fin (n+1)) (hc : Avoids J cut C) (hc' : Avoids J cut' C)
    {marked : Fin r} (hw : (rowDiagram J hr hn W).Wraps marked)
    {a a' : Address r} (ha : Recovers J cut W a) (ha' : Recovers J cut' W a')
    {t : Vertex P E n} (ht : t ∈ supportTypes J C) :
    addressAt J cut a t = addressAt J cut' a' t := by
  classical
  have : NeZero r := ⟨by omega⟩
  funext i
  obtain ⟨b,hb,hi⟩ := Finset.mem_image.mp ((rowDiagram J hr hn W).covers_rows W
    (fun b => row b.val) (fun _ _ h _ hi => row_cover J hr hn W h hi)
    Wrapping.RowDiagram.finRotate_orbit hw i)
  have ht' : (anchor J b.val).2.1 ∈ supportTypes J C :=
    Finset.mem_biUnion.mpr ⟨b,hW hb,anchor_mem_types J b.val⟩
  have hrel := J.relativeAlignment_reachable hn (supportLinks J C) cut cut' hc hc'
    (hC _ ht _ ht') i
  have hp := permutation_coordinates (J.alignment cut t i) (J.alignment cut' t i)
    (J.alignment cut (anchor J b.val).2.1 i) (J.alignment cut' (anchor J b.val).2.1 i)
    hrel (anchor J b.val).2.2
  change (J.alignment cut t i).symm (a i) = (J.alignment cut' t i).symm (a' i)
  rw [← hi, ← (ha b hb).1, ← (ha' b hb).1, firstLabel_anchor, firstLabel_anchor]
  simpa only [hi] using hp

theorem admissible_cut_change (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (C : Finset (Block (n := n) J)) (hC : SupportConnected J hn C)
    (cut cut' : E → Fin (n+1)) (hc : Avoids J cut C) (hc' : Avoids J cut' C)
    {h : J.Shifts n} (hh : Admissible J hr hn marked Q cut C h) :
    Admissible J hr hn marked Q cut' C h := by
  refine ⟨hh.1, ?_⟩
  intro W hW hcW hw a' ha'
  obtain ⟨a,ha⟩ := recovered_address J hr hn W cut (avoids_mono J hW hc) hw hcW
  obtain ⟨hreal,hscalar⟩ := hh.2 W hW hcW hw a ha
  refine ⟨?_,?_⟩
  · intro p hp
    rw [← addressAt_cut_independent_superset J hr hn C W hW hC cut cut' hc hc' hw ha ha' hp]
    exact hreal p hp
  · intro hnr q hq
    rw [← addressAt_cut_independent_superset J hr hn C W hW hC cut cut' hc hc' hw ha ha' hq]
    exact hscalar hnr q hq

theorem admissible_restrict (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (C D : Finset (Block (n := n) J)) (hD : D ⊆ C)
    (hC : SupportConnected J hn C) (hDc : SupportConnected J hn D)
    (hsize : (supportLinks J C).card < n+1)
    (cut : E → Fin (n+1)) (hc : Avoids J cut C)
    {h : J.Shifts n} (hh : Admissible J hr hn marked Q cut C h) :
    Admissible J hr hn marked Q cut D h := by
  classical
  refine ⟨fun l hl => hh.1 l (supportLinks_mono J hD hl), ?_⟩
  intro W hW hcW hw a ha
  obtain ⟨hreal,hscalar⟩ := hh.2 W (hW.trans hD) hcW hw a ha
  refine ⟨fun p hp => hreal p (supportTypes_mono J hD hp), ?_⟩
  intro hnrD q hq
  by_cases hnr : NoReal J C
  · exact hscalar hnr q (supportTypes_mono J hD hq)
  · have hex : ∃ p, Sum.inl p ∈ supportTypes J C := by
      simpa only [NoReal, not_forall, not_not] using hnr
    obtain ⟨p,hp⟩ := hex
    have had := wrapping_address_allowed_superset J hr hn D W hW hDc hnrD cut
      (avoids_mono J hD hc) hw hcW ha hq
    apply J.scalar_image_of_real hn Q (supportLinks J C) hsize cut hc h hh.1 q p
      (hC _ (supportTypes_mono J hD hq) _ hp) (addressAt J cut a (.inr q)) had
    simpa only [addressAt, Equiv.apply_symm_apply, addressAt_real] using hreal p hp
end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} (J : ProductImages.Instance r P E)

theorem admissible_lift (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (C D : Finset (Block (n := n) J)) (hD : D ⊆ C)
    (hC : SupportConnected J hn C) (hDc : SupportConnected J hn D)
    (hcard : C.card ≤ r+1) (hsize : (supportLinks J C).card < n+1)
    (hcardD : D.card = r) (hw : (rowDiagram J hr hn D).Wraps marked)
    (cut : E → Fin (n+1)) (hc : Avoids J cut C)
    {h : J.Shifts n} (hh : Admissible J hr hn marked Q cut D h) :
    ∃ g : J.Shifts n, Admissible J hr hn marked Q cut C g ∧
      ∀ t ∈ supportTypes J D, J.AgreeAt h g t := by
  classical
  obtain ⟨a,ha⟩ := recovered_address J hr hn D cut (avoids_mono J hD hc) hw hcardD
  have had := hh.2 D (Finset.Subset.refl _) hcardD hw a ha
  have hsizeD : (supportLinks J D).card < n+1 :=
    lt_of_le_of_lt (Finset.card_le_card (supportLinks_mono J hD)) hsize
  by_cases hnrD : NoReal J D
  · obtain ⟨t,ht⟩ := supportTypes_nonempty J
      (show D.Nonempty from Finset.card_pos.mp (by omega))
    obtain ⟨q,rfl⟩ : ∃ q, t = Sum.inr q := by
      cases t with
      | inl p => exact (hnrD p ht).elim
      | inr q => exact ⟨q,rfl⟩
    have hqa : J.Allowed q.1 (addressAt J cut a (.inr q)) :=
      wrapping_address_allowed_superset J hr hn D D (Finset.Subset.refl _) hDc hnrD
        cut (avoids_mono J hD hc) hw hcardD ha ht
    obtain ⟨g,hg,hgq,hgreal⟩ := J.lift_scalar_to_cut hn Q (supportLinks J C) cut hc q
      (addressAt J cut a (.inr q)) hqa (had.2 hnrD q ht)
    have hcond : AddressCondition J Q cut C a g := by
      refine ⟨?_,?_⟩
      · intro p hp
        simpa only [addressAt, Equiv.apply_symm_apply, addressAt_real] using
          hgreal p (hC _ (supportTypes_mono J hD ht) _ hp)
      · intro hnrC q' hq'
        have hqC := supportTypes_mono J hD ht
        have he := J.scalar_constant hn (supportLinks J C) g hg q
          (support_noReal_reach J hn C hnrC hqC) (hC _ hqC _ hq')
        rw [← he,hgq]
        obtain ⟨hwire,haddr⟩ := internal_same_address J hn C hC hnrC cut hc a hqC hq'
        simpa only [hwire,haddr] using had.2 hnrD q ht
    refine ⟨g,admissible_of_one J hr hn marked Q cut C D hcard hD hcardD hw a ha g hg hcond,?_⟩
    intro t ht'
    exact J.agree_from_internal hn (supportLinks J D) hh.1
      (fun l hl => hg l (supportLinks_mono J hD hl)) q hgq.symm
      (support_noReal_reach J hn D hnrD ht) (hDc _ ht _ ht')
  · obtain ⟨p,hp⟩ : ∃ p, Sum.inl p ∈ supportTypes J D := by
      simpa only [NoReal, not_forall, not_not] using hnrD
    let g := J.cutShifts cut h.1
    have hg : J.ShiftSystem (supportLinks J C) g :=
      fun l hl => J.cutShifts_equation hn cut h.1 l (hc l hl)
    have hcond : AddressCondition J Q cut C a g := by
      refine ⟨?_,?_⟩
      · intro p' hp'
        have hpp := at_most_one_real hn J.source J.target (supportLinks J C) hsize
          (hC _ (supportTypes_mono J hD hp) _ hp')
        subst p'
        exact had.1 p hp
      · intro hnrC
        exact (hnrC p (supportTypes_mono J hD hp)).elim
    refine ⟨g,admissible_of_one J hr hn marked Q cut C D hcard hD hcardD hw a ha g hg hcond,?_⟩
    intro t ht
    exact J.agree_from_real hn (supportLinks J D) hsizeD hh.1
      (fun l hl => hg l (supportLinks_mono J hD hl)) p rfl (hDc _ hp _ ht)
end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance
variable {r n : ℕ} {P : Type uVariable7} {E : Type uVariable8} (J : ProductImages.Instance r P E)

theorem componentBlocks_map_subset (hr : 2 ≤ r) (hn : 0 < n)
    {V U : Finset (Block (n := n) J)} (h : V ⊆ U)
    (d : (diagram J hr hn V).ConnectedComponent) :
    componentBlocks J hr hn V d ⊆
      componentBlocks J hr hn U (componentMap J hr hn h d) := by
  intro b hb
  obtain ⟨hb,he⟩ := (mem_componentBlocks J hr hn V d b).mp hb
  apply (mem_componentBlocks J hr hn U _ b).mpr
  exact ⟨h hb, (congrArg (componentMap J hr hn h) he)⟩

theorem wrapping_component_all (hr : 3 ≤ r) (hn : 0 < n)
    (V : Finset (Block (n := n) J)) (hV : V.card ≤ r) (marked : Fin r)
    (d : (diagram J (by omega) hn V).ConnectedComponent)
    (hw : (rowDiagram J hr hn (componentBlocks J (by omega) hn V d)).Wraps marked) :
    componentBlocks J (by omega) hn V d = V ∧ V.card = r := by
  have hsub := componentBlocks_subset J (by omega) hn V d
  have hge := wrapping_card_ge J hr hn _ hw
  have hle := Finset.card_le_card hsub
  exact ⟨Finset.eq_of_subset_of_card_le hsub (by omega), by omega⟩

theorem wrapping_component_unique (hr : 3 ≤ r) (hn : 0 < n)
    (V : Finset (Block (n := n) J)) (hV : V.card ≤ r) (marked : Fin r)
    {d d' : (diagram J (by omega) hn V).ConnectedComponent}
    (hw : (rowDiagram J hr hn (componentBlocks J (by omega) hn V d)).Wraps marked)
    (hw' : (rowDiagram J hr hn (componentBlocks J (by omega) hn V d')).Wraps marked) : d = d' := by
  obtain ⟨he,hc⟩ := wrapping_component_all J hr hn V hV marked d hw
  obtain ⟨he',_⟩ := wrapping_component_all J hr hn V hV marked d' hw'
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0 < V.card by omega)
  have hbd : b ∈ componentBlocks J (by omega) hn V d := (Finset.ext_iff.mp he b).mpr hb
  have hbd' : b ∈ componentBlocks J (by omega) hn V d' := (Finset.ext_iff.mp he' b).mpr hb
  exact ((mem_componentBlocks J (by omega) hn V d b).mp hbd).2.symm.trans
    ((mem_componentBlocks J (by omega) hn V d' b).mp hbd').2

theorem vectorShift_agree {h g : J.Shifts n} {t : Vertex P E n}
    (he : J.AgreeAt h g t) : vectorShift J h t = vectorShift J g t := by
  cases t with
  | inl p => exact he
  | inr q => exact congrArg (fun b : Affine.Bit => fun _ : Fin 1 => b) he

theorem potentialValues_shift_agree (marked : Fin r) (h g : J.Shifts n)
    (M : Potentials (n := n) J) (a : Readout r n P E)
    (ha : J.AgreeAt h g (end0 J a).2.1) :
    potentialValues J marked h M a = potentialValues J marked g M a := by
  cases a with
  | inl x =>
    change J.AgreeAt h g x.type at ha
    simp only [potentialValues, vectorShift_agree J ha]
  | inr _ => rfl

theorem potentialValues_potentials_agree (marked : Fin r) (h : J.Shifts n)
    (M N : Potentials (n := n) J) (a : Readout r n P E)
    (he0 : M (end0 J a) = N (end0 J a)) (he1 : M (end1 J a) = N (end1 J a)) :
    potentialValues J marked h M a = potentialValues J marked h N a := by
  cases a with
  | inl x => simp only [potentialValues, end0, end1] at he0 he1 ⊢; rw [he0,he1]
  | inr y => simp only [potentialValues, end0, end1] at he0 he1 ⊢; rw [he0,he1]

theorem readout_type_mem {b : RawBlock r n P E} {a : Readout r n P E}
    (ha : HasReadout J b a) : (end0 J a).2.1 ∈ typesOf J b := by
  classical
  cases b with
  | inl h => cases ha; simp [typesOf, end0]
  | inr s =>
    rcases ha with rfl | rfl | rfl | rfl <;>
      simp [typesOf, end0, squareLeft, squareRight, squareBottom, squareTop]

theorem representedValues_on_block (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
    (U : Finset (Block (n := n) J))
    (h : (diagram J hr hn U).ConnectedComponent → J.Shifts n)
    (M : Potentials (n := n) J) {b : Block (n := n) J} (hb : b ∈ U)
    {a : Readout r n P E} (ha : HasReadout J b.val a) :
    representedValues J hr hn marked U h M a =
      potentialValues J marked (h ((diagram J hr hn U).connectedComponentMk (anchor J b.val))) M a := by
  unfold representedValues
  rw [← (readout_component J hr hn U hb ha).1]

theorem offsetFamily_nonempty (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (marked : Fin r) (Q : J.Witness) (U : Finset (Block (n := n) J)) (hU : U.card ≤ r+1) :
    ∃ F : ReadoutValues (n := n) J, OffsetFamily J hr hn marked Q U F := by
  classical
  obtain ⟨cut,hcut⟩ := exists_unused_cut (supportLinks J U)
    (lt_of_le_of_lt ((supportLinks_card J U).trans hU) hlarge)
  have hc : Avoids J cut U := by
    intro l hl he
    exact hcut l.1 (by simpa only [← he,Prod.eta] using hl)
  have hex (c : (diagram J (by omega) hn U).ConnectedComponent) :=
    admissible_exists J hr hn marked Q (componentBlocks J (by omega) hn U c)
      (component_support_connected J (by omega) hn U c)
      ((Finset.card_le_card (componentBlocks_subset J (by omega) hn U c)).trans hU)
      cut (avoids_mono J (componentBlocks_subset J (by omega) hn U c) hc)
  choose h hh using hex
  refine ⟨representedValues J (by omega) hn marked U h (fun _ => 0), cut,hc,h,(fun _ => 0),hh,?_⟩
  exact fun b hb a ha => representedValues_on_block J (by omega) hn marked U h _ hb ha
end VariableWL.Blocks

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_ExactProjection
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.BlockCoordinates.coordinateFintype _root_.OAI.VariableWL.BlockCoordinates.defaultProperNumberings _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E)

theorem component_links_small (hr : 2 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (U : Finset (Block (n := n) J)) (hU : U.card ≤ r+1)
    (c : (diagram J hr hn U).ConnectedComponent) :
    (supportLinks J (componentBlocks J hr hn U c)).card < n+1 :=
  lt_of_le_of_lt ((supportLinks_card J _).trans
    ((Finset.card_le_card (componentBlocks_subset J hr hn U c)).trans hU)) hlarge

theorem offsetFamily_restrict (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (marked : Fin r) (Q : J.Witness) (U V : Finset (Block (n := n) J))
    (hU : U.card ≤ r+1) (hVU : V ⊆ U) {F : ReadoutValues (n := n) J}
    (hF : OffsetFamily J hr hn marked Q U F) : OffsetFamily J hr hn marked Q V F := by
  classical
  obtain ⟨cut,hc,h,M,hh,hF⟩ := hF
  refine ⟨cut,avoids_mono J hVU hc, fun d => h (componentMap J (by omega) hn hVU d),M,?_,?_⟩
  · intro d
    apply admissible_restrict J hr hn marked Q
      (componentBlocks J (by omega) hn U (componentMap J (by omega) hn hVU d))
      (componentBlocks J (by omega) hn V d)
      (componentBlocks_map_subset J (by omega) hn hVU d)
      (component_support_connected J (by omega) hn U _)
      (component_support_connected J (by omega) hn V d)
      (component_links_small J (by omega) hn hlarge U hU _) cut
      (avoids_mono J (componentBlocks_subset J (by omega) hn U _) hc)
    exact hh _
  · intro b hb a ha
    exact hF b (hVU hb) a ha

theorem choose_extension_shifts (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (marked : Fin r) (Q : J.Witness) (U V : Finset (Block (n := n) J))
    (hU : U.card ≤ r+1) (hV : V.card ≤ r) (hVU : V ⊆ U)
    (cut : E → Fin (n+1)) (hc : Avoids J cut U)
    (h : (diagram J (by omega) hn V).ConnectedComponent → J.Shifts n)
    (hh : ∀ d, Admissible J hr hn marked Q cut (componentBlocks J (by omega) hn V d) (h d)) :
    ∃ g : (diagram J (by omega) hn U).ConnectedComponent → J.Shifts n,
      (∀ c, Admissible J hr hn marked Q cut (componentBlocks J (by omega) hn U c) (g c)) ∧
      ∀ d, (rowDiagram J hr hn (componentBlocks J (by omega) hn V d)).Wraps marked →
        ∀ t ∈ supportTypes J (componentBlocks J (by omega) hn V d),
          J.AgreeAt (h d) (g (componentMap J (by omega) hn hVU d)) t := by
  classical
  have hex (c : (diagram J (by omega) hn U).ConnectedComponent) :
      ∃ g : J.Shifts n, Admissible J hr hn marked Q cut
          (componentBlocks J (by omega) hn U c) g ∧
        ∀ d : (diagram J (by omega) hn V).ConnectedComponent, componentMap J (by omega) hn hVU d = c →
          (rowDiagram J hr hn (componentBlocks J (by omega) hn V d)).Wraps marked →
          ∀ t ∈ supportTypes J (componentBlocks J (by omega) hn V d), J.AgreeAt (h d) g t := by
    by_cases he : ∃ d : (diagram J (by omega) hn V).ConnectedComponent, componentMap J (by omega) hn hVU d = c ∧
        (rowDiagram J hr hn (componentBlocks J (by omega) hn V d)).Wraps marked
    · obtain ⟨d,hd,hw⟩ := he
      have hsub : componentBlocks J (by omega) hn V d ⊆ componentBlocks J (by omega) hn U c := by
        rw [← hd]
        exact componentBlocks_map_subset J (by omega) hn hVU d
      obtain ⟨hall,hcard⟩ := wrapping_component_all J hr hn V hV marked d hw
      obtain ⟨g,hg,hagree⟩ := admissible_lift J hr hn marked Q
        (componentBlocks J (by omega) hn U c) (componentBlocks J (by omega) hn V d)
        hsub (component_support_connected J (by omega) hn U c)
        (component_support_connected J (by omega) hn V d)
        ((Finset.card_le_card (componentBlocks_subset J (by omega) hn U c)).trans hU)
        (component_links_small J (by omega) hn hlarge U hU c)
        ((congrArg Finset.card hall).trans hcard) hw cut
        (avoids_mono J (componentBlocks_subset J (by omega) hn U c) hc) (hh d)
      refine ⟨g,hg,?_⟩
      intro d' _ hw'
      have hdd := wrapping_component_unique J hr hn V hV marked hw hw'
      subst d'
      exact hagree
    · obtain ⟨g,hg⟩ := admissible_exists J hr hn marked Q
        (componentBlocks J (by omega) hn U c) (component_support_connected J (by omega) hn U c)
        ((Finset.card_le_card (componentBlocks_subset J (by omega) hn U c)).trans hU)
        cut (avoids_mono J (componentBlocks_subset J (by omega) hn U c) hc)
      exact ⟨g,hg, fun d hd hw => (he ⟨d,hd,hw⟩).elim⟩
  choose g hg hagree using hex
  exact ⟨g,hg,fun d hw => hagree _ d rfl hw⟩

theorem offsetFamily_extend_strict (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (marked : Fin r) (Q : J.Witness) (U V : Finset (Block (n := n) J))
    (hU : U.card ≤ r+1) (hV : V.card ≤ r) (hVU : V ⊆ U)
    {F : ReadoutValues (n := n) J} (hF : OffsetFamily J hr hn marked Q V F) :
    ∃ G : ReadoutValues (n := n) J, OffsetFamily J hr hn marked Q U G ∧
      ∀ b ∈ V, ∀ a, HasReadout J b.val a → G a = F a := by
  classical
  obtain ⟨cut₀,hc₀,h,M,hh,hF⟩ := hF
  obtain ⟨cut,hcut⟩ := exists_unused_cut (supportLinks J U)
    (lt_of_le_of_lt ((supportLinks_card J U).trans hU) hlarge)
  have hc : Avoids J cut U := by
    intro l hl he
    exact hcut l.1 (by simpa only [← he,Prod.eta] using hl)
  have hh' (d) : Admissible J hr hn marked Q cut (componentBlocks J (by omega) hn V d) (h d) :=
    admissible_cut_change J hr hn marked Q _ (component_support_connected J (by omega) hn V d)
      cut₀ cut (avoids_mono J (componentBlocks_subset J (by omega) hn V d) hc₀)
      (avoids_mono J ((componentBlocks_subset J (by omega) hn V d).trans hVU) hc) (hh d)
  obtain ⟨g,hg,hagree⟩ := choose_extension_shifts J hr hn hlarge marked Q U V hU hV hVU cut hc h hh'
  have hex (d : (diagram J (by omega) hn V).ConnectedComponent) :
      ∃ M' : Potentials (n := n) J, ∀ b ∈ componentBlocks J (by omega) hn V d,
        ∀ a, HasReadout J b.val a →
          potentialValues J marked (g (componentMap J (by omega) hn hVU d)) M' a =
            potentialValues J marked (h d) M a := by
    by_cases hw : (rowDiagram J hr hn (componentBlocks J (by omega) hn V d)).Wraps marked
    · refine ⟨M,?_⟩
      intro b hb a ha
      exact (potentialValues_shift_agree J marked (h d) (g (componentMap J (by omega) hn hVU d)) M a
        (hagree d hw _ (Finset.mem_biUnion.mpr ⟨b,hb,readout_type_mem J ha⟩))).symm
    · apply gauge_nonwrapping J hr hn _ marked (h d) (g (componentMap J (by omega) hn hVU d)) M
        (hh' d).1 _ hw
      intro l hl
      exact (hg _).1 l (supportLinks_mono J (componentBlocks_map_subset J (by omega) hn hVU d) hl)
  choose Ms hMs using hex
  let N : Potentials (n := n) J := fun v => Ms ((diagram J (by omega) hn V).connectedComponentMk v) v
  let G := representedValues J (by omega) hn marked U g N
  refine ⟨G,⟨cut,hc,g,N,hg,?_⟩,?_⟩
  · exact fun b hb a ha => representedValues_on_block J (by omega) hn marked U g N hb ha
  · intro b hb a ha
    let d := (diagram J (by omega) hn V).connectedComponentMk (anchor J b.val)
    have hb' : b ∈ componentBlocks J (by omega) hn V d :=
      (mem_componentBlocks J (by omega) hn V d b).mpr ⟨hb,rfl⟩
    obtain ⟨he0,he1⟩ := readout_component J (by omega) hn V hb ha
    have hN := potentialValues_potentials_agree J marked
      (g (componentMap J (by omega) hn hVU d)) N (Ms d) a
      (show N (end0 J a) = Ms d (end0 J a) by dsimp only [N,d]; rw [← he0])
      (show N (end1 J a) = Ms d (end1 J a) by dsimp only [N,d]; rw [← he1])
    change representedValues J (by omega) hn marked U g N a = F a
    rw [representedValues_on_block J (by omega) hn marked U g N (hVU hb) ha]
    exact hN.trans ((hMs d b hb' a ha).trans (hF b hb a ha).symm)

theorem offsetFamily_exact_projection (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (marked : Fin r) (Q : J.Witness) (U V : Finset (Block (n := n) J))
    (hU : U.card ≤ r+1) (hVU : V ⊆ U) {F : ReadoutValues (n := n) J} :
    OffsetFamily J hr hn marked Q V F ↔
      ∃ G : ReadoutValues (n := n) J, OffsetFamily J hr hn marked Q U G ∧
        ∀ b ∈ V, ∀ a, HasReadout J b.val a → G a = F a := by
  classical
  constructor
  · intro hF
    by_cases he : V = U
    · subst U
      exact ⟨F,hF,fun _ _ _ _ => rfl⟩
    · apply offsetFamily_extend_strict J hr hn hlarge marked Q U V hU _ hVU hF
      have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hVU,he⟩)
      omega
  · rintro ⟨G,hG,hGF⟩
    obtain ⟨cut,hc,h,M,hh,hrep⟩ := offsetFamily_restrict J hr hn hlarge marked Q U V hU hVU hG
    exact ⟨cut,hc,h,M,hh,fun b hb a ha => (hGF b hb a ha).symm.trans (hrep b hb a ha)⟩
end VariableWL.Blocks

namespace VariableWL.Blocks
open scoped CharTwo
open Subdivision ProductImages.Instance VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} (J : ProductImages.Instance r P E)

theorem valueOfReadouts_carries (F : ReadoutValues (n := n) J)
    {b : RawBlock r n P E} {a : Readout r n P E} (ha : HasReadout J b a) :
    Carries J b (valueOfReadouts J F b) a (F a) := by
  cases b with
  | inl h => cases ha; exact ⟨rfl,HEq.rfl⟩
  | inr s =>
    rcases ha with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨rfl,HEq.rfl⟩
    · exact Or.inr (Or.inl ⟨rfl,HEq.rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl,HEq.rfl⟩))

end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} (J : ProductImages.Instance r P E)

theorem valueOfReadouts_congr {b : RawBlock r n P E} {F G : ReadoutValues (n := n) J}
    (he : ∀ a, HasReadout J b a → F a = G a) : valueOfReadouts J F b = valueOfReadouts J G b := by
  cases b with
  | inl h => exact he _ rfl
  | inr s =>
    dsimp only [valueOfReadouts]
    rw [he _ (Or.inl rfl), he _ (Or.inr (Or.inl rfl)),
      he _ (Or.inr (Or.inr (Or.inl rfl))), he _ (Or.inr (Or.inr (Or.inr rfl)))]

theorem offsetLists_nonempty (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (marked : Fin r) (Q : J.Witness) (U : Finset (Block (n := n) J)) (hU : U.card ≤ r+1) :
    (OffsetLists J hr hn marked Q U).Nonempty := by
  obtain ⟨F,hF⟩ := offsetFamily_nonempty J hr hn hlarge marked Q U hU
  exact ⟨familyList J hr hn marked Q U hF,F,hF,fun _ => rfl⟩

theorem exact_projection (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (marked : Fin r) (Q : J.Witness) (U V : Finset (Block (n := n) J))
    (hU : U.card ≤ r+1) (hVU : V ⊆ U) :
    restrictList J marked hVU '' OffsetLists J hr hn marked Q U = OffsetLists J hr hn marked Q V := by
  ext ξ
  constructor
  · rintro ⟨η,⟨F,hF,hη⟩,rfl⟩
    exact ⟨F,offsetFamily_restrict J hr hn hlarge marked Q U V hU hVU hF,
      fun b => hη ⟨b.val,hVU b.property⟩⟩
  · rintro ⟨F,hF,hξ⟩
    obtain ⟨G,hG,hGF⟩ := (offsetFamily_exact_projection J hr hn hlarge marked Q U V hU hVU).mp hF
    refine ⟨familyList J hr hn marked Q U hG, ⟨G,hG,fun _ => rfl⟩,?_⟩
    funext b
    apply Subtype.ext
    exact (valueOfReadouts_congr J (fun a ha => hGF b.val b.property a ha)).trans (hξ b).symm
end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable7} {E : Type uVariable8} (J : ProductImages.Instance r P E)

theorem readout_valueOfReadouts (hr : 2 ≤ r) (hn : 0 < n)
    (F : ReadoutValues (n := n) J) {b : RawBlock r n P E} {a : Readout r n P E}
    (ha : HasReadout J b a) : readout J (valueOfReadouts J F b) ha = F a :=
  readout_eq J hr hn ha (valueOfReadouts_carries J F ha)

theorem offsetLists_agree (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (U : Finset (Block (n := n) J)) {ξ : ∀ b : ↑U, Valuation J marked 1 b.val}
    (hξ : ξ ∈ OffsetLists J hr hn marked Q U) (b c : ↑U)
    (a : Readout r n P E) (hb : HasReadout J b.val.val a) (hc : HasReadout J c.val.val a) :
    readout J (ξ b).val hb = readout J (ξ c).val hc := by
  obtain ⟨F,hF,hξ⟩ := hξ
  rw [hξ b, hξ c, readout_valueOfReadouts J (by omega) hn,
    readout_valueOfReadouts J (by omega) hn]
end VariableWL.Blocks

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_GeneralGame
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.Game
variable {G H : Graph} {q : ℕ} {B : Type uVariable5} [DecidableEq B]

theorem mem_active (part : Fin G.order → B) (p : Position G H q) (b : B) :
    b ∈ active part p ↔ ∃ i a, p i = some a ∧ part a.1 = b := by
  simp only [active,Finset.mem_eraseNone,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨a,ha,he⟩ := Option.map_eq_some_iff.mp hi
    exact ⟨i,a,ha,he⟩
  · rintro ⟨i,a,ha,he⟩
    exact ⟨i,by simp [ha,he]⟩

theorem active_card_le (part : Fin G.order → B) (p : Position G H q) :
    (active part p).card ≤ q := by
  exact (Finset.card_eraseNone_le _).trans ((Finset.card_image_le).trans (by simp))

theorem active_card_lt_vacant (part : Fin G.order → B) (p : Position G H q)
    (i : Fin q) (hi : p i = none) : (active part p).card < q := by
  have hm : none ∈ Finset.univ.image (fun j => (p j).map (fun a => part a.1)) :=
    Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simp [hi]⟩
  have hc : (Finset.univ.image (fun j => (p j).map (fun a => part a.1))).card ≤ q :=
    Finset.card_image_le.trans (by simp)
  rw [active,Finset.card_eraseNone_of_mem hm]
  have hp : 0 < q := Nat.zero_le i.val |>.trans_lt i.isLt
  omega

theorem active_mono (part : Fin G.order → B) {p p' : Position G H q}
    (hp : Subposition p' p) : active part p' ⊆ active part p := by
  intro b hb
  obtain ⟨i,a,ha,rfl⟩ := (mem_active part p' b).mp hb
  exact (mem_active part p _).mpr ⟨i,a,hp i a ha,rfl⟩

theorem active_update_subset (part : Fin G.order → B) (p : Position G H q)
    (i : Fin q) (a : Fin G.order × Fin H.order) :
    active part (Function.update p i (some a)) ⊆ insert (part a.1) (active part p) := by
  intro b hb
  obtain ⟨j,c,hc,rfl⟩ := (mem_active part _ b).mp hb
  by_cases hj : j = i
  · subst j
    have he : a = c := by simpa using hc
    subst c
    exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem ((mem_active part p _).mpr
      ⟨j,c,by simpa only [Function.update_of_ne hj] using hc,rfl⟩)

theorem winning_of_block_families {Z : B → Type uVariable6}
    (part : Fin G.order → B)
    (maps : (∀ b, Z b) → (Fin G.order ≃ Fin H.order))
    (locality : ∀ ξ η v, ξ (part v) = η (part v) → maps ξ v = maps η v)
    (pool : Finset B → Set (∀ b, Z b))
    (empty : (pool ∅).Nonempty)
    (down : ∀ U V, U.card ≤ q → V ⊆ U → pool U ⊆ pool V)
    (extend : ∀ U, U.card < q → ∀ b ξ, ξ ∈ pool U →
      ∃ η ∈ pool (insert b U), ∀ c ∈ U, η c = ξ c)
    (safe : ∀ U ξ, ξ ∈ pool U → ∀ v w, part v ∈ U → part w ∈ U →
      (G.graph.Adj v w ↔ H.graph.Adj (maps ξ v) (maps ξ w))) :
    Winning (fun _ : Fin q => none : Position G H q) := by
  classical
  let S : Set (Position G H q) := {p | ∃ ξ, ξ ∈ pool (active part p) ∧
    ∀ i a, p i = some a → a.2 = maps ξ a.1}
  refine ⟨S,?_,?_,?_,?_⟩
  · obtain ⟨ξ,hξ⟩ := empty
    refine ⟨ξ,?_,by simp⟩
    have he : active part (fun _ : Fin q => none : Position G H q) = ∅ := by
      ext b
      simp [mem_active]
    simpa only [he] using hξ
  · rintro p ⟨ξ,hξ,hp⟩ i j a b ha hb
    have hpa := hp i a ha
    have hpb := hp j b hb
    rw [hpa,hpb]
    exact ⟨(maps ξ).injective.eq_iff.symm,safe _ ξ hξ _ _
      ((mem_active part p _).mpr ⟨i,a,ha,rfl⟩)
      ((mem_active part p _).mpr ⟨j,b,hb,rfl⟩)⟩
  · rintro p ⟨ξ,hξ,hp⟩ p' hp'
    exact ⟨ξ,down _ _ (active_card_le part p) (active_mono part hp') hξ,
      fun i a ha => hp i a (hp' i a ha)⟩
  · rintro p ⟨ξ,hξ,hp⟩ i hi
    have hex := fun b => extend (active part p) (active_card_lt_vacant part p i hi) b ξ hξ
    choose η hη hkeep using hex
    let θ : ∀ b, Z b := fun b => η b b
    refine ⟨maps θ,fun v => ?_⟩
    refine ⟨η (part v),down _ _ ?_ (active_update_subset part p i (v,maps θ v)) (hη _),?_⟩
    · exact (Finset.card_insert_le _ _).trans (by have := active_card_lt_vacant part p i hi; omega)
    · intro j a ha
      by_cases hj : j = i
      · subst j
        have he : (v,maps θ v) = a := by simpa using ha
        subst a
        exact locality θ (η (part v)) v rfl
      · have ha' : p j = some a := by simpa only [Function.update_of_ne hj] using ha
        exact (hp j a ha').trans (locality ξ (η (part v)) a.1
          (hkeep (part v) (part a.1) ((mem_active part p _).mpr ⟨j,a,ha',rfl⟩)).symm)
end VariableWL.Game

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_GeneralReduction
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.BlockCoordinates.coordinateFintype _root_.OAI.VariableWL.BlockCoordinates.defaultProperNumberings _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10

namespace VariableWL.Blocks
attribute [local instance] Classical.propDecidable
open VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E) (marked : Fin r)

theorem completeList_mem (U : Finset (Block (n := n) J))
    (ξ : ∀ b : ↑U, Valuation J marked 1 b.val) (b : ↑U) :
    completeList J marked U ξ b.val = ξ b := by
  classical
  simp [completeList,b.property]

theorem globalPool_nonempty (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (Q : J.Witness) (U : Finset (Block (n := n) J)) (hU : U.card ≤ r+1) :
    (GlobalPool J marked hr hn Q U).Nonempty := by
  obtain ⟨ξ,hξ⟩ := offsetLists_nonempty J hr hn hlarge marked Q U hU
  refine ⟨completeList J marked U ξ,?_⟩
  change (fun b : ↑U => completeList J marked U ξ b.val) ∈ OffsetLists J hr hn marked Q U
  simpa only [completeList_mem] using hξ

theorem globalPool_down (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (Q : J.Witness) (U V : Finset (Block (n := n) J)) (hU : U.card ≤ r+1) (hVU : V ⊆ U) :
    GlobalPool J marked hr hn Q U ⊆ GlobalPool J marked hr hn Q V := by
  intro ξ hξ
  change (fun b : ↑V => ξ b.val) ∈ OffsetLists J hr hn marked Q V
  rw [← exact_projection J hr hn hlarge marked Q U V hU hVU]
  exact ⟨fun b : ↑U => ξ b.val,hξ,rfl⟩

theorem globalPool_extend (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (Q : J.Witness) (U : Finset (Block (n := n) J)) (hU : U.card < r+1)
    (b : Block (n := n) J) (ξ : ∀ c : Block (n := n) J, Valuation J marked 1 c)
    (hξ : ξ ∈ GlobalPool J marked hr hn Q U) :
    ∃ η ∈ GlobalPool J marked hr hn Q (insert b U), ∀ c ∈ U, η c = ξ c := by
  classical
  have hsize : (insert b U).card ≤ r+1 := Finset.card_insert_le _ _ |>.trans (by omega)
  have hsub : U ⊆ insert b U := Finset.subset_insert _ _
  rw [GlobalPool,Set.mem_ofPred_eq,← exact_projection J hr hn hlarge marked Q (insert b U) U hsize hsub] at hξ
  obtain ⟨η,hη,he⟩ := hξ
  refine ⟨completeList J marked (insert b U) η,?_,?_⟩
  · change (fun c : ↑(insert b U) => completeList J marked (insert b U) η c.val) ∈ OffsetLists J hr hn marked Q (insert b U)
    simpa only [completeList_mem] using hη
  · intro c hc
    exact (completeList_mem J marked (insert b U) η ⟨c,hsub hc⟩).trans (congrFun he ⟨c,hc⟩)
end VariableWL.Blocks

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PortGraph
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {V : Type uVariable7} (Y : PortGraph V) (color : V → ℕ)

theorem same_owner_reachable (x y : Vertex color) (ho : x.owner = y.owner) :
    (graph Y color).Reachable x y := by
  have hbase (z : Vertex color) : (graph Y color).Reachable z (Vertex.triangle z.owner z.port) := by
    induction he : z.level using Nat.strong_induction_on generalizing z with
    | h l ih =>
      by_cases hl : l = 0
      · have hz : z = Vertex.triangle z.owner z.port := Vertex.ext rfl rfl (he.trans hl)
        exact (congrArg ((graph Y color).Reachable z) hz).mp (.refl z)
      · let prev : Vertex color := ⟨z.owner,z.port,l-1,by have := z.bound; omega⟩
        have ha : (graph Y color).Adj z prev := Or.inl ⟨rfl,Or.inr ⟨rfl,Or.inr (by dsimp [prev]; omega)⟩⟩
        exact ha.reachable.trans (ih (l-1) (by omega) prev rfl)
  have htri : (graph Y color).Reachable (Vertex.triangle x.owner x.port) (Vertex.triangle y.owner y.port) := by
    by_cases hp : x.port = y.port
    · have he : Vertex.triangle (color := color) x.owner x.port = Vertex.triangle y.owner y.port := by rw [ho,hp]
      rw [he]
    · exact ((triangle_adj_triangle Y color _ _ _ _).mpr ⟨ho,hp⟩).reachable
  exact (hbase x).trans (htri.trans (hbase y).symm)

theorem underlying_edge_reachable {v w : V} (h : Y.graph.Adj v w) (j k : Fin 3) :
    (graph Y color).Reachable (Vertex.triangle v j) (Vertex.triangle w k) := by
  obtain ⟨a,b,he⟩ := h
  have hc : (graph Y color).Adj (Vertex.connector v a) (Vertex.connector w b) := Or.inr ⟨rfl,rfl,he⟩
  exact (same_owner_reachable Y color (Vertex.triangle v j) (Vertex.connector v a) rfl).trans
    (hc.reachable.trans (same_owner_reachable Y color (Vertex.connector w b) (Vertex.triangle w k) rfl))

theorem connected (hY : Y.graph.Connected) : (graph Y color).Connected := by
  have : Nonempty V := hY.nonempty
  have : Nonempty (Vertex color) := ⟨Vertex.triangle (Classical.choice ‹Nonempty V›) 0⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨p⟩ := hY x.owner y.owner
  have walk_lift {v w : V} (q : Y.graph.Walk v w) :
      (graph Y color).Reachable (Vertex.triangle v 0) (Vertex.triangle w 0) := by
    induction q with
    | nil => exact .refl _
    | cons ha q ih => exact (underlying_edge_reachable Y color ha 0 0).trans ih
  exact (same_owner_reachable Y color x (Vertex.triangle x.owner 0) rfl).trans
    ((walk_lift p).trans (same_owner_reachable Y color (Vertex.triangle y.owner 0) y rfl))

end VariableWL.SubcubicRealization

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PrefixParts
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.PrefixParts
open VariableWL.Affine
open scoped CharTwo
attribute [local instance] Classical.propDecidable

namespace Data

variable (D : Data)

variable {D}

variable (D)

theorem tree_to_leaf {ε : Bit} (c : Fin D.channels) (z : D.Valuation ε) :
    ∀ h (hq : D.root c ≤ h) (ha : h ≤ D.dimension),
    (D.graph ε).Reachable (.inr (.inr (Tree.ofValuation c h hq ha z)))
      (.inr (.inr (Tree.ofValuation c D.dimension (D.root_le c) le_rfl z))) := by
  intro h hq ha
  induction hd : D.dimension-h generalizing h with
  | zero => have he : h=D.dimension := by omega
            subst h
            exact SimpleGraph.Reachable.refl _
  | succ d ih =>
    have hlt : h < D.dimension := by omega
    have hs : (D.graph ε).Adj (.inr (.inr (Tree.ofValuation c h hq ha z)))
        (.inr (.inr (Tree.ofValuation c (h+1) (by omega) (by omega) z))) := by
      refine Or.inl ⟨rfl,rfl,?_⟩
      change truncate h (truncate (h+1) (z.val ∘ D.order c))=truncate h (z.val ∘ D.order c)
      exact truncate_truncate (by omega) _
    exact hs.reachable.trans (ih (h+1) (by omega) (by omega) (by omega))

theorem spine_to_zero {ε : Bit} (c : Fin D.channels) (z : D.Valuation ε) :
    (D.graph ε).Reachable (.inr (.inl (c,z))) (.inr (.inl (⟨0,D.positive⟩,z))) := by
  induction hc : c.val generalizing c with
  | zero => have he : c=⟨0,D.positive⟩ := Fin.ext hc
            subst c; exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    let d : Fin D.channels := ⟨k,by omega⟩
    have hs : (D.graph ε).Adj (.inr (.inl (c,z))) (.inr (.inl (d,z))) := Or.inr ⟨hc.symm,rfl⟩
    exact hs.reachable.trans (ih d rfl)

theorem leaf_spine {ε : Bit} (c : Fin D.channels) (z : D.Valuation ε) :
    (D.graph ε).Adj (.inr (.inr (Tree.ofValuation c D.dimension (D.root_le c) le_rfl z)))
      (.inr (.inl (c,z))) := Or.inl ⟨rfl,rfl,truncate_full _⟩

theorem connected (ε : Bit) : (D.graph ε).Connected := by
  have hp : ∀ x : D.Vertex ε, (D.graph ε).Reachable x (.inl ()) := by
    have hs : ∀ (c : Fin D.channels) (z : D.Valuation ε),
        (D.graph ε).Reachable (.inr (.inl (c,z))) (.inl ()) := by
      intro c z
      have hr : D.root ⟨0,D.positive⟩ ≤ 0 := by rw [D.zero_root]
      have hroot : (D.graph ε).Adj (.inl ())
          (.inr (.inr (Tree.ofValuation ⟨0,D.positive⟩ 0 hr (Nat.zero_le _) z))) := Or.inl ⟨rfl,rfl⟩
      exact (D.spine_to_zero c z).trans ((D.leaf_spine ⟨0,D.positive⟩ z).reachable.symm.trans
        ((D.tree_to_leaf ⟨0,D.positive⟩ z 0 hr (Nat.zero_le _)).symm.trans hroot.reachable.symm))
    intro x
    rcases x with x | (⟨c,z⟩ | t)
    · cases x; exact SimpleGraph.Reachable.refl _
    · exact hs c z
    · obtain ⟨z,hz⟩ := t.property.2
      have he : t=Tree.ofValuation t.channel t.height t.property.1 (by have ht : t.height < D.dimension+1 := t.val.2.1.isLt; omega) z :=
        Tree.ext rfl rfl hz.symm
      rw [he]
      exact (D.tree_to_leaf _ _ _ _ _).trans ((D.leaf_spine _ _).reachable.trans (hs _ _))
  exact ⟨fun x y => (hp x).trans (hp y).symm⟩

end Data
end VariableWL.PrefixParts

namespace VariableWL.PrefixParts.Data
open VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {D : Data}

theorem slot_translation (ξ : D.Valuation 1) (x y : D.Vertex 0)
    (ha : (D.graph 0).Adj x y) :
    slot (D.vertexTranslation ξ x) (D.vertexTranslation ξ y)=localPorts ξ x (slot x y) := by
  have h : Forward x y ∨ Forward y x := ha
  rcases x with x | (⟨c,z⟩ | t)
  · rcases y with y | (y | u) <;> rfl
  · rcases y with y | (y | u) <;> rfl
  · rcases y with y | (⟨c,z⟩ | u)
    · change 0=localPorts ξ (.inr (.inr t)) 0
      exact (localPorts_zero ξ _).symm
    · have hl : t.channel=c ∧ t.height=D.dimension ∧ t.bits=z.val ∘ D.order c := by
        simpa only [Forward,or_false] using h
      change 1=(if ht : t.height<D.dimension then _ else Equiv.refl (Fin 3)) 1
      simp only [hl.2.1,lt_self_iff_false,dite_false,Equiv.refl_apply]
    · rcases h with h | h
      · have h' := (D.treeTranslation_step ξ t u).mpr h
        change slot (.inr (.inr (D.treeTranslation ξ t))) (.inr (.inr (D.treeTranslation ξ u)))=_
        rw [slot_child h',slot_child h]
        have hh := h.2.1
        change bitPort ((u.bits+truncate u.height (ξ.val ∘ D.order u.channel)) ⟨t.height,h.lower_lt⟩)=_
        rw [show localPorts ξ (.inr (.inr t))=shiftPorts (ξ.val (D.order t.channel ⟨t.height,h.lower_lt⟩)) by
          simp only [localPorts,dite_eq_left h.lower_lt],shiftPorts_bitPort]
        congr 1
        simp only [Pi.add_apply,truncate,ite_eq_left (show t.height<u.height by omega),Function.comp_apply,h.1]
      · have h' := (D.treeTranslation_step ξ u t).mpr h
        change slot (.inr (.inr (D.treeTranslation ξ t))) (.inr (.inr (D.treeTranslation ξ u)))=_
        rw [slot_parent h',slot_parent h,localPorts_zero]

end VariableWL.PrefixParts.Data

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PrefixWiring
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.BlockCoordinates.defaultProperNumberings _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.PrefixParts.Data
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {D : Data}

theorem ports_translation (ξ : D.Valuation 1) (x y : D.Vertex 0) (i j : Fin 3) :
    (D.ports 1).edge (D.vertexTranslation ξ x,localPorts ξ x i)
      (D.vertexTranslation ξ y,localPorts ξ y j) ↔ (D.ports 0).edge (x,i) (y,j) := by
  change ((D.graph 1).Adj (D.vertexTranslation ξ x) (D.vertexTranslation ξ y) ∧
    localPorts ξ x i=slot (D.vertexTranslation ξ x) (D.vertexTranslation ξ y) ∧
    localPorts ξ y j=slot (D.vertexTranslation ξ y) (D.vertexTranslation ξ x)) ↔
    ((D.graph 0).Adj x y ∧ i=slot x y ∧ j=slot y x)
  have hAdj : (D.graph 1).Adj (D.vertexTranslation ξ x) (D.vertexTranslation ξ y) ↔
      (D.graph 0).Adj x y := (D.translationIso ξ).map_adj_iff
  rw [hAdj]
  constructor
  · rintro ⟨h,hi,hj⟩
    rw [slot_translation ξ x y h] at hi
    rw [slot_translation ξ y x h.symm] at hj
    exact ⟨h,(localPorts ξ x).injective hi,(localPorts ξ y).injective hj⟩
  · rintro ⟨h,hi,hj⟩
    rw [slot_translation ξ x y h,slot_translation ξ y x h.symm]
    exact ⟨h,congrArg _ hi,congrArg _ hj⟩

end VariableWL.PrefixParts.Data

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable7} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)] (W : Wiring D)

omit [Fintype B] in
theorem internal_translation (ξ : ∀ b, (D b).Valuation 1)
    (a b : Vertex D 0 × Fin 3) :
    (internal D 1).edge (incidenceTranslation D ξ a) (incidenceTranslation D ξ b) ↔
      (internal D 0).edge a b := by
  rcases a with ⟨⟨d,x⟩,i⟩
  rcases b with ⟨⟨e,y⟩,j⟩
  constructor
  · rintro ⟨h,he⟩
    change d=e at h
    subst e
    exact ⟨rfl,(Data.ports_translation (ξ d) x y i j).mp he⟩
  · rintro ⟨h,he⟩
    change d=e at h
    subst e
    exact ⟨rfl,(Data.ports_translation (ξ d) x y i j).mpr he⟩

omit [Fintype B] in
theorem rootPorts_translation (ξ : ∀ b, (D b).Valuation 1)
    (a b : Vertex D 0 × Fin 3) (hξ : CompatiblePair D W ξ a.1.1 b.1.1) :
    (W.rootPorts D 1).edge (incidenceTranslation D ξ a) (incidenceTranslation D ξ b) ↔
      (W.rootPorts D 0).edge a b := by
  constructor
  · rintro ⟨x,y,ha,hb,hm,hv⟩
    let x₀ := (rootTranslation D ξ).symm x
    let y₀ := (rootTranslation D ξ).symm y
    have hx : rootTranslation D ξ x₀=x := (rootTranslation D ξ).apply_symm_apply x
    have hy : rootTranslation D ξ y₀=y := (rootTranslation D ξ).apply_symm_apply y
    have ha₀ : a=(rootVertex D x₀,0) := (incidenceTranslation D ξ).injective (by
      rw [translate_root_incidence,hx]; exact ha)
    have hb₀ : b=(rootVertex D y₀,0) := (incidenceTranslation D ξ).injective (by
      rw [translate_root_incidence,hy]; exact hb)
    have hm₀ : W.mate x₀.1=y₀.1 := hm
    have hs : rootShift D ξ x₀.1=rootShift D ξ y₀.1 := by
      rw [← hm₀]
      apply hξ
      · rw [ha₀]; rfl
      · rw [hb₀,hm₀]; rfl
    rw [← hx,← hy,rootTranslation_bits,rootTranslation_bits,hs] at hv
    exact ⟨x₀,y₀,ha₀,hb₀,hm₀,add_right_cancel hv⟩
  · rintro ⟨x,y,rfl,rfl,hm,hv⟩
    refine ⟨rootTranslation D ξ x,rootTranslation D ξ y,
      translate_root_incidence D ξ x,translate_root_incidence D ξ y,hm,?_⟩
    have hs : rootShift D ξ x.1=rootShift D ξ y.1 := by
      rw [← hm]
      exact hξ x.1 rfl (congrArg Sigma.fst hm)
    rw [rootTranslation_bits,rootTranslation_bits,hv,hs]

omit [FiniteNumbering (SortTag D)] in
theorem anchorPorts_translation (ξ : ∀ b, (D b).Valuation 1)
    (a b : Vertex D 0 × Fin 3) :
    (anchorPorts D 1).edge (incidenceTranslation D ξ a) (incidenceTranslation D ξ b) ↔
      (anchorPorts D 0).edge a b := by
  have hf : ∀ a b, (anchorPorts D 0).edge a b →
      (anchorPorts D 1).edge (incidenceTranslation D ξ a) (incidenceTranslation D ξ b) := by
    intro a b h
    rcases h with ⟨x,y,rfl,rfl,hxy⟩ | ⟨x,y,rfl,rfl,hxy⟩
    · exact Or.inl ⟨x,y,rfl,rfl,hxy⟩
    · exact Or.inr ⟨x,y,rfl,rfl,hxy⟩
  refine ⟨?_,hf a b⟩
  intro h
  have hi : ∀ v x i, incidenceTranslation D ξ v=(anchor D 1 x,i) → v=(anchor D 0 x,i) := by
    intro v x i hv
    exact (incidenceTranslation D ξ).injective hv
  rcases h with ⟨x,y,ha,hb,hxy⟩ | ⟨x,y,hb,ha,hxy⟩
  · exact Or.inl ⟨x,y,hi a x 2 ha,hi b y 1 hb,hxy⟩
  · exact Or.inr ⟨x,y,hi b x 2 hb,hi a y 1 ha,hxy⟩

omit [FiniteNumbering (SortTag D)] in

theorem ports_translation (ξ : ∀ b, (D b).Valuation 1)
    (a b : Vertex D 0 × Fin 3) (hξ : CompatiblePair D W ξ a.1.1 b.1.1) :
    (W.ports D 1).edge (incidenceTranslation D ξ a) (incidenceTranslation D ξ b) ↔
      (W.ports D 0).edge a b := by
  change (_ ∨ _ ∨ _) ↔ (_ ∨ _ ∨ _)
  rw [internal_translation D ξ a b,rootPorts_translation D W ξ a b hξ,
    anchorPorts_translation D ξ a b]

end VariableWL.PrefixParts.Wiring

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable8} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)] (W : Wiring D)

omit [FiniteNumbering (SortTag D)] in
theorem part_reachable (ε : Bit) (b : B) (x y : (D b).Vertex ε) :
    (W.ports D ε).graph.Reachable ⟨b,x⟩ ⟨b,y⟩ :=
  ((D b).connected ε x y).map (partHom D W ε b)

omit [FiniteNumbering (SortTag D)] in
theorem anchor_adj (ε : Bit) (b c : B)
    (h : (enumeration B b).val+1=(enumeration B c).val) :
    (W.ports D ε).graph.Adj (anchor D ε b) (anchor D ε c) :=
  ⟨2,1,Or.inr (Or.inr (Or.inl ⟨b,c,rfl,rfl,h⟩))⟩

omit [FiniteNumbering (SortTag D)] in

theorem connected [Nonempty B] (ε : Bit) : (W.ports D ε).graph.Connected := by
  have hn : 0 < Fintype.card B := Fintype.card_pos
  let b₀ : B := (enumeration B).symm ⟨0,hn⟩
  have hp : ∀ (j : ℕ) (hj : j<Fintype.card B),
      (W.ports D ε).graph.Reachable (anchor D ε ((enumeration B).symm ⟨j,hj⟩))
        (anchor D ε b₀) := by
    intro j
    induction j with
    | zero => intro hj; exact SimpleGraph.Reachable.refl _
    | succ j ih =>
        intro hj
        have hj' : j<Fintype.card B := by omega
        have hadj := anchor_adj D W ε ((enumeration B).symm ⟨j,hj'⟩)
          ((enumeration B).symm ⟨j+1,hj⟩) (by simp only [Equiv.apply_symm_apply])
        exact hadj.reachable.symm.trans (ih hj')
  have hv : ∀ x : Vertex D ε, (W.ports D ε).graph.Reachable x (anchor D ε b₀) := by
    rintro ⟨b,x⟩
    have hb := hp (enumeration B b).val (enumeration B b).isLt
    rw [Fin.eta,Equiv.symm_apply_apply] at hb
    exact (part_reachable D W ε b x (.inl ())).trans hb
  have : Nonempty (Vertex D ε) := ⟨anchor D ε b₀⟩
  exact ⟨fun x y => (hv x).trans (hv y).symm⟩

theorem uncolored_connected [Nonempty B] (ε : Bit) : (uncolored D W ε).Connected :=
  SubcubicRealization.connected (W.ports D ε) (color D) (connected D W ε)

theorem uncolored_subcubic (ε : Bit) (x : UncoloredVertex D ε) :
    (uncolored D W ε).degree x ≤ 3 := SubcubicRealization.degree_le_three _ _ x

theorem uncoloredTranslation_adj (ξ : ∀ b, (D b).Valuation 1)
    (x y : UncoloredVertex D 0) (hξ : CompatiblePair D W ξ x.owner.1 y.owner.1) :
    (uncolored D W 1).Adj (uncoloredTranslation D ξ x) (uncoloredTranslation D ξ y) ↔
      (uncolored D W 0).Adj x y :=
  SubcubicRealization.vertexEquiv_adj (W.ports D 0) (W.ports D 1) _ _ _ x y
    (ports_translation D W ξ (x.owner,x.port) (y.owner,y.port) hξ).symm

omit [FiniteNumbering B] in
theorem equal_order : Fintype.card (UncoloredVertex D 0)=Fintype.card (UncoloredVertex D 1) := by
  let ξ : ∀ b, (D b).Valuation 1 := fun b => ⟨(D b).nonempty 1 |>.choose,(D b).nonempty 1 |>.choose_spec⟩
  exact Fintype.card_congr (uncoloredTranslation D ξ)

end VariableWL.PrefixParts.Wiring

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Coordinates
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7

namespace VariableWL.BlockCoordinates
open VariableWL.Affine VariableWL.Blocks Subdivision VariableWL.PrefixParts
open VariableWL.PrefixParts.Wiring
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} (J : ProductImages.Instance r P E)

variable [Fintype P] [Fintype E] [∀ b : Block (n := n) J, FiniteNumbering (Proper J b)]

theorem rootShift_encode (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
    (ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b) (b : Block (n := n) J) (p : Proper J b) :
    rootShift (data J hr hn marked) (encodeList J hr hn marked ξ) (channelEquiv J hr hn marked ⟨b,p⟩)=
      pad (readoutEquiv J p.2.val (readout J (ξ b).val p.2.property.1)) :=
  data_prefix J hr hn marked b p (ξ b)

theorem compatible_of_agree (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
    (ξ : ∀ b : Block (n := n) J, Valuation J marked 1 b) {b c : Block (n := n) J}
    (h : General.Agree J marked ⟨b,ξ b⟩ ⟨c,ξ c⟩) :
    CompatiblePair (data J hr hn marked) (wiring J hr hn marked) (encodeList J hr hn marked ξ) b c := by
  intro d hd hc
  obtain ⟨⟨e,p⟩,rfl⟩ := (channelEquiv J hr hn marked).surjective d
  change e=b at hd
  subst e
  rw [mate_channel] at hc ⊢
  change p.1.val=c at hc
  rw [rootShift_encode,rootShift_encode]
  change pad (readoutEquiv J p.2.val (readout J (ξ b).val p.2.property.1))=
    pad (readoutEquiv J p.2.val (readout J (ξ p.1.val).val p.2.property.2))
  have hag : General.Agree J marked ⟨b,ξ b⟩ ⟨p.1.val,ξ p.1.val⟩ := hc.symm ▸ h
  rw [hag p.2.val p.2.property.1 p.2.property.2]

end VariableWL.BlockCoordinates

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
variable {B : Type uVariable7} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)]

omit [FiniteNumbering B] in
theorem uncoloredTranslation_local (ξ η : ∀ b, (D b).Valuation 1)
    (x : UncoloredVertex D 0) (h : ξ x.owner.1=η x.owner.1) :
    uncoloredTranslation D ξ x=uncoloredTranslation D η x := by
  apply SubcubicRealization.Vertex.ext
  · change (⟨x.owner.1,(D x.owner.1).vertexTranslation (ξ x.owner.1) x.owner.2⟩ : Vertex D 1)=
      ⟨x.owner.1,(D x.owner.1).vertexTranslation (η x.owner.1) x.owner.2⟩
    rw [h]
  · change Data.localPorts (ξ x.owner.1) x.owner.2 x.port=Data.localPorts (η x.owner.1) x.owner.2 x.port
    rw [h]
  · rfl
end VariableWL.PrefixParts.Wiring

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_SubcubicGame
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.Subcubic
open VariableWL.Affine VariableWL.Blocks VariableWL.PrefixParts VariableWL.PrefixParts.Wiring
open VariableWL.BlockCoordinates
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} [Fintype P] [Fintype E]
  (J : ProductImages.Instance r P E) [∀ b : Block (n := n) J, FiniteNumbering (Proper J b)] [FiniteNumbering (Block (n := n) J)] (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
  [FiniteNumbering (SortTag (data (n := n) J hr hn marked))]

theorem numberedTranslation_local (ξ η : ∀ b : Block (n := n) J, Valuation J marked 1 b)
    (v : Fin (finiteGraph J hr hn marked 0).order)
    (h : ξ (numberedPart J hr hn marked v)=η (numberedPart J hr hn marked v)) :
    numberedTranslation J hr hn marked ξ v=numberedTranslation J hr hn marked η v := by
  apply congrArg (Fintype.equivFin (Vertex J hr hn marked 1))
  apply uncoloredTranslation_local
  exact congrArg (valuationEquiv J hr hn marked _ 1) h

theorem winning_of_witness (hr3 : 3 ≤ r) (hlarge : r+1 < n+1) (Q : J.Witness) :
    Game.Winning (fun _ : Fin (r+1) => none :
      Game.Position (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) (r+1)) := by
  classical
  apply Game.winning_of_block_families (numberedPart J hr hn marked)
    (numberedTranslation J hr hn marked) (numberedTranslation_local J hr hn marked)
    (GlobalPool J marked hr3 hn Q)
  · exact globalPool_nonempty J marked hr3 hn hlarge Q ∅ (by simp)
  · exact globalPool_down J marked hr3 hn hlarge Q
  · exact globalPool_extend J marked hr3 hn hlarge Q
  · intro U ξ hξ v w hv hw
    let x := (Fintype.equivFin (Vertex J hr hn marked 0)).symm v
    let y := (Fintype.equivFin (Vertex J hr hn marked 0)).symm w
    have hag : General.Agree J marked ⟨x.owner.1,ξ x.owner.1⟩ ⟨y.owner.1,ξ y.owner.1⟩ := by
      intro a ha hb
      exact offsetLists_agree J hr3 hn marked Q U hξ ⟨x.owner.1,hv⟩ ⟨y.owner.1,hw⟩ a ha hb
    have hh := (uncoloredTranslation_adj (data J hr hn marked) (wiring J hr hn marked)
      (encodeList J hr hn marked ξ) x y (compatible_of_agree J hr hn marked ξ hag)).symm
    change (graph J hr hn marked 0).Adj x y ↔
      (graph J hr hn marked 1).Adj
        ((Fintype.equivFin (Vertex J hr hn marked 1)).symm
          ((Fintype.equivFin (Vertex J hr hn marked 1)) (translation J hr hn marked ξ x)))
        ((Fintype.equivFin (Vertex J hr hn marked 1)).symm
          ((Fintype.equivFin (Vertex J hr hn marked 1)) (translation J hr hn marked ξ y)))
    simpa only [Equiv.symm_apply_apply,graph,translation] using hh

end VariableWL.Subcubic

namespace VariableWL.Subcubic
open VariableWL.Affine VariableWL.Blocks VariableWL.PrefixParts VariableWL.PrefixParts.Wiring
open VariableWL.BlockCoordinates
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} [Fintype P] [Fintype E]
  (J : ProductImages.Instance r P E) [∀ b : Block (n := n) J, FiniteNumbering (Proper J b)] [FiniteNumbering (Block (n := n) J)] (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
  [FiniteNumbering (SortTag (data (n := n) J hr hn marked))]

theorem consistent_of_winning
    (hwin : Game.Winning (fun _ : Fin (r+1) => none :
      Game.Position (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) (r+1))) :
    J.Consistent := ⟨extractedWitness J marked hr hn (attainedRings J hr hn marked hwin)⟩

omit [Fintype P] [Fintype E] in
include marked in
theorem block_nonempty [Nonempty P] : Nonempty (Block (n := n) J) := by
  obtain ⟨p⟩ := ‹Nonempty P›
  exact ⟨siteRing (n := n) J (.inl p) (realAddress J p (fun _ => false)) marked⟩

theorem positive_order [Nonempty P] (ε : Bit) : 0 < (finiteGraph J hr hn marked ε).order := by
  classical
  let : Nonempty (Block (n := n) J) := block_nonempty J marked
  obtain ⟨b⟩ := ‹Nonempty (Block (n := n) J)›
  exact Fintype.card_pos_iff.mpr ⟨SubcubicRealization.Vertex.triangle (anchor (data J hr hn marked) ε b) 0⟩

theorem connected [Nonempty P] (ε : Bit) : (finiteGraph J hr hn marked ε).graph.Connected := by
  let : Nonempty (Block (n := n) J) := block_nonempty J marked
  exact (TypedGame.numbering (graph J hr hn marked ε)).connected_iff.mp
    (uncolored_connected (data J hr hn marked) (wiring J hr hn marked) ε)

theorem degree_le_three (ε : Bit) : VariableWL.Subcubic (finiteGraph J hr hn marked ε) := by
  classical
  intro v
  let e := TypedGame.numbering (graph J hr hn marked ε)
  have h := uncolored_subcubic (data J hr hn marked) (wiring J hr hn marked) ε (e.symm v)
  have he : (graph J hr hn marked ε).degree (e.symm v)=
      (finiteGraph J hr hn marked ε).graph.degree v := by
    simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_congr (e.symm.mapNeighborSet v).symm
  exact he ▸ h

theorem equal_order : (finiteGraph J hr hn marked 0).order=(finiteGraph J hr hn marked 1).order :=
  Wiring.equal_order (data J hr hn marked)

theorem equivalent_iff_consistent [Nonempty P] (hr3 : 3 ≤ r) (hlarge : r+1 < n+1) :
    Equivalent (finiteGraph J hr hn marked 0) (finiteGraph J hr hn marked 1) r ↔ J.Consistent := by
  rw [Game.equivalent_iff_winning hr (positive_order J hr hn marked 0)]
  exact ⟨consistent_of_winning J hr hn marked,
    fun ⟨Q⟩ => winning_of_witness J hr hn marked hr3 hlarge Q⟩

end VariableWL.Subcubic

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Circuit
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12 uVariable13 uVariable14

namespace VariableWL.Circuit
attribute [local instance] Classical.propDecidable
open VariableWL.ScalarImages
variable (S : Type uVariable1) (A : Type uVariable2) (E : Type uVariable3)

variable {S A E}
namespace System
variable (C : System S A E)

namespace Witness
variable {C} (Q : C.Witness)

theorem propagates (e : E)
    (hs : output S A (C.source e) '' Q.gates (C.source e)={0}) :
    input S A (C.destination e) '' Q.gates (target S A (C.destination e))={0} :=
  zero_propagates (Q.buffers_nonempty e) ((Q.first e).symm.trans hs)
    ((Q.second e).symm.trans hs) (Q.last e)

theorem true_zero {g : Gate S A} (hg : C.TrueGate g) : output S A g '' Q.gates g={0} := by
  induction hg with
  | seed s hs => simpa [output] using Q.seed s hs
  | scalar e s he hs ih =>
    have hz := Q.propagates e ih
    have heq := congrArg (fun p : Port S A => input S A p '' Q.gates (target S A p)) he
    rw [heq] at hz
    simpa [input,output] using hz
  | and a e f he hf hs ht ihe ihf =>
    have h0 : Prod.fst '' Q.gates (.inr a)={0} := by
      have hz := Q.propagates e ihe
      have heq := congrArg (fun p : Port S A => input S A p '' Q.gates (target S A p)) he
      rw [heq] at hz
      exact hz
    have h1 : Prod.snd '' Q.gates (.inr a)={0} := by
      have hz := Q.propagates f ihf
      have heq := congrArg (fun p : Port S A => input S A p '' Q.gates (target S A p)) hf
      rw [heq] at hz
      exact hz
    change sum '' Q.gates (.inr a)={0}
    rw [zero_buffer_unique (Q.gates_nonempty (.inr a)) h0 h1]
    simp [sum]

include Q in
theorem tests_false : ∀ s ∈ C.tests, ¬ C.TrueGate (.inl s) := by
  intro s hs ht
  have h := Q.true_zero ht
  have he : ({1} : Set Bit)={0} := by simp [output,Q.test s hs] at h
  have hz : (1 : Bit)=0 := Set.mem_singleton_iff.mp (he ▸ Set.mem_singleton (1 : Bit))
  exact one_ne_zero hz
end Witness

variable (hfalse : ∀ s ∈ C.tests, ¬ C.TrueGate (.inl s))

theorem consistent_iff : Nonempty C.Witness ↔ ∀ s ∈ C.tests, ¬ C.TrueGate (.inl s) :=
  ⟨fun ⟨Q⟩ => Q.tests_false,fun h => ⟨C.witness h⟩⟩

end System
end VariableWL.Circuit

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_CellularCircuit
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10

namespace VariableWL.Circuit
open VariableWL.Affine ProductImages.Instance
attribute [local instance] Classical.propDecidable
variable {S : Type uVariable1} {A : Type uVariable2} {r : ℕ}

namespace Description
variable {E : Type uVariable5} {R : Type uVariable6} (D : Description r S A E R)

theorem consistency_iff (h : D.Terminal) : D.consistency.Consistent ↔
    ∀ s ∈ (D.expanded h).tests, ¬ (D.expanded h).TrueGate (.inl s) := by
  rw [← System.consistent_iff]
  exact ⟨fun ⟨Q⟩ => ⟨D.decodeWitness h Q⟩,fun ⟨Q⟩ => ⟨D.encodeWitness h Q⟩⟩

end Description
end VariableWL.Circuit

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Binary
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.Binary
attribute [local instance] Classical.propDecidable

theorem exists_allowed {d : ℕ} (bit : Bool) (x : Digits d)
    (hx : x ≠ fun _ => bit) : ∃ h, Allowed bit h x := by
  classical
  let U := Finset.univ.filter (fun i => x i ≠ bit)
  have hu : U.Nonempty := by
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hx
    exact ⟨i,by simp [U,hi]⟩
  let h := U.min' hu
  have hh : x h ≠ bit := (Finset.mem_filter.mp (Finset.min'_mem U hu)).2
  refine ⟨h,(allowed_iff bit h x).mpr ⟨?_,?_⟩⟩
  · cases he : x h <;> cases bit <;> simp_all
  · intro i hi
    by_contra he
    have him : i ∈ U := by simp [U,he]
    have hle : h ≤ i := Finset.min'_le U i him
    exact not_le_of_gt hi hle

theorem number_borrow {d : ℕ} (h : Fin d) (x : Digits d) (hx : Allowed false h x) :
    number (flip h x)+1=number x := by
  induction d with
  | zero => exact Fin.elim0 h
  | succ d ih =>
    cases h using Fin.cases with
    | zero =>
      have hh : x 0=true := (allowed_iff false 0 x).mp hx |>.1
      have ht : (fun i : Fin d => flip 0 x i.succ)=(fun i : Fin d => x i.succ) := by
        funext i
        simp [flip,table]
      simp only [number]
      rw [ht]
      simp [flip,table,hh,Nat.add_comm]
    | succ h =>
      obtain ⟨hh,hlt⟩ := (allowed_iff false h.succ x).mp hx
      have hz : x 0=false := hlt 0 (Fin.succ_pos h)
      have htail : Allowed false h (fun i : Fin d => x i.succ) :=
        (allowed_iff false h _).mpr ⟨hh,fun i hi => hlt i.succ (Fin.succ_lt_succ_iff.mpr hi)⟩
      have ht : (fun i : Fin d => flip h.succ x i.succ)=flip h (fun i : Fin d => x i.succ) := by
        funext i
        simp [flip,table]
      have he := ih h (fun i : Fin d => x i.succ) htail
      simp only [number]
      rw [ht]
      simp only [flip,table,Fin.zero_le,ite_eq_left,hz,Bool.not_false,Bool.toNat_false,Bool.toNat_true,zero_add]
      omega

theorem cyclicAllowed_none {d : ℕ} (bit : Bool) (x : Digits d) :
    CyclicAllowed bit none x ↔ x=fun _ => bit := by
  simp only [CyclicAllowed,cyclicDomain,Finset.mem_singleton]
  exact ⟨fun h => funext h,fun h i => congrFun h i⟩

theorem exists_cyclicAllowed {d : ℕ} (bit : Bool) (x : Digits d) : ∃ h, CyclicAllowed bit h x := by
  by_cases hx : x=fun _ => bit
  · exact ⟨none,(cyclicAllowed_none bit x).mpr hx⟩
  · obtain ⟨h,hh⟩ := exists_allowed bit x hx
    exact ⟨some h,hh⟩

theorem cyclic_increment {d : ℕ} (h : Option (Fin d)) (x : Digits d) (hx : CyclicAllowed true h x) :
    number (cyclicFlip h x)=(number x+1) % 2^d := by
  cases h with
  | none =>
    have he := (cyclicAllowed_none true x).mp hx
    subst x
    change number (fun _ : Fin d => false)=(number (fun _ : Fin d => true)+1) % 2^d
    rw [number_false,number_true,Nat.mod_self]
  | some h =>
    have he := number_flip h x hx
    have ht := number_lt (flip h x)
    change number (flip h x)=(number x+1) % 2^d
    rw [← he,Nat.mod_eq_of_lt ht]

theorem cyclic_decrement {d : ℕ} (h : Option (Fin d)) (x : Digits d) (hx : CyclicAllowed false h x) :
    number (cyclicFlip h x)=(number x+2^d-1) % 2^d := by
  cases h with
  | none =>
    have he := (cyclicAllowed_none false x).mp hx
    subst x
    have hn := number_true d
    have ht := number_lt (fun _ : Fin d => true)
    have hn' : number (fun _ : Fin d => true)=2^d-1 := by omega
    change number (fun _ : Fin d => true)=(number (fun _ : Fin d => false)+2^d-1) % 2^d
    rw [number_false,Nat.zero_add,← hn',Nat.mod_eq_of_lt ht]
  | some h =>
    have he := number_borrow h x hx
    have ht := number_lt (flip h x)
    change number (flip h x)=(number x+2^d-1) % 2^d
    have hh : number x+2^d-1=number (flip h x)+2^d := by omega
    rw [hh,Nat.add_mod_right,Nat.mod_eq_of_lt ht]

end VariableWL.Binary

namespace VariableWL.Binary
attribute [local instance] Classical.propDecidable

theorem number_lt_iff {d : ℕ} (μ x : Digits d) : number μ<number x ↔ ∃ h, GreaterAt μ x h := by
  induction d with
  | zero => simp [number]
  | succ d ih =>
    let μ' : Digits d := fun i => μ i.succ
    let x' : Digits d := fun i => x i.succ
    have hμ : (μ 0).toNat ≤ 1 := by cases μ 0 <;> decide
    have hx : (x 0).toNat ≤ 1 := by cases x 0 <;> decide
    constructor
    · intro hlt
      change (μ 0).toNat+2*number μ'<(x 0).toNat+2*number x' at hlt
      by_cases ht : number μ'<number x'
      · obtain ⟨h,hm,hh,hhi⟩ := (ih μ' x').mp ht
        refine ⟨h.succ,hm,hh,?_⟩
        intro i hi
        cases i using Fin.cases with
        | zero => exact False.elim (by simp at hi)
        | succ i => exact hhi i (Fin.succ_lt_succ_iff.mp hi)
      · have he : number μ'=number x' := by omega
        have het : μ'=x' := number_injective he
        have hμ0 : μ 0=false := by
          cases heμ : μ 0
          · rfl
          · simp only [heμ,Bool.toNat_true] at hlt
            omega
        have hx0 : x 0=true := by
          cases hex : x 0
          · simp only [hex,Bool.toNat_false] at hlt
            omega
          · rfl
        refine ⟨0,hμ0,hx0,?_⟩
        intro i hi
        cases i using Fin.cases with
        | zero => exact False.elim (lt_irrefl _ hi)
        | succ i => exact (congrFun het i).symm
    · rintro ⟨h,hμh,hxh,hhi⟩
      cases h using Fin.cases with
      | zero =>
        have he : x'=μ' := funext (fun i => hhi i.succ (Fin.succ_pos i))
        change (μ 0).toNat+2*number μ'<(x 0).toNat+2*number x'
        rw [he,hμh,hxh]
        simp
      | succ h =>
        have ht : number μ'<number x' := (ih μ' x').mpr
          ⟨h,hμh,hxh,fun i hi => hhi i.succ (Fin.succ_lt_succ_iff.mpr hi)⟩
        change (μ 0).toNat+2*number μ'<(x 0).toNat+2*number x'
        omega

theorem threshold_none {d : ℕ} (μ x : Digits d) : ThresholdAllowed μ none x ↔ x=μ := by
  simp only [ThresholdAllowed,thresholdDomain,Finset.mem_singleton]
  exact ⟨fun h => funext h,fun h i => congrFun h i⟩

theorem threshold_some {d : ℕ} (μ x : Digits d) (h : {h : Fin d // μ h=false}) :
    ThresholdAllowed μ (some h) x ↔ GreaterAt μ x h.val := by
  constructor
  · intro hh
    exact ⟨h.property,by simpa [thresholdDomain] using hh h.val,
      fun i hi => by simpa [thresholdDomain,hi] using hh i⟩
  · rintro ⟨_,hh,hhi⟩ i
    by_cases hi : h.val < i
    · simp [thresholdDomain,hi,hhi i hi]
    · by_cases he : i=h.val
      · subst i
        simp [thresholdDomain,hh]
      · simp [thresholdDomain,hi,he]

theorem threshold_exact {d : ℕ} (μ x : Digits d) :
    (∃ h, ThresholdAllowed μ h x) ↔ number μ ≤ number x := by
  constructor
  · rintro ⟨h,hh⟩
    cases h with
    | none => rw [(threshold_none μ x).mp hh]
    | some h => exact Nat.le_of_lt ((number_lt_iff μ x).mpr ⟨h.val,(threshold_some μ x h).mp hh⟩)
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · obtain ⟨i,hi⟩ := (number_lt_iff μ x).mp h
      exact ⟨some ⟨i,hi.1⟩,(threshold_some μ x ⟨i,hi.1⟩).mpr hi⟩
    · exact ⟨none,(threshold_none μ x).mpr (number_injective h).symm⟩

end VariableWL.Binary

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_ProductCellular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.Circuit.ProductCellular
open Binary ProductImages.Instance
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable1} {d m : ℕ}

namespace Data
variable (D : Data L d m)

theorem seeds_exact (f : L) (x : Address d) : (f,x) ∈ D.description.requests false ↔
    number (timeBits x)=0 ∧ f=D.initial (Binary.equivalence d (positionBits x)) := by
  classical
  have ht : (∀ i, timeBits x i=false) ↔ number (timeBits x)=0 := by
    constructor
    · intro h; rw [funext h,number_false]
    · intro h
      have he := number_injective (h.trans (number_false d).symm)
      exact congrFun he
  constructor
  · rintro ⟨b,hg,hb,hreq⟩
    rcases b with (j|h)|f'
    · have hp := (D.request_parts _ _).mp hreq
      have hx : positionBits x=D.inputBits j := funext (fun i => Finset.mem_singleton.mp (hp.2 i))
      refine ⟨ht.mp (fun i => Finset.mem_singleton.mp (hp.1 i)),?_⟩
      change D.input j=f at hg
      rw [initial,equivalence_val,hx,D.number_inputBits]
      simpa using hg.symm
    · have hp := (D.request_parts _ _).mp hreq
      have hj : m ≤ number (positionBits x) := by
        rw [← D.number_threshold]
        exact (threshold_exact _ _).mp ⟨h,hp.2⟩
      refine ⟨ht.mp (fun i => Finset.mem_singleton.mp (hp.1 i)),?_⟩
      change D.blank=f at hg
      simp [initial,not_lt.mpr hj,hg]
    · cases hb
  · rintro ⟨hx,hf⟩
    by_cases hj : number (positionBits x) < m
    · let j : Fin m := ⟨number (positionBits x),hj⟩
      refine ⟨.inl (.inl j),?_,rfl,?_⟩
      · change D.input j=f
        simpa [initial,hj,j] using hf.symm
      · apply (D.request_parts _ _).mpr
        refine ⟨fun i => by simpa [requestTimeDomain] using (ht.mpr hx i),?_⟩
        have hp : positionBits x=D.inputBits j := number_injective (by rw [D.number_inputBits])
        intro i
        simp [requestPositionDomain,← hp]
    · obtain ⟨h,hh⟩ := (threshold_exact D.threshold (positionBits x)).mpr (by rw [D.number_threshold]; omega)
      refine ⟨.inl (.inr h),?_,rfl,?_⟩
      · change D.blank=f
        simpa [initial,hj] using hf.symm
      · exact (D.request_parts _ _).mpr
          ⟨fun i => by simpa [requestTimeDomain] using (ht.mpr hx i),hh⟩

end Data

end VariableWL.Circuit.ProductCellular

namespace VariableWL.Circuit.ProductCellular
open Binary
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable8} {d m : ℕ}

theorem address_ext {x y : Address d} (ht : number (timeBits x)=number (timeBits y))
    (hp : position x=position y) : x=y := by
  have htime := number_injective ht
  have hpos := (Binary.equivalence d).injective hp
  rw [← join_parts x,← join_parts y,htime,hpos]

theorem index_increment (h : Option (Fin d)) (x : Digits d) (hx : CyclicAllowed true h x) :
    Binary.equivalence d (cyclicFlip h x)=Binary.equivalence d x+1 := by
  apply Fin.ext
  simpa only [equivalence_val,Fin.val_add,Fin.val_one',Nat.add_mod_mod] using cyclic_increment h x hx

theorem index_decrement (h : Option (Fin d)) (x : Digits d) (hx : CyclicAllowed false h x) :
    Binary.equivalence d (cyclicFlip h x)=Binary.equivalence d x-1 := by
  by_cases hd : d=0
  · subst d
    have : Subsingleton (Fin (2^0)) := by change Subsingleton (Fin 1); infer_instance
    exact Subsingleton.elim _ _
  · have hp : 1 < 2^d := by
      obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
      have he : 0 < 2^e := pow_pos (by decide) _
      rw [pow_succ]
      omega
    apply Fin.ext
    simp only [equivalence_val,Fin.val_sub,Fin.val_one',Nat.mod_eq_of_lt hp]
    have he := cyclic_decrement h x hx
    convert he using 1
    congr 1
    omega

namespace Data
variable (D : Data L d m)

 theorem left_coordinates (abc : Cellular.Triple L) (h : Fin d) (j : Option (Fin d))
    (x : Address d) (hx : D.description.Allowed (abc,left h j) x) :
    number (timeBits (D.description.mapAddress (abc,left h j) x))=number (timeBits x)+1 ∧
    position (D.description.mapAddress (abc,left h j) x)=position x+1 := by
  obtain ⟨ht,hp⟩ := (D.allowed_parts _ _ _).mp hx
  constructor
  · rw [time_mapAddress]
    change number (Binary.flip h (timeBits x))=number (timeBits x)+1
    exact number_flip h (timeBits x) ht
  · change Binary.equivalence d (positionBits (D.description.mapAddress (abc,left h j) x))=Binary.equivalence d (positionBits x)+1
    rw [position_mapAddress]
    change Binary.equivalence d (Binary.cyclicFlip j (positionBits x))=Binary.equivalence d (positionBits x)+1
    exact index_increment j (positionBits x) hp

 theorem center_coordinates (abc : Cellular.Triple L) (h : Fin d)
    (x : Address d) (hx : D.description.Allowed (abc,center h) x) :
    number (timeBits (D.description.mapAddress (abc,center h) x))=number (timeBits x)+1 ∧
    position (D.description.mapAddress (abc,center h) x)=position x := by
  obtain ⟨ht,_⟩ := (D.allowed_parts _ _ _).mp hx
  constructor
  · rw [time_mapAddress]
    change number (Binary.flip h (timeBits x))=number (timeBits x)+1
    exact number_flip h (timeBits x) ht
  · simp only [position,position_mapAddress,positionMap,center,id_eq]

 theorem right_coordinates (abc : Cellular.Triple L) (h : Fin d) (j : Option (Fin d))
    (x : Address d) (hx : D.description.Allowed (abc,right h j) x) :
    number (timeBits (D.description.mapAddress (abc,right h j) x))=number (timeBits x)+1 ∧
    position (D.description.mapAddress (abc,right h j) x)=position x-1 := by
  obtain ⟨ht,hp⟩ := (D.allowed_parts _ _ _).mp hx
  constructor
  · rw [time_mapAddress]
    change number (Binary.flip h (timeBits x))=number (timeBits x)+1
    exact number_flip h (timeBits x) ht
  · change Binary.equivalence d (positionBits (D.description.mapAddress (abc,right h j) x))=Binary.equivalence d (positionBits x)-1
    rw [position_mapAddress]
    change Binary.equivalence d (Binary.cyclicFlip j (positionBits x))=Binary.equivalence d (positionBits x)-1
    exact index_decrement j (positionBits x) hp

@[simp] theorem same_map (abc : Cellular.Triple L) (v : Bool) (x : Address d) :
    D.description.mapAddress (abc,same v) x=x := by
  apply address_ext
  · simp only [time_mapAddress,timeMap,same,id_eq]
  · simp only [position,position_mapAddress,positionMap,same,id_eq]

 theorem meaningful_edge (e : D.description.ExpandedEdges) :
    D.gateMeaning (D.system.source e) → D.portMeaning (D.system.destination e) := by
  rcases e with ⟨⟨⟨a,b,c⟩,k⟩,x,hx⟩
  rcases k with ⟨h,j⟩ | h | ⟨h,j⟩ | v
  · obtain ⟨ht,hp⟩ := D.left_coordinates (a,b,c) h j x hx
    change D.state (number (timeBits x)) (position x)=a →
      0 < number (timeBits (D.description.mapAddress ((a,b,c),left h j) x)) ∧
      D.state (number (timeBits (D.description.mapAddress ((a,b,c),left h j) x))-1)
        (position (D.description.mapAddress ((a,b,c),left h j) x)-1)=a
    simp only [ht,hp,Nat.add_sub_cancel,add_sub_cancel_right,Nat.zero_lt_succ,true_and]
    exact id
  · obtain ⟨ht,hp⟩ := D.center_coordinates (a,b,c) h x hx
    change D.state (number (timeBits x)) (position x)=b →
      0 < number (timeBits (D.description.mapAddress ((a,b,c),center h) x)) ∧
      D.state (number (timeBits (D.description.mapAddress ((a,b,c),center h) x))-1)
        (position (D.description.mapAddress ((a,b,c),center h) x))=b
    simp only [ht,hp,Nat.add_sub_cancel,Nat.zero_lt_succ,true_and]
    exact id
  · obtain ⟨ht,hp⟩ := D.right_coordinates (a,b,c) h j x hx
    change D.state (number (timeBits x)) (position x)=c →
      0 < number (timeBits (D.description.mapAddress ((a,b,c),right h j) x)) ∧
      D.state (number (timeBits (D.description.mapAddress ((a,b,c),right h j) x))-1)
        (position (D.description.mapAddress ((a,b,c),right h j) x)+1)=c
    simp only [ht,hp,Nat.add_sub_cancel,sub_add_cancel,Nat.zero_lt_succ,true_and]
    exact id
  · cases v
    · change D.gateMeaning (.inr (((a,b,c),false),x)) →
        D.gateMeaning (.inr (((a,b,c),false),D.description.mapAddress ((a,b,c),same false) x))
      rw [D.same_map]
      exact id
    · change D.gateMeaning (.inr (((a,b,c),true),x)) →
        D.state (number (timeBits (D.description.mapAddress ((a,b,c),same true) x)))
          (position (D.description.mapAddress ((a,b,c),same true) x))=D.rule a b c
      rw [D.same_map]
      rintro ⟨ht,ha,hb,hc⟩
      have he : number (timeBits x)=(number (timeBits x)-1)+1 := by omega
      change D.cellular.state (number (timeBits x)) (position x)=D.rule a b c
      rw [he,Cellular.Data.state]
      change D.rule (D.state (number (timeBits x)-1) (position x-1))
        (D.state (number (timeBits x)-1) (position x))
        (D.state (number (timeBits x)-1) (position x+1))=D.rule a b c
      rw [ha,hb,hc]

 theorem true_meaning {g} (h : D.system.TrueGate g) : D.gateMeaning g := by
  induction h with
  | seed s hs =>
    rcases s with ⟨f,x⟩
    obtain ⟨ht,hf⟩ := (D.seeds_exact f x).mp hs
    change D.cellular.state (number (timeBits x)) (position x)=f
    rw [ht,Cellular.Data.state]
    exact hf.symm
  | scalar e s he hs ih =>
    have hh := D.meaningful_edge e ih
    rw [he] at hh
    exact hh
  | and a e f he hf hs ht ihe ihf =>
    have hh := D.meaningful_edge e ihe
    have hk := D.meaningful_edge f ihf
    rw [he] at hh
    rw [hf] at hk
    rcases a with ⟨⟨abc,v⟩,x⟩
    cases v
    · exact ⟨hh.1,hh.2,hk.2⟩
    · exact ⟨hh.1,hh.2.1,hh.2.2,hk.2⟩

end Data
end VariableWL.Circuit.ProductCellular

namespace VariableWL.Circuit.ProductCellular
open Binary
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable9} {d m : ℕ}

theorem previousTime_case (x : Address d) (hx : 0 < number (timeBits x)) :
    ∃ h, Binary.Allowed true h (previousTime x) := by
  apply exists_allowed
  intro he
  have ht := number_lt (timeBits x)
  have ht' := number_true d
  rw [← he,number_previousTime] at ht'
  omega

namespace Data
variable (D : Data L d m)

theorem incoming_left (abc : Cellular.Triple L) (x : Address d) (hx : 0 < number (timeBits x)) :
    ∃ e : D.description.ExpandedEdges,
      D.system.source e=.inl (abc.1,backAddress x (position x-1)) ∧
      D.system.destination e=.inr (((abc,false),x),false) := by
  obtain ⟨h,hh⟩ := previousTime_case x hx
  let z := backAddress x (position x-1)
  obtain ⟨j,hj⟩ := exists_cyclicAllowed true (positionBits z)
  have hz : D.description.Allowed (abc,left h j) z := by
    apply (D.allowed_parts _ _ _).mpr
    exact ⟨fun i => by simpa only [z,backAddress,time_join,timeDomain,left] using hh i,hj⟩
  have hm : D.description.mapAddress (abc,left h j) z=x := by
    obtain ⟨ht,hp⟩ := D.left_coordinates abc h j z hz
    apply address_ext
    · rw [ht]
      change number (timeBits (backAddress x (position x-1)))+1=number (timeBits x)
      rw [time_backAddress]
      omega
    · rw [hp]
      exact by simp only [z,position_backAddress,sub_add_cancel]
  refine ⟨⟨(abc,left h j),z,hz⟩,rfl,?_⟩
  change portAt (.inr ((abc,false),false)) (D.description.mapAddress (abc,left h j) z)=_
  rw [hm]
  rfl

theorem incoming_center (abc : Cellular.Triple L) (x : Address d) (hx : 0 < number (timeBits x)) :
    ∃ e : D.description.ExpandedEdges,
      D.system.source e=.inl (abc.2.1,backAddress x (position x)) ∧
      D.system.destination e=.inr (((abc,false),x),true) := by
  obtain ⟨h,hh⟩ := previousTime_case x hx
  let z := backAddress x (position x)
  have hz : D.description.Allowed (abc,center h) z := by
    apply (D.allowed_parts _ _ _).mpr
    exact ⟨fun i => by simpa only [z,backAddress,time_join,timeDomain,center] using hh i,
      fun i => Finset.mem_univ _⟩
  have hm : D.description.mapAddress (abc,center h) z=x := by
    obtain ⟨ht,hp⟩ := D.center_coordinates abc h z hz
    apply address_ext
    · rw [ht]
      change number (timeBits (backAddress x (position x)))+1=number (timeBits x)
      rw [time_backAddress]
      omega
    · rw [hp]
      exact position_backAddress x _
  refine ⟨⟨(abc,center h),z,hz⟩,rfl,?_⟩
  change portAt (.inr ((abc,false),true)) (D.description.mapAddress (abc,center h) z)=_
  rw [hm]
  rfl

theorem incoming_right (abc : Cellular.Triple L) (x : Address d) (hx : 0 < number (timeBits x)) :
    ∃ e : D.description.ExpandedEdges,
      D.system.source e=.inl (abc.2.2,backAddress x (position x+1)) ∧
      D.system.destination e=.inr (((abc,true),x),true) := by
  obtain ⟨h,hh⟩ := previousTime_case x hx
  let z := backAddress x (position x+1)
  obtain ⟨j,hj⟩ := exists_cyclicAllowed false (positionBits z)
  have hz : D.description.Allowed (abc,right h j) z := by
    apply (D.allowed_parts _ _ _).mpr
    exact ⟨fun i => by simpa only [z,backAddress,time_join,timeDomain,right] using hh i,hj⟩
  have hm : D.description.mapAddress (abc,right h j) z=x := by
    obtain ⟨ht,hp⟩ := D.right_coordinates abc h j z hz
    apply address_ext
    · rw [ht]
      change number (timeBits (backAddress x (position x+1)))+1=number (timeBits x)
      rw [time_backAddress]
      omega
    · rw [hp]
      exact by simp only [z,position_backAddress,add_sub_cancel_right]
  refine ⟨⟨(abc,right h j),z,hz⟩,rfl,?_⟩
  change portAt (.inr ((abc,true),true)) (D.description.mapAddress (abc,right h j) z)=_
  rw [hm]
  rfl

theorem state_true (x : Address d) :
    D.system.TrueGate (.inl (D.state (number (timeBits x)) (position x),x)) := by
  have hall : ∀ t, ∀ x : Address d, number (timeBits x)=t →
      D.system.TrueGate (.inl (D.state t (position x),x)) := by
    intro t
    induction t with
    | zero =>
      intro x hx
      apply System.TrueGate.seed
      exact (D.seeds_exact _ _).mpr ⟨hx,rfl⟩
    | succ t ih =>
      intro x hx
      have hxpos : 0 < number (timeBits x) := by omega
      let abc : Cellular.Triple L := (D.state t (position x-1),D.state t (position x),D.state t (position x+1))
      obtain ⟨e0,hs0,hp0⟩ := D.incoming_left abc x hxpos
      obtain ⟨e1,hs1,hp1⟩ := D.incoming_center abc x hxpos
      obtain ⟨e2,hs2,hp2⟩ := D.incoming_right abc x hxpos
      have hi (j : Fin (2^d)) : number (timeBits (backAddress x j))=t := by rw [time_backAddress,hx]; omega
      have ht0 : D.system.TrueGate (D.system.source e0) := by
        rw [hs0]
        simpa only [abc,position_backAddress] using ih (backAddress x (position x-1)) (hi _)
      have ht1 : D.system.TrueGate (D.system.source e1) := by
        rw [hs1]
        simpa only [abc,position_backAddress] using ih (backAddress x (position x)) (hi _)
      have ht2 : D.system.TrueGate (D.system.source e2) := by
        rw [hs2]
        simpa only [abc,position_backAddress] using ih (backAddress x (position x+1)) (hi _)
      have hu : D.system.TrueGate (.inr ((abc,false),x)) := .and _ e0 e1 hp0 hp1 ht0 ht1
      let e3 : D.description.ExpandedEdges := ⟨(abc,same false),x,D.same_allowed abc false x⟩
      have hp3 : D.system.destination e3=.inr (((abc,true),x),false) := by
        change portAt (.inr ((abc,true),false)) (D.description.mapAddress (abc,same false) x)=_
        rw [D.same_map]
        rfl
      have hv : D.system.TrueGate (.inr ((abc,true),x)) := .and _ e3 e2 hp3 hp2 hu ht2
      let e4 : D.description.ExpandedEdges := ⟨(abc,same true),x,D.same_allowed abc true x⟩
      apply System.TrueGate.scalar e4 _ _ hv
      change portAt (.inl (D.rule abc.1 abc.2.1 abc.2.2)) (D.description.mapAddress (abc,same true) x)=_
      rw [D.same_map]
      rfl
  exact hall _ x rfl

theorem scalar_true_iff (f : L) (x : Address d) : D.system.TrueGate (.inl (f,x)) ↔
    D.state (number (timeBits x)) (position x)=f := by
  refine ⟨D.true_meaning,fun h => ?_⟩
  rw [← h]
  exact D.state_true x

theorem true_test_iff : (∃ s ∈ D.system.tests, D.system.TrueGate (.inl s)) ↔
    ∃ j, D.state (2^d-1) j ∈ D.accepting := by
  constructor
  · rintro ⟨⟨f,x⟩,hs,ht⟩
    obtain ⟨hx,hf⟩ := (D.tests_exact f x).mp hs
    have he := (D.scalar_true_iff f x).mp ht
    rw [hx] at he
    exact ⟨position x,he ▸ hf⟩
  · rintro ⟨j,hj⟩
    let x : Address d := join (fun _ => true) ((Binary.equivalence d).symm j)
    have ht : number (timeBits x)=2^d-1 := by
      simp only [x,time_join]
      have h := number_true d
      omega
    have hp : position x=j := by simp only [x,position_index_join,Equiv.apply_symm_apply]
    refine ⟨(D.state (2^d-1) j,x),(D.tests_exact _ _).mpr ⟨ht,hj⟩,?_⟩
    apply (D.scalar_true_iff _ _).mpr
    rw [ht,hp]

theorem consistency_iff : D.description.consistency.Consistent ↔
    ∀ j, D.state (2^d-1) j ∉ D.accepting := by
  rw [D.description.consistency_iff D.terminal]
  simpa only [not_exists,not_and] using not_congr D.true_test_iff

end Data
end VariableWL.Circuit.ProductCellular

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Program
attribute [-instance] _root_.OAI.VariableWL.MachineOneHead.instFintypeControl _root_.OAI.VariableWL.MachineReduction.comparisonFintype _root_.OAI.VariableWL.MachineReduction.letterFintype _root_.OAI.VariableWL.MachineReduction.realFintype _root_.OAI.VariableWL.MachineReduction.realNonempty _root_.OAI.VariableWL.MultiStack.instFintypeLabel _root_.OAI.VariableWL.MultiStack.instFintypeMotion _root_.OAI.VariableWL.MultiStack.instFintypeVars _root_.OAI.VariableWL.MultiStack.instInhabitedLabel _root_.OAI.VariableWL.MultiStack.instInhabitedVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation

variable {Γ : Type}

theorem configuration_ext {M : Machine} {a b : Configuration M}
    (hc : a.control=b.control) (hh : a.heads=b.heads) (hs : a.cells=b.cells) : a=b := by
  cases a
  cases b
  congr

namespace Program
variable {Q Γ : Type} {k : ℕ}

noncomputable section
variable [Fintype Q] [Fintype Γ]

 theorem controlCode_injective : Function.Injective (controlCode (Q:=Q)) := by
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some q => have := congrArg Fin.val h; dsimp [controlCode] at this; omega
  | some a => cases b with
    | none => have := congrArg Fin.val h; dsimp [controlCode] at this; omega
    | some b =>
      congr 1
      apply (Fintype.equivFin Q).injective
      apply Fin.ext
      have := congrArg Fin.val h
      simpa only [controlCode, Nat.add_right_cancel_iff] using this

 theorem symbolCode_injective : Function.Injective (symbolCode (Γ:=Γ)) := by
  intro a b h
  have hv := congrArg Fin.val h
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases b with
      | inl b => cases b
                 · change 0=1 at hv; omega
                 · change 0=2 at hv; omega
      | inr b => change 0=(Fintype.equivFin Γ b).val+3 at hv; omega
  | some a => cases b with
    | none => cases a with
      | inl a => cases a
                 · change 1=0 at hv; omega
                 · change 2=0 at hv; omega
      | inr a => change (Fintype.equivFin Γ a).val+3=0 at hv; omega
    | some b => cases a with
      | inl a => cases b with
        | inl b => cases a <;> cases b
                   · rfl
                   · change 1=2 at hv; omega
                   · change 2=1 at hv; omega
                   · rfl
        | inr b => cases a
                   · change 1=(Fintype.equivFin Γ b).val+3 at hv; omega
                   · change 2=(Fintype.equivFin Γ b).val+3 at hv; omega
      | inr a => cases b with
        | inl b => cases b
                   · change (Fintype.equivFin Γ a).val+3=1 at hv; omega
                   · change (Fintype.equivFin Γ a).val+3=2 at hv; omega
        | inr b =>
          congr 2
          apply (Fintype.equivFin Γ).injective
          apply Fin.ext
          change (Fintype.equivFin Γ a).val+3=(Fintype.equivFin Γ b).val+3 at hv
          omega

 @[simp] theorem control_roundtrip (q : Option Q) : controlDecode (controlCode q)=q :=
  Function.leftInverse_invFun controlCode_injective q
 @[simp] theorem symbol_roundtrip (a : Symbol Γ) : symbolDecode (symbolCode a)=a :=
  Function.leftInverse_invFun symbolCode_injective a

 theorem encodeWord (w : Word) (i : ℤ) :
    symbolCode (typedWordCells (Γ:=Γ) w i)=wordCells (Fintype.card Γ) w i := by
  unfold typedWordCells wordCells
  split_ifs
  · cases w[i.toNat]? with
    | none => rfl
    | some b => cases b <;> rfl
  · rfl

 theorem encode_initial (P : Program Q Γ k) (w : Word) :
    P.encodeState (initial w)=VariableWL.initial P.compile w := by
  apply configuration_ext <;> try rfl
  funext j i
  change symbolCode ((if j=0 then typedWordCells w else fun _ => none) i) =
    (if j=0 then wordCells _ w else fun _ => 0) i
  split_ifs with h
  · exact encodeWord w i
  · rfl

 theorem encode_step (P : Program Q Γ k) (s : State Q Γ k) :
    VariableWL.step P.compile (P.encodeState s)=(P.step s).map P.encodeState := by
  unfold VariableWL.step step
  change ((P.transition (controlDecode (controlCode s.control))
    (fun j => symbolDecode (symbolCode (s.cells j (s.heads j))))).map _).map _ = _
  simp only [control_roundtrip,symbol_roundtrip,Option.map_map]
  cases P.transition s.control (fun j => s.cells j (s.heads j)) with
  | none => rfl
  | some data =>
    apply congrArg some
    apply configuration_ext <;> try rfl
    funext j i
    change (if i=s.heads j then symbolCode (data.2 j).1 else symbolCode (s.cells j i)) =
      symbolCode (if i=s.heads j then (data.2 j).1 else s.cells j i)
    split_ifs <;> rfl

 theorem encode_run (P : Program Q Γ k) (w : Word) (t : ℕ) :
    VariableWL.run P.compile w t=P.encodeState (P.run w t) := by
  induction t with
  | zero => exact (P.encode_initial w).symm
  | succ t ih =>
    simp only [VariableWL.run,run,ih,P.encode_step]
    cases P.step (P.run w t) <;> rfl

 theorem compile_outputs (P : Program Q Γ k) {w out : Word} {T : ℕ}
    (h : P.OutputsWithin w out T) : VariableWL.OutputsWithin P.compile w out T := by
  obtain ⟨t,ht,halt,hout⟩ := h
  refine ⟨t,ht,?_,?_⟩
  · rw [P.encode_run,P.encode_step,halt]
    rfl
  · rw [P.encode_run]
    funext i
    change symbolCode ((P.run w t).cells 0 i)=wordCells _ out i
    rw [congrFun hout i]
    exact encodeWord out i

end
end Program
end VariableWL.Computation

namespace VariableWL.Computation

variable {Γ : Type}

 theorem typedWordCells_nil (i : ℤ) : typedWordCells (Γ:=Γ) [] i=none := by
  unfold typedWordCells
  split_ifs <;> rfl

 theorem typedWordCells_cons (b : Bool) (w : Word) (i : ℤ) :
    typedWordCells (Γ:=Γ) (b::w) i =
      if i=0 then bitSymbol b else typedWordCells w (i-1) := by
  by_cases hi : i=0
  · subst i
    rfl
  · rw [ite_eq_right hi]
    by_cases hn : i < 0
    · unfold typedWordCells
      rw [ite_eq_right (by omega),ite_eq_right (by omega)]
    · obtain ⟨n,hnat⟩ : ∃ n : ℕ, i=(n+1:ℕ) := by
        refine ⟨i.toNat-1,?_⟩
        have := Int.toNat_of_nonneg (by omega : 0 ≤ i)
        omega
      subst i
      unfold typedWordCells
      rw [ite_eq_left (by omega),ite_eq_left (by omega)]
      have hsub : ((n+1:ℕ):ℤ)-1=(n:ℤ) := by omega
      simp only [hsub,Int.toNat_natCast,List.getElem?_cons_succ]

 @[simp] theorem stackCells_nil (i : ℤ) : stackCells (Γ:=Γ) [] i=none :=
  typedWordCells_nil _

 theorem stackCells_cons (b : Bool) (w : Word) (i : ℤ) :
    stackCells (Γ:=Γ) (b::w) i =
      if i=stackHead w-1 then bitSymbol b else stackCells w i := by
  unfold stackCells
  rw [typedWordCells_cons]
  apply if_congr
  · simp only [List.length_cons,stackHead]
    omega
  · rfl
  · congr 1
    simp only [List.length_cons]
    omega

 theorem stackCells_head (w : Word) : stackCells (Γ:=Γ) w (stackHead w)=
    w.head?.bind bitSymbol := by
  cases w with
  | nil => simp
  | cons b w =>
    rw [stackCells_cons,ite_eq_left]
    · rfl
    · simp only [stackHead,List.length_cons]
      omega

 theorem stackCells_below (w : Word) (i : ℤ) (h : i < stackHead w) :
    stackCells (Γ:=Γ) w i=none := by
  unfold stackCells typedWordCells
  rw [ite_eq_right]
  unfold stackHead at h
  omega

namespace Stack

 theorem firstUpdate (a : Action) (w : Word) :
    stackHead w + (a.firstMove w.head?).displacement = stackHead (a.apply w) := by
  cases a <;> cases w <;>
    simp [stackHead,Action.firstMove,Action.apply,Motion.displacement]
  all_goals omega

 theorem secondUpdate (a : Action) (w : Word) (i : ℤ) :
    (if i=stackHead (a.apply w) then
      a.secondWrite (if stackHead (a.apply w)=stackHead w then
        a.firstWrite w.head? else stackCells w (stackHead (a.apply w)))
    else if i=stackHead w then a.firstWrite w.head? else stackCells (Γ:=Γ) w i) =
    stackCells (a.apply w) i := by
  cases a with
  | keep =>
    simp only [Action.apply,Action.secondWrite,Action.firstWrite,reduceCtorEq,ite_false,ite_true]
    split_ifs with h
    · subst i
      exact (stackCells_head w).symm
    · rfl
  | pop =>
    cases w with
    | nil => simp [Action.apply,Action.secondWrite,Action.firstWrite]
    | cons b w =>
      simp only [Action.apply,List.tail_cons,Action.secondWrite,Action.firstWrite,ite_true]
      have hh : stackHead (b::w)=stackHead w-1 := by
        simp only [stackHead,List.length_cons]; omega
      have hn : stackHead w ≠ stackHead w-1 := by omega
      simp only [hh,stackCells_cons,ite_eq_right hn]
      by_cases hi : i=stackHead w
      · subst i
        simp only [ite_true]
      · rw [ite_eq_right hi]
        by_cases hj : i=stackHead w-1
        · subst i
          simp only [ite_true]
          exact (stackCells_below w _ (by omega)).symm
        · simp only [ite_eq_right hj]
  | push b =>
    simp only [Action.apply,Action.secondWrite,Action.firstWrite,reduceCtorEq,ite_false]
    rw [stackCells_cons]
    have hh : stackHead (b::w)=stackHead w-1 := by
      simp only [stackHead,List.length_cons]; omega
    rw [hh]
    split_ifs with h₁ h₂
    · rfl
    · subst i
      exact (stackCells_head w).symm
    · rfl

variable {Q : Type} {k : ℕ}

 theorem Action.length_apply_le (a : Action) (w : Word) : (a.apply w).length ≤ w.length+1 := by
  cases a <;> cases w <;> simp [Action.apply]
  all_goals omega

 theorem Machine.length_run (M : Machine Q k) (w : Word) (t : ℕ) (j : Fin (k+1)) :
    ((M.run w t).tapes j).length ≤ w.length+t := by
  induction t with
  | zero =>
    dsimp [Machine.run,Machine.initial]
    split_ifs <;> simp
  | succ t ih =>
    simp only [Machine.run]
    unfold Machine.step
    cases h : M.transition (M.run w t).control (fun i => ((M.run w t).tapes i).head?) with
    | none => dsimp; omega
    | some d =>
      dsimp
      exact (Action.length_apply_le _ _).trans (by omega)

end Stack
end VariableWL.Computation

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Stack
attribute [-instance] _root_.OAI.VariableWL.MachineReduction.comparisonFintype _root_.OAI.VariableWL.MachineReduction.realFintype _root_.OAI.VariableWL.MachineReduction.realNonempty _root_.OAI.VariableWL.MultiStack.instFintypeMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation

variable {Q Γ : Type} {k : ℕ}

namespace Program
variable {Q Γ : Type} {k : ℕ}

 theorem evolve_add (P : Program Q Γ k) (s : State Q Γ k) (n m : ℕ) :
    P.evolve s (n+m)=P.evolve (P.evolve s n) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (P.step (P.evolve s (n+m))).getD (P.evolve s (n+m)) = _
    rw [ih]
    rfl

 theorem evolve_run (P : Program Q Γ k) (w : Word) (n : ℕ) :
    P.evolve (initial w) n=P.run w n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [evolve,run,ih]

 theorem evolve_one (P : Program Q Γ k) {s s' : State Q Γ k} (h : P.step s=some s') :
    P.evolve s 1=s' := by simp only [evolve,h,Option.getD_some]

end Program

 theorem state_ext {Q Γ : Type} {k : ℕ} {s t : State Q Γ k}
    (hc : s.control=t.control) (hh : s.heads=t.heads) (hs : s.cells=t.cells) : s=t := by
  cases s
  cases t
  congr

namespace Stack

 theorem step_eq_intermediate (P : Program Q Γ k) (s : Computation.State Q Γ k)
    (q : Option Q) (data : Fin (k+1) → Symbol Γ × Motion)
    (h : P.transition s.control (fun j => s.cells j (s.heads j))=some (q,data)) :
    P.step s=some (intermediate s q data) := by
  unfold Program.step
  rw [h]
  rfl

 theorem Machine.execute_two (M : Machine Q k) (s : State Q k)
    (q : Q) (acts : Fin (k+1) → Action)
    (h : M.transition s.control (fun j => (s.tapes j).head?)=some (q,acts)) :
    M.program.evolve (M.execState s) 2=
      M.execState ⟨q,fun j => (acts j).apply (s.tapes j)⟩ := by
  let data : Fin (k+2) → Symbol PUnit × Motion := Fin.cases (none,.stay)
    (fun j => ((acts j).firstWrite (s.tapes j).head?,
      (acts j).firstMove (s.tapes j).head?))
  let mid := intermediate (M.execState s) (some (.pending q acts)) data
  have hs : M.program.step (M.execState s)=some mid := by
    apply step_eq_intermediate
    dsimp only [Machine.program,Machine.execState]
    simp only [Fin.cases_succ,stackCells_head,readBit_bind,h]
    rfl
  have ht : M.program.step mid=some (M.execState ⟨q,fun j => (acts j).apply (s.tapes j)⟩) := by
    let data' : Fin (k+2) → Symbol PUnit × Motion :=
      Fin.cases (mid.cells 0 (mid.heads 0),.stay)
        (fun j => ((acts j).secondWrite (mid.cells j.succ (mid.heads j.succ)),.stay))
    have he : M.program.step mid=some (intermediate mid (some (.execute q)) data') := by
      apply step_eq_intermediate
      rfl
    rw [he]
    apply congrArg some
    apply state_ext
    · rfl
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · change (stackHead (s.tapes j)+((acts j).firstMove _).displacement)+0 = _
        rw [add_zero,firstUpdate]
        rfl
    · funext i x
      refine Fin.cases ?_ (fun j => ?_) i
      · change (if x=0+0 then (if 0+0=0 then none else none)
          else if x=0 then none else none)=none
        simp only [ite_self]
      · change (if x=stackHead (s.tapes j)+((acts j).firstMove _).displacement then
          (acts j).secondWrite (if stackHead (s.tapes j)+((acts j).firstMove _).displacement=
            stackHead (s.tapes j) then (acts j).firstWrite _ else
            stackCells (s.tapes j) (stackHead (s.tapes j)+((acts j).firstMove _).displacement))
          else if x=stackHead (s.tapes j) then (acts j).firstWrite _ else stackCells (s.tapes j) x) = _
        rw [firstUpdate]
        exact secondUpdate _ _ _
  simp only [Program.evolve,hs,Option.getD_some,ht]

end Stack
end VariableWL.Computation

namespace VariableWL.Computation

variable {Q Γ : Type} {k : ℕ}

 theorem typedWordCells_snoc (w : Word) (b : Bool) (i : ℤ) :
    typedWordCells (Γ:=Γ) (w++[b]) i =
      if i=(w.length:ℤ) then bitSymbol b else typedWordCells w i := by
  induction w generalizing i with
  | nil =>
    rw [List.nil_append,typedWordCells_cons]
    simp only [typedWordCells_nil,List.length_nil,Nat.cast_zero]
  | cons a w ih =>
    rw [List.cons_append,typedWordCells_cons,typedWordCells_cons,ih]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    split_ifs <;> first | rfl | (exfalso; omega)

namespace Stack

 theorem twoTapeUpdates (q qmid qfinal : Option Q) (h : ℤ) (c : ℤ → Symbol Γ)
    (ws : Fin (k+1) → Word) (io : Symbol Γ × Motion) (acts : Fin (k+1) → Action) :
    let mid := intermediate (tapeState q h c ws) qmid (firstData ws io acts)
    intermediate mid qfinal (secondData mid acts) =
      tapeState qfinal (h+io.2.displacement) (fun i => if i=h then io.1 else c i)
        (fun j => (acts j).apply (ws j)) := by
  dsimp only
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change h+io.2.displacement+0=h+io.2.displacement
      omega
    · change stackHead (ws j)+((acts j).firstMove _).displacement+0=stackHead _
      rw [add_zero,firstUpdate]
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=h+io.2.displacement then
        (if h+io.2.displacement=h then io.1 else c (h+io.2.displacement))
        else if x=h then io.1 else c x) = if x=h then io.1 else c x
      split_ifs <;> simp_all
    · change (if x=stackHead (ws j)+((acts j).firstMove _).displacement then
        (acts j).secondWrite (if stackHead (ws j)+((acts j).firstMove _).displacement=
          stackHead (ws j) then (acts j).firstWrite _ else
          stackCells (ws j) (stackHead (ws j)+((acts j).firstMove _).displacement))
        else if x=stackHead (ws j) then (acts j).firstWrite _ else stackCells (ws j) x) = _
      rw [firstUpdate]
      exact secondUpdate _ _ _

 theorem pushInput_apply (p : Word) (b : Bool) :
    (fun j : Fin (k+1) => (pushInput b j).apply (inputTapes p j))=inputTapes (p++[b]) := by
  funext j
  simp only [pushInput,inputTapes]
  split_ifs <;> simp [Action.apply,List.reverse_append]

 theorem inputCells_scan (p w : Word) (hp : 0 < p.length) :
    inputCells p w p.length=w.head?.bind bitSymbol := by
  unfold inputCells
  rw [ite_eq_right (by omega),sub_self]
  cases w <;> rfl

 theorem inputCells_blank (p : Word) (i : ℤ) : inputCells p [] i=
    if i=0 then marker else none := by
  simp only [inputCells,typedWordCells_nil]

 theorem inputCells_next (p w : Word) (b : Bool) (hp : 0 < p.length) (i : ℤ) :
    (if i=p.length then none else inputCells p (b::w) i)=inputCells (p++[b]) w i := by
  unfold inputCells
  rw [typedWordCells_cons]
  simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
  by_cases hz : i=0
  · subst i
    rw [ite_eq_right (by omega),ite_eq_left rfl,ite_eq_left rfl]
  · rw [ite_eq_right hz,ite_eq_right hz]
    by_cases hi : i=p.length
    · subst i
      rw [ite_eq_left rfl]
      have : (p.length:ℤ)-((p.length:ℤ)+1) = -1 := by omega
      rw [this]
      unfold typedWordCells
      rfl
    · rw [ite_eq_right hi,ite_eq_right (by omega)]
      congr 1
      omega

 theorem Machine.loading_two (M : Machine Q k) (p w : Word) (b : Bool) (hp : 0 < p.length) :
    M.program.evolve (M.loading p (b::w)) 2=M.loading (p++[b]) w := by
  let io : Symbol PUnit × Motion := (none,.right)
  let mid := intermediate (M.loading p (b::w)) (some (.put b))
    (firstData (inputTapes p) io (pushInput b))
  have hs : M.program.step (M.loading p (b::w))=some mid := by
    apply step_eq_intermediate
    dsimp only [Machine.program,Machine.loading,tapeState]
    simp only [Fin.cases_zero,inputCells_scan p _ hp,List.head?_cons,Option.bind_some,readBit_bit]
    congr 1
    funext j
    change (stackCells (inputTapes p j) (stackHead (inputTapes p j)),
      if j=0 then Motion.left else .stay) = _
    rw [stackCells_head]
    dsimp only [pushInput]
    split_ifs <;> rfl
  have ht : M.program.step mid=some (intermediate mid (some .read) (secondData mid (pushInput b))) := by
    apply step_eq_intermediate
    dsimp only [Machine.program,mid,intermediate]
    congr 1
    funext j
    dsimp only [pushInput]
    split_ifs <;> rfl
  simp only [Program.evolve,hs,Option.getD_some,ht]
  rw [show mid=intermediate (tapeState (some .read) p.length (inputCells p (b::w))
      (inputTapes p)) (some (.put b)) (firstData (inputTapes p) io (pushInput b)) from rfl]
  rw [twoTapeUpdates,pushInput_apply]
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (p.length:ℤ)+1=((p++[b]).length:ℤ)
      simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
    · rfl
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · exact inputCells_next p w b hp x
    · rfl

end Stack
end VariableWL.Computation

namespace VariableWL.Computation.Stack

variable {Q : Type} {k : ℕ}

 theorem initial_tapeState (w : Word) :
    Program.initial (Q:=Control Q k) (Γ:=PUnit) (k:=k+1) w =
    tapeState none 0 (typedWordCells w) (inputTapes []) := by
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (0:ℤ)=stackHead (inputTapes [] j)
      simp [inputTapes,stackHead]
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (if j.succ=0 then typedWordCells w else fun _ => none) x=stackCells (inputTapes [] j) x
      rw [ite_eq_right (Fin.succ_ne_zero j)]
      simp [inputTapes]

 theorem Machine.initial_two (M : Machine Q k) (b : Bool) (w : Word) :
    M.program.evolve (Program.initial (b::w)) 2=M.loading [b] w := by
  rw [initial_tapeState]
  let start : Computation.State (Control Q k) PUnit (k+1) := tapeState (none : Option (Control Q k)) 0 (typedWordCells (b::w)) (inputTapes [])
  let io : Symbol PUnit × Motion := (marker,.right)
  let mid := intermediate start (some (.put b)) (firstData (inputTapes []) io (pushInput b))
  have hs : M.program.step start=some mid := by
    apply step_eq_intermediate
    change instruction (Control.put (Q:=Q) (k:=k) b) (marker,.right)
      (fun j => (stackCells (inputTapes [] j) (stackHead (inputTapes [] j)),
        if j=0 then Motion.left else .stay)) = _
    congr 1
    funext j
    rw [stackCells_head]
    dsimp only [pushInput]
    split_ifs <;> rfl
  have ht : M.program.step mid=some (intermediate mid (some .read) (secondData mid (pushInput b))) := by
    apply step_eq_intermediate
    dsimp only [Machine.program,mid,intermediate]
    congr 1
    funext j
    dsimp only [pushInput]
    split_ifs <;> rfl
  change M.program.evolve start 2=_
  simp only [Program.evolve,hs,Option.getD_some,ht]
  rw [show mid=intermediate start (some (.put b)) (firstData (inputTapes []) io (pushInput b)) from rfl]
  rw [show start=tapeState (none : Option (Control Q k)) 0 (typedWordCells (b::w)) (inputTapes []) from rfl]
  rw [twoTapeUpdates,pushInput_apply]
  apply state_ext
  · rfl
  · rfl
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=0 then marker else typedWordCells (b::w) x)=inputCells [b] w x
      rw [typedWordCells_cons]
      unfold inputCells
      simp only [List.length_singleton,Nat.cast_one]
      split_ifs <;> rfl
    · rfl

 theorem Machine.loading_all (M : Machine Q k) (p w : Word) (hp : 0 < p.length) :
    M.program.evolve (M.loading p w) (2*w.length)=M.loading (p++w) [] := by
  induction w generalizing p with
  | nil => simp only [List.length_nil,mul_zero,Program.evolve,List.append_nil]
  | cons b w ih =>
    have he : 2*(b::w).length=2+2*w.length := by simp only [List.length_cons]; omega
    rw [he,Program.evolve_add,M.loading_two p w b hp]
    rw [ih (p++[b]) (by simp only [List.length_append,List.length_singleton]; omega)]
    simp only [List.append_assoc,List.singleton_append]

 theorem Machine.back_zero (M : Machine Q k) (ws : Fin (k+1) → Word) :
    M.program.step (M.backState 0 ws)=some (M.execState ⟨M.start,ws⟩) := by
  unfold Program.step
  change (instruction (Control.execute (k:=k) M.start) (none,.stay)
    (fun j => (stackCells (ws j) (stackHead (ws j)),.stay))).map _ = _
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact add_zero _
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=0 then none else if x=0 then marker else none)=none
      split_ifs <;> rfl
    · change (if x=stackHead (ws j) then stackCells (ws j) (stackHead (ws j))
        else stackCells (ws j) x)=stackCells (ws j) x
      split_ifs with h
      · rw [h]
      · rfl

 theorem Machine.back_succ (M : Machine Q k) (n : ℕ) (ws : Fin (k+1) → Word) :
    M.program.step (M.backState (n+1) ws)=some (M.backState n ws) := by
  have hz : ((n+1:ℕ):ℤ)≠0 := by omega
  unfold Program.step
  dsimp only [Machine.program,Machine.backState,tapeState,Fin.cases_zero]
  rw [ite_eq_right hz]
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change ((n+1:ℕ):ℤ)+(-1)=(n:ℤ)
      omega
    · exact add_zero _
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=((n+1:ℕ):ℤ) then none else if x=0 then marker else none)=
        if x=0 then marker else none
      split_ifs <;> first | rfl | (exfalso; omega)
    · change (if x=stackHead (ws j) then stackCells (ws j) (stackHead (ws j))
        else stackCells (ws j) x)=stackCells (ws j) x
      split_ifs with h
      · rw [h]
      · rfl

 theorem Machine.back_all (M : Machine Q k) (n : ℕ) (ws : Fin (k+1) → Word) :
    M.program.evolve (M.backState n ws) (n+1)=M.execState ⟨M.start,ws⟩ := by
  induction n with
  | zero => exact M.program.evolve_one (M.back_zero ws)
  | succ n ih =>
    rw [show n+1+1=1+(n+1) by omega,Program.evolve_add]
    rw [M.program.evolve_one (M.back_succ n ws),ih]

 theorem Machine.loading_end (M : Machine Q k) (p : Word) (hp : 0 < p.length) :
    M.program.step (M.loading p [])=some (M.backState (p.length-1) (inputTapes p)) := by
  unfold Program.step
  dsimp only [Machine.program,Machine.loading,tapeState,Fin.cases_zero]
  rw [inputCells_scan p [] hp]
  change (instruction (Control.back : Control Q k) (none,.left)
    (fun j => (stackCells (inputTapes p j) (stackHead (inputTapes p j)),.stay))).map _ = _
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (p.length:ℤ)+(-1)=((p.length-1:ℕ):ℤ)
      omega
    · exact add_zero _
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=p.length then none else inputCells p [] x)=if x=0 then marker else none
      rw [inputCells_blank]
      split_ifs <;> first | rfl | (exfalso; omega)
    · change (if x=stackHead (inputTapes p j) then stackCells (inputTapes p j) (stackHead (inputTapes p j))
        else stackCells (inputTapes p j) x)=stackCells (inputTapes p j) x
      split_ifs with h
      · rw [h]
      · rfl

 theorem Machine.initial_empty (M : Machine Q k) :
    M.program.evolve (Program.initial []) 1=M.execState (M.initial []) := by
  apply Program.evolve_one
  rw [initial_tapeState]
  unfold Program.step
  change (instruction (Control.execute (k:=k) M.start) (none,.stay)
    (fun j => (stackCells (inputTapes [] j) (stackHead (inputTapes [] j)),.stay))).map _ = _
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact add_zero _
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=0 then none else typedWordCells [] x)=none
      simp only [typedWordCells_nil,ite_self]
    · change (if x=stackHead (inputTapes [] j) then stackCells (inputTapes [] j) (stackHead (inputTapes [] j))
        else stackCells (inputTapes [] j) x)=stackCells (inputTapes [] j) x
      split_ifs with h
      · rw [h]
      · rfl

 theorem Machine.initialize_ (M : Machine Q k) (w : Word) :
    M.program.run w (3*w.length+1)=M.execState (M.initial w) := by
  rw [← Program.evolve_run]
  cases w with
  | nil => exact M.initial_empty
  | cons b w =>
    have hn : 3*(b::w).length+1=2+(2*w.length+(1+(w.length+1))) := by
      simp only [List.length_cons]; omega
    rw [hn,Program.evolve_add,M.initial_two,Program.evolve_add,
      M.loading_all [b] w (by simp),Program.evolve_add]
    rw [M.program.evolve_one (M.loading_end ([b]++w) (by simp)),
      show ([b]++w).length-1=w.length by simp,M.back_all]
    rfl

end VariableWL.Computation.Stack

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_OneHead
attribute [-instance] _root_.OAI.VariableWL.MachineReduction.comparisonFintype _root_.OAI.VariableWL.MachineReduction.realFintype _root_.OAI.VariableWL.MachineReduction.realNonempty _root_.OAI.VariableWL.MultiStack.instFintypeMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10

namespace VariableWL.Computation

variable {Q Γ : Type} {k : ℕ}

 theorem stackCells_pop (b : Bool) (w : Word) (i : ℤ) :
    (if i=stackHead (b::w) then none else stackCells (Γ:=Γ) (b::w) i)=stackCells w i := by
  rw [stackCells_cons]
  have hh : stackHead (b::w)=stackHead w-1 := by
    simp only [stackHead,List.length_cons]; omega
  rw [hh]
  split_ifs with h
  · subst i
    exact (stackCells_below w _ (by omega)).symm
  · rfl

namespace Stack

 theorem Machine.output_step (M : Machine Q k) (p remaining : Word) (b : Bool) (ws : Fin (k+1) → Word) :
    M.program.step (M.outputState p (b::remaining) ws)=some (M.outputState (p++[b]) remaining ws) := by
  unfold Program.step
  dsimp only [Machine.program,Machine.outputState,tapeState,Fin.cases_succ]
  rw [stackCells_head,Function.update_self,List.head?_cons,Option.bind_some,readBit_bit]
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (p.length:ℤ)+1=((p++[b]).length:ℤ)
      simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
    · change stackHead (Function.update ws M.output (b::remaining) j)+
        (if j=M.output then Motion.right else .stay).displacement=
        stackHead (Function.update ws M.output remaining j)
      by_cases h : j=M.output
      · subst j
        simp only [Function.update_self,ite_true,Motion.displacement,stackHead,List.length_cons]
        omega
      · simp only [Function.update_of_ne h,ite_eq_right h,Motion.displacement,add_zero]
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=p.length then bitSymbol b else typedWordCells p x)=typedWordCells (p++[b]) x
      exact (typedWordCells_snoc p b x).symm
    · change (if x=stackHead (Function.update ws M.output (b::remaining) j) then
        (if j=M.output then none else stackCells (Function.update ws M.output (b::remaining) j)
          (stackHead (Function.update ws M.output (b::remaining) j)))
        else stackCells (Function.update ws M.output (b::remaining) j) x)=
        stackCells (Function.update ws M.output remaining j) x
      by_cases h : j=M.output
      · subst j
        simp only [Function.update_self,ite_true]
        exact stackCells_pop b remaining x
      · simp only [Function.update_of_ne h,ite_eq_right h]
        split_ifs with hx
        · rw [hx]
        · rfl

 theorem Machine.output_all (M : Machine Q k) (p remaining : Word) (ws : Fin (k+1) → Word) :
    M.program.evolve (M.outputState p remaining ws) remaining.length=
      M.outputState (p++remaining) [] ws := by
  induction remaining generalizing p with
  | nil => simp only [List.length_nil,Program.evolve,List.append_nil]
  | cons b remaining ih =>
    rw [show (b::remaining).length=1+remaining.length by simp only [List.length_cons]; omega,
      Program.evolve_add,M.program.evolve_one (M.output_step p remaining b ws),ih]
    simp only [List.append_assoc,List.singleton_append]

 theorem Machine.output_halt (M : Machine Q k) (p : Word) (ws : Fin (k+1) → Word) :
    M.program.step (M.outputState p [] ws)=none := by
  unfold Program.step
  dsimp only [Machine.program,Machine.outputState,tapeState,Fin.cases_succ]
  rw [Function.update_self,stackCells_nil]
  rfl

 theorem Machine.execute_halt (M : Machine Q k) (s : State Q k) (h : M.step s=none) :
    M.program.step (M.execState s)=some (M.outputState [] (s.tapes M.output) s.tapes) := by
  have ht : M.transition s.control (fun j => (s.tapes j).head?)=none := by
    unfold Machine.step at h
    exact Option.map_eq_none_iff.mp h
  unfold Program.step
  dsimp only [Machine.program,Machine.execState,Fin.cases_succ]
  rw [show (fun j => readBit (stackCells (s.tapes j) (stackHead (s.tapes j))))=
      (fun j => (s.tapes j).head?) by funext j; rw [stackCells_head,readBit_bind],ht]
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change stackHead (s.tapes j)+0=stackHead ((Function.update s.tapes M.output (s.tapes M.output)) j)
      rw [Function.update_eq_self,add_zero]
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=0 then none else none)=typedWordCells [] x
      simp only [ite_self,typedWordCells_nil]
    · change (if x=stackHead (s.tapes j) then stackCells (s.tapes j) (stackHead (s.tapes j))
        else stackCells (s.tapes j) x)=stackCells ((Function.update s.tapes M.output (s.tapes M.output)) j) x
      rw [Function.update_eq_self]
      split_ifs with hx
      · rw [hx]
      · rfl

 theorem Machine.execute_run (M : Machine Q k) (w : Word) (t : ℕ)
    (hno : ∀ u < t, M.step (M.run w u)≠none) :
    M.program.evolve (M.execState (M.initial w)) (2*t)=M.execState (M.run w t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (fun u hu => hno u (by omega))
    have hne := hno t (by omega)
    unfold Machine.step at hne
    have htrans : M.transition (M.run w t).control (fun j => ((M.run w t).tapes j).head?)≠none := by
      intro he
      apply hne
      rw [he]
      rfl
    obtain ⟨⟨q,acts⟩,ht⟩ := Option.ne_none_iff_exists'.mp htrans
    rw [show 2*(t+1)=2*t+2 by omega,Program.evolve_add,ih',M.execute_two (M.run w t) q acts ht]
    simp only [Machine.run,Machine.step,ht,Option.map_some,Option.getD_some]

 theorem Machine.compile_outputs (M : Machine Q k) {w out : Word} {T : ℕ}
    (h : M.OutputsWithin w out T) :
    M.program.OutputsWithin w out (4*(w.length+T+1)) := by
  obtain ⟨t,ht,halt,hout⟩ := h
  let haltPred := fun n => M.step (M.run w n)=none
  have hex : ∃ n, haltPred n := ⟨t,halt⟩
  let t₀ := Nat.find hex
  have ht₀ : t₀ ≤ t := Nat.find_min' hex halt
  have hstop : M.step (M.run w t₀)=none := Nat.find_spec hex
  have hn : ∀ u < t₀, M.step (M.run w u)≠none := by
    intro u hu
    exact Nat.find_min hex hu
  have stable {a : ℕ} (ha : M.step (M.run w a)=none) (n : ℕ) :
      M.run w (a+n)=M.run w a := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change (M.step (M.run w (a+n))).getD (M.run w (a+n))=_
      rw [ih,ha]
      rfl
  have hout₀ : (M.run w t₀).tapes M.output=out := by
    have hs := stable hstop (t-t₀)
    rw [Nat.add_sub_of_le ht₀] at hs
    rw [← hs]
    exact hout
  have hlen : out.length ≤ w.length+t₀ := by
    rw [← hout₀]
    exact M.length_run w t₀ M.output
  let elapsed := 3*w.length+1+(2*t₀+(1+out.length))
  have hr : M.program.run w elapsed=M.outputState out [] (M.run w t₀).tapes := by
    rw [← Program.evolve_run]
    unfold elapsed
    rw [Program.evolve_add,Program.evolve_run,M.initialize_,Program.evolve_add,
      M.execute_run w t₀ hn,Program.evolve_add,
      M.program.evolve_one (M.execute_halt (M.run w t₀) hstop),hout₀,M.output_all]
    rfl
  refine ⟨elapsed,by unfold elapsed; omega,?_,?_⟩
  · rw [hr]
    exact M.output_halt _ _
  · rw [hr]
    rfl

 theorem Machine.outputs_compile [Fintype Q] (M : Machine Q k) {w out : Word} {T : ℕ}
    (h : M.OutputsWithin w out T) :
    VariableWL.OutputsWithin M.compile w out (4*(w.length+T+1)) :=
  M.program.compile_outputs (M.compile_outputs h)

end Stack
end VariableWL.Computation

namespace VariableWL.OneHead

variable {Q : Type uVariable1} {Γ : Type uVariable2} {A : Type uVariable3}

theorem incoming_encode [DecidableEq A] (M : Program Q Γ) (s : State Q Γ A)
    (m : Motion) (i : A) : M.incoming m (encode s i) =
      if i=s.head ∧ (M.action s.control (s.cells s.head)).2.2=m
      then some (M.action s.control (s.cells s.head)).1 else none := by
  unfold Program.incoming encode
  by_cases h : i=s.head
  · subst i
    simp only [ite_true,Option.bind_some,true_and]
  · simp only [h,ite_false,Option.bind_none,false_and]

theorem rule_encode [AddCommGroup A] [DecidableEq A] (M : Program Q Γ)
    (u : A) (s : State Q Γ A) (i : A) :
    M.rule (encode s (i-u)) (encode s i) (encode s (i+u)) = encode (M.next u s) i := by
  apply Prod.ext
  · dsimp only [Program.rule,encode,Program.next]
    by_cases h : i=s.head
    · subst i
      simp only [ite_true,Option.elim_some,Function.update_self]
    · simp only [h,ite_false,Option.elim_none]
      exact (Function.update_of_ne h _ _).symm
  · change (M.incoming .right (encode s (i-u))).or
        ((M.incoming .stay (encode s i)).or (M.incoming .left (encode s (i+u)))) =
        if i=move u (M.action s.control (s.cells s.head)).2.2 s.head
        then some (M.action s.control (s.cells s.head)).1 else none
    rw [incoming_encode,incoming_encode,incoming_encode]
    cases h : (M.action s.control (s.cells s.head)).2.2 <;>
      simp only [move,reduceCtorEq,and_false,and_true,ite_false,Option.or_none,Option.none_or,
        sub_eq_iff_eq_add,eq_sub_iff_add_eq] <;> congr 1

theorem accepting_encode [DecidableEq A] (M : Program Q Γ) (s : State Q Γ A) :
    (∃ i, M.acceptingCell (encode s i)) ↔ M.accepting s.control (s.cells s.head)=true := by
  constructor
  · rintro ⟨i,q,hq,ha⟩
    by_cases hi : i=s.head
    · subst i
      have he : s.control=q := by simpa only [encode,ite_true,Option.some.injEq] using hq
      simpa only [encode,← he] using ha
    · simp only [encode,hi,ite_false] at hq
      cases hq
  · intro h
    exact ⟨s.head,s.control,by simp [encode],h⟩

theorem next_of_halt [AddGroup A] [DecidableEq A] (M : Program Q Γ) (u : A) (s : State Q Γ A)
    (h : M.transition s.control (s.cells s.head)=none) : M.next u s=s := by
  classical
  simp only [Program.next,Program.action,h,Option.getD_none,move,Function.update_eq_self]

theorem run_of_halt [AddGroup A] [DecidableEq A] (M : Program Q Γ) (u : A) (s : State Q Γ A)
    (h : M.transition s.control (s.cells s.head)=none) (t : ℕ) : M.run u s t=s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Program.run,ih,next_of_halt M u s h]

theorem run_add [AddGroup A] [DecidableEq A] (M : Program Q Γ) (u : A) (s : State Q Γ A) (a b : ℕ) :
    M.run u s (a+b)=M.run u (M.run u s a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change M.next u (M.run u s (a+b))=M.next u (M.run u (M.run u s a) b)
    rw [ih]

theorem run_freeze [AddGroup A] [DecidableEq A] (M : Program Q Γ) (u : A) (s : State Q Γ A) (a b : ℕ)
    (hab : a ≤ b) (h : M.transition (M.run u s a).control
      ((M.run u s a).cells (M.run u s a).head)=none) : M.run u s b=M.run u s a := by
  obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [run_add,run_of_halt M u _ h]

theorem head_bounds (M : Program Q Γ) (s : State Q Γ ℤ) (t : ℕ) :
    s.head-(t:ℤ) ≤ (M.run 1 s t).head ∧ (M.run 1 s t).head ≤ s.head+t := by
  induction t with
  | zero => simp [Program.run]
  | succ t ih =>
    change _ ≤ move 1 (M.action _ _).2.2 _ ∧ move 1 (M.action _ _).2.2 _ ≤ _
    cases (M.action (M.run 1 s t).control ((M.run 1 s t).cells (M.run 1 s t).head)).2.2 <;>
      simp only [move,Nat.cast_add,Nat.cast_one] <;> omega

end VariableWL.OneHead

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_StackSimulation
attribute [-instance] _root_.OAI.VariableWL.MultiStack.instFintypeMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12 uVariable13 uVariable14 uVariable15 uVariable16 uVariable17 uVariable18 uVariable19

namespace VariableWL.OneHead
variable {Q : Type uVariable1} {Γ : Type uVariable2} {A : Type uVariable3} {B : Type uVariable4} [AddCommGroup A] [AddCommGroup B] [DecidableEq A] [DecidableEq B]

theorem next_related (M : Program Q Γ) (u : A) (v : B) (f : A →+ B) (S : Set A)
    (hf : Set.InjOn f S) (hu : f u=v) (s : State Q Γ A) (t : State Q Γ B)
    (hr : Related f S s t) (hs : s.head ∈ S) :
    Related f S (M.next u s) (M.next v t) := by
  classical
  obtain ⟨hq,hh,hc⟩ := hr
  have ha : M.action t.control (t.cells t.head)=M.action s.control (s.cells s.head) := by
    rw [hq,hh,hc s.head hs]
  refine ⟨?_,?_,?_⟩
  · change (M.action t.control (t.cells t.head)).1=(M.action s.control (s.cells s.head)).1
    rw [ha]
  · change move v (M.action t.control (t.cells t.head)).2.2 t.head=
      f (move u (M.action s.control (s.cells s.head)).2.2 s.head)
    rw [ha,hh]
    cases (M.action s.control (s.cells s.head)).2.2 <;> simp [move,hu]
  · intro i hi
    change Function.update t.cells t.head (M.action t.control (t.cells t.head)).2.1 (f i)=
      Function.update s.cells s.head (M.action s.control (s.cells s.head)).2.1 i
    rw [ha,hh]
    by_cases he : i=s.head
    · subst i
      simp only [Function.update_self]
    · have hne : f i ≠ f s.head := fun h => he (hf hi hs h)
      rw [Function.update_of_ne hne,Function.update_of_ne he,hc i hi]

theorem run_related (M : Program Q Γ) (u : A) (v : B) (f : A →+ B) (S : Set A)
    (hf : Set.InjOn f S) (hu : f u=v) (s : State Q Γ A) (t : State Q Γ B)
    (hr : Related f S s t) (T : ℕ) (hs : ∀ n < T, (M.run u s n).head ∈ S) :
    Related f S (M.run u s T) (M.run v t T) := by
  induction T with
  | zero => exact hr
  | succ T ih =>
    exact next_related M u v f S hf hu _ _ (ih (fun n hn => hs n (by omega))) (hs T (by omega))

theorem cast_injOn_window (N T : ℕ) (hN : 2*T < N) :
    Set.InjOn (Int.castAddHom (ZMod N)) (window T) := by
  intro a ha b hb he
  change (a : ZMod N)=(b : ZMod N) at he
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub a b N).mp he
  have hab : -(N:ℤ) < b-a ∧ b-a < N := by
    have : (2:ℤ)*T < N := by exact_mod_cast hN
    obtain ⟨ha,ha'⟩ := ha
    obtain ⟨hb,hb'⟩ := hb
    omega
  obtain ⟨k,hk⟩ := hd
  have hNp : (0:ℤ)<N := by exact_mod_cast (show 0<N by omega)
  have hk0 : k=0 := by
    by_contra hh
    rcases lt_or_gt_of_ne hh with hn | hp
    · have hk1 : k ≤ -1 := by omega
      have hh := mul_le_mul_of_nonneg_left hk1 (le_of_lt hNp)
      omega
    · have hk1 : 1 ≤ k := by omega
      have hh := mul_le_mul_of_nonneg_left hk1 (le_of_lt hNp)
      omega
  rw [hk0,mul_zero] at hk
  omega

variable {m : ℕ}

theorem ringInput_cast (N T : ℕ) (hN : 2*T < N) (hm : m ≤ T)
    (blank : Γ) (w : Fin m → Γ) (i : ℤ) (hi : i ∈ window T) :
    ringInput N blank w (i : ZMod N)=lineInput blank w i := by
  have hNp : 0<N := by omega
  let : NeZero N := ⟨by omega⟩
  obtain ⟨hil,hir⟩ := hi
  by_cases h0 : 0 ≤ i
  · have hin : i < N := by omega
    have hv : ((i : ZMod N).val:ℤ)=i := by
      rw [ZMod.val_intCast,Int.emod_eq_of_lt h0 hin]
    have hvn : (i : ZMod N).val=i.toNat := by omega
    unfold ringInput lineInput
    split_ifs with h h'
    · congr 1
      apply Fin.ext
      exact hvn
    · omega
    · omega
    · rfl
  · have hmod : i % N=i+N := by
      have hmod0 : 0 ≤ i+(N:ℤ) := by omega
      have hmodN : i+(N:ℤ)<N := by omega
      have hx := Int.emod_eq_of_lt hmod0 hmodN
      simpa only [Int.add_emod_right] using hx
    have hv : ((i : ZMod N).val:ℤ)=i+N := by rw [ZMod.val_intCast,hmod]
    have hm' : ¬(i : ZMod N).val < m := by omega
    simp only [ringInput,hm',dite_false,lineInput,h0,false_and]

theorem initial_related (M : Program Q Γ) (N T : ℕ) (hN : 2*T<N) (hm : m ≤ T)
    (blank : Γ) (w : Fin m → Γ) :
    Related (Int.castAddHom (ZMod N)) (window T) (lineInitial M blank w) (ringInitial M N blank w) := by
  refine ⟨rfl,by simp [ringInitial,lineInitial],?_⟩
  intro i hi
  exact ringInput_cast N T hN hm blank w i hi

theorem line_ring_related (M : Program Q Γ) (N T : ℕ) (hN : 2*T<N) (hm : m ≤ T)
    (blank : Γ) (w : Fin m → Γ) (t : ℕ) (ht : t ≤ T) :
    Related (Int.castAddHom (ZMod N)) (window T)
      (M.run 1 (lineInitial M blank w) t) (M.run 1 (ringInitial M N blank w) t) := by
  apply run_related M 1 1 (Int.castAddHom (ZMod N)) (window T)
      (cast_injOn_window N T hN) (by simp) _ _ (initial_related M N T hN hm blank w) t
  intro n hn
  obtain ⟨hl,hr⟩ := head_bounds M (lineInitial M blank w) n
  change 0-(n:ℤ) ≤ _ at hl
  change _ ≤ 0+(n:ℤ) at hr
  constructor <;> omega

theorem line_ring_acceptance (M : Program Q Γ) (N T : ℕ) (hN : 2*T<N) (hm : m ≤ T)
    (blank : Γ) (w : Fin m → Γ) (t : ℕ) (ht : t ≤ T) :
    M.accepting (M.run 1 (ringInitial M N blank w) t).control
      ((M.run 1 (ringInitial M N blank w) t).cells (M.run 1 (ringInitial M N blank w) t).head) =
    M.accepting (M.run 1 (lineInitial M blank w) t).control
      ((M.run 1 (lineInitial M blank w) t).cells (M.run 1 (lineInitial M blank w) t).head) := by
  obtain ⟨hq,hh,hc⟩ := line_ring_related M N T hN hm blank w t ht
  rw [hq,hh,hc]
  obtain ⟨hl,hr⟩ := head_bounds M (lineInitial M blank w) t
  change 0-(t:ℤ) ≤ _ at hl
  change _ ≤ 0+(t:ℤ) at hr
  constructor <;> omega

end VariableWL.OneHead

namespace VariableWL.OneHead
variable {Q : Type uVariable5} {Γ : Type uVariable6} {m d : ℕ}

theorem finEquiv_val (N : ℕ) [NeZero N] (j : Fin N) : (ZMod.finEquiv N j).val=j.val := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N => rfl

theorem product_initial (M : Program Q Γ) (blank : Γ) (w : Fin m → Γ)
    (hfit : m < 2^d) (hm : 0 < m) (j : Fin (2^d)) :
    (product M blank w hfit).initial j =
      encode (ringInitial M (2^d) blank w) (ZMod.finEquiv (2^d) j) := by
  have hf : (ZMod.finEquiv (2^d) j).val=j.val := finEquiv_val _ j
  have hz : ZMod.finEquiv (2^d) j=0 ↔ j.val=0 := by
    rw [← (ZMod.finEquiv (2^d)).map_zero,(ZMod.finEquiv (2^d)).injective.eq_iff]
    exact Fin.ext_iff
  unfold Circuit.ProductCellular.Data.initial product
  dsimp only [encode,ringInitial,ringInput,markedInput]
  rw [hf]
  by_cases h : j.val < m
  · simp only [dite_eq_left h,hz]
  · have hj : j.val ≠ 0 := by omega
    simp only [dite_eq_right h,hz,hj,ite_false]

theorem product_state (M : Program Q Γ) (blank : Γ) (w : Fin m → Γ)
    (hfit : m < 2^d) (hm : 0 < m) (t : ℕ) (j : Fin (2^d)) :
    (product M blank w hfit).state t j =
      encode (M.run 1 (ringInitial M (2^d) blank w) t) (ZMod.finEquiv (2^d) j) := by
  induction t generalizing j with
  | zero => exact product_initial M blank w hfit hm j
  | succ t ih =>
    change M.rule ((product M blank w hfit).state t (j-1))
      ((product M blank w hfit).state t j) ((product M blank w hfit).state t (j+1)) = _
    rw [ih,ih,ih]
    simp only [map_sub,map_one,map_add]
    exact rule_encode M 1 _ _

theorem product_acceptance (M : Program Q Γ) (blank : Γ) (w : Fin m → Γ)
    (hfit : m < 2^d) (hm : 0 < m) (T t : ℕ) (hN : 2*T < 2^d) (hmT : m ≤ T) (ht : t ≤ T) :
    (∃ j, (product M blank w hfit).state t j ∈ (product M blank w hfit).accepting) ↔
    M.accepting (M.run 1 (lineInitial M blank w) t).control
      ((M.run 1 (lineInitial M blank w) t).cells (M.run 1 (lineInitial M blank w) t).head)=true := by
  have he : (∃ j, (product M blank w hfit).state t j ∈ (product M blank w hfit).accepting) ↔
      ∃ i : ZMod (2^d), M.acceptingCell (encode (M.run 1 (ringInitial M (2^d) blank w) t) i) := by
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨ZMod.finEquiv _ j,by
        change M.acceptingCell _ at hj
        simpa only [product_state M blank w hfit hm] using hj⟩
    · rintro ⟨i,hi⟩
      obtain ⟨j,rfl⟩ := (ZMod.finEquiv (2^d)).surjective i
      exact ⟨j,by
        change M.acceptingCell _
        simpa only [product_state M blank w hfit hm] using hi⟩
  rw [he,accepting_encode,line_ring_acceptance M (2^d) T hN hmT blank w t ht]

end VariableWL.OneHead

namespace VariableWL.OneHead
variable {Q : Type uVariable7} {Γ : Type uVariable8} {m d : ℕ}

theorem line_ring_halt (M : Program Q Γ) (N T : ℕ) (hN : 2*T<N) (hm : m ≤ T)
    (blank : Γ) (w : Fin m → Γ) (t : ℕ) (ht : t ≤ T)
    (h : M.transition (M.run 1 (lineInitial M blank w) t).control
      ((M.run 1 (lineInitial M blank w) t).cells (M.run 1 (lineInitial M blank w) t).head)=none) :
    M.transition (M.run 1 (ringInitial M N blank w) t).control
      ((M.run 1 (ringInitial M N blank w) t).cells (M.run 1 (ringInitial M N blank w) t).head)=none := by
  obtain ⟨hq,hh,hc⟩ := line_ring_related M N T hN hm blank w t ht
  rw [hq,hh,hc]
  · exact h
  · obtain ⟨hl,hr⟩ := head_bounds M (lineInitial M blank w) t
    change 0-(t:ℤ) ≤ _ at hl
    change _ ≤ 0+(t:ℤ) at hr
    constructor <;> omega

theorem product_final_acceptance (M : Program Q Γ) (blank : Γ) (w : Fin m → Γ)
    (hfit : m < 2^d) (hm : 0 < m) (T t : ℕ) (hN : 2*T < 2^d) (hmT : m ≤ T) (ht : t ≤ T)
    (halt : M.transition (M.run 1 (lineInitial M blank w) t).control
      ((M.run 1 (lineInitial M blank w) t).cells (M.run 1 (lineInitial M blank w) t).head)=none) :
    (∃ j, (product M blank w hfit).state (2^d-1) j ∈ (product M blank w hfit).accepting) ↔
    M.accepting (M.run 1 (lineInitial M blank w) t).control
      ((M.run 1 (lineInitial M blank w) t).cells (M.run 1 (lineInitial M blank w) t).head)=true := by
  have hf := run_freeze M (1 : ZMod (2^d)) (ringInitial M (2^d) blank w) t (2^d-1)
    (by omega) (line_ring_halt M (2^d) T hN hmT blank w t ht halt)
  have he : ∀ j, (product M blank w hfit).state (2^d-1) j=(product M blank w hfit).state t j := by
    intro j
    rw [product_state M blank w hfit hm,product_state M blank w hfit hm,hf]
  simp only [he]
  exact product_acceptance M blank w hfit hm T t hN hmT ht

theorem product_consistent_iff (M : Program Q Γ) (blank : Γ) (w : Fin m → Γ)
    (hfit : m < 2^d) (hm : 0 < m) (T t : ℕ) (hN : 2*T < 2^d) (hmT : m ≤ T) (ht : t ≤ T)
    (halt : M.transition (M.run 1 (lineInitial M blank w) t).control
      ((M.run 1 (lineInitial M blank w) t).cells (M.run 1 (lineInitial M blank w) t).head)=none) :
    (product M blank w hfit).description.consistency.Consistent ↔
    M.accepting (M.run 1 (lineInitial M blank w) t).control
      ((M.run 1 (lineInitial M blank w) t).cells (M.run 1 (lineInitial M blank w) t).head)=false := by
  rw [Circuit.ProductCellular.Data.consistency_iff]
  have h := product_final_acceptance M blank w hfit hm T t hN hmT ht halt
  simpa only [not_exists,Bool.not_eq_true] using not_congr h

end VariableWL.OneHead

namespace VariableWL.BoundedSimulation

namespace Steps
variable {S : Type uVariable10} {f : S → Option S} {a b c : S} {n m : ℕ}
theorem trans (h : Steps f n a b) (h' : Steps f m b c) : Steps f (n+m) a c := by
  induction h with
  | zero => simpa only [Nat.zero_add] using h'
  | @succ n a b c hab h ih => simpa only [Nat.succ_add] using Steps.succ hab (ih h')

theorem single (h : f a=some b) : Steps f 1 a b := Steps.succ h (Steps.zero b)

theorem tail (h : Steps f n a b) (h' : f b=some c) : Steps f (n+1) a c := h.trans (single h')

theorem head (h : f a=some b) (h' : Steps f n b c) : Steps f (n+1) a c := Steps.succ h h'
end Steps

theorem evolve_add {S : Type uVariable12} (f : S → Option S) (a : S) (n m : ℕ) :
    evolve f a (n+m)=evolve f (evolve f a n) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (f (evolve f a (n+m))).getD (evolve f a (n+m))=
      (f (evolve f (evolve f a n) m)).getD (evolve f (evolve f a n) m)
    rw [ih]

theorem Steps.evolve {S : Type uVariable13} {f : S → Option S} {n : ℕ} {a b : S}
    (h : Steps f n a b) : evolve f a n=b := by
  induction h with
  | zero => rfl
  | @succ n a b c hab h ih =>
    rw [Nat.add_comm,evolve_add]
    have he : BoundedSimulation.evolve f a 1=b := by change (f a).getD a=b; rw [hab]; rfl
    rw [he]
    exact ih

namespace Within
variable {S : Type uVariable15} {f : S → Option S} {a b c : S} {n m : ℕ}
theorem zero (a : S) : Within f a a 0 := ⟨0,le_rfl,Steps.zero a⟩
theorem mono (h : Within f a b n) (hn : n ≤ m) : Within f a b m :=
  let ⟨t,ht,hs⟩ := h; ⟨t,ht.trans hn,hs⟩
theorem trans (h : Within f a b n) (h' : Within f b c m) : Within f a c (n+m) := by
  obtain ⟨i,hi,h⟩ := h
  obtain ⟨j,hj,h'⟩ := h'
  exact ⟨i+j,Nat.add_le_add hi hj,h.trans h'⟩
theorem single (h : f a=some b) : Within f a b 1 := ⟨1,le_rfl,Steps.single h⟩
theorem head (h : f a=some b) (h' : Within f b c n) : Within f a c (n+1) := by
  simpa only [Nat.add_comm 1] using (single h).trans h'
theorem tail (h : Within f a b n) (h' : f b=some c) : Within f a c (n+1) := h.trans (single h')
end Within

end VariableWL.BoundedSimulation

namespace VariableWL.StackSimulation
open Turing TM2to1 TM2to1.Λ' VariableWL.BoundedSimulation
variable {K : Type uVariable16} {Γ : K → Type uVariable19} {Λ : Type uVariable17} {σ : Type uVariable18} [DecidableEq K]

omit [DecidableEq K] in
theorem operations_run {k : K} (s : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    operations (stRun s q)=operations q+1 := by cases s <;> rfl

omit [DecidableEq K] in
theorem stWrite_length {k : K} (v : σ) (l : List (Γ k)) (s : StAct K Γ σ k) :
    (stWrite v l s).length ≤ l.length+1 := by
  cases s <;> simp only [stWrite,List.length_cons,List.length_tail]
  all_goals omega

theorem stepAux_length (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (B : ℕ)
    (hS : ∀ k, (S k).length ≤ B) : ∀ k, ((TM2.stepAux q v S).stk k).length ≤ B+operations q := by
  induction q using stmtStRec generalizing v S B with
  | run k s q ih =>
    rw [step_run,operations_run]
    have hS' : ∀ j, (Function.update S k (stWrite v (S k) s) j).length ≤ B+1 := by
      intro j
      by_cases hj : j=k
      · subst j; rw [Function.update_self]; exact (stWrite_length v (S k) s).trans (Nat.add_le_add_right (hS k) 1)
      · rw [Function.update_of_ne hj]; exact (hS j).trans (by omega)
    intro j
    have h := ih (stVar v (S k) s) _ (B+1) hS' j
    omega
  | load f q ih => exact ih (f v) S B hS
  | branch p q r ihq ihr =>
    cases hp : p v
    · simpa only [TM2.stepAux,hp,Bool.cond_false,operations] using
        (fun k => (ihr v S B hS k).trans (Nat.add_le_add_left (le_max_right _ _) B))
    · simpa only [TM2.stepAux,hp,Bool.cond_true,operations] using
        (fun k => (ihq v S B hS k).trans (Nat.add_le_add_left (le_max_left _ _) B))
  | goto f => exact hS
  | halt => exact hS

variable (M : Λ → TM2.Stmt Γ Λ σ)

theorem go_steps {k : K} (o q v) {S : List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : L.map (proj k)=ListBlank.mk (S.map some).reverse) (n : ℕ) (H : n ≤ S.length) :
    Steps (TM1.step (tr M)) n ⟨some (go k o q),v,Tape.mk' ∅ (addBottom L)⟩
      ⟨some (go k o q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => exact Steps.zero _
  | succ n ih =>
    apply (ih (by omega)).tail
    rw [Function.iterate_succ_apply']
    simp only [TM1.step,TM1.stepAux,tr,Tape.mk'_nth_nat,Tape.move_right_n_head,addBottom_nth_snd]
    rw [stk_nth_val _ hL,List.getElem?_eq_getElem]
    · rfl
    · rwa [List.length_reverse]

theorem return_steps {q v} {L : ListBlank (∀ k, Option (Γ k))} (n : ℕ) :
    Steps (TM1.step (tr M)) n
      ⟨some (ret q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      ⟨some (ret q),v,Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => exact Steps.zero _
  | succ n ih =>
    refine Steps.head ?_ ih
    simp only [TM1.step]
    rw [Option.some_inj,tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,
      addBottom_nth_succ_fst,TM1.stepAux,Function.iterate_succ',Function.comp_apply,Tape.move_right_left]
    rfl

theorem normal_bound (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k))
    (L : ListBlank (∀ k, Option (Γ k)))
    (hL : ∀ k, L.map (proj k)=ListBlank.mk ((S k).map some).reverse)
    (B : ℕ) (hS : ∀ k, (S k).length ≤ B) :
    ∃ c, TrCfg (TM2.stepAux q v S) c ∧
      Within (TM1.step (tr M)) (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L))) c
        (operations q * (2*(B+operations q)+2)) := by
  induction q using stmtStRec generalizing v S L B with
  | run k o q ih =>
    rw [trNormal_run,step_run,operations_run]
    let S' := Function.update S k (stWrite v (S k) o)
    let v' := stVar v (S k) o
    obtain ⟨L',hL',hs⟩ := tr_respects_aux₂ (Λ := Λ) hL o
    have hS' : ∀ j, (S' j).length ≤ B+1 := by
      intro j
      dsimp only [S']
      by_cases hj : j=k
      · subst j
        rw [Function.update_self]
        exact (stWrite_length v (S k) o).trans (Nat.add_le_add_right (hS k) 1)
      · rw [Function.update_of_ne hj]
        exact (hS j).trans (by omega)
    obtain ⟨c,hc,hpath⟩ := ih v' S' L' hL' (B+1) hS'
    refine ⟨c,hc,?_⟩
    have hgo : Within (TM1.step (tr M))
        ⟨some (go k o q),v,Tape.mk' ∅ (addBottom L)⟩
        ⟨some (go k o q),v,(Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩
          (S k).length := ⟨_,le_rfl,go_steps M o q v (hL k) _ le_rfl⟩
    have hend : TM1.step (tr M)
        ⟨some (go k o q),v,(Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩ =
        some ⟨some (ret q),v',(Tape.move Dir.right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
      simp only [TM1.step,tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,addBottom_nth_snd,
        stk_nth_val _ (hL k),List.getElem?_eq_none (le_of_eq List.length_reverse),Option.isNone,cond]
      rw [hs]
      rfl
    have hret : Within (TM1.step (tr M))
        ⟨some (ret q),v',(Tape.move Dir.right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))⟩
        ⟨some (ret q),v',Tape.mk' ∅ (addBottom L')⟩ (S' k).length :=
      ⟨_,le_rfl,return_steps M _⟩
    have hbottom : TM1.step (tr M) ⟨some (ret q),v',Tape.mk' ∅ (addBottom L')⟩ =
        some (TM1.stepAux (trNormal q) v' (Tape.mk' ∅ (addBottom L'))) := by
      simp only [TM1.step,tr,TM1.stepAux,Tape.mk'_head,addBottom_head_fst,Bool.cond_true]
    change Within _ ⟨some (go k o q),v,Tape.mk' ∅ (addBottom L)⟩ c _
    apply (((hgo.tail hend).trans hret).tail hbottom |>.trans hpath).mono
    have hp := hS k
    have hp' := hS' k
    nlinarith
  | load f q ih => exact ih (f v) S L hL B hS
  | branch p q r ihq ihr =>
    cases hp : p v
    · dsimp only [TM2.stepAux,trNormal,TM1.stepAux]
      rw [hp]
      obtain ⟨c,hc,hpath⟩ := ihr v S L hL B hS
      refine ⟨c,hc,hpath.mono ?_⟩
      have hr : operations r ≤ operations (.branch p q r) := le_max_right _ _
      exact Nat.mul_le_mul hr (by omega)
    · dsimp only [TM2.stepAux,trNormal,TM1.stepAux]
      rw [hp]
      obtain ⟨c,hc,hpath⟩ := ihq v S L hL B hS
      refine ⟨c,hc,hpath.mono ?_⟩
      have hq : operations q ≤ operations (.branch p q r) := le_max_left _ _
      exact Nat.mul_le_mul hq (by omega)
  | goto f =>
    refine ⟨_,TrCfg.mk L hL,?_⟩
    simpa only [trNormal,TM1.stepAux,TM2.stepAux,operations,zero_mul,Option.map_some] using
      (Within.zero (f := TM1.step (tr M)) ⟨some (normal (f v)),v,Tape.mk' ∅ (addBottom L)⟩)
  | halt =>
    refine ⟨_,TrCfg.mk L hL,?_⟩
    simpa only [trNormal,TM1.stepAux,TM2.stepAux,operations,zero_mul,Option.map_none] using
      (Within.zero (f := TM1.step (tr M)) ⟨none,v,Tape.mk' ∅ (addBottom L)⟩)

end VariableWL.StackSimulation

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_MultiStack
attribute [-instance] _root_.OAI.VariableWL.MachineOneHead.instFintypeControl _root_.OAI.VariableWL.MachineReduction.comparisonFintype _root_.OAI.VariableWL.MachineReduction.letterFintype _root_.OAI.VariableWL.MachineReduction.realFintype _root_.OAI.VariableWL.MachineReduction.realNonempty _root_.OAI.VariableWL.MultiStack.instFintypeMotion _root_.OAI.VariableWL.MultiStack.instFintypeVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9

namespace VariableWL.StackSimulation
open Turing TM2to1 TM2to1.Λ' VariableWL.BoundedSimulation
variable {K : Type uVariable1} {Γ : K → Type uVariable9} {Λ : Type uVariable2} {σ : Type uVariable3} [DecidableEq K]
variable (M : Λ → TM2.Stmt Γ Λ σ) (C : ℕ) (hC : ∀ l, operations (M l) ≤ C)
include hC

 theorem next_length (c : TM2.Cfg Γ Λ σ) (B : ℕ) (hc : ∀ k, (c.stk k).length ≤ B) :
    ∀ k, (((TM2.step M c).getD c).stk k).length ≤ B+C := by
  rcases c with ⟨q,v,S⟩
  cases q with
  | none => exact fun k => (hc k).trans (Nat.le_add_right B C)
  | some q =>
    exact fun k => (stepAux_length (M q) v S B hc k).trans (Nat.add_le_add_left (hC q) B)

 theorem evolve_length (c : TM2.Cfg Γ Λ σ) (B : ℕ) (hc : ∀ k, (c.stk k).length ≤ B) (n : ℕ) :
    ∀ k, ((evolve (TM2.step M) c n).stk k).length ≤ B+n*C := by
  induction n with
  | zero => simpa only [evolve,Nat.zero_mul,Nat.add_zero] using hc
  | succ n ih =>
    intro k
    have h := next_length M C hC _ _ ih k
    simpa only [evolve,Nat.succ_mul,Nat.add_assoc] using h

 theorem one_bound (c : TM2.Cfg Γ Λ σ) (d : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ)
    (h : TrCfg c d) (B : ℕ) (hc : ∀ k, (c.stk k).length ≤ B) :
    ∃ d', TrCfg ((TM2.step M c).getD c) d' ∧
      Within (TM1.step (tr M)) d d' (1+C*(2*(B+C)+2)) := by
  cases h with
  | @mk q v S L hL =>
    cases q with
    | none =>
      refine ⟨_,TrCfg.mk L hL,(Within.zero _).mono (Nat.zero_le _)⟩
    | some q =>
      obtain ⟨d',hd',hp⟩ := normal_bound M (M q) v S L hL B hc
      refine ⟨d',hd',?_⟩
      have hs : TM1.step (tr M) ⟨some (normal q),v,Tape.mk' ∅ (addBottom L)⟩ =
          some (TM1.stepAux (trNormal (M q)) v (Tape.mk' ∅ (addBottom L))) := rfl
      apply (hp.head hs).mono
      have hh := hC q
      have hb : operations (M q)*(2*(B+operations (M q))+2) ≤ C*(2*(B+C)+2) :=
        Nat.mul_le_mul hh (by omega)
      omega

 theorem run_bound (c : TM2.Cfg Γ Λ σ) (d : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ)
    (h : TrCfg c d) (B : ℕ) (hc : ∀ k, (c.stk k).length ≤ B) (n : ℕ) :
    ∃ d', TrCfg (evolve (TM2.step M) c n) d' ∧
      Within (TM1.step (tr M)) d d' (n*(1+C*(2*(B+n*C+C)+2))) := by
  induction n with
  | zero => exact ⟨d,h,by simpa only [Nat.zero_mul] using (Within.zero (f := TM1.step (tr M)) d)⟩
  | succ n ih =>
    obtain ⟨dn,hdn,hpn⟩ := ih
    obtain ⟨dn',hdn',hpn'⟩ := one_bound M C hC _ dn hdn (B+n*C) (evolve_length M C hC c B hc n)
    refine ⟨dn',hdn',(hpn.trans hpn').mono ?_⟩
    have hb : 1+C*(2*(B+n*C+C)+2) ≤ 1+C*(2*(B+(n+1)*C+C)+2) := by
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul_left
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    calc
      n*(1+C*(2*(B+n*C+C)+2))+(1+C*(2*(B+n*C+C)+2))
          = (n+1)*(1+C*(2*(B+n*C+C)+2)) := by ring
      _ ≤ (n+1)*(1+C*(2*(B+(n+1)*C+C)+2)) := Nat.mul_le_mul_left _ hb

end VariableWL.StackSimulation

namespace VariableWL.BoundedSimulation.Steps
variable {S : Type uVariable4} {f : S → Option S} {n : ℕ} {a b c : S}

theorem rebase (he : f a=f b) (hn : 0<n) (h : Steps f n b c) : Steps f n a c := by
  cases h with
  | zero => omega
  | succ hs ht => exact Steps.succ (he.trans hs) ht

end VariableWL.BoundedSimulation.Steps

namespace VariableWL.UnitSimulation
open Turing VariableWL.BoundedSimulation
variable {Γ : Type uVariable5} {Λ : Type uVariable6} {σ : Type uVariable7} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]

variable (M : Λ → TM1.Stmt Γ Λ σ)

theorem statement_bound (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    ∃ n, 0<n ∧ n ≤ instructions q ∧
      Steps (TM0.step (TM1to0.tr M)) n ⟨(some q,v),T⟩
        (TM1to0.trCfg M (TM1.stepAux q v T)) := by
  induction q generalizing v T with
  | move d q ih =>
    obtain ⟨n,hn,hnq,h⟩ := ih v (T.move d)
    refine ⟨n+1,by omega,by simpa only [instructions] using Nat.add_le_add_right hnq 1,?_⟩
    exact Steps.head rfl h
  | write a q ih =>
    obtain ⟨n,hn,hnq,h⟩ := ih v (T.write (a T.1 v))
    refine ⟨n+1,by omega,by simpa only [instructions] using Nat.add_le_add_right hnq 1,?_⟩
    exact Steps.head rfl h
  | load a q ih =>
    obtain ⟨n,hn,hnq,h⟩ := ih (a T.1 v) T
    refine ⟨n,hn,hnq,?_⟩
    have he : TM0.step (TM1to0.tr M) ⟨(some (.load a q),v),T⟩ =
        TM0.step (TM1to0.tr M) ⟨(some q,a T.1 v),T⟩ := rfl
    simpa only [TM1.stepAux] using h.rebase he hn
  | branch p q r ihq ihr =>
    cases hp : p T.1 v
    · obtain ⟨n,hn,hnr,h⟩ := ihr v T
      refine ⟨n,hn,hnr.trans (le_max_right _ _),?_⟩
      have he : TM0.step (TM1to0.tr M) ⟨(some (.branch p q r),v),T⟩ =
          TM0.step (TM1to0.tr M) ⟨(some r,v),T⟩ := by
        simp only [TM0.step,TM1to0.tr,TM1to0.trAux,hp,Bool.cond_false]
      simpa only [TM1.stepAux,hp,Bool.cond_false] using h.rebase he hn
    · obtain ⟨n,hn,hnq,h⟩ := ihq v T
      refine ⟨n,hn,hnq.trans (le_max_left _ _),?_⟩
      have he : TM0.step (TM1to0.tr M) ⟨(some (.branch p q r),v),T⟩ =
          TM0.step (TM1to0.tr M) ⟨(some q,v),T⟩ := by
        simp only [TM0.step,TM1to0.tr,TM1to0.trAux,hp,Bool.cond_true]
      simpa only [TM1.stepAux,hp,Bool.cond_true] using h.rebase he hn
  | goto f =>
    refine ⟨1,by omega,le_rfl,Steps.single ?_⟩
    simp only [TM0.step,TM1to0.tr,TM1to0.trAux,TM1.stepAux,TM1to0.trCfg,
      Option.map_some,Tape.write_self]
  | halt =>
    refine ⟨1,by omega,le_rfl,Steps.single ?_⟩
    simp only [TM0.step,TM1to0.tr,TM1to0.trAux,TM1.stepAux,TM1to0.trCfg,
      Option.map_none,Option.map_some,Tape.write_self]

 theorem one_bound (S : Finset Λ) (C : ℕ) (hC : ∀ l ∈ S, instructions (M l) ≤ C)
    (c : TM1.Cfg Γ Λ σ) (hc : c.l ∈ Finset.insertNone S) :
    Within (TM0.step (TM1to0.tr M)) (TM1to0.trCfg M c)
      (TM1to0.trCfg M ((TM1.step M c).getD c)) C := by
  rcases c with ⟨q,v,T⟩
  cases q with
  | none => exact (Within.zero _).mono (Nat.zero_le _)
  | some q =>
    obtain ⟨n,_,hn,h⟩ := statement_bound M (M q) v T
    exact ⟨n,hn.trans (hC q (Finset.some_mem_insertNone.mp hc)),h⟩

 theorem steps_bound (S : Finset Λ) (hS : TM1.Supports M S) (C : ℕ)
    (hC : ∀ l ∈ S, instructions (M l) ≤ C) {a b : TM1.Cfg Γ Λ σ}
    {n : ℕ} (h : Steps (TM1.step M) n a b) (ha : a.l ∈ Finset.insertNone S) :
    Within (TM0.step (TM1to0.tr M)) (TM1to0.trCfg M a) (TM1to0.trCfg M b) (n*C) := by
  induction h with
  | zero => simpa only [Nat.zero_mul] using (Within.zero (f := TM0.step (TM1to0.tr M)) _)
  | @succ n a b c hs ht ih =>
    have hb := TM1.step_supports M hS hs ha
    have hfirst := one_bound M S C hC a ha
    rw [hs,Option.getD_some] at hfirst
    have hr := hfirst.trans (ih hb)
    simpa only [Nat.succ_mul,Nat.add_comm C] using hr

end VariableWL.UnitSimulation

namespace VariableWL.MultiStack
open Turing
variable (M : Machine)

theorem readAll_sem (ls : List (K M)) (q : Statement M) (v : Vars M) (S : Stacks M) :
    TM2.stepAux (readAll M ls q) v S=TM2.stepAux q (readVars M ls v S) S := by
  induction ls generalizing v with
  | nil => simp only [readAll,readVars,List.not_mem_nil,ite_false]
  | cons j ls ih =>
    simp only [readAll,TM2.stepAux,ih]
    congr 1
    apply Vars.ext <;> try rfl
    funext k
    simp only [readVars,List.mem_cons]
    by_cases hk : k ∈ ls
    · simp only [hk,or_true,ite_true]
    · simp only [hk,or_false,ite_false]
      by_cases he : k=j
      · subst k; cases S (j,true) <;> simp [List.headI]
      · simp only [he,ite_false,Function.update_of_ne he]

theorem readVars_all (v : Vars M) (S : Stacks M) :
    readVars M (allTapes M) v S={v with reads := fun j => (S (j,true)).headI} := by
  apply Vars.ext <;> try rfl
  funext j
  simp only [readVars,allTapes,List.mem_ofFn]
  simp

theorem writeTape_sem (j : K M) (q : Statement M) (v : Vars M) (S : Stacks M) :
    TM2.stepAux (writeTape M j q) v S =
      TM2.stepAux q (writeVars M v S j ((getData M v).2 j).2)
        (writeStacks M S j ((getData M v).2 j).1 ((getData M v).2 j).2) := by
  have hf : (j,false) ≠ (j,true) := by simp
  have ht : (j,true) ≠ (j,false) := Ne.symm hf
  have hh (l : List (Γ M)) : l.head?.getD 0=l.headI := by cases l <;> rfl
  cases hm : ((getData M v).2 j).2 <;>
    simp only [writeTape,TM2.stepAux,hm,decide_true,decide_false,Bool.cond_true,Bool.cond_false,
      reduceCtorEq,
      writeVars,writeStacks,Function.update_self,Function.update_of_ne hf,Function.update_of_ne ht,hh]
  all_goals simp only [getData,Function.update_idem,Function.update_comm hf]

theorem writeVars_data (v : Vars M) (S : Stacks M) (j : K M) (m : Motion) :
    (writeVars M v S j m).data=v.data := by cases m <;> rfl

theorem writeStacks_other (S : Stacks M) (j k : K M) (h : k ≠ j) (a : Γ M) (m : Motion) (b : Bool) :
    writeStacks M S j a m (k,b)=S (k,b) := by
  have hf : (k,b) ≠ (j,false) := by simp [h]
  have ht : (k,b) ≠ (j,true) := by simp [h]
  cases m <;> simp only [writeStacks,Function.update_of_ne hf,Function.update_of_ne ht]

theorem tape_writeStacks (S : Stacks M) (j : K M) (a : Γ M) (m : Motion) :
    tape M (writeStacks M S j a m) j=applyMotion M ((tape M S j).write a) m := by
  have hf : (j,false) ≠ (j,true) := by simp
  have ht : (j,true) ≠ (j,false) := Ne.symm hf
  cases m <;> simp [tape,writeStacks,applyMotion,Tape.mk₂,Tape.write_mk',
    ListBlank.head_mk,ListBlank.tail_mk,ListBlank.cons_mk,List.headI,hf]

theorem writeAll_sem (ls : List (K M)) (q : Statement M) (v : Vars M) (S : Stacks M) :
    ∃ v', v'.data=v.data ∧ TM2.stepAux (writeAll M ls q) v S=
      TM2.stepAux q v' (applyStacks M ls (getData M v) S) := by
  induction ls generalizing v S with
  | nil => exact ⟨v,rfl,rfl⟩
  | cons j ls ih =>
    rw [writeAll,writeTape_sem]
    obtain ⟨v',hv',hh⟩ := ih (writeVars M v S j ((getData M v).2 j).2)
      (writeStacks M S j ((getData M v).2 j).1 ((getData M v).2 j).2)
    refine ⟨v',hv'.trans (writeVars_data M v S j _),?_⟩
    simpa only [applyStacks,getData,writeVars_data] using hh

theorem tape_applyStacks (ls : List (K M)) (hn : ls.Nodup) (d : Data M) (S : Stacks M) (j : K M) :
    tape M (applyStacks M ls d S) j =
      if j ∈ ls then applyMotion M ((tape M S j).write (d.2 j).1) (d.2 j).2 else tape M S j := by
  induction ls generalizing S with
  | nil => rfl
  | cons k ls ih =>
    rw [applyStacks,ih hn.tail]
    by_cases he : j=k
    · subst j
      simp only [(List.nodup_cons.mp hn).1,ite_false,List.mem_cons_self,ite_true,tape_writeStacks]
    · have ho : tape M (writeStacks M S k (d.2 k).1 (d.2 k).2) j=tape M S j := by
        simp only [tape,writeStacks_other M S k j he]
      rw [ho]
      simp only [List.mem_cons,he,false_or]

end VariableWL.MultiStack

namespace VariableWL.MultiStack
open Turing BoundedSimulation
variable (M : Machine)

theorem applyMotion_nth (T : Tape (Γ M)) (m : Motion) (i : ℤ) :
    (applyMotion M T m).nth i=T.nth (i+m.displacement) := by
  cases m <;> simp [applyMotion,Motion.displacement,sub_eq_add_neg]

theorem allTapes_mem (j : K M) : j ∈ allTapes M := by
  exact List.mem_ofFn.mpr ⟨j,rfl⟩
theorem allTapes_nodup : (allTapes M).Nodup := by
  unfold allTapes
  exact List.nodup_ofFn.mpr Function.injective_id

theorem simulate_step {c c' : Configuration M} (s : Config M) (h : Related M c s)
    (hs : step M c=some c') :
    ∃ s', TM2.step (program M) s=some s' ∧ Related M c' s' := by
  obtain ⟨hl,ht⟩ := h
  obtain ⟨d,hd,rfl⟩ := Option.map_eq_some_iff.mp hs
  have hr : (fun j => (s.stk (j,true)).headI)=scanned c := by
    funext j
    simpa only [tape,Tape.mk₂,Tape.mk',ListBlank.head_mk,scanned,Tape.nth_zero,Int.add_zero] using ht j 0
  let v : Vars M := {s.var with reads := scanned c, data := some d}
  obtain ⟨v',hv',he⟩ := writeAll_sem M (allTapes M)
    (.goto (fun v => .simulate (getData M v).1)) v s.stk
  have hv : getData M v'=d := by simp only [getData,hv',v,Option.getD_some]
  let s' : Config M := ⟨some (.simulate d.1),v',applyStacks M (allTapes M) d s.stk⟩
  refine ⟨s',?_,rfl,?_⟩
  · cases s with
    | mk l var stk =>
      dsimp only at hl
      subst l
      simp only [TM2.step,program,readAll_sem,readVars_all,TM2.stepAux,hr,hd,
        Option.isSome_some,Bool.cond_true]
      change some (TM2.stepAux (writeAll M (allTapes M) _) v stk)=some s'
      rw [he]
      simp only [TM2.stepAux,s']
      rw [hv]
      rfl
  · intro j i
    change (tape M (applyStacks M (allTapes M) d s.stk) j).nth i = _
    rw [tape_applyStacks M _ (allTapes_nodup M),ite_eq_left (allTapes_mem M j),
      applyMotion_nth,Tape.write_nth]
    change (if i+(d.2 j).2.displacement=0 then (d.2 j).1 else
      (tape M s.stk j).nth (i+(d.2 j).2.displacement)) =
      if c.heads j+(d.2 j).2.displacement+i=c.heads j then (d.2 j).1
      else c.cells j (c.heads j+(d.2 j).2.displacement+i)
    rw [ht]
    have he : i+(d.2 j).2.displacement=0 ↔ c.heads j+(d.2 j).2.displacement+i=c.heads j := by omega
    simp only [he]
    congr 2
    omega

theorem simulate_steps {c c' : Configuration M} {n : ℕ} (s : Config M) (h : Related M c s)
    (hs : Steps (step M) n c c') :
    ∃ s', Steps (TM2.step (program M)) n s s' ∧ Related M c' s' := by
  induction hs generalizing s with
  | zero => exact ⟨s,Steps.zero s,h⟩
  | succ hs ht ih =>
    obtain ⟨s',hstep,hrel⟩ := simulate_step M s h hs
    obtain ⟨s'',hrun,hrel'⟩ := ih s' hrel
    exact ⟨s'',Steps.head hstep hrun,hrel'⟩

theorem simulate_halt (c : Configuration M) (s : Config M) (h : Related M c s)
    (hs : step M c=none) :
    TM2.step (program M) s = some
      ⟨some (.drain false),{reads := scanned c, data := none, answer := false},s.stk⟩ := by
  obtain ⟨hl,ht⟩ := h
  have hd : M.transition c.control (scanned c)=none := Option.map_eq_none_iff.mp hs
  have hr : (fun j => (s.stk (j,true)).headI)=scanned c := by
    funext j
    simpa only [tape,Tape.mk₂,Tape.mk',ListBlank.head_mk,scanned,Tape.nth_zero,Int.add_zero] using ht j 0
  cases s with
  | mk l var stk =>
    dsimp only at hl
    subst l
    simp only [TM2.step,program,readAll_sem,readVars_all,TM2.stepAux,hr,hd,
      Option.isSome_none,Bool.cond_false]

end VariableWL.MultiStack

namespace VariableWL.MultiStack
open Turing BoundedSimulation
variable (M : Machine)

theorem tape_nth_nat (S : Stacks M) (j : K M) (i : ℕ) :
    (tape M S j).nth i=(S (j,true)).getI i := by simp [tape,Tape.mk₂]
theorem tape_nth_neg (S : Stacks M) (j : K M) (i : ℕ) :
    (tape M S j).nth (-(i+1 : ℕ) : ℤ)=(S (j,false)).getI i := rfl

theorem initial_related (w : Word) : Related M (initial M w) (initialConfig M w) := by
  refine ⟨rfl,?_⟩
  intro j i
  change (tape M (initialStacks M w) j).nth i=(if j=0 then wordCells M.workSymbols w else fun _ => 0) (0+i)
  rw [Int.zero_add]
  cases i with
  | ofNat i =>
    change (tape M (initialStacks M w) j).nth (i : ℤ)=_
    rw [tape_nth_nat M (initialStacks M w) j i]
    by_cases hj : j=0
    · subst j
      simp only [initialStacks,Function.update_self,ite_true]
      change (List.map (inputSymbol M) w).getI i=wordCells M.workSymbols w (i : ℤ)
      simp only [wordCells,Int.natCast_nonneg,ite_true,Int.toNat_natCast,
        List.getI_eq_getElem?_getD,List.getElem?_map]
      cases hw : w[i]? with
      | none => rfl
      | some b => cases b <;> rfl
    · have h : (j,true) ≠ (0,true) := by simp [hj]
      simp only [initialStacks,Function.update_of_ne h,ite_eq_right hj,List.getI_nil]
      rfl
  | negSucc i =>
    have hn : Int.negSucc i=(-(i+1:ℕ):ℤ) := by omega
    rw [hn,tape_nth_neg]
    have h : (j,false) ≠ (0,true) := by simp
    simp only [initialStacks,Function.update_of_ne h,List.getI_nil]
    have hneg : ¬ (0 : ℤ) ≤ -(i+1:ℕ) := by omega
    by_cases hj : j=0
    · simp only [hj,ite_true,wordCells,hneg,ite_false]
      rfl
    · simp only [hj,ite_false]
      rfl

theorem initial_lengths (w : Word) (j : Slot M) : ((initialConfig M w).stk j).length ≤ w.length := by
  change (initialStacks M w j).length ≤ _
  by_cases hj : j=(0,true)
  · subst j; simp [initialStacks]
  · simp [initialStacks,Function.update_of_ne hj]

end VariableWL.MultiStack

namespace VariableWL.BoundedSimulation
variable {S : Type uVariable8}
theorem evolve_steps (f : S → Option S) (a : S) (n : ℕ) :
    ∃ t ≤ n, Steps f t a (evolve f a n) := by
  induction n with
  | zero => exact ⟨0,le_rfl,Steps.zero a⟩
  | succ n ih =>
    obtain ⟨t,ht,h⟩ := ih
    cases he : f (evolve f a n) with
    | none => exact ⟨t,by omega,by simpa only [evolve,he,Option.getD_none] using h⟩
    | some c => exact ⟨t+1,by omega,by simpa only [evolve,he,Option.getD_some] using h.tail he⟩
end VariableWL.BoundedSimulation

namespace VariableWL
 theorem run_eq_evolve (M : Machine) (w : Word) (n : ℕ) :
    run M w n=BoundedSimulation.evolve (step M) (initial M w) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run,BoundedSimulation.evolve,ih]
end VariableWL

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_MachineSimulation
attribute [-instance] _root_.OAI.VariableWL.MachineReduction.comparisonFintype _root_.OAI.VariableWL.MachineReduction.letterFintype _root_.OAI.VariableWL.MachineReduction.realFintype _root_.OAI.VariableWL.MachineReduction.realNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2

namespace VariableWL.MultiStack
open Turing BoundedSimulation
variable (M : Machine)

theorem drain_stage (b : Bool) (S : Stacks M) (v : Vars M) :
    Steps (TM2.step (program M)) ((S (0,b)).length+1)
      ⟨some (.drain b),v,S⟩
      ⟨drainLabel M b,drainVars M v (S (0,b)),Function.update S (0,b) []⟩ := by
  generalize he : S (0,b)=l
  induction l generalizing S v with
  | nil =>
    apply Steps.single
    simp only [TM2.step,program,TM2.stepAux,he,List.head?_nil,List.tail_nil,
      Option.isSome_none,reduceCtorEq,decide_false,Bool.or_false,
      Function.update_self,drainVars,found,List.contains_nil]
    cases b <;> rfl
  | cons a l ih =>
    let v' : Vars M :=
      { reads := Function.update v.reads 0 1
        data := none
        answer := v.answer || decide (a=2) }
    let S' : Stacks M := Function.update S (0,b) l
    have hs : TM2.step (program M) ⟨some (.drain b),v,S⟩=
        some ⟨some (.drain b),v',S'⟩ := by
      simp only [TM2.step,program,TM2.stepAux,he,List.head?_cons,List.tail_cons,
        Option.isSome_some,Function.update_self,Option.some.injEq]
      rfl
    have hh := ih S' v' (Function.update_self _ _ _)
    have hc : drainVars M v' l=drainVars M v (a::l) := by
      simp only [drainVars,v',Function.update_idem,found,List.contains_cons,Bool.or_assoc]
      congr 1
      have hd : decide (a=2)=(2==a) := by
        by_cases h : a=2
        · subst a; simp
        · have h' : (2 : Γ M) ≠ a := Ne.symm h
          simp [h,h']
      rw [hd]
    have hS : Function.update S' (0,b) []=Function.update S (0,b) [] := by
      exact Function.update_idem _ _ _
    simpa only [List.length_cons,hc,hS] using Steps.head hs hh

theorem drain_both (S : Stacks M) (v : Vars M) :
    ∃ s', Steps (TM2.step (program M)) ((S (0,false)).length+(S (0,true)).length+2)
      ⟨some (.drain false),v,S⟩ s' ∧ s'.l=none ∧
      s'.var.answer=(v.answer || (found M (S (0,false)) || found M (S (0,true)))) := by
  have h0 := drain_stage M false S v
  have h1 := drain_stage M true (Function.update S (0,false) []) (drainVars M v (S (0,false)))
  have hn : ((0 : K M),true) ≠ (0,false) := by simp
  rw [Function.update_of_ne hn] at h1
  have hh := h0.trans h1
  refine ⟨⟨none,drainVars M (drainVars M v (S (0,false))) (S (0,true)),
    Function.update (Function.update S (0,false) []) (0,true) []⟩,?_,rfl,?_⟩
  · have he : (S (0,false)).length+1+((S (0,true)).length+1)=
        (S (0,false)).length+(S (0,true)).length+2 := by omega
    simpa only [he,drainLabel,ite_true] using hh
  · simp only [drainVars,Bool.or_assoc]

end VariableWL.MultiStack

namespace VariableWL.MultiStack
open Turing BoundedSimulation
variable (M : Machine)

theorem exists_getI_two (l : List (Γ M)) : (∃ n, l.getI n=2) ↔ 2 ∈ l := by
  constructor
  · rintro ⟨n,hn⟩
    by_cases hl : n < l.length
    · rw [List.getI_eq_getElem _ hl] at hn
      exact hn ▸ List.getElem_mem hl
    · rw [List.getI_eq_default _ (by omega)] at hn
      have : (0 : Γ M)=2 := hn
      have hh := congrArg Fin.val this
      change 0=2 % (M.workSymbols+3) at hh
      rw [Nat.mod_eq_of_lt (by omega)] at hh
      omega
  · intro h
    obtain ⟨n,hn,he⟩ := List.mem_iff_getElem.mp h
    exact ⟨n,(List.getI_eq_getElem _ hn).trans he⟩

theorem tape_two_iff (S : Stacks M) (j : K M) : (∃ i, (tape M S j).nth i=2) ↔
    (found M (S (j,false)) || found M (S (j,true)))=true := by
  simp only [Bool.or_eq_true,found,List.contains_iff_mem]
  constructor
  · rintro ⟨i,hi⟩
    cases i with
    | ofNat n =>
      exact Or.inr ((exists_getI_two M _).mp ⟨n,(tape_nth_nat M S j n).symm.trans hi⟩)
    | negSucc n =>
      exact Or.inl ((exists_getI_two M _).mp ⟨n,hi⟩)
  · rintro (h | h)
    · obtain ⟨n,hn⟩ := (exists_getI_two M _).mpr h
      exact ⟨(-(n+1:ℕ):ℤ),hn⟩
    · obtain ⟨n,hn⟩ := (exists_getI_two M _).mpr h
      exact ⟨(n:ℤ),(tape_nth_nat M S j n).trans hn⟩

theorem symbol_zero_ne_two : (0 : Γ M) ≠ 2 := by
  intro h
  have hh := congrArg Fin.val h
  change 0=2 % (M.workSymbols+3) at hh
  rw [Nat.mod_eq_of_lt (by omega)] at hh
  omega

theorem symbol_one_ne_two : (1 : Γ M) ≠ 2 := by
  intro h
  have hh := congrArg Fin.val h
  change 1 % (M.workSymbols+3)=2 % (M.workSymbols+3) at hh
  rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at hh
  omega

theorem word_two_iff (b : Bool) : (∃ i, wordCells M.workSymbols [b] i=2) ↔ b=true := by
  constructor
  · rintro ⟨i,hi⟩
    unfold wordCells at hi
    split_ifs at hi with h
    · cases hn : i.toNat with
      | zero =>
        cases b with
        | false => exact (symbol_one_ne_two M (by simpa only [hn,List.getElem?_cons_zero] using hi)).elim
        | true => rfl
      | succ n => exact (symbol_zero_ne_two M (by simpa only [hn,List.getElem?_cons_succ,List.getElem?_nil] using hi)).elim
    · exact (symbol_zero_ne_two M hi).elim
  · rintro rfl
    exact ⟨0,rfl⟩

theorem related_output (c : Configuration M) (s : Config M) (h : Related M c s)
    (b : Bool) (hout : c.cells 0=wordCells M.workSymbols [b]) :
    (found M (s.stk (0,false)) || found M (s.stk (0,true)))=b := by
  apply Bool.eq_iff_iff.mpr
  rw [← tape_two_iff]
  have he : (∃ i, (tape M s.stk 0).nth i=2) ↔ ∃ i, wordCells M.workSymbols [b] i=2 := by
    constructor
    · rintro ⟨i,hi⟩
      rw [h.2,hout] at hi
      exact ⟨_,hi⟩
    · rintro ⟨i,hi⟩
      refine ⟨i-c.heads 0,?_⟩
      rw [h.2,hout]
      simpa only [add_sub_cancel] using hi
  exact he.trans (word_two_iff M b)

theorem operations_le (l : Label M) : StackSimulation.operations (program M l) ≤ operationsBound M :=
  Finset.le_sup (f := fun l : Label M => StackSimulation.operations (program M l)) (Finset.mem_univ l)

theorem outputs_simulated (w : Word) (b : Bool) (T : ℕ) (h : OutputsWithin M w [b] T) :
    ∃ n ≤ T+2*(w.length+T*operationsBound M)+3,
      ∃ s : Config M, Steps (TM2.step (program M)) n (initialConfig M w) s ∧
        s.l=none ∧ s.var.answer=b := by
  obtain ⟨t,ht,hhalt,hout⟩ := h
  obtain ⟨u,hu,hsteps⟩ := evolve_steps (step M) (initial M w) t
  rw [← run_eq_evolve] at hsteps
  obtain ⟨s,hs,hrel⟩ := simulate_steps M (initialConfig M w) (initial_related M w) hsteps
  have hlen := StackSimulation.evolve_length (program M) (operationsBound M) (operations_le M)
    (initialConfig M w) w.length (initial_lengths M w) u
  rw [hs.evolve] at hlen
  have hstop := simulate_halt M (run M w t) s hrel hhalt
  obtain ⟨s',hfinish,hl,ha⟩ := drain_both M s.stk
    {reads := scanned (run M w t), data := none, answer := false}
  have hh := hs.trans ((Steps.single hstop).trans hfinish)
  refine ⟨_,?_,s',hh,hl,?_⟩
  · have h0 := hlen (0,false)
    have h1 := hlen (0,true)
    have huT : u ≤ T := hu.trans ht
    have hc := Nat.mul_le_mul_right (operationsBound M) huT
    omega
  · rw [ha,Bool.false_or]
    exact related_output M (run M w t) s hrel b hout

end VariableWL.MultiStack

namespace VariableWL.TM0Adapter
open Turing BoundedSimulation
variable {Γ : Type uVariable1} {Λ : Type uVariable2} [Inhabited Γ] [Inhabited Λ]
variable (M : TM0.Machine Γ Λ) (S : Finset Λ) (hS : TM0.Supports M (S : Set Λ))

variable (accept : Λ → Γ → Bool)

omit [Inhabited Γ] in
theorem program_none (q : Control S) (a : Γ) (h : M q.val a=none) :
    (program M S hS accept).transition q a=none := by
  dsimp only [program]
  split <;> simp_all

omit [Inhabited Γ] in
theorem program_some (q : Control S) (a : Γ) (r : Λ) (t : TM0.Stmt Γ)
    (h : M q.val a=some (r,t)) :
    (program M S hS accept).transition q a=some (⟨r,hS.2 h q.property⟩,action a t) := by
  dsimp only [program]
  split
  · rename_i he
    rw [h] at he
    cases he
  · rename_i q' t' he
    have he' : (q',t')=(r,t) := Option.some.inj (he.symm.trans h)
    cases he'
    rfl

theorem next_related {c c' : TM0.Cfg Γ Λ} (s : OneHead.State (Control S) Γ ℤ)
    (hr : Related S c s) (hc : TM0.step M c=some c') :
    Related S c' ((program M S hS accept).next 1 s) := by
  have ha : s.cells s.head=c.Tape.1 := by simpa only [Tape.nth_zero,Int.add_zero] using (hr.2 0).symm
  obtain ⟨⟨q,t⟩,ht,rfl⟩ := Option.map_eq_some_iff.mp hc
  have ht' : M s.control.val (s.cells s.head)=some (q,t) := by rw [hr.1,ha]; exact ht
  have hp := program_some M S hS accept s.control (s.cells s.head) q t ht'
  constructor
  · simp only [OneHead.Program.next,OneHead.Program.action,hp,Option.getD_some]
  · intro i
    simp only [OneHead.Program.next,OneHead.Program.action,hp,Option.getD_some]
    cases t with
    | write b =>
      simp only [action,OneHead.move,Tape.write_nth,Function.update_apply]
      rw [hr.2]
      by_cases hi : i=0
      · subst i; simp
      · have hne : s.head+i ≠ s.head := by omega
        simp only [hi,hne,ite_false]
    | move d =>
      cases d <;>
        simp only [action,OneHead.move,Function.update_eq_self,Tape.move_left_nth,Tape.move_right_nth] <;>
        rw [hr.2] <;> congr 1 <;> omega

theorem steps_related {c c' : TM0.Cfg Γ Λ} {n : ℕ} (s : OneHead.State (Control S) Γ ℤ)
    (hr : Related S c s) (hc : Steps (TM0.step M) n c c') :
    Related S c' ((program M S hS accept).run 1 s n) := by
  induction hc generalizing s with
  | zero => exact hr
  | @succ n c c₁ c₂ ht hs ih =>
    have hh := ih ((program M S hS accept).next 1 s) (next_related M S hS accept s hr ht)
    rw [show n+1=1+n by omega,OneHead.run_add]
    exact hh

theorem halt_related {c : TM0.Cfg Γ Λ} (s : OneHead.State (Control S) Γ ℤ)
    (hr : Related S c s) (hc : TM0.step M c=none) :
    (program M S hS accept).transition s.control (s.cells s.head)=none := by
  have ha : s.cells s.head=c.Tape.1 := by simpa only [Tape.nth_zero,Int.add_zero] using (hr.2 0).symm
  apply program_none
  rw [hr.1,ha]
  exact Option.map_eq_none_iff.mp hc

theorem acceptance_related {c : TM0.Cfg Γ Λ} (s : OneHead.State (Control S) Γ ℤ)
    (hr : Related S c s) :
    (program M S hS accept).accepting s.control (s.cells s.head)=accept c.q c.Tape.1 := by
  change accept s.control.val (s.cells s.head)=_
  rw [hr.1]
  congr 1
  simpa only [Tape.nth_zero,Int.add_zero] using (hr.2 0).symm

theorem initial_related (w : List Γ) :
    Related S (TM0.init w) (OneHead.lineInitial (program M S hS accept) default (fun j : Fin w.length => w[j])) := by
  refine ⟨rfl,?_⟩
  intro i
  change (Tape.mk₁ w).nth i=OneHead.lineInput default (fun j : Fin w.length => w[j]) (0+i)
  rw [Int.zero_add]
  cases i with
  | ofNat n =>
    change (Tape.mk₁ w).nth (n : ℤ)=OneHead.lineInput default (fun j : Fin w.length => w[j]) (n : ℤ)
    simp only [Tape.mk₁,Tape.mk₂,Tape.mk'_nth_nat,ListBlank.nth_mk,
      OneHead.lineInput,Int.natCast_nonneg,true_and,Int.toNat_natCast]
    by_cases hn : n < w.length
    · have hc : (n : ℤ) < w.length := by omega
      simp only [dite_eq_left hc,List.getI_eq_getElem _ hn]
      rfl
    · have hc : ¬ (n : ℤ) < w.length := by omega
      simp only [dite_eq_right hc,List.getI_eq_default w (show w.length ≤ n by omega)]
  | negSucc n =>
    have hn : ¬ (0 : ℤ) ≤ Int.negSucc n := by omega
    change default=OneHead.lineInput default (fun j : Fin w.length => w[j]) (Int.negSucc n)
    simp only [OneHead.lineInput,hn,false_and,dite_false]

end VariableWL.TM0Adapter

namespace VariableWL.MachineOneHead
open Turing BoundedSimulation
variable (M : Machine)

theorem instructions_le (l : Label1 M) (hl : l ∈ support1 M) :
    UnitSimulation.instructions (program1 M l) ≤ instructionsBound M :=
  Finset.le_sup (f := fun l => UnitSimulation.instructions (program1 M l)) hl

theorem input_pos (w : Word) : 0 < (input M w).length := Nat.succ_pos _

 theorem outputs_oneHead (w : Word) (b : Bool) (T : ℕ) (h : OutputsWithin M w [b] T) :
    ∃ t ≤ time M w.length T,
      (oneHead M).transition ((oneHead M).run 1
        (OneHead.lineInitial (oneHead M) default (fun j : Fin (input M w).length => (input M w)[j])) t).control
        (((oneHead M).run 1
        (OneHead.lineInitial (oneHead M) default (fun j : Fin (input M w).length => (input M w)[j])) t).cells
          ((oneHead M).run 1
        (OneHead.lineInitial (oneHead M) default (fun j : Fin (input M w).length => (input M w)[j])) t).head)=none ∧
      (oneHead M).accepting ((oneHead M).run 1
        (OneHead.lineInitial (oneHead M) default (fun j : Fin (input M w).length => (input M w)[j])) t).control
        (((oneHead M).run 1
        (OneHead.lineInitial (oneHead M) default (fun j : Fin (input M w).length => (input M w)[j])) t).cells
          ((oneHead M).run 1
        (OneHead.lineInitial (oneHead M) default (fun j : Fin (input M w).length => (input M w)[j])) t).head)= !b := by
  obtain ⟨n,hn,s,hs,hl,ha⟩ := MultiStack.outputs_simulated M w b T h
  have hinit := TM2to1.trCfg_init (K := MultiStack.Slot M) (Γ := fun _ => MultiStack.Γ M) (Λ := MultiStack.Label M) (σ := MultiStack.Vars M)
    (0,true) (w.map (MultiStack.inputSymbol M))
  obtain ⟨d,hd,u,hu,hrun⟩ := StackSimulation.run_bound (MultiStack.program M)
    (MultiStack.operationsBound M) (MultiStack.operations_le M) (MultiStack.initialConfig M w)
    (TM1.init (input M w)) hinit w.length (MultiStack.initial_lengths M w) n
  rw [hs.evolve] at hd
  have hdl : d.l=none := by cases hd; simpa only [Option.map_eq_none_iff] using hl
  have hdv : d.var=s.var := by cases hd; rfl
  have hi : (TM1.init (input M w) : TM1.Cfg (Alphabet M) (Label1 M) (MultiStack.Vars M)).l
      ∈ Finset.insertNone (support1 M) := Finset.some_mem_insertNone.mpr (supported1 M).1
  obtain ⟨t,ht,hunit⟩ := UnitSimulation.steps_bound (program1 M) (support1 M) (supported1 M)
    (instructionsBound M) (instructions_le M) hrun hi
  have hr := TM0Adapter.steps_related (program0 M) (support0 M) (supported0 M)
    (fun q _ => !q.2.answer) _ (TM0Adapter.initial_related (program0 M) (support0 M) (supported0 M)
      (fun q _ => !q.2.answer) (input M w)) hunit
  have hhalt : TM0.step (program0 M) (TM1to0.trCfg (program1 M) d)=none := by
    simp only [TM0.step,TM1to0.trCfg,program0,TM1to0.tr,hdl,Option.map_none]
  refine ⟨t,?_,TM0Adapter.halt_related _ _ _ _ _ hr hhalt,?_⟩
  · apply ht.trans
    apply Nat.mul_le_mul_right
    apply hu.trans
    apply Nat.mul_le_mul hn
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hn) _) _
  · exact (TM0Adapter.acceptance_related _ _ _ _ _ hr).trans (by
      change (! d.var.answer)= !b
      rw [hdv,ha])

end VariableWL.MachineOneHead

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_MachineReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.MachineOneHead
variable (M : Machine)

theorem stackTime_le (m T : ℕ) : stackTime M m T ≤ linearConstant M*(m+T+1) := by
  unfold stackTime linearConstant
  have hC := Nat.zero_le (MultiStack.operationsBound M)
  nlinarith

theorem time_le (m T : ℕ) : time M m T ≤ quadraticConstant M*(m+T+1)^2 := by
  let X := m+T+1
  have hx : 1 ≤ X := by dsimp [X]; omega
  have hm : m ≤ X := by dsimp [X]; omega
  have hc : MultiStack.operationsBound M ≤ MultiStack.operationsBound M*X := Nat.le_mul_of_pos_right _ hx
  have hsum : m+stackTime M m T*MultiStack.operationsBound M+MultiStack.operationsBound M ≤
      (1+linearConstant M*MultiStack.operationsBound M+MultiStack.operationsBound M)*X := by
    have hs := Nat.mul_le_mul_right (MultiStack.operationsBound M) (stackTime_le M m T)
    dsimp only [X] at hx hm hc ⊢
    nlinarith
  have hfactor : 1+MultiStack.operationsBound M*(2*(m+stackTime M m T*MultiStack.operationsBound M+
      MultiStack.operationsBound M)+2) ≤
      (1+MultiStack.operationsBound M*(2*(1+linearConstant M*MultiStack.operationsBound M+
      MultiStack.operationsBound M)+2))*X := by
    have hh : 2*(m+stackTime M m T*MultiStack.operationsBound M+MultiStack.operationsBound M)+2 ≤
        (2*(1+linearConstant M*MultiStack.operationsBound M+MultiStack.operationsBound M)+2)*X := by
      nlinarith
    have := Nat.mul_le_mul_left (MultiStack.operationsBound M) hh
    nlinarith
  unfold time quadraticConstant
  calc
    _ ≤ (linearConstant M*X)*((1+MultiStack.operationsBound M*
      (2*(1+linearConstant M*MultiStack.operationsBound M+MultiStack.operationsBound M)+2))*X)*instructionsBound M :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (stackTime_le M m T) hfactor)
    _ = _ := by dsimp [X]; ring

theorem inputExponent_ge_time (c d m : ℕ) : c*(m+1)^d ≤ inputExponent c d m := by
  unfold inputExponent
  rw [pow_succ,← Nat.mul_assoc]
  exact (Nat.mul_le_mul_right _ (Nat.le_succ c)).trans
    (Nat.le_mul_of_pos_right _ (by omega))

theorem exponential_input_bound (c d m : ℕ) :
    m+2^(c*(m+1)^d)+1 ≤ 2^(inputExponent c d m+1) := by
  have ht : 2^(c*(m+1)^d) ≤ 2^inputExponent c d m :=
    Nat.pow_le_pow_right (by omega) (inputExponent_ge_time c d m)
  have hm : m+1 ≤ 2^inputExponent c d m :=
    (inputExponent_ge_length c d m).trans (Nat.le_of_lt (Nat.lt_two_pow_self))
  rw [pow_succ]
  omega

theorem simulation_bound (c d m : ℕ) :
    time M m (2^(c*(m+1)^d)) ≤ 2^simulationExponent M c d m := by
  have h := time_le M m (2^(c*(m+1)^d))
  have hp := Nat.pow_le_pow_left (exponential_input_bound c d m) 2
  have hc : quadraticConstant M ≤ 2^(quadraticConstant M+1) :=
    (Nat.le_succ _).trans (Nat.le_of_lt Nat.lt_two_pow_self)
  refine h.trans ((Nat.mul_le_mul hc hp).trans_eq ?_)
  rw [← pow_mul,← pow_add]
  congr 1
  unfold simulationExponent
  omega

end VariableWL.MachineOneHead

namespace VariableWL.MachineReduction
open MachineOneHead
attribute [local instance] Classical.propDecidable
variable (M : Machine) (c d : ℕ)

theorem internal_pos (w : Word) : 0 < internal M c d w := by unfold internal; omega

theorem enough_links (w : Word) : dimension M c d w+1 < internal M c d w+1 := by
  unfold internal
  omega

theorem consistent_iff_output (w : Word) (b : Bool)
    (h : OutputsWithin M w [b] (2^(c*(w.length+1)^d))) :
    (imageInstance M c d w).Consistent ↔ b=true := by
  obtain ⟨t,ht,halt,accept⟩ := outputs_oneHead M w b _ h
  have he := OneHead.product_consistent_iff (oneHead M) default
    (fun j : Fin (input M w).length => (input M w)[j]) (fits M c d w) (input_pos M w)
    (2^simulationExponent M c d w.length) t (ring_budget M c d w.length)
    ((input_length M w).trans (input_fits_budget M c d w.length))
    (ht.trans (simulation_bound M c d w.length)) halt
  change (imageInstance M c d w).Consistent ↔ _ at he
  rw [he,accept]
  cases b <;> decide

end VariableWL.MachineReduction

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Encoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack
open VariableWL.BoundedSimulation

namespace Code
variable {k : ℕ}

theorem machine_step (C : Code k) (o : Fin (k+1)) : (C.machine o).step=C.step := rfl

theorem lift_steps {A B : Code k} (f : A.Control → B.Control)
    (hf : ∀ q h q' u, A.transition q h=some (q',u) → B.transition (f q) h=some (f q',u))
    {s t : State A.Control k} {n : ℕ} (hst : Steps A.step n s t) :
    Steps B.step n (liftState f s) (liftState f t) := by
  induction hst with
  | zero => exact Steps.zero _
  | @succ n s t u hst htu ih =>
    apply Steps.succ ?_ ih
    unfold step at hst ⊢
    cases ht : A.transition s.control (heads s.tapes) with
    | none => simp [ht] at hst
    | some data =>
      rcases data with ⟨q,a⟩
      simp only [ht,Option.map_some,Option.some.injEq] at hst
      subst t
      change (B.transition (f s.control) (heads s.tapes)).map _ = _
      rw [hf _ _ _ _ ht]
      rfl

 theorem eval_steps {C : Code k} {s t : Stores k} {n : ℕ} (h : Eval C s n t) :
    ∃ q, Steps C.step n ⟨C.start,s⟩ ⟨q,t⟩ ∧ C.transition q (heads t)=none := by
  induction h with
  | skip s => exact ⟨(),Steps.zero _,rfl⟩
  | action a s => exact ⟨true,Steps.single rfl,rfl⟩
  | @seq a b s t u n m ha hb ia ib =>
    obtain ⟨qa,hqa,hhalt⟩ := ia
    obtain ⟨qb,hqb,hhaltb⟩ := ib
    refine ⟨.inr qb,?_,?_⟩
    · have hleft := lift_steps (B := .seq a b) Sum.inl
        (by intro q h q' v hv; simp only [transition,hv]) hqa
      have hcross : (Code.seq a b).step ⟨.inl qa,t⟩=some ⟨.inr b.start,t⟩ := by
        simp only [step,transition,hhalt,Option.map_some,execute_nop]
      have hright := lift_steps (B := .seq a b) Sum.inr
        (by intro q h q' v hv; simp only [transition,hv,Option.map_some]) hqb
      exact (hleft.tail hcross).trans hright
    · simp only [transition,hhaltb,Option.map_none]
  | @branch_true p a b s t n hp ha ih =>
    obtain ⟨q,hq,hh⟩ := ih
    refine ⟨.inr (.inl q),?_,?_⟩
    · have hbody := lift_steps (B := .branch p a b) (fun q => Sum.inr (Sum.inl q))
        (by intro q h q' u hu; simp only [transition,hu,Option.map_some]) hq
      exact hbody.head (by simp [step,start,transition,hp,liftState])
    · simp only [transition,hh,Option.map_none]
  | @branch_false p a b s t n hp ha ih =>
    obtain ⟨q,hq,hh⟩ := ih
    refine ⟨.inr (.inr q),?_,?_⟩
    · have hbody := lift_steps (B := .branch p a b) (fun q => Sum.inr (Sum.inr q))
        (by intro q h q' u hu; simp only [transition,hu,Option.map_some]) hq
      exact hbody.head (by simp [step,start,transition,hp,liftState])
    · simp only [transition,hh,Option.map_none]
  | loop_false hp => exact ⟨.inl (),Steps.zero _,by simp [transition,hp]⟩
  | @loop_true p a s t u n m hp ha hb ia ib =>
    obtain ⟨qa,hqa,hhalta⟩ := ia
    obtain ⟨qb,hqb,hhaltb⟩ := ib
    refine ⟨qb,?_,hhaltb⟩
    have hbody := lift_steps (B := .loop p a) Sum.inr
      (by intro q h q' v hv; simp only [transition,hv]) hqa
    have hin : (Code.loop p a).step ⟨.inl (),s⟩=some ⟨.inr a.start,s⟩ := by
      simp [step,transition,hp]
    have hout : (Code.loop p a).step ⟨.inr qa,t⟩=some ⟨.inl (),t⟩ := by
      simp only [step,transition,hhalta,Option.map_some,execute_nop]
    exact ((hbody.head hin).tail hout).trans hqb

 theorem eval_outputs (C : Code k) (o : Fin (k+1)) (w : Word) {t : Stores k} {n : ℕ}
    (h : Eval C (fun j => if j=0 then w.reverse else []) n t) :
    VariableWL.OutputsWithin (C.machine o).compile w (t o) (4*(w.length+n+1)) := by
  obtain ⟨q,hq,hh⟩ := eval_steps h
  apply Machine.outputs_compile
  have hr : (C.machine o).run w n=⟨q,t⟩ := by
    have he := hq.evolve
    have hrun (i) : (C.machine o).run w i=BoundedSimulation.evolve C.step ⟨C.start,fun j => if j=0 then w.reverse else []⟩ i := by
      induction i with
      | zero => rfl
      | succ i ih => change ((C.machine o).step _).getD _=_; rw [machine_step,ih]; rfl
    rw [hrun]
    exact he
  refine ⟨n,le_rfl,?_,?_⟩
  · rw [hr,machine_step]
    simp only [step,hh,Option.map_none]
  · rw [hr]
    rfl

end Code
end VariableWL.Computation.Stack

namespace VariableWL.Encoding
attribute [local instance] Classical.propDecidable

theorem header_code (n : ℕ) (v : Word) : header (List.replicate n true ++ false::v)=some (n,v) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,header,ih,Option.map_some]

 theorem integer_code (n : ℕ) (v : Word) : integer (integerCode n ++ v)=some (n,v) := by
  unfold integerCode
  simp only [List.append_assoc,List.singleton_append]
  change integer (List.replicate n.bits.length true ++ false::(n.bits++v))=_
  unfold integer
  rw [header_code]
  simp only [List.length_append,Nat.le_add_right,ite_true,
    List.take_left,value_bits,List.drop_left]

 theorem integer_prefix_injective {n m : ℕ} {u v : Word}
    (h : integerCode n++u=integerCode m++v) : n=m ∧ u=v := by
  have he := congrArg integer h
  rw [integer_code,integer_code] at he
  exact Prod.mk.inj (Option.some.inj he)

 theorem matrix_flat (G : Graph) : matrix G =
    (List.ofFn fun i : Fin G.order => List.ofFn fun j : Fin G.order => decide (G.graph.Adj i j)).flatten := by
  classical
  unfold matrix
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hn : 0 < G.order := Nat.zero_lt_of_lt i.isLt
  have hd : (⟨i.val*G.order+j.val,by have := Nat.mul_le_mul_right G.order (Nat.succ_le_of_lt i.isLt); nlinarith [j.isLt]⟩ : Fin (G.order*G.order)).divNat=i := by
    apply Fin.ext
    simp [Fin.divNat,Nat.add_div,Nat.div_eq_of_lt j.isLt,hn,Nat.mod_lt _ hn]
  have hm : (⟨i.val*G.order+j.val,by have := Nat.mul_le_mul_right G.order (Nat.succ_le_of_lt i.isLt); nlinarith [j.isLt]⟩ : Fin (G.order*G.order)).modNat=j := by
    apply Fin.ext
    simp [Fin.modNat,Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  rw [hd,hm]

 theorem graphCode_eq (G : Graph) : graphCode G=integerCode G.order++matrix G := by
  rw [matrix_flat]
  rfl

 theorem graph_prefix_injective {G H : Graph} {u v : Word}
    (h : graphCode G++u=graphCode H++v) : G=H ∧ u=v := by
  classical
  rw [graphCode_eq,graphCode_eq,List.append_assoc,List.append_assoc] at h
  obtain ⟨hn,ht⟩ := integer_prefix_injective h
  rcases G with ⟨n,g⟩
  rcases H with ⟨m,hg⟩
  change n=m at hn
  subst m
  obtain ⟨hm,hu⟩ := List.append_inj ht (by simp)
  refine ⟨?_,hu⟩
  have hadj : g.Adj=hg.Adj := by
    funext i j
    have hf := List.ofFn_inj.mp hm
    let p : Fin (n*n) := ⟨i.val*n+j.val,by nlinarith [i.isLt,j.isLt]⟩
    have hp := congrFun hf p
    have hn : 0<n := Nat.zero_lt_of_lt i.isLt
    have hd : p.divNat=i := by apply Fin.ext; simp [p,Fin.divNat,Nat.add_div,Nat.div_eq_of_lt j.isLt,hn,Nat.mod_lt _ hn]
    have hmod : p.modNat=j := by apply Fin.ext; simp [p,Fin.modNat,Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
    change decide (g.Adj p.divNat p.modNat)=decide (hg.Adj p.divNat p.modNat) at hp
    rw [hd,hmod] at hp
    exact propext (by simpa only [decide_eq_decide] using hp)
  have hgEq := SimpleGraph.ext hadj
  subst hg
  rfl

 theorem pair_injective {G H G' H' : Graph} {k k' : ℕ}
    (h : pairCode G H k=pairCode G' H' k') : G=G' ∧ H=H' ∧ k=k' := by
  unfold pairCode at h
  rw [List.append_assoc,List.append_assoc] at h
  obtain ⟨hg,ht⟩ := graph_prefix_injective h
  obtain ⟨hh,hk⟩ := graph_prefix_injective ht
  have hi := integer_prefix_injective (u := []) (v := []) (by simpa using hk)
  exact ⟨hg,hh,hi.1⟩

 theorem pair_mem_WL (G H : Graph) (k : ℕ) : pairCode G H k ∈ WL ↔ 2≤k ∧ Equivalent G H k := by
  constructor
  · rintro ⟨G',H',k',he,hk,hh⟩
    obtain ⟨rfl,rfl,rfl⟩ := pair_injective he
    exact ⟨hk,hh⟩
  · rintro ⟨hk,hh⟩
    exact ⟨G,H,k,rfl,hk,hh⟩

 theorem pair_mem_SubWL (G H : Graph) (k : ℕ) : pairCode G H k ∈ SubWL ↔
    2≤k ∧ 0<G.order ∧ G.order=H.order ∧ G.graph.Connected ∧ H.graph.Connected ∧
      Subcubic G ∧ Subcubic H ∧ Equivalent G H k := by
  constructor
  · rintro ⟨G',H',k',he,hh⟩
    obtain ⟨rfl,rfl,rfl⟩ := pair_injective he
    exact hh
  · intro hh
    exact ⟨G,H,k,rfl,hh⟩

end VariableWL.Encoding

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Procedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.Procedure
open Code
variable {k : ℕ}

 theorem outputs {f : Stores k → Stores k} {T : Stores k → ℕ} (o : Fin (k+1))
    (h : Realizes f T) : ∃ M : VariableWL.Machine, ∀ w : Word,
      VariableWL.OutputsWithin M w
        (f (fun j => if j=0 then w.reverse else []) o)
        (4*(w.length+T (fun j => if j=0 then w.reverse else [])+1)) := by
  obtain ⟨e,C,hC⟩ := h
  let out : Fin (k+e+1) := ⟨o.val,by omega⟩
  refine ⟨(C.machine out).compile,fun w => ?_⟩
  let s : Stores k := fun j => if j=0 then w.reverse else []
  obtain ⟨n,hn,he⟩ := hC s
  have hs : extend e s=(fun j => if j=0 then w.reverse else []) := by
    funext j
    by_cases hj : j.val<k+1
    · simp only [extend,hj,dite_true,s]
      have hz : (⟨j.val,hj⟩ : Fin (k+1))=0 ↔ j=0 := by simp only [Fin.ext_iff,Fin.val_zero]
      simp only [hz]
    · rw [extend_back _ _ _ (by omega)]
      have hz : j≠0 := by intro hz; subst j; simp only [Fin.val_zero] at hj; omega
      simp only [hz,ite_false]
  rw [hs] at he
  have ho := eval_outputs C out w he
  rw [extend_front] at ho
  obtain ⟨t,ht,hh,hout⟩ := ho
  exact ⟨t,ht.trans (by dsimp only [s] at hn; omega),hh,hout⟩

end VariableWL.Computation.Stack.Procedure

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_ExponentialRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.Recipe
variable {n : ℕ}

theorem outputs (P : Certified 1) : ∃M : VariableWL.Machine,∀w : Word,
    OutputsWithin M w (P.value (fun _=>w.reverse)) (4*(w.length+P.time (fun _=>w.reverse)+1)) := by
  obtain ⟨M,hM⟩ := Procedure.outputs (1 : Fin 2) (P.compiled 1 (fun _=>0) 1)
  refine ⟨M,fun w=>?_⟩
  have h := hM w
  have he : (fun j : Fin 2=>if j=0 then w.reverse else []) ∘ (fun _ : Fin 1=>(0 : Fin 2))=(fun _=>w.reverse) := rfl
  simp only [Function.update_self,he,show (1 : Fin 2)≠0 by decide,ite_false,List.length_nil,Nat.mul_zero,Nat.add_zero] at h
  exact h

end VariableWL.Computation.Stack.Recipe

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Descriptor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

theorem binaryLength_number (N : Expr n) (v : Env n) : (binaryLength N).number v=(N.number v).size := by
  rw [binaryLength,count_number]
  simp only [le_bit,capPow_number,numeral_number,input_number,cons_zero,List.length_replicate,add_number,up_number]
  have he (j : ℕ) : decide (min (2^j) (N.number v+1)≤N.number v)=decide (j<(N.number v).size) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,Nat.lt_size]
    omega
  simp only [he]
  rw [Recipe.count_range_lt,Nat.min_eq_right]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem binaryDigit_bit (N I : Expr n) (v : Env n) (h : I.number v<(N.number v).size) :
    (binaryDigit N I).bit v=(N.number v).testBit (I.number v) := by
  have hp := Nat.lt_size.mp h
  rw [binaryDigit,eq_bit,mod_number,div_number,capPow_number,add_number]
  simp only [numeral_number,Nat.min_eq_left (show 2^I.number v≤N.number v+1 by omega)]
  exact Nat.testBit_eq_decide_div_mod_eq.symm

theorem binaryEncode_value (N : Expr n) (v : Env n) : (binaryEncode N).value v=(N.number v).bits := by
  rw [binaryEncode,collect_value,binaryLength_number]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,Nat.size_eq_bits_len]
  · intro i hi hi'
    rw [List.getElem_map,List.getElem_range]
    have h : (input (0 : Fin (n+1))).number (cons (List.replicate i true) v)<(N.up.number (cons (List.replicate i true) v)).size := by
      simpa only [input_number,cons_zero,List.length_replicate,up_number,List.length_map,List.length_range] using hi
    rw [binaryDigit_bit _ _ _ h]
    simp only [up_number,input_number,cons_zero,List.length_replicate,Nat.testBit_eq_inth,List.getI_eq_getElem _ hi']

theorem integerEncode_value (N : Expr n) (v : Env n) : (integerEncode N).value v=integerCode (N.number v) := by
  simp only [integerEncode,append_value,literal_value]
  change List.replicate ((binaryEncode N).value v).length true ++ ([false] ++ (binaryEncode N).value v)=_
  rw [binaryEncode_value]
  exact List.append_assoc _ _ _ |>.symm

theorem graphEncode_value (N A : Expr n) (v : Env n) (G : Graph)
    (hn : N.number v=G.order) (ha : A.value v=Encoding.matrix G) :
    (graphEncode N A).value v=graphCode G := by
  rw [graphEncode,append_value,integerEncode_value,hn,ha,Encoding.graphCode_eq]

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

theorem underOne_value (P : Expr (n+1)) (v : Env n) (a b : Word) :
    (underOne P).value (cons a (cons b v))=P.value (cons a v) := by
  apply congrArg P.program.value
  funext i
  exact Fin.cases rfl (fun _=>rfl) i

theorem underOne_bit (P : Expr (n+1)) (v : Env n) (a b : Word) :
    (underOne P).bit (cons a (cons b v))=P.bit (cons a v) := by
  unfold Expr.bit
  rw [underOne_value]

theorem select_number (N : Expr n) (P : Expr (n+1)) (I : Expr n) (v : Env n) :
    (select N P I).number v=Descriptor.pick (N.number v)
      (fun j=>P.bit (cons (List.replicate j true) v)) (I.number v) := by
  simp only [select,count_number,le_bit,add_number,input_number,cons_zero,List.length_replicate,
    numeral_number,underOne_bit,up_number]
  rfl

theorem apply₂_value (F : Expr (n+2)) (A B : Expr n) (v : Env n) :
    (apply₂ F A B).value v=F.value (cons (A.value v) (cons (B.value v) v)) := by
  simp only [apply₂,bind_value,up_value]

end VariableWL.Computation.Stack.PolyRecipe

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PortListing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

theorem underTwo_value (P : Expr (n+2)) (v : Env n) (a b c : Word) :
    (underTwo P).value (cons a (cons b (cons c v)))=P.value (cons a (cons b v)) := by
  apply congrArg P.program.value
  funext i
  exact Fin.cases rfl (fun i=>Fin.cases rfl (fun _=>rfl) i) i

theorem underTwo_bit (P : Expr (n+2)) (v : Env n) (a b c : Word) :
    (underTwo P).bit (cons a (cons b (cons c v)))=P.bit (cons a (cons b v)) := by
  unfold Expr.bit
  rw [underTwo_value]

theorem apply₂_bit (F : Expr (n+2)) (A B : Expr n) (v : Env n) :
    (apply₂ F A B).bit v=F.bit (cons (A.value v) (cons (B.value v) v)) := by
  unfold Expr.bit
  rw [apply₂_value]

theorem count_value (N : Expr n) (P : Expr (n+1)) (v : Env n) :
    (count N P).value v=List.replicate ((count N P).number v) true := by
  change (Recipe.countTrue N.program P.program).value v=_
  rw [Recipe.countTrue_value,count_number]
  rfl

theorem select_value (N : Expr n) (P : Expr (n+1)) (I : Expr n) (v : Env n) :
    (select N P I).value v=List.replicate (Descriptor.pick (N.number v)
      (fun j=>P.bit (cons (List.replicate j true) v)) (I.number v)) true := by
  rw [select,count_value]
  change List.replicate ((select N P I).number v) true=_
  rw [select_number]

theorem GraphListing.order_number (D : GraphListing n) (v : Env n) :
    D.order.number v=Descriptor.rank (D.eval v).valid (D.eval v).bound := count_number ..

theorem GraphListing.matrix_value (D : GraphListing n) (v : Env n) :
    D.matrix.value v=NumericPromise.pack (D.order.number v) (fun i j=>
      (D.eval v).edge (Descriptor.pick (D.eval v).bound (D.eval v).valid i)
        (Descriptor.pick (D.eval v).bound (D.eval v).valid j)) := by
  simp only [GraphListing.matrix,collect_value,mul_number,apply₂_bit,select_value,
    up_number,div_number,mod_number,input_number,cons_zero,List.length_replicate,underOne_bit,underTwo_bit]
  rfl

theorem GraphListing.matrix_correct (D : GraphListing n) (v : Env n) (h : (D.eval v).Sound) :
    D.matrix.value v=Encoding.matrix ((D.eval v).graph h) := by
  classical
  rw [D.matrix_value,Encoding.matrix]
  apply List.ext_getElem
  · simp only [NumericPromise.pack,List.length_map,List.length_range,List.length_ofFn,
      Descriptor.Data.graph,D.order_number]
  · intro i hi hi'
    simp only [NumericPromise.pack,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    rw [D.order_number]
    simp only [Descriptor.Data.graph,Fin.divNat,Fin.modNat]
    exact Bool.decide_eq_true.symm

theorem GraphListing.code_correct (D : GraphListing n) (v : Env n) (h : (D.eval v).Sound) :
    D.code.value v=graphCode ((D.eval v).graph h) :=
  graphEncode_value _ _ _ _ (D.order_number v) (D.matrix_correct v h)

theorem outputs (P : Expr 1) : ∃M : VariableWL.Machine,∃c d : ℕ,∀w : Word,
    OutputsWithin M w (P.value (fun _=>w.reverse)) (c*(w.length+1)^d) := by
  obtain ⟨M,hM⟩ := Recipe.outputs P.program
  obtain ⟨f,hf,hP⟩ := P.polynomial
  obtain ⟨c,d,hcd⟩ := ((Growth.constant 4).mul ((Growth.ident.add hf).add (Growth.constant 1)))
  refine ⟨M,c,d,fun w=>?_⟩
  have ht := hP w.length (fun _=>w.reverse) (fun _=>by simp)
  obtain ⟨t,htime,hh,ho⟩ := hM w
  refine ⟨t,htime.trans (le_trans ?_ (hcd w.length)),hh,ho⟩
  have hp : P.program.time (fun _=>w.reverse)≤f w.length := by omega
  dsimp only [id]
  exact Nat.mul_le_mul_left 4 (by omega)

theorem reduces (P : Expr 1) (L R : Language)
    (h : ∀w : Word,w∈L ↔ P.value (fun _=>w.reverse)∈R) : PolytimeReduces L R := by
  obtain ⟨M,c,d,hP⟩ := outputs P
  exact ⟨M,c,d,fun w=>⟨P.value (fun _=>w.reverse),hP w,h w⟩⟩

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n m : ℕ}

theorem length_value (P : Expr n) (v : Env n) :
    (length P).value v=List.replicate (P.number v) true := Recipe.len_value ..

theorem applyNat_value (P : Expr (n+1)) (I : Expr n) (v : Env n) :
    (applyNat P I).value v=P.value (cons (List.replicate (I.number v) true) v) := by
  rw [applyNat,bind_value,length_value]

theorem applyNat_bit (P : Expr (n+1)) (I : Expr n) (v : Env n) :
    (applyNat P I).bit v=P.bit (cons (List.replicate (I.number v) true) v) := by
  unfold Expr.bit
  rw [applyNat_value]

theorem applyNat_number (P : Expr (n+1)) (I : Expr n) (v : Env n) :
    (applyNat P I).number v=P.number (cons (List.replicate (I.number v) true) v) := by
  change ((applyNat P I).value v).length=_
  rw [applyNat_value]
  rfl

theorem applyNat₂_bit (P : Expr (n+2)) (I J : Expr n) (v : Env n) :
    (applyNat₂ P I J).bit v=P.bit (cons (List.replicate (I.number v) true)
      (cons (List.replicate (J.number v) true) v)) := by
  simp only [applyNat₂,applyNat_bit,up_number]

namespace PortListing

theorem eval_up (D : PortListing n) (v : Env n) (w : Word) : D.up.eval (cons w v)=D.eval v := by
  apply Descriptor.PortData.ext
  · rfl
  · funext i; exact underOne_bit D.valid v _ _
  · funext i; change ((underOne D.color).value _).length=_; rw [underOne_value]; rfl
  · rfl
  · funext i j; exact underTwo_bit D.incidence v _ _ _

theorem stride_number (D : PortListing n) (v : Env n) : D.stride.number v=(D.eval v).stride := by
  simp only [stride,add_number,numeral_number,Descriptor.PortData.stride,eval]

theorem owner_number (D : PortListing n) (I : Expr n) (v : Env n) :
    (D.owner I).number v=(D.eval v).owner (I.number v) := by
  simp only [owner,div_number,stride_number,numeral_number,Descriptor.PortData.owner]

theorem port_number (D : PortListing n) (I : Expr n) (v : Env n) :
    (D.port I).number v=(D.eval v).port (I.number v) := by
  simp only [port,mod_number,div_number,stride_number,numeral_number,Descriptor.PortData.port]

theorem level_number (D : PortListing n) (I : Expr n) (v : Env n) :
    (D.level I).number v=(D.eval v).level (I.number v) := by
  simp only [level,mod_number,stride_number,Descriptor.PortData.level]

theorem expandedValid_bit (D : PortListing n) (I : Expr n) (v : Env n) :
    (D.expandedValid I).bit v=(D.eval v).expanded.valid (I.number v) := by
  simp only [expandedValid,conj_bit,applyNat_bit,applyNat_number,lt_bit,add_number,
    numeral_number,owner_number,level_number]
  rfl

theorem expandedEdge_bit (D : PortListing n) (I J : Expr n) (v : Env n) :
    (D.expandedEdge I J).bit v=(D.eval v).expanded.edge (I.number v) (J.number v) := by
  simp only [expandedEdge,disj_bit,conj_bit,eq_bit,neg_bit,applyNat₂_bit,add_number,mul_number,
    numeral_number,owner_number,port_number,level_number]
  have hd : (!(decide ((D.eval v).port (I.number v)=(D.eval v).port (J.number v)))) =
      decide ((D.eval v).port (I.number v)≠(D.eval v).port (J.number v)) := decide_not.symm
  rw [hd]
  rfl

theorem expanded_eval (D : PortListing n) (v : Env n) :
    D.expanded.eval v=(D.eval v).expanded := by
  apply Descriptor.data_ext
  · simp only [expanded,GraphListing.eval,mul_number,numeral_number,stride_number,Descriptor.PortData.expanded,eval]
  · funext i
    simp only [expanded,GraphListing.eval,expandedValid_bit,input_number,cons_zero,List.length_replicate,eval_up]
  · funext i j
    simp only [expanded,GraphListing.eval,expandedEdge_bit,input_number,cons_zero,NumericProgram.cons_one,
      List.length_replicate,eval_up]

end PortListing
end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

theorem fixedNat_number (N : ℕ) (f : Fin N → ℕ) (I : Expr n) (v : Env n)
    (h : I.number v<N) : (fixedNat N f I).number v=f ⟨I.number v,h⟩ := by
  induction N generalizing I with
  | zero => omega
  | succ N ih =>
    rw [fixedNat,NumericProgram.choose_number,eq_bit,numeral_number]
    by_cases hi : I.number v=0
    · rw [ite_eq_left (by simpa using hi),numeral_number]
      exact congrArg f (Fin.ext hi.symm)
    · rw [ite_eq_right (by simpa using hi),ih (fun i=>f i.succ) _ (by simp only [sub_number,numeral_number]; omega)]
      apply congrArg f
      apply Fin.ext
      simp only [Fin.val_succ,sub_number,numeral_number]
      omega

theorem fixedBool_bit (N : ℕ) (f : Fin N → Bool) (I : Expr n) (v : Env n)
    (h : I.number v<N) : (fixedBool N f I).bit v=f ⟨I.number v,h⟩ := by
  simp only [fixedBool,eq_bit,fixedNat_number N _ I v h,numeral_number]
  cases f ⟨I.number v,h⟩ <;> rfl

end VariableWL.Computation.Stack.PolyRecipe

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PrefixAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

theorem applyNat₂_number (P : Expr (n+2)) (I J : Expr n) (v : Env n) :
    (applyNat₂ P I J).number v=P.number (cons (List.replicate (I.number v) true)
      (cons (List.replicate (J.number v) true) v)) := by
  simp only [applyNat₂,applyNat_number,up_number]

theorem applyNat₃_bit (P : Expr (n+3)) (I J K : Expr n) (v : Env n) :
    (applyNat₃ P I J K).bit v=P.bit (cons (List.replicate (I.number v) true)
      (cons (List.replicate (J.number v) true) (cons (List.replicate (K.number v) true) v))) := by
  simp only [applyNat₃,applyNat_bit,applyNat₂_bit,up_number]

theorem applyNat₃_number (P : Expr (n+3)) (I J K : Expr n) (v : Env n) :
    (applyNat₃ P I J K).number v=P.number (cons (List.replicate (I.number v) true)
      (cons (List.replicate (J.number v) true) (cons (List.replicate (K.number v) true) v))) := by
  simp only [applyNat₃,applyNat_number,applyNat₂_number,up_number]

theorem fixedNat_zero (N : ℕ) (f : Fin N → ℕ) (I : Expr n) (v : Env n)
    (h : N≤I.number v) : (fixedNat N f I).number v=0 := by
  induction N generalizing I with
  | zero => rfl
  | succ N ih =>
    rw [fixedNat,NumericProgram.choose_number,eq_bit,numeral_number,
      ite_eq_right (by simp only [decide_eq_true_eq]; omega)]
    exact ih _ _ (by simp only [sub_number,numeral_number]; omega)

theorem fixedNat_total (N : ℕ) (f : Fin N → ℕ) (I : Expr n) (v : Env n) :
    (fixedNat N f I).number v=tableLookup f (I.number v) := by
  unfold tableLookup
  split_ifs with h
  · exact fixedNat_number N f I v h
  · exact fixedNat_zero N f I v (Nat.le_of_not_gt h)

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

theorem fixedNat₂_number (N M : ℕ) (f : ℕ → ℕ → ℕ) (I J : Expr n) (v : Env n)
    (hi : I.number v<N) (hj : J.number v<M) :
    (fixedNat₂ N M f I J).number v=f (I.number v) (J.number v) := by
  have hm : 0<M := by omega
  have hq : (add (mul I (numeral M)) J).number v<N*M := by
    simp only [add_number,mul_number,numeral_number]
    exact (Nat.add_lt_add_left hj _).trans_le (by rw [←Nat.succ_mul]; exact Nat.mul_le_mul_right M hi)
  rw [fixedNat₂,fixedNat_number _ _ _ _ hq]
  simp only [add_number,mul_number,numeral_number]
  rw [Nat.mul_comm (I.number v) M,Nat.mul_add_div hm,Nat.div_eq_of_lt hj,Nat.add_zero,
    Nat.mul_add_mod,Nat.mod_eq_of_lt hj]

theorem fixedNat₃_number (N M K : ℕ) (f : ℕ → ℕ → ℕ → ℕ) (I J L : Expr n) (v : Env n)
    (hi : I.number v<N) (hj : J.number v<M) (hk : L.number v<K) :
    (fixedNat₃ N M K f I J L).number v=f (I.number v) (J.number v) (L.number v) := by
  have hk' : 0<K := by omega
  have hq : (add (mul J (numeral K)) L).number v<M*K := by
    simp only [add_number,mul_number,numeral_number]
    exact (Nat.add_lt_add_left hk _).trans_le (by rw [←Nat.succ_mul]; exact Nat.mul_le_mul_right K hj)
  rw [fixedNat₃,fixedNat₂_number _ _ _ _ _ _ hi hq]
  simp only [add_number,mul_number,numeral_number]
  rw [Nat.mul_comm (J.number v) K,Nat.mul_add_div hk',Nat.div_eq_of_lt hk,Nat.add_zero,
    Nat.mul_add_mod,Nat.mod_eq_of_lt hk]

theorem fixedBool₂_bit (N M : ℕ) (f : ℕ → ℕ → Bool) (I J : Expr n) (v : Env n)
    (hi : I.number v<N) (hj : J.number v<M) :
    (fixedBool₂ N M f I J).bit v=f (I.number v) (J.number v) := by
  simp only [fixedBool₂,eq_bit,fixedNat₂_number _ _ _ _ _ _ hi hj,numeral_number]
  cases f (I.number v) (J.number v) <;> rfl

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.PrefixAlphabet.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}

 theorem paddedEqual_bit (I J : Expr n) (v : Env n) (hi : I.number v<vectorCount) (hj : J.number v<vectorCount) :
    (paddedEqual I J).bit v=PrefixAlphabet.paddedEqual (I.number v) (J.number v) := fixedBool₂_bit _ _ _ _ _ _ hi hj

end VariableWL.PrefixAlphabet.Program

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PrefixDescriptor
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}
theorem table₂_number (N M : ℕ) (f : ℕ → ℕ → ℕ) (I J : Expr n) (v : Env n) :
    (table₂ N M f I J).number v=if I.number v<N ∧ J.number v<M then f (I.number v) (J.number v) else 0 := by
  simp only [table₂,NumericProgram.choose_number,conj_bit,lt_bit,numeral_number,Bool.and_eq_true,decide_eq_true_eq]
  split_ifs with h
  · exact fixedNat₂_number _ _ _ _ _ _ h.1 h.2
  · rfl

theorem table₃_number (N M K : ℕ) (f : ℕ → ℕ → ℕ → ℕ) (I J L : Expr n) (v : Env n) :
    (table₃ N M K f I J L).number v=if I.number v<N ∧ J.number v<M ∧ L.number v<K then f (I.number v) (J.number v) (L.number v) else 0 := by
  simp only [table₃,NumericProgram.choose_number,conj_bit,lt_bit,numeral_number,Bool.and_eq_true,decide_eq_true_eq]
  by_cases h : I.number v<N ∧ J.number v<M ∧ L.number v<K
  · rw [ite_eq_left ⟨⟨h.1,h.2.1⟩,h.2.2⟩,ite_eq_left h]
    exact fixedNat₃_number _ _ _ _ _ _ _ _ h.1 h.2.1 h.2.2
  · rw [ite_eq_right (by tauto),ite_eq_right h]

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.PrefixAlphabet
open VariableWL.Affine
 theorem truncate_cap {a : ℕ} (ha : a≤6) (z : Vec a) (h : ℕ) :
    PrefixParts.Data.truncate (min h 7) z=PrefixParts.Data.truncate h z := by
  ext i
  have hi := i.isLt
  simp only [PrefixParts.Data.truncate]
  split_ifs <;> first | rfl | omega
 theorem prefixCode_cap (p h i : ℕ) : prefixCode p (min h 7) i=prefixCode p h i := by
  unfold prefixCode
  split_ifs with hp hi
  · congr 2
    apply congrArg (Sigma.mk _)
    exact truncate_cap (by have := (permuted (orderNumber.symm ⟨p,hp⟩) (vectorNumber.symm ⟨i,hi⟩)).1.isLt; omega) _ h
  all_goals rfl
 theorem trim_cap (h i : ℕ) : trim (min h 7) i=trim h i := by
  unfold trim
  split_ifs with hi
  · congr 2
    apply congrArg (Sigma.mk _)
    exact truncate_cap (by have := (vectorNumber.symm ⟨i,hi⟩).1.isLt; omega) _ h
  · rfl
 theorem prefixCode_zero {p h i : ℕ} (hp : ¬p<orderCount ∨ ¬i<vectorCount) : prefixCode p h i=0 := by
  unfold prefixCode
  rcases hp with hp | hi
  · rw [dite_eq_right hp]
  · split_ifs <;> omega
 theorem trim_zero {h i : ℕ} (hi : ¬i<vectorCount) : trim h i=0 := dite_eq_right hi
 theorem bit_zero {i h : ℕ} (hp : ¬i<vectorCount ∨ ¬h<7) : bit i h=0 := by
  unfold bit
  rcases hp with hi | hh
  · rw [dite_eq_right hi]
  · split_ifs with hi
    · dsimp only
      rw [dite_eq_right (by have hbound := (vectorNumber.symm ⟨i,hi⟩).1.isLt; omega)]
    · rfl

namespace TotalProgram
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}
 theorem prefixCode_number (P H I : Expr n) (v : Env n) :
    (prefixCode P H I).number v=PrefixAlphabet.prefixCode (P.number v) (H.number v) (I.number v) := by
  simp only [prefixCode,table₃_number,minimum_number,numeral_number]
  split_ifs with h
  · exact prefixCode_cap _ _ _
  · apply Eq.symm
    exact prefixCode_zero (by have := Nat.min_le_right (H.number v) 7; omega)
 theorem trim_number (H I : Expr n) (v : Env n) :
    (trim H I).number v=PrefixAlphabet.trim (H.number v) (I.number v) := by
  simp only [trim,table₂_number,minimum_number,numeral_number]
  split_ifs with h
  · exact trim_cap _ _
  · exact (trim_zero (by have := Nat.min_le_right (H.number v) 7; omega)).symm
 theorem bit_number (I H : Expr n) (v : Env n) :
    (bit I H).number v=PrefixAlphabet.bit (I.number v) (H.number v) := by
  simp only [bit,table₂_number]
  split_ifs with h
  · rfl
  · exact (bit_zero (by tauto)).symm
end TotalProgram
end VariableWL.PrefixAlphabet

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_PrefixListing
attribute [-instance] _root_.OAI.VariableWL.AffineAlphabet.linearFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1

namespace VariableWL.PrefixDescriptor.Data
attribute [local instance] Classical.propDecidable
variable (D : Data) (x y : Raw) (i j : ℕ)
theorem treeValid_true : D.treeValid x=true ↔
    (D.root x.block x.channel≤x.height ∧ x.height≤D.dimension x.block) ∧
    (List.range PrefixAlphabet.vectorCount).any (fun z=>D.legal x.block z &&
      decide (PrefixAlphabet.prefixCode (D.order x.block x.channel) x.height z=x.vector))=true := by
  simp only [treeValid,Bool.and_eq_true,decide_eq_true_eq]
theorem validRaw_true : D.validRaw x=true ↔ D.validBlock x.block=true ∧
    ((x.kind=0 ∧ x.channel=0 ∧ x.height=0 ∧ x.vector=0) ∨
      (x.kind=1 ∧ x.channel<D.channels x.block ∧ x.height=0) ∧ D.legal x.block x.vector=true ∨
      (x.kind=2 ∧ x.channel<D.channels x.block) ∧ D.treeValid x=true) := by
  simp only [validRaw,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,or_assoc]
theorem sortValid_true : D.sortValid x=true ↔ D.validBlock x.block=true ∧
    ((x.kind=0 ∧ x.channel=0 ∧ x.height=0) ∨
      (x.kind=1 ∧ x.channel<D.channels x.block ∧ x.height=0) ∨
      (x.kind=2 ∧ x.channel<D.channels x.block ∧ D.root x.block x.channel≤x.height ∧
        x.height≤D.dimension x.block)) := by
  simp only [sortValid,Bool.and_eq_true,decide_eq_true_eq]
theorem forward_true : D.forward x y=true ↔
    (x.kind=0 ∧ y.kind=2 ∧ y.channel=0 ∧ y.height=0) ∨
    (x.kind=1 ∧ y.kind=1 ∧ x.channel+1=y.channel ∧ x.vector=y.vector) ∨
    (x.kind=2 ∧ y.kind=2 ∧ x.channel=y.channel ∧ x.height+1=y.height ∧
      PrefixAlphabet.trim x.height y.vector=x.vector) ∨
    (x.kind=2 ∧ y.kind=1 ∧ x.channel=y.channel ∧ x.height=D.dimension x.block ∧
      x.vector=PrefixAlphabet.prefixCode (D.order x.block y.channel) (D.dimension x.block) y.vector) := by
  simp only [forward,Bool.or_eq_true,decide_eq_true_eq,or_assoc]
theorem internal_true : D.internal x y i j=true ↔
    (x.block=y.block ∧ (D.forward x y=true ∨ D.forward y x=true)) ∧
    (i=D.slot x y ∧ j=D.slot y x) := by
  simp only [internal,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
theorem roots_true : D.roots x y i j=true ↔
    ((x.kind=2 ∧ y.kind=2 ∧ i=0 ∧ j=0 ∧ x.channel≠0 ∧ y.channel≠0 ∧
      x.height=D.root x.block x.channel ∧ y.height=D.root y.block y.channel) ∧
      D.matching (x.block*D.channelBound+x.channel) (y.block*D.channelBound+y.channel)=true) ∧
      PrefixAlphabet.paddedEqual x.vector y.vector=true := by
  simp only [roots,Bool.and_eq_true,decide_eq_true_eq]
theorem anchors_true : D.anchors x y i j=true ↔
    x.kind=0 ∧ y.kind=0 ∧
    ((i=2 ∧ j=1 ∧ Descriptor.rank D.validBlock x.block+1=Descriptor.rank D.validBlock y.block) ∨
      (i=1 ∧ j=2 ∧ Descriptor.rank D.validBlock y.block+1=Descriptor.rank D.validBlock x.block)) := by
  simp only [anchors,decide_eq_true_eq]
end VariableWL.PrefixDescriptor.Data

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}
theorem underOne_number (P : Expr (n+1)) (v : Env n) (a b : Word) :
    (underOne P).number (cons a (cons b v))=P.number (cons a v) := by
  change ((underOne P).value _).length=_
  rw [underOne_value]
  rfl
theorem underTwo_number (P : Expr (n+2)) (v : Env n) (a b c : Word) :
    (underTwo P).number (cons a (cons b (cons c v)))=P.number (cons a (cons b v)) := by
  change ((underTwo P).value _).length=_
  rw [underTwo_value]
  rfl
end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.PrefixAlphabet.TotalProgram
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}
 theorem paddedEqual_bit (I J : Expr n) (v : Env n) :
    (paddedEqual I J).bit v=PrefixAlphabet.paddedEqual (I.number v) (J.number v) := by
  simp only [paddedEqual,choose_bit,conj_bit,lt_bit,numeral_number,Bool.and_eq_true,decide_eq_true_eq]
  split_ifs with h
  · exact Program.paddedEqual_bit _ _ _ h.1 h.2
  · have hf : (literal [false] : Expr n).bit v=false := rfl
    rw [hf]
    unfold PrefixAlphabet.paddedEqual
    by_cases hi : I.number v<vectorCount
    · have hj : ¬J.number v<vectorCount := fun hj=>h ⟨hi,hj⟩
      rw [dite_eq_left hi,dite_eq_right hj]
    · rw [dite_eq_right hi]
end VariableWL.PrefixAlphabet.TotalProgram

namespace VariableWL.PrefixDescriptor.Program
attribute [local instance] Classical.propDecidable
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}

theorem RawExpr.eval_up (x : RawExpr n) (v : Env n) (a : Word) : x.up.eval (cons a v)=x.eval v := rfl

namespace Listing
variable (D : Listing n)

theorem eval_up (v : Env n) (a : Word) : D.up.eval (cons a v)=D.eval v := by
  unfold eval up
  congr 1
  · funext i; exact underOne_bit ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i j; exact underTwo_number ..
  · funext i j; exact underTwo_number ..
  · funext i j; exact underTwo_bit ..
  · funext i j; exact underTwo_bit ..

 theorem sortBound_number (v : Env n) : D.sortBound.number v=(D.eval v).sortBound := by
  simp only [sortBound,mul_number,numeral_number,Data.sortBound,eval]
 theorem bound_number (v : Env n) : D.bound.number v=(D.eval v).bound := by
  simp only [bound,mul_number,numeral_number,sortBound_number,Data.bound]
 theorem tag_number (x : RawExpr n) (v : Env n) : (D.tag x).number v=(D.eval v).tag (x.eval v) := by
  simp only [tag,add_number,mul_number,numeral_number,Data.tag,RawExpr.eval,eval]
 theorem unpack_eval (I : Expr n) (v : Env n) : (D.unpack I).eval v=(D.eval v).unpack (I.number v) := by
  simp only [unpack,RawExpr.eval,div_number,mod_number,numeral_number,Data.unpack,eval]

 theorem treePossible_bit (x : RawExpr n) (J : Expr n) (v : Env n) :
    (D.treePossible x J).bit v=((D.eval v).legal (x.eval v).block (J.number v) &&
      decide (PrefixAlphabet.prefixCode ((D.eval v).order (x.eval v).block (x.eval v).channel)
        (x.eval v).height (J.number v)=(x.eval v).vector)) := by
  simp only [treePossible,conj_bit,applyNat₂_bit,eq_bit,PrefixAlphabet.TotalProgram.prefixCode_number,applyNat₂_number]
  rfl
 theorem treeValid_bit (x : RawExpr n) (v : Env n) :
    (D.treeValid x).bit v=(D.eval v).treeValid (x.eval v) := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.treeValid_true]
  simp only [treeValid,conj_bit,le_bit,applyNat₂_number,applyNat_number,any_bit,numeral_number,
    treePossible_bit,eval_up,RawExpr.eval_up,input_number,cons_zero,List.length_replicate]
  dsimp only [eval,RawExpr.eval]
  simp only [Bool.and_eq_true,decide_eq_true_eq]
 theorem validRaw_bit (x : RawExpr n) (v : Env n) :
    (D.validRaw x).bit v=(D.eval v).validRaw (x.eval v) := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.validRaw_true]
  simp only [validRaw,conj_bit,disj_bit,eq_bit,lt_bit,applyNat_bit,applyNat_number,applyNat₂_bit,
    numeral_number,treeValid_bit,RawExpr.eval,eval]
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  simp only [and_assoc]
 theorem valid_bit (I : Expr n) (v : Env n) :
    (D.valid I).bit v=(D.eval v).valid (I.number v) := by
  rw [valid,validRaw_bit,unpack_eval]
  rfl

 theorem sortValid_bit (x : RawExpr n) (v : Env n) :
    (D.sortValid x).bit v=(D.eval v).sortValid (x.eval v) := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.sortValid_true]
  simp only [sortValid,conj_bit,disj_bit,eq_bit,lt_bit,le_bit,applyNat_bit,applyNat_number,applyNat₂_number,
    numeral_number,RawExpr.eval,eval]
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
 theorem sortPredicate_bit (I : Expr n) (v : Env n) :
    (D.sortPredicate I).bit v=(D.eval v).sortPredicate (I.number v) := by
  rw [sortPredicate,sortValid_bit,unpack_eval,mul_number,numeral_number]
  rfl
 theorem color_number (I : Expr n) (v : Env n) :
    (D.color I).number v=(D.eval v).color (I.number v) := by
  simp only [color,add_number,numeral_number,count_number,tag_number,unpack_eval,sortPredicate_bit,
    eval_up,input_number,cons_zero,List.length_replicate]
  rfl
 theorem colorBound_number (v : Env n) : D.colorBound.number v=(D.eval v).colorBound := by
  simp only [colorBound,add_number,numeral_number,count_number,sortBound_number,sortPredicate_bit,
    eval_up,input_number,cons_zero,List.length_replicate]
  rfl

 theorem forward_bit (x y : RawExpr n) (v : Env n) :
    (D.forward x y).bit v=(D.eval v).forward (x.eval v) (y.eval v) := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.forward_true]
  simp only [forward,conj_bit,disj_bit,eq_bit,add_number,numeral_number,applyNat_number,applyNat₂_number,
    PrefixAlphabet.TotalProgram.trim_number,PrefixAlphabet.TotalProgram.prefixCode_number,
    RawExpr.eval,eval]
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  simp only [and_assoc,or_assoc]
 theorem slot_number (x y : RawExpr n) (v : Env n) :
    (D.slot x y).number v=(D.eval v).slot (x.eval v) (y.eval v) := by
  simp only [slot,NumericProgram.choose_number,eq_bit,lt_bit,add_number,numeral_number,applyNat_number,
    PrefixAlphabet.TotalProgram.bit_number,decide_eq_true_eq,Data.slot,RawExpr.eval,eval]
  rfl
 theorem internal_bit (x y : RawExpr n) (I J : Expr n) (v : Env n) :
    (D.internal x y I J).bit v=(D.eval v).internal (x.eval v) (y.eval v) (I.number v) (J.number v) := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.internal_true]
  simp only [internal,conj_bit,disj_bit,eq_bit,forward_bit,slot_number,RawExpr.eval]
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]

 theorem roots_bit (x y : RawExpr n) (I J : Expr n) (v : Env n) :
    (D.roots x y I J).bit v=(D.eval v).roots (x.eval v) (y.eval v) (I.number v) (J.number v) := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.roots_true]
  simp only [roots,conj_bit,eq_bit,neg_bit,applyNat₂_number,applyNat₂_bit,add_number,mul_number,
    numeral_number,PrefixAlphabet.TotalProgram.paddedEqual_bit,RawExpr.eval,eval,
    ]
  simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
  simp only [and_assoc]
 theorem anchors_bit (x y : RawExpr n) (I J : Expr n) (v : Env n) :
    (D.anchors x y I J).bit v=(D.eval v).anchors (x.eval v) (y.eval v) (I.number v) (J.number v) := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.anchors_true]
  simp only [anchors,conj_bit,disj_bit,eq_bit,add_number,numeral_number,count_number,
    RawExpr.eval,eval,Descriptor.rank]
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  simp only [and_assoc]
 theorem incidence_bit (I J : Expr n) (v : Env n) :
    (D.incidence I J).bit v=(D.eval v).incidence (I.number v) (J.number v) := by
  simp only [incidence,disj_bit,internal_bit,roots_bit,anchors_bit,unpack_eval,div_number,mod_number,numeral_number]
  rfl

 theorem portListing_eval (v : Env n) : D.portListing.eval v=(D.eval v).portData := by
  unfold PortListing.eval Data.portData
  dsimp only [portListing]
  apply Descriptor.PortData.ext
  all_goals dsimp only
  · exact D.bound_number v
  · funext i; simp only [valid_bit,eval_up,input_number,cons_zero,List.length_replicate ]
  · funext i; simp only [color_number,eval_up,input_number,cons_zero,List.length_replicate ]
  · exact D.colorBound_number v
  · funext i j; simp only [incidence_bit,eval_up,input_number,cons_zero,show (1 : Fin (n+2))=(0 : Fin (n+1)).succ from rfl,cons_succ,List.length_replicate ]
end Listing
end VariableWL.PrefixDescriptor.Program

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BlockDescriptor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8

namespace VariableWL.BlockDescriptor.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}
namespace Listing
variable (D : Listing n)
 theorem eval_up (v : Env n) (a : Word) : D.up.eval (cons a v)=D.eval v := by
  unfold eval up
  congr 1
  · funext i; exact underOne_bit ..
  · funext i; exact underOne_bit ..
  · funext i j; exact underTwo_bit ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i j; exact underTwo_number ..
  · funext i j; exact underTwo_bit ..

 theorem properBound_number (v : Env n) : D.properBound.number v=(D.eval v).properBound := by
  simp only [properBound,mul_number,Core.properBound,eval]
 theorem channelBound_number (v : Env n) : D.channelBound.number v=(D.eval v).channelBound := by
  simp only [channelBound,add_number,numeral_number,properBound_number,Core.channelBound]
 theorem proper_bit (B I : Expr n) (v : Env n) : (D.proper B I).bit v=(D.eval v).proper (B.number v) (I.number v) := by
  simp only [proper,conj_bit,neg_bit,eq_bit,div_number,mod_number,applyNat_bit,applyNat₂_bit,Core.proper,eval]
  rw [←decide_not]
  rfl
 theorem channels_number (B : Expr n) (v : Env n) : (D.channels B).number v=(D.eval v).channels (B.number v) := by
  simp only [channels,add_number,count_number,properBound_number,proper_bit,eval_up,up_number,input_number,
    cons_zero,List.length_replicate,numeral_number,Core.channels,Descriptor.rank]
 theorem select_number (B C : Expr n) (v : Env n) : (D.select B C).number v=(D.eval v).select (B.number v) (C.number v) := by
  simp only [select,Computation.Stack.PolyRecipe.select_number,properBound_number,proper_bit,eval_up,up_number,input_number,
    cons_zero,List.length_replicate,sub_number,numeral_number,Core.select]
 theorem other_number (B C : Expr n) (v : Env n) : (D.other B C).number v=(D.eval v).other (B.number v) (C.number v) := by
  simp only [other,div_number,select_number,Core.other,eval]
 theorem readout_number (B C : Expr n) (v : Env n) : (D.readout B C).number v=(D.eval v).readout (B.number v) (C.number v) := by
  simp only [readout,mod_number,select_number,Core.readout,eval]
 theorem root_number (B C : Expr n) (v : Env n) : (D.root B C).number v=(D.eval v).root (B.number v) (C.number v) := by
  simp only [root,NumericProgram.choose_number,eq_bit,numeral_number,applyNat_number,readout_number,
    decide_eq_true_eq,Core.root,eval]
 theorem order_number (B C : Expr n) (v : Env n) : (D.order B C).number v=(D.eval v).order (B.number v) (C.number v) := by
  simp only [order,NumericProgram.choose_number,eq_bit,numeral_number,applyNat_number,applyNat₂_number,readout_number,
    decide_eq_true_eq,Core.order,eval]
 theorem matching_bit (I J : Expr n) (v : Env n) : (D.matching I J).bit v=(D.eval v).matching (I.number v) (J.number v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [matching,conj_bit,eq_bit,other_number,readout_number,div_number,mod_number,channelBound_number,
    Core.matching,Bool.and_eq_true,decide_eq_true_eq]

 theorem prefix_eval (v : Env n) : D.toPrefix.eval v=(D.eval v).toPrefix := by
  unfold toPrefix PrefixDescriptor.Program.Listing.eval Core.toPrefix
  congr 1
  · exact D.channelBound_number v
  · funext i; simp only [channels_number,eval_up,input_number,cons_zero,List.length_replicate]
  · funext i j; simp only [root_number,eval_up,input_number,cons_zero,NumericProgram.cons_one,List.length_replicate]
  · funext i j; simp only [order_number,eval_up,input_number,cons_zero,NumericProgram.cons_one,List.length_replicate]
  · funext i j; simp only [matching_bit,eval_up,input_number,cons_zero,NumericProgram.cons_one,List.length_replicate]
end Listing
end VariableWL.BlockDescriptor.Program

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BlockCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.Descriptor.Presentation
attribute [local instance] Classical.propDecidable
 theorem boolean_bound : boolean.bound=2 := rfl
 theorem boolean_valid (i : ℕ) : boolean.valid i=true := rfl
end VariableWL.Descriptor.Presentation

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}
theorem underThree_value (P : Expr (n+3)) (v : Env n) (a b c d : Word) :
    (underThree P).value (cons a (cons b (cons c (cons d v))))=P.value (cons a (cons b (cons c v))) := by
  apply congrArg P.program.value
  funext i
  exact Fin.cases rfl (fun i=>Fin.cases rfl (fun i=>Fin.cases rfl (fun _=>rfl) i) i) i
theorem underThree_number (P : Expr (n+3)) (v : Env n) (a b c d : Word) :
    (underThree P).number (cons a (cons b (cons c (cons d v))))=P.number (cons a (cons b (cons c v))) := by
  unfold Expr.number
  rw [underThree_value]
theorem underThree_bit (P : Expr (n+3)) (v : Env n) (a b c d : Word) :
    (underThree P).bit (cons a (cons b (cons c (cons d v))))=P.bit (cons a (cons b (cons c v))) := by
  unfold Expr.bit
  rw [underThree_value]
end VariableWL.Computation.Stack.PolyRecipe

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BlockListing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.BlockCatalog.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}
 theorem literal_true_bit (v : Env n) : (literal [true] : Expr n).bit v=true := rfl
namespace Listing
variable (D : Listing n)
theorem eval_up (v : Env n) (a : Word) : D.up.eval (cons a v)=D.eval v := by
  unfold eval up
  congr 1
  · funext i; exact underOne_bit ..
  · funext i; exact underOne_bit ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i j a; exact underThree_bit ..
  · funext i j a; exact underThree_number ..

theorem vertices_number (v : Env n) : (D.vertices ).number v=(D.eval v).vertices  := by
  simp only [vertices,add_number,mul_number,Data.vertices,eval]

theorem links_number (v : Env n) : (D.links ).number v=(D.eval v).links  := by
  simp only [links,add_number,mul_number,numeral_number,Data.links,eval]

theorem horizontals_number (v : Env n) : (D.horizontals ).number v=(D.eval v).horizontals  := by
  simp only [horizontals,mul_number,numeral_number,vertices_number,Data.horizontals,eval]

theorem squares_number (v : Env n) : (D.squares ).number v=(D.eval v).squares  := by
  simp only [squares,mul_number,numeral_number,links_number,Data.squares,eval]

theorem verticals_number (v : Env n) : (D.verticals ).number v=(D.eval v).verticals  := by
  simp only [verticals,mul_number,numeral_number,links_number,Data.verticals,eval]

theorem blocks_number (v : Env n) : (D.blocks ).number v=(D.eval v).blocks  := by
  simp only [blocks,add_number,horizontals_number,squares_number,Data.blocks,eval]

theorem reads_number (v : Env n) : (D.reads ).number v=(D.eval v).reads  := by
  simp only [reads,add_number,horizontals_number,verticals_number,Data.reads,eval]

theorem validVertex_bit (I : Expr n) (v : Env n) : (D.validVertex I).bit v=(D.eval v).validVertex (I.number v) := by
  simp only [validVertex,div_number,sub_number,choose_bit,lt_bit,applyNat_bit,decide_eq_true_eq,Data.validVertex,eval]
  rfl

theorem validLink_bit (I : Expr n) (v : Env n) : (D.validLink I).bit v=(D.eval v).validLink (I.number v) := by
  simp only [validLink,add_number,div_number,numeral_number,applyNat_bit,Data.validLink,eval]

theorem validH_bit (I : Expr n) (v : Env n) : (D.validH I).bit v=(D.eval v).validH (I.number v) := by
  simp only [validH,div_number,mod_number,numeral_number,vertices_number,validVertex_bit,Data.validH,eval]

theorem validS_bit (I : Expr n) (v : Env n) : (D.validS I).bit v=(D.eval v).validS (I.number v) := by
  simp only [validS,div_number,mod_number,numeral_number,links_number,validLink_bit,Data.validS,eval]

theorem validV_bit (I : Expr n) (v : Env n) : (D.validV I).bit v=(D.eval v).validV (I.number v) := by
  simp only [validV,div_number,mod_number,numeral_number,links_number,validLink_bit,Data.validV,eval]

theorem rawValid_bit (I : Expr n) (v : Env n) : (D.rawValid I).bit v=(D.eval v).rawValid (I.number v) := by
  simp only [rawValid,sub_number,choose_bit,lt_bit,decide_eq_true_eq,horizontals_number,validH_bit,validS_bit,Data.rawValid,eval]
  rfl

theorem readValid_bit (I : Expr n) (v : Env n) : (D.readValid I).bit v=(D.eval v).readValid (I.number v) := by
  simp only [readValid,sub_number,choose_bit,lt_bit,decide_eq_true_eq,horizontals_number,validH_bit,validV_bit,Data.readValid,eval]
  rfl

theorem hrow_number (I : Expr n) (v : Env n) : (D.hrow I).number v=(D.eval v).hrow (I.number v) := by
  simp only [hrow,div_number,numeral_number,vertices_number,Data.hrow,eval]

theorem htype_number (I : Expr n) (v : Env n) : (D.htype I).number v=(D.eval v).htype (I.number v) := by
  simp only [htype,div_number,mod_number,numeral_number,vertices_number,Data.htype,eval]

theorem srow_number (I : Expr n) (v : Env n) : (D.srow I).number v=(D.eval v).srow (I.number v) := by
  simp only [srow,div_number,numeral_number,links_number,Data.srow,eval]

theorem slink_number (I : Expr n) (v : Env n) : (D.slink I).number v=(D.eval v).slink (I.number v) := by
  simp only [slink,div_number,mod_number,numeral_number,links_number,Data.slink,eval]

theorem first_number (I : Expr n) (v : Env n) : (first I).number v=Data.first (I.number v) := by
  simp only [first,div_number,mod_number,numeral_number,Data.first]

theorem last_number (I : Expr n) (v : Env n) : (last I).number v=Data.last (I.number v) := by
  simp only [last,mod_number,numeral_number,Data.last]

theorem next_number (I : Expr n) (v : Env n) : (D.next I).number v=(D.eval v).next (I.number v) := by
  simp only [next,add_number,mod_number,numeral_number,Data.next,eval]

theorem labels_bit (T I A : Expr n) (v : Env n) : (D.labels T I A).bit v=(D.eval v).labels (T.number v) (I.number v) (A.number v) := by
  simp only [labels,choose_bit,lt_bit,literal_true_bit,applyNat₃_bit,div_number,sub_number,decide_eq_true_eq,Data.labels,eval]
  rfl

theorem horizontalValid_bit (I : Expr n) (v : Env n) : (D.horizontalValid I).bit v=(D.eval v).horizontalValid (I.number v) := by
  simp only [horizontalValid,conj_bit,labels_bit,htype_number,hrow_number,first_number,last_number,next_number,Data.horizontalValid]

theorem squareValid_bit (I : Expr n) (v : Env n) : (D.squareValid I).bit v=(D.eval v).squareValid (I.number v) := by
  simp only [squareValid,add_number,div_number,numeral_number,conj_bit,applyNat₃_bit,srow_number,slink_number,first_number,last_number,next_number,Data.squareValid,eval]

theorem validBlock_bit (I : Expr n) (v : Env n) : (D.validBlock I).bit v=(D.eval v).validBlock (I.number v) := by
  simp only [validBlock,conj_bit,rawValid_bit,choose_bit,lt_bit,horizontals_number,decide_eq_true_eq,sub_number,horizontalValid_bit,squareValid_bit,Data.validBlock]

theorem left_number (L : Expr n) (v : Env n) : (D.left L).number v=(D.eval v).left (L.number v) := by
  simp only [left,add_number,mul_number,div_number,mod_number,sub_number,numeral_number,NumericProgram.choose_number,eq_bit,applyNat_number,decide_eq_true_eq,Data.left,eval]
  rfl

theorem right_number (L : Expr n) (v : Env n) : (D.right L).number v=(D.eval v).right (L.number v) := by
  simp only [right,add_number,mul_number,div_number,mod_number,numeral_number,NumericProgram.choose_number,eq_bit,applyNat_number,decide_eq_true_eq,Data.right,eval]
  rfl

theorem output_number (L I A : Expr n) (v : Env n) : (D.output L I A).number v=(D.eval v).output (L.number v) (I.number v) (A.number v) := by
  simp only [output,add_number,div_number,mod_number,numeral_number,NumericProgram.choose_number,eq_bit,applyNat₃_number,decide_eq_true_eq,Data.output,eval]
  rfl

theorem horizontalCode_number (I T A B : Expr n) (v : Env n) : (D.horizontalCode I T A B).number v=(D.eval v).horizontalCode (I.number v) (T.number v) (A.number v) (B.number v) := by
  simp only [horizontalCode,add_number,mul_number,numeral_number,vertices_number,Data.horizontalCode,eval]

theorem verticalCode_number (I L A : Expr n) (v : Env n) : (D.verticalCode I L A).number v=(D.eval v).verticalCode (I.number v) (L.number v) (A.number v) := by
  simp only [verticalCode,add_number,mul_number,numeral_number,links_number,horizontals_number,Data.verticalCode,eval]

theorem squareLeft_number (S : Expr n) (v : Env n) : (D.squareLeft S).number v=(D.eval v).squareLeft (S.number v) := by
  simp only [squareLeft,srow_number,slink_number,first_number,last_number,left_number,horizontalCode_number,Data.squareLeft,eval]

theorem squareRight_number (S : Expr n) (v : Env n) : (D.squareRight S).number v=(D.eval v).squareRight (S.number v) := by
  simp only [squareRight,srow_number,slink_number,first_number,last_number,next_number,right_number,output_number,horizontalCode_number,Data.squareRight,eval]

theorem squareBottom_number (S : Expr n) (v : Env n) : (D.squareBottom S).number v=(D.eval v).squareBottom (S.number v) := by
  simp only [squareBottom,srow_number,slink_number,first_number,verticalCode_number,Data.squareBottom,eval]

theorem squareTop_number (S : Expr n) (v : Env n) : (D.squareTop S).number v=(D.eval v).squareTop (S.number v) := by
  simp only [squareTop,srow_number,slink_number,last_number,next_number,verticalCode_number,Data.squareTop,eval]

theorem has_bit (B A : Expr n) (v : Env n) : (D.has B A).bit v=(D.eval v).has (B.number v) (A.number v) := by
  simp only [has,sub_number,choose_bit,disj_bit,eq_bit,lt_bit,decide_eq_true_eq,horizontals_number,squareLeft_number,squareRight_number,squareBottom_number,squareTop_number,Data.has]
  split_ifs <;> apply Bool.eq_iff_iff.mpr <;> simp only [Bool.or_eq_true,decide_eq_true_eq]

end Listing
end VariableWL.BlockCatalog.Program

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_AffineCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.AffineAlphabet
open VariableWL.Affine
attribute [local instance] Classical.propDecidable
 theorem horizontalLegal_false {d i : ℕ} (h : ¬(d<3 ∧ i<PrefixAlphabet.vectorCount)) : horizontalLegal d i=false := by
  apply Bool.eq_false_iff.mpr
  intro he
  obtain ⟨hd,z,hz⟩ := of_decide_eq_true he
  have hi := PrefixAlphabet.encode_lt (by simp only [Fintype.card_fin]; omega) (horizontalEncode d z)
  exact h ⟨by omega,hz ▸ hi⟩
 theorem squareLegal_false {l r c i : ℕ} (h : ¬(l<formCount ∧ r<formCount ∧ i<PrefixAlphabet.vectorCount)) : squareLegal l r c i=false := by
  unfold squareLegal
  split_ifs with hl hr
  · apply Bool.eq_false_iff.mpr
    intro he
    obtain ⟨z,_,hz⟩ := of_decide_eq_true he
    have hi := PrefixAlphabet.encode_lt (square_count_le (formNumber.symm ⟨l,hl⟩).1 (formNumber.symm ⟨r,hr⟩).1)
      (squareEncode _ _ z)
    exact h ⟨hl,hr,hz ▸ hi⟩
  all_goals rfl
 theorem squareLegal_mod (l r c i : ℕ) : squareLegal l r (c%2) i=squareLegal l r c i := by
  unfold squareLegal
  split_ifs <;> simp only [ZMod.natCast_mod]
 theorem horizontalOrder_false {d : ℕ} (h : ¬d<3) : horizontalOrder d=0 := dite_eq_right (by omega)
 theorem squareOrder_false {d e a : ℕ} (h : ¬(d<3 ∧ e<3)) : squareOrder d e a=0 := by
  unfold squareOrder
  split_ifs <;> omega
 theorem squareOrder_cap (d e a : ℕ) : squareOrder d e (min a 3)=squareOrder d e a := by
  by_cases ha : a≤3
  · rw [Nat.min_eq_left ha]
  · have h3 : 3≤a := by omega
    rw [Nat.min_eq_right h3]
    unfold squareOrder
    simp only [show ¬a=0 by omega,show ¬a=1 by omega,ite_false]
    split_ifs <;> simp_all [show a≠2 by omega]
 theorem zeroOrder_false {d : ℕ} (h : ¬d<7) : zeroOrder d=0 := dite_eq_right (by omega)
end VariableWL.AffineAlphabet

namespace VariableWL.AffineAlphabet.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}
 theorem horizontalOrder_number (D : Expr n) (v : Env n) : (horizontalOrder D).number v=AffineAlphabet.horizontalOrder (D.number v) := by
  rw [horizontalOrder,fixedNat_total]
  unfold tableLookup
  split_ifs with h
  · rfl
  · exact (horizontalOrder_false h).symm
 theorem zeroOrder_number (D : Expr n) (v : Env n) : (zeroOrder D).number v=AffineAlphabet.zeroOrder (D.number v) := by
  rw [zeroOrder,fixedNat_total]
  unfold tableLookup
  split_ifs with h
  · rfl
  · exact (zeroOrder_false h).symm
 theorem squareOrder_number (D E A : Expr n) (v : Env n) :
    (squareOrder D E A).number v=AffineAlphabet.squareOrder (D.number v) (E.number v) (A.number v) := by
  simp only [squareOrder,table₃_number,minimum_number,numeral_number]
  split_ifs with h
  · exact squareOrder_cap _ _ _
  · exact (squareOrder_false (by have := Nat.min_le_right (A.number v) 3; omega)).symm
 theorem horizontalLegal_bit (D I : Expr n) (v : Env n) :
    (horizontalLegal D I).bit v=AffineAlphabet.horizontalLegal (D.number v) (I.number v) := by
  simp only [horizontalLegal,eq_bit,table₂_number,numeral_number]
  by_cases h : D.number v<3 ∧ I.number v<PrefixAlphabet.vectorCount
  · rw [ite_eq_left h]
    cases AffineAlphabet.horizontalLegal (D.number v) (I.number v) <;> rfl
  · rw [ite_eq_right h,horizontalLegal_false h]
    rfl
 theorem squareLegal_bit_bounded (L R C I : Expr n) (v : Env n) (hi : I.number v<PrefixAlphabet.vectorCount) :
    (squareLegalBody L R C I).bit v=AffineAlphabet.squareLegal (L.number v) (R.number v) (C.number v) (I.number v) := by
  have hc : C.number v%2<2 := Nat.mod_lt _ (by decide)
  have hp : 0<PrefixAlphabet.vectorCount := by omega
  have hq : C.number v%2*PrefixAlphabet.vectorCount+I.number v<2*PrefixAlphabet.vectorCount := by
    nlinarith
  simp only [squareLegalBody,eq_bit,table₃_number,add_number,mul_number,mod_number,numeral_number]
  by_cases h : L.number v<formCount ∧ R.number v<formCount ∧ C.number v%2*PrefixAlphabet.vectorCount+I.number v<2*PrefixAlphabet.vectorCount
  · rw [ite_eq_left h,PrefixDescriptor.Data.join_div _ _ _ hp hi,PrefixDescriptor.Data.join_mod _ _ _ hi,squareLegal_mod]
    cases AffineAlphabet.squareLegal (L.number v) (R.number v) (C.number v) (I.number v) <;> rfl
  · have hh : ¬(L.number v<formCount ∧ R.number v<formCount ∧ I.number v<PrefixAlphabet.vectorCount) := by
      intro ht; exact h ⟨ht.1,ht.2.1,hq⟩
    rw [ite_eq_right h,squareLegal_false hh]
    rfl
 theorem squareLegal_bit (L R C I : Expr n) (v : Env n) :
    (squareLegal L R C I).bit v=AffineAlphabet.squareLegal (L.number v) (R.number v) (C.number v) (I.number v) := by
  simp only [squareLegal,choose_bit,lt_bit,numeral_number,decide_eq_true_eq]
  split_ifs with hi
  · exact squareLegal_bit_bounded _ _ _ _ _ hi
  · rw [squareLegal_false (by tauto)]
    rfl
end VariableWL.AffineAlphabet.Program

namespace VariableWL.BlockDescriptor.Program.Listing
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
 theorem eval_blocks {n : ℕ} (B : Listing n) (v : Env n) : (B.eval v).blocks=B.blocks.number v := rfl
 theorem eval_reads {n : ℕ} (B : Listing n) (v : Env n) : (B.eval v).reads=B.reads.number v := rfl
 theorem eval_validBlock {n : ℕ} (B : Listing n) (v : Env n) : (B.eval v).validBlock=(fun i=>B.validBlock.bit (cons (List.replicate i true) v)) := rfl
 theorem eval_validRead {n : ℕ} (B : Listing n) (v : Env n) : (B.eval v).validRead=(fun i=>B.validRead.bit (cons (List.replicate i true) v)) := rfl
end VariableWL.BlockDescriptor.Program.Listing
namespace VariableWL.AffineCatalog.Data
 theorem core_blocks_eq (D : Data) : D.core.blocks=D.toData.blocks := rfl
 theorem core_reads_eq (D : Data) : D.core.reads=D.toData.reads := rfl
 theorem core_validBlock_eq (D : Data) : D.core.validBlock=D.validBlock := rfl
 theorem core_validRead_eq (D : Data) : D.core.validRead=D.readValid := rfl
end VariableWL.AffineCatalog.Data
namespace VariableWL.BlockDescriptor.Core
theorem ext_fields {X Y : Core} (hb : X.blocks=Y.blocks) (hv : X.validBlock=Y.validBlock)
    (hr : X.reads=Y.reads) (hvr : X.validRead=Y.validRead) (hh : X.has=Y.has)
    (hd : X.dimension=Y.dimension) (hrd : X.readDimension=Y.readDimension)
    (hz : X.zeroOrder=Y.zeroOrder) (ho : X.readOrder=Y.readOrder) (hl : X.legal=Y.legal) : X=Y := by
  cases X; cases Y; simp_all
end VariableWL.BlockDescriptor.Core

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_CircuitCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11

namespace VariableWL.AffineCatalog.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
open VariableWL.NumericProgram
variable {n : ℕ}
namespace Listing
variable (D : Listing n)
 theorem eval_up (v : Env n) (a : Word) : D.up.eval (cons a v)=D.eval v := by
  dsimp only [eval,up]
  congr 1
  · exact D.toListing.eval_up v a
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
 theorem vertexDimension_number (T : Expr n) (v : Env n) : (D.vertexDimension T).number v=(D.eval v).vertexDimension (T.number v) := by
  simp only [vertexDimension,lt_bit,applyNat_number,choose_number,numeral_number,lt_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.vertexDimension,eval] ; rfl

 theorem horizontalDimension_number (H : Expr n) (v : Env n) : (D.horizontalDimension H).number v=(D.eval v).horizontalDimension (H.number v) := by
  simp only [horizontalDimension,vertexDimension_number,BlockCatalog.Program.Listing.htype_number,BlockCatalog.Program.Listing.eval,Data.horizontalDimension,eval]

 theorem squareLeftDimension_number (S : Expr n) (v : Env n) : (D.squareLeftDimension S).number v=(D.eval v).squareLeftDimension (S.number v) := by
  simp only [squareLeftDimension,vertexDimension_number,BlockCatalog.Program.Listing.left_number,BlockCatalog.Program.Listing.slink_number,BlockCatalog.Program.Listing.eval,Data.squareLeftDimension,eval]

 theorem squareRightDimension_number (S : Expr n) (v : Env n) : (D.squareRightDimension S).number v=(D.eval v).squareRightDimension (S.number v) := by
  simp only [squareRightDimension,vertexDimension_number,BlockCatalog.Program.Listing.right_number,BlockCatalog.Program.Listing.slink_number,BlockCatalog.Program.Listing.eval,Data.squareRightDimension,eval]

 theorem dimension_number (B : Expr n) (v : Env n) : (D.dimension B).number v=(D.eval v).dimension (B.number v) := by
  simp only [dimension,horizontalDimension_number,squareLeftDimension_number,squareRightDimension_number,BlockCatalog.Program.Listing.horizontals_number,choose_number,add_number,sub_number,numeral_number,lt_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.dimension,eval] ; rfl

 theorem readDimension_number (A : Expr n) (v : Env n) : (D.readDimension A).number v=(D.eval v).readDimension (A.number v) := by
  simp only [readDimension,horizontalDimension_number,BlockCatalog.Program.Listing.horizontals_number,choose_number,numeral_number,lt_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.readDimension,eval] ; rfl

 theorem linkLeft_number (L : Expr n) (v : Env n) : (D.linkLeft L).number v=(D.eval v).linkLeft (L.number v) := by
  simp only [linkLeft,applyNat_number,choose_number,add_number,div_number,mod_number,numeral_number,eq_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.linkLeft,eval] ; rfl

 theorem linkRight_number (L : Expr n) (v : Env n) : (D.linkRight L).number v=(D.eval v).linkRight (L.number v) := by
  simp only [linkRight,applyNat_number,choose_number,add_number,div_number,mod_number,numeral_number,eq_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.linkRight,eval] ; rfl

 theorem linkLeftConstant_number (L : Expr n) (v : Env n) : (D.linkLeftConstant L).number v=(D.eval v).linkLeftConstant (L.number v) := by
  simp only [linkLeftConstant,applyNat_number,choose_number,add_number,div_number,mod_number,numeral_number,eq_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.linkLeftConstant,eval] ; rfl

 theorem linkRightConstant_number (L : Expr n) (v : Env n) : (D.linkRightConstant L).number v=(D.eval v).linkRightConstant (L.number v) := by
  simp only [linkRightConstant,applyNat_number,choose_number,add_number,div_number,mod_number,numeral_number,eq_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.linkRightConstant,eval] ; rfl

 theorem constant_number (S : Expr n) (v : Env n) : (D.constant S).number v=(D.eval v).constant (S.number v) := by
  simp only [constant,linkLeftConstant_number,linkRightConstant_number,BlockCatalog.Program.Listing.srow_number,BlockCatalog.Program.Listing.slink_number,choose_number,add_number,mul_number,mod_number,numeral_number,eq_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.constant,eval] ; rfl

 theorem zeroOrder_number (B : Expr n) (v : Env n) : (D.zeroOrder B).number v=(D.eval v).zeroOrder (B.number v) := by
  simp only [zeroOrder,AffineAlphabet.Program.zeroOrder_number,dimension_number,BlockCatalog.Program.Listing.eval,Data.zeroOrder,eval]

 theorem readOrder_number (B A : Expr n) (v : Env n) : (D.readOrder B A).number v=(D.eval v).readOrder (B.number v) (A.number v) := by
  simp only [readOrder,AffineAlphabet.Program.horizontalOrder_number,AffineAlphabet.Program.squareOrder_number,horizontalDimension_number,squareLeftDimension_number,squareRightDimension_number,BlockCatalog.Program.Listing.horizontals_number,BlockCatalog.Program.Listing.squareLeft_number,BlockCatalog.Program.Listing.squareRight_number,BlockCatalog.Program.Listing.squareBottom_number,choose_number,sub_number,numeral_number,eq_bit,lt_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.readOrder,eval] ; rfl

 theorem legal_bit (B I : Expr n) (v : Env n) : (D.legal B I).bit v=(D.eval v).legal (B.number v) (I.number v) := by
  simp only [legal,AffineAlphabet.Program.horizontalLegal_bit,AffineAlphabet.Program.squareLegal_bit,horizontalDimension_number,linkLeft_number,linkRight_number,constant_number,BlockCatalog.Program.Listing.horizontals_number,BlockCatalog.Program.Listing.slink_number,choose_bit,sub_number,lt_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.legal,eval] ; rfl

 theorem core_blocks_field : D.core.blocks=D.toListing.blocks := rfl
 theorem core_blocks_eval (v : Env n) : (D.core.eval v).blocks=(D.eval v).core.blocks := by
  rw [BlockDescriptor.Program.Listing.eval_blocks,core_blocks_field,Data.core_blocks_eq]
  change D.toListing.blocks.number v=(D.toListing.eval v).blocks
  exact D.toListing.blocks_number v
 theorem core_validBlock_field : D.core.validBlock=D.toListing.up.validBlock (input 0) := rfl
 theorem core_validBlock_eval (v : Env n) : (D.core.eval v).validBlock=(D.eval v).core.validBlock := by
  rw [BlockDescriptor.Program.Listing.eval_validBlock,D.core_validBlock_field,Data.core_validBlock_eq]
  funext i
  rw [BlockCatalog.Program.Listing.validBlock_bit,BlockCatalog.Program.Listing.eval_up,input_number,cons_zero,List.length_replicate]
  rfl
 theorem core_reads_field : D.core.reads=D.toListing.reads := rfl
 theorem core_reads_eval (v : Env n) : (D.core.eval v).reads=(D.eval v).core.reads := by
  rw [BlockDescriptor.Program.Listing.eval_reads,core_reads_field,Data.core_reads_eq]
  change D.toListing.reads.number v=(D.toListing.eval v).reads
  exact D.toListing.reads_number v
 theorem core_validRead_field : D.core.validRead=D.toListing.up.readValid (input 0) := rfl
 theorem core_validRead_eval (v : Env n) : (D.core.eval v).validRead=(D.eval v).core.validRead := by
  rw [BlockDescriptor.Program.Listing.eval_validRead,D.core_validRead_field,Data.core_validRead_eq]
  funext i
  rw [BlockCatalog.Program.Listing.readValid_bit,BlockCatalog.Program.Listing.eval_up,input_number,cons_zero,List.length_replicate]
  rfl
 theorem core_has_eval (v : Env n) : (D.core.eval v).has=(D.eval v).core.has := by
  funext i j
  change (D.toListing.up.up.has (input 0) (input 1)).bit (cons (List.replicate i true) (cons (List.replicate j true) v))=(D.eval v).has i j
  rw [BlockCatalog.Program.Listing.has_bit,BlockCatalog.Program.Listing.eval_up,BlockCatalog.Program.Listing.eval_up]
  simp only [input_number,cons_zero,cons_one,List.length_replicate]
  rfl
 theorem core_dimension_eval (v : Env n) : (D.core.eval v).dimension=(D.eval v).core.dimension := by
  funext i
  change (D.up.dimension (input 0)).number (cons (List.replicate i true) v)=(D.eval v).dimension i
  rw [dimension_number,eval_up,input_number,cons_zero,List.length_replicate]
 theorem core_readDimension_eval (v : Env n) : (D.core.eval v).readDimension=(D.eval v).core.readDimension := by
  funext i
  change (D.up.readDimension (input 0)).number (cons (List.replicate i true) v)=(D.eval v).readDimension i
  rw [readDimension_number,eval_up,input_number,cons_zero,List.length_replicate]
 theorem core_zeroOrder_eval (v : Env n) : (D.core.eval v).zeroOrder=(D.eval v).core.zeroOrder := by
  funext i
  change (D.up.zeroOrder (input 0)).number (cons (List.replicate i true) v)=(D.eval v).zeroOrder i
  rw [zeroOrder_number,eval_up,input_number,cons_zero,List.length_replicate]
 theorem core_readOrder_eval (v : Env n) : (D.core.eval v).readOrder=(D.eval v).core.readOrder := by
  funext i j
  change (D.up.up.readOrder (input 0) (input 1)).number (cons (List.replicate i true) (cons (List.replicate j true) v))=(D.eval v).readOrder i j
  rw [readOrder_number,eval_up,eval_up]
  simp only [input_number,cons_zero,cons_one,List.length_replicate]
 theorem core_legal_eval (v : Env n) : (D.core.eval v).legal=(D.eval v).core.legal := by
  funext i j
  change (D.up.up.legal (input 0) (input 1)).bit (cons (List.replicate i true) (cons (List.replicate j true) v))=(D.eval v).legal i j
  rw [legal_bit,eval_up,eval_up]
  simp only [input_number,cons_zero,cons_one,List.length_replicate]
 theorem core_eval (v : Env n) : D.core.eval v=(D.eval v).core := by
  exact BlockDescriptor.Core.ext_fields (D.core_blocks_eval v) (D.core_validBlock_eval v) (D.core_reads_eval v) (D.core_validRead_eval v) (D.core_has_eval v) (D.core_dimension_eval v) (D.core_readDimension_eval v) (D.core_zeroOrder_eval v) (D.core_readOrder_eval v) (D.core_legal_eval v)

end Listing
end VariableWL.AffineCatalog.Program

namespace VariableWL.CircuitCatalog
open Descriptor Circuit VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {S : Type uVariable8} {A : Type uVariable9} {E : Type uVariable10} {R : Type uVariable11}
variable (PS : Presentation S) (PA : Presentation A) (PE : Presentation E) (PR : Presentation R)
variable (C : Description r S A E R) (marked : Fin r) (ε : Bit) {D : Data}
variable (h : Good (n := n) PS PA PE PR C marked ε D)
include h
 theorem edge_first (e : E) : D.edgeCode (PE.encode e)=PE.encode e := by
  rw [Data.edgeCode,ite_eq_left (by rw [h.edges]; exact PE.encode_lt e)]
 theorem edge_second (e : E) : D.edgeCode (PE.bound+PE.encode e)=PE.encode e := by
  have he:=PE.encode_lt e
  simp only [Data.edgeCode,h.edges,ite_eq_right (by omega : ¬PE.bound+PE.encode e<PE.bound),
    ite_eq_left (by omega : PE.bound+PE.encode e<2*PE.bound),Nat.add_sub_cancel_left]
 theorem edge_third (e : E) : D.edgeCode (PE.bound+(PE.bound+PE.encode e))=PE.encode e := by
  have he:=PE.encode_lt e
  simp only [Data.edgeCode,h.edges,ite_eq_right (by omega : ¬PE.bound+(PE.bound+PE.encode e)<PE.bound),
    ite_eq_right (by omega : ¬PE.bound+(PE.bound+PE.encode e)<2*PE.bound)]
  omega
 theorem output_form (e : E) : (if D.source (PE.encode e)<D.scalars then
    AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj 0) else AffineAlphabet.encodeForm (by decide : 2≤2)
      ((LinearMap.proj (0 : Fin 2) : Vec 2 →ₗ[Bit] Bit)+LinearMap.proj 1))=
      AffineAlphabet.encodeForm (RealizationSize.dimension_le_two C.consistency (n := n) (.inl (.inl (C.source e)))) (outputLinear (C.source e)) := by
  rw [h.source,h.scalars]
  cases hg : C.source e with
  | inl s => rw [Presentation.sum_inl,ite_eq_left (PS.encode_lt s)]; rfl
  | inr a => rw [Presentation.sum_inr,ite_eq_right (by omega)]; rfl
 theorem affine_good : AffineCatalog.Good (n := n) (real PS PA PE) (comparison PE PR) C.consistency marked ε D.affine := by
  refine ⟨?_,?_,?_,?_,?_,?_,h.marked,h.epsilon⟩
  · refine ⟨h.rows,h.internal,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp only [Data.affine,Data.gates,h.scalars,h.ands,h.edges,real]; rfl
    · simp only [Data.affine,h.edges,h.requests,comparison]; rfl
    · funext i
      simp only [Data.affine,Data.gates,h.scalars,h.ands,h.edges,h.validScalar,h.validAnd,h.validEdge,real]
      rfl
    · funext i
      simp only [Data.affine,h.edges,h.validEdge,h.validRequest,comparison]
      rfl
    · intro c
      rcases c with (e|(e|e))|b
      all_goals simp only [comparison,real,Presentation.sum_inl,Presentation.sum_inr,Presentation.sum_bound,
        Presentation.sum_bound,Data.affine,Data.gates,h.scalars,h.ands,h.edges,
        Circuit.Description.comparisonSource]
      all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_first PS PA PE PR C marked ε h,h.source] }
      all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_second PS PA PE PR C marked ε h,h.source] }
      all_goals try { rw [ite_eq_right (by have:=PE.encode_lt e; omega),ite_eq_left (by have:=PE.encode_lt e; omega),edge_third PS PA PE PR C marked ε h] }
      all_goals try { rw [ite_eq_right (by omega),ite_eq_right (by omega)]; have hb : PE.bound+(PE.bound+PE.bound)+PR.encode b-3*PE.bound=PR.encode b := by omega
                      rw [hb,h.requestGate] }
    · intro c
      rcases c with (e|(e|e))|b
      all_goals simp only [comparison,real,Presentation.sum_inl,Presentation.sum_inr,Presentation.sum_bound,Presentation.unit_encode,
        Data.affine,Data.gates,h.scalars,h.ands,h.edges,Circuit.Description.comparisonTarget]
      all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_first PS PA PE PR C marked ε h] }
      all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_second PS PA PE PR C marked ε h] }
      all_goals try { rw [ite_eq_right (by have:=PE.encode_lt e; omega),ite_eq_left (by have:=PE.encode_lt e; omega),edge_third PS PA PE PR C marked ε h,h.destination] }
      all_goals try { rw [ite_eq_right (by omega),ite_eq_right (by omega)]; rfl }
    · intro c i a
      rcases c with (e|(e|e))|b
      all_goals simp only [comparison,Presentation.sum_inl,Presentation.sum_inr,Presentation.sum_bound,Data.affine,h.edges]
      all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_first PS PA PE PR C marked ε h]; exact h.domain e i a }
      all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_second PS PA PE PR C marked ε h]; exact h.domain e i a }
      all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_third PS PA PE PR C marked ε h]; exact h.domain e i a }
      all_goals try { rw [ite_eq_right (by omega)]; have hb : PE.bound+(PE.bound+PE.bound)+PR.encode b-3*PE.bound=PR.encode b := by omega
                      rw [hb]; exact h.requestDomain b i a }
    · intro c i a
      rcases c with (e|(e|e))|b
      all_goals simp only [comparison,Presentation.sum_inl,Presentation.sum_inr,Presentation.sum_bound,Data.affine,h.edges]
      all_goals try { rw [ite_eq_right (by have:=PE.encode_lt e; omega)]<;> rfl }
      all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; exact ⟨by omega,by omega⟩),edge_third PS PA PE PR C marked ε h]; exact h.map e i a }
      all_goals try { rw [ite_eq_right (by  omega)]; rfl }
  · intro p
    rcases p with (s|a)|(e|u)
    all_goals simp only [Data.affine,Data.gates,h.scalars,h.ands,h.edges,real,Presentation.sum_inl,Presentation.sum_inr,Presentation.sum_bound,Presentation.unit_encode,
      Circuit.Description.realDimension,Circuit.dimension]
    · rw [ite_eq_left (PS.encode_lt s)]
    · rw [ite_eq_right (by omega),ite_eq_left (by have:=PA.encode_lt a; omega)]
    · rw [ite_eq_right (by  omega),ite_eq_left (by have:=PE.encode_lt e; change PS.bound+PA.bound+_<_; omega)]
    · rw [ite_eq_right (by  omega),ite_eq_right (by  omega)]
  · intro c
    rcases c with (e|(e|e))|b
    all_goals simp only [Data.affine,h.edges,comparison,Presentation.sum_inl,Presentation.sum_inr,Presentation.sum_bound,Circuit.Description.consistency]
    · rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_first PS PA PE PR C marked ε h]; exact output_form PS PA PE PR C marked ε h e
    · rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_second PS PA PE PR C marked ε h]; exact output_form PS PA PE PR C marked ε h e
    · rw [ite_eq_right (by omega),ite_eq_left (by have:=PE.encode_lt e; omega)]; rfl
    · rw [ite_eq_right (by  omega),ite_eq_right (by  omega)]; rfl
  · intro c
    rcases c with (e|(e|e))|b
    all_goals simp only [Data.affine,h.edges,comparison,Presentation.sum_inl,Presentation.sum_inr,Presentation.sum_bound,Circuit.Description.consistency]
    · rw [ite_eq_left (PE.encode_lt e)]; rfl
    · rw [ite_eq_right (by omega),ite_eq_left (by have:=PE.encode_lt e; omega)]; rfl
    · rw [ite_eq_right (by omega),ite_eq_right (by have:=PE.encode_lt e; omega),ite_eq_left (by have:=PE.encode_lt e; omega),edge_third PS PA PE PR C marked ε h,h.destinationForm]; rfl
    · rw [ite_eq_right (by  omega),ite_eq_right (by  omega),ite_eq_right (by  omega)]; rfl
  · intro c; rfl
  · intro c
    rcases c with (e|(e|e))|b
    all_goals simp only [Data.affine,h.edges,comparison,Presentation.sum_inl,Presentation.sum_inr,Presentation.sum_bound,]
    all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; omega)]<;> rfl }
    rw [ite_eq_right (by  omega)]
    have hb : PE.bound+(PE.bound+PE.bound)+PR.encode b-3*PE.bound=PR.encode b := by  omega
    rw [hb,h.requestTest]
    cases C.requestTest b <;> rfl
end VariableWL.CircuitCatalog

namespace VariableWL.BlockCatalog.Data
theorem ext_fields {X Y : Data} (h1 : X.rows=Y.rows) (h2 : X.internal=Y.internal)
    (h3 : X.reals=Y.reals) (h4 : X.comparisons=Y.comparisons)
    (h5 : X.validReal=Y.validReal) (h6 : X.validComparison=Y.validComparison)
    (h7 : X.source=Y.source) (h8 : X.target=Y.target) (h9 : X.domain=Y.domain) (h10 : X.map=Y.map) : X=Y := by
  cases X; cases Y; simp_all
end VariableWL.BlockCatalog.Data
namespace VariableWL.AffineCatalog.Data
theorem ext_fields {X Y : Data} (h1 : X.toData=Y.toData) (h2 : X.realDimension=Y.realDimension)
    (h3 : X.leftForm=Y.leftForm) (h4 : X.rightForm=Y.rightForm)
    (h5 : X.leftConstant=Y.leftConstant) (h6 : X.rightConstant=Y.rightConstant)
    (h7 : X.marked=Y.marked) (h8 : X.epsilon=Y.epsilon) : X=Y := by
  cases X; cases Y; simp_all
end VariableWL.AffineCatalog.Data

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_CellularCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5

namespace VariableWL.CircuitCatalog.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
variable {n : ℕ}
namespace Listing
variable (D : Listing n)
 theorem eval_up (v : Env n) (a : Word) : D.up.eval (cons a v)=D.eval v := by
  dsimp only [eval,up]
  congr 1
  · funext i; exact underOne_bit ..
  · funext i; exact underOne_bit ..
  · funext i; exact underOne_bit ..
  · funext i; exact underOne_bit ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i j a; exact underThree_bit ..
  · funext i j a; exact underThree_number ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i j a; exact underThree_bit ..
 theorem gates_number (v : Env n) : (D.gates).number v=(D.eval v).gates := by
  simp only [gates,add_number,eval,Data.gates]
 theorem edgeCode_number (C : Expr n) (v : Env n) : (D.edgeCode C).number v=(D.eval v).edgeCode (C.number v) := by
  simp only [edgeCode,choose_number,mul_number,sub_number,numeral_number,lt_bit,decide_eq_true_eq,eval,Data.edgeCode] ; rfl
 theorem affineSource_number (C : Expr n) (v : Env n) : (D.affineSource C).number v=(D.eval v).affine.source (C.number v) := by
  simp only [affineSource,gates_number,edgeCode_number,applyNat_number,choose_number,add_number,mul_number,sub_number,numeral_number,lt_bit,decide_eq_true_eq,eval,Data.affine,Data.gates] ; rfl
 theorem affineTarget_number (C : Expr n) (v : Env n) : (D.affineTarget C).number v=(D.eval v).affine.target (C.number v) := by
  simp only [affineTarget,gates_number,edgeCode_number,applyNat_number,choose_number,add_number,mul_number,numeral_number,lt_bit,decide_eq_true_eq,eval,Data.affine,Data.gates] ; rfl
 theorem affineDomain_bit (C I A : Expr n) (v : Env n) : (D.affineDomain C I A).bit v=(D.eval v).affine.domain (C.number v) (I.number v) (A.number v) := by
  simp only [affineDomain,edgeCode_number,applyNat₃_bit,choose_bit,mul_number,sub_number,numeral_number,lt_bit,decide_eq_true_eq,eval,Data.affine,Data.gates] ; rfl
 theorem affineMap_number (C I A : Expr n) (v : Env n) : (D.affineMap C I A).number v=(D.eval v).affine.map (C.number v) (I.number v) (A.number v) := by
  simp only [affineMap,edgeCode_number,applyNat₃_number,choose_number,mul_number,numeral_number,lt_bit,le_bit,conj_bit,decide_eq_true_eq,Bool.and_eq_true,eval,Data.affine,Data.gates] ; rfl
 theorem affineDimension_number (P : Expr n) (v : Env n) : (D.affineDimension P).number v=(D.eval v).affine.realDimension (P.number v) := by
  simp only [affineDimension,gates_number,choose_number,add_number,numeral_number,lt_bit,decide_eq_true_eq,eval,Data.affine,Data.gates] ; rfl
 theorem affineLeft_number (C : Expr n) (v : Env n) : (D.affineLeft C).number v=(D.eval v).affine.leftForm (C.number v) := by
  simp only [affineLeft,edgeCode_number,applyNat_number,choose_number,mul_number,numeral_number,lt_bit,decide_eq_true_eq,eval,Data.affine,Data.gates] ; rfl
 theorem affineRight_number (C : Expr n) (v : Env n) : (D.affineRight C).number v=(D.eval v).affine.rightForm (C.number v) := by
  simp only [affineRight,edgeCode_number,applyNat_number,choose_number,mul_number,numeral_number,lt_bit,decide_eq_true_eq,eval,Data.affine,Data.gates] ; rfl
 theorem affineConstant_number (C : Expr n) (v : Env n) : (D.affineConstant C).number v=(D.eval v).affine.rightConstant (C.number v) := by
  simp only [affineConstant,applyNat_number,choose_number,mul_number,sub_number,numeral_number,lt_bit,decide_eq_true_eq,eval,Data.affine,Data.gates] ; rfl
 theorem affineValidReal_bit (I : Expr n) (v : Env n) : (D.affineValidReal I).bit v=(D.eval v).affine.validReal (I.number v) := by
  simp only [affineValidReal,gates_number,applyNat_bit,choose_bit,sub_number,lt_bit,decide_eq_true_eq,BlockCatalog.Program.literal_true_bit,eval,Data.affine,Data.gates] ; rfl
 theorem affineValidComparison_bit (C : Expr n) (v : Env n) : (D.affineValidComparison C).bit v=(D.eval v).affine.validComparison (C.number v) := by
  simp only [affineValidComparison,applyNat_bit,choose_bit,add_number,sub_number,lt_bit,decide_eq_true_eq,eval,Data.affine,Data.gates] ; rfl
 theorem affine_base_eval (v : Env n) : (D.affine.eval v).toData=(D.eval v).affine.toData := by
  apply BlockCatalog.Data.ext_fields
  · rfl
  · rfl
  · change (add D.gates (add D.edges (numeral 1))).number v=(D.eval v).gates+((D.eval v).edges+1)
    rw [add_number,gates_number,add_number,numeral_number]; rfl
  · change (add (add D.edges (add D.edges D.edges)) D.requests).number v=_
    simp only [add_number]; rfl
  · funext i
    change (D.up.affineValidReal (input 0)).bit (cons (List.replicate i true) v)=_
    rw [affineValidReal_bit,eval_up]; simp only [input_number,cons_zero,List.length_replicate]
  · funext i
    change (D.up.affineValidComparison (input 0)).bit (cons (List.replicate i true) v)=_
    rw [affineValidComparison_bit,eval_up]; simp only [input_number,cons_zero,List.length_replicate]
  · funext i
    change (D.up.affineSource (input 0)).number (cons (List.replicate i true) v)=_
    rw [affineSource_number,eval_up]; simp only [input_number,cons_zero,List.length_replicate]
  · funext i
    change (D.up.affineTarget (input 0)).number (cons (List.replicate i true) v)=_
    rw [affineTarget_number,eval_up]; simp only [input_number,cons_zero,List.length_replicate]
  · funext i j a
    change (D.up.up.up.affineDomain (input 0) (input 1) (input 2)).bit
      (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v)))=_
    rw [affineDomain_bit,eval_up,eval_up,eval_up]; simp only [input_number,cons_zero,cons_one,cons_two,List.length_replicate]
  · funext i j a
    change (D.up.up.up.affineMap (input 0) (input 1) (input 2)).number
      (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v)))=_
    rw [affineMap_number,eval_up,eval_up,eval_up]; simp only [input_number,cons_zero,cons_one,cons_two,List.length_replicate]
 theorem affine_eval (v : Env n) : D.affine.eval v=(D.eval v).affine := by
  apply AffineCatalog.Data.ext_fields
  · exact D.affine_base_eval v
  · funext i
    change (D.up.affineDimension (input 0)).number (cons (List.replicate i true) v)=_
    rw [affineDimension_number,eval_up]; simp only [input_number,cons_zero,List.length_replicate]
  · funext i
    change (D.up.affineLeft (input 0)).number (cons (List.replicate i true) v)=_
    rw [affineLeft_number,eval_up]; simp only [input_number,cons_zero,List.length_replicate]
  · funext i
    change (D.up.affineRight (input 0)).number (cons (List.replicate i true) v)=_
    rw [affineRight_number,eval_up]; simp only [input_number,cons_zero,List.length_replicate]
  · funext i; rfl
  · funext i
    change (D.up.affineConstant (input 0)).number (cons (List.replicate i true) v)=_
    rw [affineConstant_number,eval_up]; simp only [input_number,cons_zero,List.length_replicate]
  · rfl
  · rfl
end Listing
end VariableWL.CircuitCatalog.Program

namespace VariableWL.Circuit.ProductCellular.Data
 theorem input_bit {L : Type uVariable2} {d m : ℕ} (D : Data L d m) (j : Fin m) (i : Fin d) : j.val.testBit i.val=D.inputBits j i := by
  simpa only [D.number_inputBits] using (Binary.number_bit (D.inputBits j) i)
end VariableWL.Circuit.ProductCellular.Data
namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
 theorem binaryDigit_total {n : ℕ} (N I : Expr n) (v : Env n) :
    (binaryDigit N I).bit v=(N.number v).testBit (I.number v) := by
  by_cases h : I.number v<(N.number v).size
  · exact binaryDigit_bit N I v h
  · have hp : N.number v<2^I.number v := by
      have := Nat.lt_size (n := N.number v) (m := I.number v)
      omega
    rw [Nat.testBit_eq_false_of_lt hp,binaryDigit,eq_bit,mod_number,div_number,capPow_number,add_number]
    simp only [numeral_number,Nat.min_eq_right (show N.number v+1≤2^I.number v by omega),
      Nat.div_eq_of_lt (Nat.lt_succ_self _),Nat.zero_mod]
    rfl
end VariableWL.Computation.Stack.PolyRecipe

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_CellularListing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.CellularCatalog
open Descriptor Circuit VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable1} {d m n : ℕ} (P : Presentation L) (C : ProductCellular.Data L d m)
variable (marked : Fin (d+d)) (ε : Bit)
variable {D : Data} (h : Good (n := n) P C marked ε D)
include h
 theorem kinds_eq : D.kinds=(kind d).bound := by
  simp only [Data.kinds,Data.rightEnd,Data.centerEnd,Data.leftEnd,h.bits,kind,
    Presentation.sum_bound,Presentation.product_bound,Presentation.option_bound,Presentation.fin_bound,Presentation.boolean_bound]
  omega
 theorem triples_eq : D.triples=(triple P).bound := by
  simp only [Data.triples,h.letters,triple,Presentation.product_bound]
 theorem edge_parts (e : ProductCellular.Edge L d) :
    D.tripleCode ((edge P).encode e)=(triple P).encode e.1 ∧ D.kindCode ((edge P).encode e)=(kind d).encode e.2 := by
  have hk := (kind d).encode_lt e.2
  simp only [Data.tripleCode,Data.kindCode,kinds_eq P C marked ε h,edge,Presentation.product_encode]
  exact ⟨PrefixDescriptor.Data.join_div _ _ _ (by omega) hk,PrefixDescriptor.Data.join_mod _ _ _ hk⟩
 theorem triple_parts (a b c : L) :
    D.first ((triple P).encode (a,b,c))=P.encode a ∧
    D.second ((triple P).encode (a,b,c))=P.encode b ∧
    D.third ((triple P).encode (a,b,c))=P.encode c := by
  have ha:=P.encode_lt a
  have hb:=P.encode_lt b
  have hc:=P.encode_lt c
  have hbc := (P.product P).encode_lt (b,c)
  simp only [Presentation.product_encode,Presentation.product_bound] at hbc
  have hp : 0<P.bound := by omega
  change ((P.encode a*(P.bound*P.bound)+(P.encode b*P.bound+P.encode c))/(D.letters*D.letters)=_) ∧ _
  rw [h.letters,PrefixDescriptor.Data.join_div _ _ _ (Nat.mul_pos hp hp) hbc]
  refine ⟨rfl,?_,?_⟩
  · change ((P.encode a*(P.bound*P.bound)+(P.encode b*P.bound+P.encode c))/D.letters)%D.letters=_
    rw [h.letters]
    have he : P.encode a*(P.bound*P.bound)+(P.encode b*P.bound+P.encode c)=
        (P.encode a*P.bound+P.encode b)*P.bound+P.encode c := by ring
    rw [he,PrefixDescriptor.Data.join_div _ _ _ hp hc]
    exact PrefixDescriptor.Data.join_mod _ _ _ hb
  · change (P.encode a*(P.bound*P.bound)+(P.encode b*P.bound+P.encode c))%D.letters=_
    rw [h.letters]
    have he : P.encode a*(P.bound*P.bound)+(P.encode b*P.bound+P.encode c)=
        (P.encode a*P.bound+P.encode b)*P.bound+P.encode c := by ring
    rw [he,PrefixDescriptor.Data.join_mod _ _ _ hc]
 theorem kind_left (j : Fin d) (q : Option (Fin d)) :
    (kind d).encode ((Sum.inl (j,q)))=j.val*(1+D.bits)+(Presentation.fin d).option.encode q := by
  simp only [kind,Presentation.sum_inl,Presentation.product_encode,
    Presentation.option_bound,Presentation.fin_bound,Presentation.fin_encode,h.bits]
 theorem kind_center (j : Fin d) : (kind d).encode ((Sum.inr (Sum.inl j)))=D.leftEnd+j.val := by
  simp only [kind,Presentation.sum_inr,Presentation.sum_inl,
    Presentation.product_bound,Presentation.option_bound,Presentation.fin_bound,Presentation.fin_encode,Data.leftEnd,h.bits]
 theorem kind_right (j : Fin d) (q : Option (Fin d)) :
    (kind d).encode ((Sum.inr (Sum.inr (Sum.inl (j,q)))))=D.centerEnd+(j.val*(1+D.bits)+(Presentation.fin d).option.encode q) := by
  simp only [kind,Presentation.sum_inr,Presentation.sum_inl,Presentation.product_encode,
    Presentation.product_bound,Presentation.option_bound,Presentation.fin_bound,Presentation.fin_encode,Data.centerEnd,Data.leftEnd,h.bits]
  omega
 theorem kind_same (b : Bool) : (kind d).encode ((Sum.inr (Sum.inr (Sum.inr b))))=D.rightEnd+b.toNat := by
  simp only [kind,Presentation.sum_inr,Presentation.product_bound,Presentation.option_bound,
    Presentation.fin_bound,Presentation.boolean_encode,Data.rightEnd,Data.centerEnd,Data.leftEnd,h.bits]
  omega
 theorem left_lt (j : Fin d) (q : Option (Fin d)) : j.val*(1+D.bits)+(Presentation.fin d).option.encode q<D.leftEnd := by
  have hj:=j.isLt
  have hq: (Presentation.fin d).option.encode q<1+d := (Presentation.fin d).option.encode_lt q
  rw [Data.leftEnd,h.bits]
  nlinarith
 theorem left_parts (j : Fin d) (q : Option (Fin d)) :
    D.kindTime ((kind d).encode ((Sum.inl (j,q))))=j.val ∧
    D.kindPosition ((kind d).encode ((Sum.inl (j,q))))=(Presentation.fin d).option.encode q := by
  have hj:=left_lt P C marked ε h j q
  have hq : (Presentation.fin d).option.encode q<1+D.bits := by rw [h.bits]; exact (Presentation.fin d).option.encode_lt q
  rw [kind_left P C marked ε h,Data.kindTime,Data.kindPosition,ite_eq_left hj,ite_eq_left hj]
  exact ⟨PrefixDescriptor.Data.join_div _ _ _ (by omega) hq,PrefixDescriptor.Data.join_mod _ _ _ hq⟩
 theorem center_parts (j : Fin d) : D.kindTime ((kind d).encode ((Sum.inr (Sum.inl j))))=j.val := by
  rw [kind_center P C marked ε h,Data.kindTime,ite_eq_right (by omega),ite_eq_left (by have hj:=j.isLt; rw [Data.centerEnd]; rw [h.bits]; omega)]
  omega
 theorem right_parts (j : Fin d) (q : Option (Fin d)) :
    D.kindTime ((kind d).encode ((Sum.inr (Sum.inr (Sum.inl (j,q))))))=j.val ∧
    D.kindPosition ((kind d).encode ((Sum.inr (Sum.inr (Sum.inl (j,q))))))=(Presentation.fin d).option.encode q := by
  have hq : (Presentation.fin d).option.encode q<1+D.bits := by rw [h.bits]; exact (Presentation.fin d).option.encode_lt q
  have hle : D.leftEnd≤D.centerEnd := by unfold Data.centerEnd; omega
  rw [kind_right P C marked ε h,Data.kindTime,Data.kindPosition,ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),Nat.add_sub_cancel_left]
  exact ⟨PrefixDescriptor.Data.join_div _ _ _ (by omega) hq,PrefixDescriptor.Data.join_mod _ _ _ hq⟩
end VariableWL.CellularCatalog

namespace VariableWL.CellularCatalog.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
variable {n : ℕ}
 theorem bool_ite_nat (b : Bool) : (if b then 1 else 0)=b.toNat := by cases b <;> rfl
namespace Listing
variable (D : Listing n)
 theorem eval_up (v : Env n) (a : Word) : D.up.eval (cons a v)=D.eval v := by
  dsimp only [eval,up]
  congr 1
  · funext i j a; exact underThree_number ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_bit ..
 theorem leftEnd_number (v : Env n) : (D.leftEnd).number v=(D.eval v).leftEnd := by
  simp only [leftEnd,add_number,mul_number,numeral_number,eval,Data.leftEnd]
 theorem centerEnd_number (v : Env n) : (D.centerEnd).number v=(D.eval v).centerEnd := by
  simp only [centerEnd,leftEnd_number,add_number,eval,Data.centerEnd]
 theorem rightEnd_number (v : Env n) : (D.rightEnd).number v=(D.eval v).rightEnd := by
  simp only [rightEnd,leftEnd_number,centerEnd_number,add_number,eval,Data.rightEnd]
 theorem kinds_number (v : Env n) : (D.kinds).number v=(D.eval v).kinds := by
  simp only [kinds,rightEnd_number,add_number,numeral_number,eval,Data.kinds]
 theorem triples_number (v : Env n) : (D.triples).number v=(D.eval v).triples := by
  simp only [triples,mul_number,eval,Data.triples]
 theorem tripleCode_number (E : Expr n) (v : Env n) : (D.tripleCode E).number v=(D.eval v).tripleCode (E.number v) := by
  simp only [tripleCode,kinds_number,div_number,eval,Data.tripleCode]
 theorem kindCode_number (E : Expr n) (v : Env n) : (D.kindCode E).number v=(D.eval v).kindCode (E.number v) := by
  simp only [kindCode,kinds_number,mod_number,eval,Data.kindCode]
 theorem first_number (T : Expr n) (v : Env n) : (D.first T).number v=(D.eval v).first (T.number v) := by
  simp only [first,mul_number,div_number,eval,Data.first]
 theorem second_number (T : Expr n) (v : Env n) : (D.second T).number v=(D.eval v).second (T.number v) := by
  simp only [second,div_number,mod_number,eval,Data.second]
 theorem third_number (T : Expr n) (v : Env n) : (D.third T).number v=(D.eval v).third (T.number v) := by
  simp only [third,mod_number,eval,Data.third]
 theorem kindTime_number (K : Expr n) (v : Env n) : (D.kindTime K).number v=(D.eval v).kindTime (K.number v) := by
  simp only [kindTime,leftEnd_number,centerEnd_number,choose_number,add_number,sub_number,div_number,numeral_number,lt_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.kindTime] ; rfl
 theorem kindPosition_number (K : Expr n) (v : Env n) : (D.kindPosition K).number v=(D.eval v).kindPosition (K.number v) := by
  simp only [kindPosition,leftEnd_number,centerEnd_number,choose_number,add_number,sub_number,mod_number,numeral_number,lt_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.kindPosition] ; rfl
 theorem source_number (E : Expr n) (v : Env n) : (D.source E).number v=(D.eval v).source (E.number v) := by
  simp only [source,leftEnd_number,centerEnd_number,rightEnd_number,tripleCode_number,kindCode_number,first_number,second_number,third_number,choose_number,add_number,mul_number,sub_number,numeral_number,lt_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.source] ; rfl
 theorem destination_number (E : Expr n) (v : Env n) : (D.destination E).number v=(D.eval v).destination (E.number v) := by
  simp only [destination,centerEnd_number,rightEnd_number,tripleCode_number,kindCode_number,first_number,second_number,third_number,applyNat₃_number,choose_number,add_number,mul_number,numeral_number,lt_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.destination] ; rfl
 theorem destinationForm_number (E : Expr n) (v : Env n) : (D.destinationForm E).number v=(D.eval v).destinationForm (E.number v) := by
  simp only [destinationForm,leftEnd_number,rightEnd_number,kindCode_number,choose_number,add_number,numeral_number,lt_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.destinationForm] ; rfl
 theorem carryDomain_bit (B H I A : Expr n) (v : Env n) : (D.carryDomain B H I A).bit v=Data.carryDomain (B.number v) (H.number v) (I.number v) (A.number v) := by
  simp only [carryDomain,choose_bit,sub_number,numeral_number,eq_bit,lt_bit,BlockCatalog.Program.literal_true_bit,decide_eq_true_eq,decide_eq_true_eq,Data.carryDomain]
 theorem cyclicDomain_bit (B H I A : Expr n) (v : Env n) : (D.cyclicDomain B H I A).bit v=Data.cyclicDomain (B.number v) (H.number v) (I.number v) (A.number v) := by
  simp only [cyclicDomain,carryDomain_bit,choose_bit,sub_number,numeral_number,eq_bit,decide_eq_true_eq,decide_eq_true_eq,Data.cyclicDomain]
 theorem domain_bit (E I A : Expr n) (v : Env n) : (D.domain E I A).bit v=(D.eval v).domain (E.number v) (I.number v) (A.number v) := by
  simp only [domain,leftEnd_number,centerEnd_number,rightEnd_number,kindCode_number,kindTime_number,kindPosition_number,carryDomain_bit,cyclicDomain_bit,choose_bit,sub_number,numeral_number,lt_bit,BlockCatalog.Program.literal_true_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.domain] ; rfl
 theorem map_number (E I A : Expr n) (v : Env n) : (D.map E I A).number v=(D.eval v).map (E.number v) (I.number v) (A.number v) := by
  simp only [map,leftEnd_number,centerEnd_number,rightEnd_number,kindCode_number,kindTime_number,kindPosition_number,choose_number,sub_number,numeral_number,eq_bit,lt_bit,le_bit,disj_bit,decide_eq_true_eq,Bool.or_eq_true,decide_eq_true_eq,eval,Data.map] ; rfl
 theorem initialEnd_number (v : Env n) : (D.initialEnd).number v=(D.eval v).initialEnd := by
  simp only [initialEnd,add_number,numeral_number,eval,Data.initialEnd]
 theorem validRequest_bit (B : Expr n) (v : Env n) : (D.validRequest B).bit v=(D.eval v).validRequest (B.number v) := by
  simp only [validRequest,initialEnd_number,applyNat_bit,choose_bit,sub_number,numeral_number,eq_bit,lt_bit,neg_bit,binaryDigit_total,BlockCatalog.Program.literal_true_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.validRequest] ; rfl
 theorem requestGate_number (B : Expr n) (v : Env n) : (D.requestGate B).number v=(D.eval v).requestGate (B.number v) := by
  simp only [requestGate,initialEnd_number,applyNat_number,choose_number,sub_number,lt_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.requestGate] ; rfl
 theorem requestTest_number (B : Expr n) (v : Env n) : (D.requestTest B).number v=(D.eval v).requestTest (B.number v) := by
  simp only [requestTest,initialEnd_number,choose_number,numeral_number,lt_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.requestTest] ; rfl
 theorem requestPositionDomain_bit (B I A : Expr n) (v : Env n) : (D.requestPositionDomain B I A).bit v=(D.eval v).requestPositionDomain (B.number v) (I.number v) (A.number v) := by
  simp only [requestPositionDomain,initialEnd_number,choose_number,choose_bit,sub_number,numeral_number,eq_bit,lt_bit,disj_bit,binaryDigit_total,BlockCatalog.Program.literal_true_bit,decide_eq_true_eq,Bool.or_eq_true,decide_eq_true_eq,bool_ite_nat,eval,Data.requestPositionDomain] ; rfl
 theorem requestDomain_bit (B I A : Expr n) (v : Env n) : (D.requestDomain B I A).bit v=(D.eval v).requestDomain (B.number v) (I.number v) (A.number v) := by
  simp only [requestDomain,requestTest_number,requestPositionDomain_bit,choose_bit,sub_number,eq_bit,lt_bit,decide_eq_true_eq,decide_eq_true_eq,eval,Data.requestDomain] ; rfl
end Listing
end VariableWL.CellularCatalog.Program

namespace VariableWL.CellularCatalog
open Descriptor Circuit VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable2} {d m n : ℕ} (P : Presentation L) (C : ProductCellular.Data L d m)
variable (marked : Fin (d+d)) (ε : Bit) {D : Data} (h : Good (n := n) P C marked ε D)
include h
 theorem left_bounds (j : Fin d) (q : Option (Fin d)) :
    (kind d).encode ((Sum.inl (j,q)))<D.leftEnd ∧
    (kind d).encode ((Sum.inl (j,q)))<D.centerEnd ∧
    (kind d).encode ((Sum.inl (j,q)))<D.rightEnd := by
  have ha:=left_lt P C marked ε h j q
  rw [←kind_left P C marked ε h] at ha
  dsimp only [Data.centerEnd,Data.rightEnd]
  omega
 theorem center_bounds (j : Fin d) :
    D.leftEnd≤(kind d).encode ((Sum.inr (Sum.inl j))) ∧
    (kind d).encode ((Sum.inr (Sum.inl j)))<D.centerEnd ∧
    (kind d).encode ((Sum.inr (Sum.inl j)))<D.rightEnd := by
  rw [kind_center P C marked ε h]
  have hj:=j.isLt
  dsimp only [Data.centerEnd,Data.rightEnd]
  rw [h.bits]
  omega
 theorem right_bounds (j : Fin d) (q : Option (Fin d)) :
    D.leftEnd≤(kind d).encode ((Sum.inr (Sum.inr (Sum.inl (j,q))))) ∧
    D.centerEnd≤(kind d).encode ((Sum.inr (Sum.inr (Sum.inl (j,q))))) ∧
    (kind d).encode ((Sum.inr (Sum.inr (Sum.inl (j,q)))))<D.rightEnd := by
  rw [kind_right P C marked ε h]
  have ha:=left_lt P C marked ε h j q
  dsimp only [Data.rightEnd,Data.centerEnd]
  omega
 theorem same_bounds (b : Bool) :
    D.leftEnd≤(kind d).encode ((Sum.inr (Sum.inr (Sum.inr b)))) ∧
    D.centerEnd≤(kind d).encode ((Sum.inr (Sum.inr (Sum.inr b)))) ∧
    D.rightEnd≤(kind d).encode ((Sum.inr (Sum.inr (Sum.inr b)))) := by
  rw [kind_same P C marked ε h]
  dsimp only [Data.rightEnd,Data.centerEnd]
  omega
 theorem source_eq (e : ProductCellular.Edge L d) :
    D.source ((edge P).encode e)=(P.sum (ands P)).encode (ProductCellular.source e) := by
  rcases e with ⟨⟨a,b,c⟩,k⟩
  rw [Data.source,(edge_parts P C marked ε h ((a,b,c),k)).1,(edge_parts P C marked ε h ((a,b,c),k)).2]
  have ht:=triple_parts P C marked ε h a b c
  rcases k with ⟨j,q⟩ | j | ⟨j,q⟩ | v
  all_goals dsimp only
  · have hb:=left_bounds P C marked ε h j q
    rw [ite_eq_left hb.1,ht.1]; rfl
  · have hb:=center_bounds P C marked ε h j
    rw [ite_eq_right (by omega),ite_eq_left hb.2.1,ht.2.1]; rfl
  · have hb:=right_bounds P C marked ε h j q
    rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left hb.2.2,ht.2.2]; rfl
  · have hb:=same_bounds P C marked ε h v
    rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),kind_same P C marked ε h,Nat.add_sub_cancel_left,h.letters]
    rfl
 theorem destination_eq (e : ProductCellular.Edge L d) :
    D.destination ((edge P).encode e)=(P.sum (ands P)).encode (target L (Cellular.Triple L × Bool) (ProductCellular.destination C.rule e)) := by
  rcases e with ⟨⟨a,b,c⟩,k⟩
  rw [Data.destination,(edge_parts P C marked ε h ((a,b,c),k)).1,(edge_parts P C marked ε h ((a,b,c),k)).2]
  have ht:=triple_parts P C marked ε h a b c
  rcases k with ⟨j,q⟩ | j | ⟨j,q⟩ | v
  all_goals dsimp only
  · have hb:=left_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.1,h.letters]
    simp only [ProductCellular.destination,target,Presentation.sum_inr,ands,Presentation.product_encode,Presentation.boolean_bound,Presentation.boolean_encode,Bool.toNat_false,Nat.add_zero]
  · have hb:=center_bounds P C marked ε h j
    rw [ite_eq_left hb.2.1,h.letters]
    simp only [ProductCellular.destination,target,Presentation.sum_inr,ands,Presentation.product_encode,Presentation.boolean_bound,Presentation.boolean_encode,Bool.toNat_false,Nat.add_zero]
  · have hb:=right_bounds P C marked ε h j q
    rw [ite_eq_right (by omega),ite_eq_left (by omega),h.letters]
    rfl
  · have hb:=same_bounds P C marked ε h v
    rw [ite_eq_right (by omega),kind_same P C marked ε h]
    cases v
    · rw [Bool.toNat_false,Nat.add_zero,ite_eq_left (by omega),h.letters]; rfl
    · rw [Bool.toNat_true,ite_eq_right (by omega),ht.1,ht.2.1,ht.2.2,h.rule]; rfl
 theorem destinationForm_eq (e : ProductCellular.Edge L d) :
    D.destinationForm ((edge P).encode e)=AffineAlphabet.encodeForm
      (by cases ProductCellular.destination C.rule e <;> simp only [dimension] <;> decide)
      (inputLinear (ProductCellular.destination C.rule e)) := by
  rcases e with ⟨abc,k⟩
  rw [Data.destinationForm,(edge_parts P C marked ε h (abc,k)).2]
  rcases k with ⟨j,q⟩ | j | ⟨j,q⟩ | v
  all_goals dsimp only
  · have hb:=left_bounds P C marked ε h j q
    rw [ite_eq_left hb.1]; rfl
  · have hb:=center_bounds P C marked ε h j
    rw [ite_eq_right (by omega),ite_eq_left hb.2.2]; rfl
  · have hb:=right_bounds P C marked ε h j q
    rw [ite_eq_right (by omega),ite_eq_left hb.2.2]; rfl
  · have hb:=same_bounds P C marked ε h v
    rw [ite_eq_right (by omega),ite_eq_right (by omega),kind_same P C marked ε h]
    cases v
    · rw [Bool.toNat_false,Nat.add_zero,ite_eq_left (by omega)]; rfl
    · rw [Bool.toNat_true,ite_eq_right (by omega)]; rfl
end VariableWL.CellularCatalog

namespace VariableWL.CellularCatalog
open Descriptor Circuit VariableWL.Affine
attribute [local instance] Classical.propDecidable
 theorem bool_nat_eq (a b : Bool) : a.toNat=b.toNat ↔ a=b := by cases a <;> cases b <;> decide
 theorem carryDomain_eq {d : ℕ} (bit a : Bool) (h i : Fin d) :
    Data.carryDomain bit.toNat h.val i.val a.toNat=true ↔ a∈Binary.domain bit h i := by
  simp only [Data.carryDomain,Binary.domain,Fin.lt_def,Fin.ext_iff]
  split_ifs <;> cases bit <;> cases a <;> simp_all
 theorem cyclicDomain_eq {d : ℕ} (bit a : Bool) (q : Option (Fin d)) (i : Fin d) :
    Data.cyclicDomain bit.toNat ((Presentation.fin d).option.encode q) i.val a.toNat=true ↔ a∈Binary.cyclicDomain bit q i := by
  cases q with
  | none => simp only [Data.cyclicDomain,Presentation.option_none,ite_true,Binary.cyclicDomain,decide_eq_true_eq,Finset.mem_singleton,bool_nat_eq]
  | some j =>
    simp only [Data.cyclicDomain,Presentation.option_some,Presentation.fin_encode,
      ite_eq_right (show ¬1+j.val=0 by omega),show 1+j.val-1=j.val by omega,Binary.cyclicDomain]
    exact carryDomain_eq bit a j i
 theorem carryMap_eq {d : ℕ} (h i : Fin d) (a : Bool) :
    (if i.val≤h.val then 1-a.toNat else a.toNat)=(Binary.table h i a).toNat := by
  simp only [Binary.table,Fin.le_def]
  split_ifs <;> cases a <;> rfl
 theorem cyclicMap_eq {d : ℕ} (q : Option (Fin d)) (i : Fin d) (a : Bool) :
    (if (Presentation.fin d).option.encode q=0 ∨ i.val<(Presentation.fin d).option.encode q then 1-a.toNat else a.toNat)=
      (Binary.cyclicTable q i a).toNat := by
  cases q with
  | none => simp only [Presentation.option_none,true_or,ite_true,Binary.cyclicTable]; cases a <;> rfl
  | some j =>
    simp only [Presentation.option_some,Presentation.fin_encode,Binary.cyclicTable]
    simpa only [show (1+j.val=0 ∨ i.val<1+j.val) ↔ i.val≤j.val by omega] using carryMap_eq j i a
variable {L : Type uVariable3} {d m n : ℕ} (P : Presentation L) (C : ProductCellular.Data L d m)
variable (marked : Fin (d+d)) (ε : Bit) {D : Data} (h : Good (n := n) P C marked ε D)
include h
 theorem domain_time (e : ProductCellular.Edge L d) (i : Fin d) (a : Bool) :
    D.domain ((edge P).encode e) (i.castAdd d).val a.toNat=true ↔ a∈ProductCellular.timeDomain e.2 i := by
  rcases e with ⟨abc,k⟩
  rw [Data.domain,(edge_parts P C marked ε h (abc,k)).2]
  have hi : (i.castAdd d).val<D.bits := by simpa only [Fin.val_castAdd,h.bits] using i.isLt
  rcases k with ⟨j,q⟩ | j | ⟨j,q⟩ | v
  all_goals dsimp only
  · have hb:=left_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.2,ite_eq_left hi,(left_parts P C marked ε h j q).1]
    exact carryDomain_eq true a j i
  · have hb:=center_bounds P C marked ε h j
    rw [ite_eq_left hb.2.2,ite_eq_left hi,center_parts P C marked ε h j]
    exact carryDomain_eq true a j i
  · have hb:=right_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.2,ite_eq_left hi,(right_parts P C marked ε h j q).1]
    exact carryDomain_eq true a j i
  · have hb:=same_bounds P C marked ε h v
    rw [ite_eq_right (by omega)]; simp only [ProductCellular.timeDomain,Finset.mem_univ]
 theorem domain_position (e : ProductCellular.Edge L d) (i : Fin d) (a : Bool) :
    D.domain ((edge P).encode e) (Fin.natAdd d i).val a.toNat=true ↔ a∈ProductCellular.positionDomain e.2 i := by
  rcases e with ⟨abc,k⟩
  rw [Data.domain,(edge_parts P C marked ε h (abc,k)).2]
  have hi : ¬(Fin.natAdd d i).val<D.bits := by simp only [Fin.val_natAdd,h.bits]; omega
  have hs : (Fin.natAdd d i).val-D.bits=i.val := by simp only [Fin.val_natAdd,h.bits,Nat.add_sub_cancel_left]
  rcases k with ⟨j,q⟩ | j | ⟨j,q⟩ | v
  all_goals dsimp only
  · have hb:=left_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.2,ite_eq_right hi,ite_eq_left hb.1,(left_parts P C marked ε h j q).2,hs]
    exact cyclicDomain_eq true a q i
  · have hb:=center_bounds P C marked ε h j
    rw [ite_eq_left hb.2.2,ite_eq_right hi,ite_eq_right (by omega),ite_eq_left hb.2.1]
    simp only [ProductCellular.positionDomain,Finset.mem_univ]
  · have hb:=right_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.2,ite_eq_right hi,ite_eq_right (by omega),ite_eq_right (by omega),(right_parts P C marked ε h j q).2,hs]
    exact cyclicDomain_eq false a q i
  · have hb:=same_bounds P C marked ε h v
    rw [ite_eq_right (by omega)]; simp only [ProductCellular.positionDomain,Finset.mem_univ]
 theorem domain_eq (e : ProductCellular.Edge L d) (i : Fin (d+d)) (a : Bool) :
    D.domain ((edge P).encode e) i.val a.toNat=true ↔ a∈C.description.domain e i := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simpa only [ProductCellular.Data.description,ProductCellular.join_left] using domain_time P C marked ε h e j a
  · simpa only [ProductCellular.Data.description,ProductCellular.join_right] using domain_position P C marked ε h e j a
 theorem map_time (e : ProductCellular.Edge L d) (i : Fin d) (a : Bool) :
    D.map ((edge P).encode e) (i.castAdd d).val a.toNat=(ProductCellular.timeMap e.2 i a).toNat := by
  rcases e with ⟨abc,k⟩
  rw [Data.map,(edge_parts P C marked ε h (abc,k)).2]
  have hi : (i.castAdd d).val<D.bits := by simpa only [Fin.val_castAdd,h.bits] using i.isLt
  rcases k with ⟨j,q⟩ | j | ⟨j,q⟩ | v
  all_goals dsimp only
  · have hb:=left_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.2,ite_eq_left hi,(left_parts P C marked ε h j q).1]
    exact carryMap_eq j i a
  · have hb:=center_bounds P C marked ε h j
    rw [ite_eq_left hb.2.2,ite_eq_left hi,center_parts P C marked ε h j]
    exact carryMap_eq j i a
  · have hb:=right_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.2,ite_eq_left hi,(right_parts P C marked ε h j q).1]
    exact carryMap_eq j i a
  · have hb:=same_bounds P C marked ε h v
    rw [ite_eq_right (by omega)]; rfl
 theorem map_position (e : ProductCellular.Edge L d) (i : Fin d) (a : Bool) :
    D.map ((edge P).encode e) (Fin.natAdd d i).val a.toNat=(ProductCellular.positionMap e.2 i a).toNat := by
  rcases e with ⟨abc,k⟩
  rw [Data.map,(edge_parts P C marked ε h (abc,k)).2]
  have hi : ¬(Fin.natAdd d i).val<D.bits := by simp only [Fin.val_natAdd,h.bits]; omega
  have hs : (Fin.natAdd d i).val-D.bits=i.val := by simp only [Fin.val_natAdd,h.bits,Nat.add_sub_cancel_left]
  rcases k with ⟨j,q⟩ | j | ⟨j,q⟩ | v
  all_goals dsimp only
  · have hb:=left_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.2,ite_eq_right hi,ite_eq_left (Or.inl hb.1),(left_parts P C marked ε h j q).2,hs]
    exact cyclicMap_eq q i a
  · have hb:=center_bounds P C marked ε h j
    rw [ite_eq_left hb.2.2,ite_eq_right hi,ite_eq_right (by omega)]; rfl
  · have hb:=right_bounds P C marked ε h j q
    rw [ite_eq_left hb.2.2,ite_eq_right hi,ite_eq_left (Or.inr hb.2.1),(right_parts P C marked ε h j q).2,hs]
    exact cyclicMap_eq q i a
  · have hb:=same_bounds P C marked ε h v
    rw [ite_eq_right (by omega)]; rfl
 theorem map_eq (e : ProductCellular.Edge L d) (i : Fin (d+d)) (a : Bool) :
    D.map ((edge P).encode e) i.val a.toNat=(C.description.map e i a).toNat := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simpa only [ProductCellular.Data.description,ProductCellular.join_left] using map_time P C marked ε h e j a
  · simpa only [ProductCellular.Data.description,ProductCellular.join_right] using map_position P C marked ε h e j a
end VariableWL.CellularCatalog

namespace VariableWL.CellularCatalog
open Descriptor Circuit VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable4} {d m n : ℕ} (P : Presentation L) (C : ProductCellular.Data L d m)
variable (marked : Fin (d+d)) (ε : Bit) {D : Data} (h : Good (n := n) P C marked ε D)
include h
omit h in
 theorem request_first (j : Fin m) : (request P C).encode (.inl (.inl j))=j.val := rfl
omit h in
 theorem request_none : (request P C).encode (.inl (.inr none))=m := by
  simp only [request,Presentation.sum_inl,Presentation.sum_inr,Presentation.fin_bound,Presentation.option_none,Nat.add_zero]
omit h in
 theorem request_some (j : {i : Fin d // C.threshold i=false}) :
    (request P C).encode (.inl (.inr (some j)))=m+(1+j.val.val) := rfl
 theorem request_accepting (f : {a : L // a∈C.accepting}) :
    (request P C).encode (.inr f)=D.initialEnd+P.encode f.val := by
  simp only [request,Presentation.sum_inr,Presentation.sum_bound,Presentation.option_bound,
    Presentation.fin_bound,zeroBit,Presentation.filter_bound,accepting,Presentation.filter_encode,Data.initialEnd,h.bits,h.inputLength]
 theorem initialEnd_eq : D.initialEnd=m+(1+d) := by rw [Data.initialEnd,h.bits,h.inputLength]
 theorem request_gate (b : C.Request) : D.requestGate ((request P C).encode b)=P.encode (C.requestGate b) := by
  rcases b with (j|q)|f
  · rw [request_first P C,Data.requestGate,ite_eq_left (by rw [h.inputLength]; exact j.isLt),h.input]; rfl
  · cases q with
    | none => rw [request_none P C,Data.requestGate,h.inputLength,ite_eq_right (by omega),initialEnd_eq P C marked ε h,ite_eq_left (by omega),h.blank]; rfl
    | some j =>
      rw [request_some P C,Data.requestGate,h.inputLength,ite_eq_right (by omega),initialEnd_eq P C marked ε h,ite_eq_left (by have:=j.val.isLt; omega),h.blank]; rfl
  · rw [request_accepting P C marked ε h,Data.requestGate,ite_eq_right (by rw [initialEnd_eq P C marked ε h,h.inputLength]; omega),ite_eq_right (by omega),Nat.add_sub_cancel_left]; rfl
 theorem request_test (b : C.Request) : D.requestTest ((request P C).encode b)=(if C.requestTest b then 1 else 0) := by
  rcases b with (j|q)|f
  · rw [request_first P C,Data.requestTest,initialEnd_eq P C marked ε h,ite_eq_left (by have:=j.isLt; omega)]; rfl
  · cases q with
    | none => rw [request_none P C,Data.requestTest,initialEnd_eq P C marked ε h,ite_eq_left (by omega)]; rfl
    | some j => rw [request_some P C,Data.requestTest,initialEnd_eq P C marked ε h,ite_eq_left (by have:=j.val.isLt; omega)]; rfl
  · rw [request_accepting P C marked ε h,Data.requestTest,ite_eq_right (by omega)]; rfl
 theorem request_position (b : C.Request) (i : Fin d) (a : Bool) :
    D.requestPositionDomain ((request P C).encode b) i.val a.toNat=true ↔ a∈C.requestPositionDomain b i := by
  rcases b with (j|q)|f
  · rw [request_first P C,Data.requestPositionDomain,ite_eq_left (by rw [h.inputLength]; exact j.isLt),C.input_bit j i]
    simp only [decide_eq_true_eq,bool_nat_eq,ProductCellular.Data.requestPositionDomain,Finset.mem_singleton]
  · cases q with
    | none =>
      rw [request_none P C,Data.requestPositionDomain,h.inputLength,ite_eq_right (by omega),initialEnd_eq P C marked ε h,ite_eq_left (by omega),ite_eq_left (Or.inl rfl),C.threshold_bit i]
      simp only [decide_eq_true_eq,bool_nat_eq,ProductCellular.Data.requestPositionDomain,Binary.thresholdDomain,Finset.mem_singleton]
    | some j =>
      rw [request_some P C,Data.requestPositionDomain,h.inputLength,ite_eq_right (by omega),initialEnd_eq P C marked ε h,ite_eq_left (by have:=j.val.isLt; omega)]
      have hs : m+(1+j.val.val)-m-1=j.val.val := by omega
      simp only [hs,show (m+(1+j.val.val)=m ∨ j.val.val < i.val) ↔ j.val.val < i.val by omega]
      conv_lhs => rw [C.threshold_bit i]
      simp only [ProductCellular.Data.requestPositionDomain,Binary.thresholdDomain,Fin.lt_def,Fin.ext_iff]
      split_ifs <;> cases a <;> cases hi : C.threshold i <;> simp_all
  · rw [request_accepting P C marked ε h,Data.requestPositionDomain,
      ite_eq_right (by rw [initialEnd_eq P C marked ε h,h.inputLength]; omega),ite_eq_right (by omega)]
    simp only [ProductCellular.Data.requestPositionDomain,Finset.mem_univ]
 theorem request_domain (b : C.Request) (i : Fin (d+d)) (a : Bool) :
    D.requestDomain ((request P C).encode b) i.val a.toNat=true ↔ a∈C.description.requestDomain b i := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · rw [Data.requestDomain,ite_eq_left (by simpa only [h.bits,Fin.val_castAdd] using j.isLt),request_test P C marked ε h]
    simp only [ProductCellular.Data.description,ProductCellular.join_left]
    rcases b with (t|q)|f <;> cases a <;> simp only [ProductCellular.Data.requestTest,
      ProductCellular.Data.requestTimeDomain,Bool.false_eq_true,ite_false,ite_true,Bool.toNat_true,Bool.toNat_false,
      decide_true,Finset.mem_singleton] <;> decide
  · rw [Data.requestDomain,ite_eq_right (by simp only [h.bits,Fin.val_natAdd]; omega)]
    have hs : (Fin.natAdd d j).val-D.bits=j.val := by simp only [Fin.val_natAdd,h.bits,Nat.add_sub_cancel_left]
    rw [hs]
    simpa only [ProductCellular.Data.description,ProductCellular.join_right] using request_position P C marked ε h b j a
 theorem valid_request : D.validRequest=(request P C).valid := by
  funext b
  simp only [Data.validRequest,request,Presentation.sum_valid,Presentation.fin_valid,
    Presentation.fin_bound,Presentation.option_valid,Presentation.sum_bound,Presentation.option_bound,
    zeroBit,Presentation.filter_bound,Presentation.filter_valid,accepting,h.valid,Bool.true_and,
    h.inputLength,initialEnd_eq P C marked ε h,Presentation.fin_bound,h.accepting]
  by_cases hb : b < m
  · simp only [ite_eq_left hb,ite_eq_left (by omega : b < m+(1+d))]
  · rw [ite_eq_right hb]
    by_cases he : b=m
    · subst b; simp
    · by_cases hc : b < m+(1+d)
      · simp only [ite_eq_left hc,ite_eq_right he,ite_eq_right hb,ite_eq_right (by omega : ¬ b - m < 1)]
      · simp only [ite_eq_right hc,ite_eq_right he]
 theorem and_valid : (ands P).valid=fun _=>true := by
  funext i
  simp only [ands,triple,Presentation.product_valid,Presentation.boolean_valid,h.valid,Bool.true_and]
 theorem edge_valid : (edge (d := d) P).valid=fun _=>true := by
  funext i
  simp only [edge,triple,kind,Presentation.product_valid,Presentation.sum_valid,Presentation.option_valid,
    Presentation.fin_valid,Presentation.boolean_valid,h.valid,Bool.true_and,ite_self]
 theorem catalog_good : CircuitCatalog.Good (n := n) P (ands P) (edge P) (request P C) C.description marked ε D.catalog := by
  refine ⟨?_,h.internal,h.letters,?_,?_,?_,h.valid.symm,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,h.marked,h.epsilon⟩
  · change D.bits+D.bits=d+d; rw [h.bits]
  · change D.triples*2=(ands P).bound
    rw [triples_eq P C marked ε h]; rfl
  · change D.triples*D.kinds=(edge P).bound
    rw [triples_eq P C marked ε h,kinds_eq P C marked ε h]; rfl
  · change D.initialEnd+D.letters=(request P C).bound
    simp only [initialEnd_eq P C marked ε h,h.letters,request,Presentation.sum_bound,Presentation.option_bound,
      Presentation.fin_bound,zeroBit,Presentation.filter_bound,accepting]
  · exact (and_valid P C marked ε h).symm
  · exact (edge_valid P C marked ε h).symm
  · exact valid_request P C marked ε h
  · exact source_eq P C marked ε h
  · exact destination_eq P C marked ε h
  · exact destinationForm_eq P C marked ε h
  · exact domain_eq P C marked ε h
  · exact map_eq P C marked ε h
  · exact request_gate P C marked ε h
  · exact request_test P C marked ε h
  · exact request_domain P C marked ε h
end VariableWL.CellularCatalog

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_MachineCellular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.CircuitCatalog.Data
 theorem ext_fields {D E : Data}
    (h1 : D.rows=E.rows) (h2 : D.internal=E.internal) (h3 : D.scalars=E.scalars)
    (h4 : D.ands=E.ands) (h5 : D.edges=E.edges) (h6 : D.requests=E.requests)
    (h7 : D.validScalar=E.validScalar) (h8 : D.validAnd=E.validAnd) (h9 : D.validEdge=E.validEdge)
    (h10 : D.validRequest=E.validRequest) (h11 : D.source=E.source) (h12 : D.destination=E.destination)
    (h13 : D.destinationForm=E.destinationForm) (h14 : D.domain=E.domain) (h15 : D.map=E.map)
    (h16 : D.requestGate=E.requestGate) (h17 : D.requestTest=E.requestTest)
    (h18 : D.requestDomain=E.requestDomain) (h19 : D.marked=E.marked) (h20 : D.epsilon=E.epsilon) : D=E := by
  cases D; cases E; congr
end VariableWL.CircuitCatalog.Data
namespace VariableWL.CircuitCatalog.Program.Listing
open Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
theorem eval_validRequest {n : ℕ} (D : Listing n) (v : Env n) (i : ℕ) : (D.eval v).validRequest i=D.validRequest.bit (cons (List.replicate i true) v) := rfl
theorem eval_source {n : ℕ} (D : Listing n) (v : Env n) (i : ℕ) : (D.eval v).source i=D.source.number (cons (List.replicate i true) v) := rfl
theorem eval_destination {n : ℕ} (D : Listing n) (v : Env n) (i : ℕ) : (D.eval v).destination i=D.destination.number (cons (List.replicate i true) v) := rfl
theorem eval_destinationForm {n : ℕ} (D : Listing n) (v : Env n) (i : ℕ) : (D.eval v).destinationForm i=D.destinationForm.number (cons (List.replicate i true) v) := rfl
theorem eval_domain {n : ℕ} (D : Listing n) (v : Env n) (i j a : ℕ) : (D.eval v).domain i j a=D.domain.bit (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v))) := rfl
theorem eval_map {n : ℕ} (D : Listing n) (v : Env n) (i j a : ℕ) : (D.eval v).map i j a=D.map.number (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v))) := rfl
theorem eval_requestGate {n : ℕ} (D : Listing n) (v : Env n) (i : ℕ) : (D.eval v).requestGate i=D.requestGate.number (cons (List.replicate i true) v) := rfl
theorem eval_requestTest {n : ℕ} (D : Listing n) (v : Env n) (i : ℕ) : (D.eval v).requestTest i=D.requestTest.number (cons (List.replicate i true) v) := rfl
theorem eval_requestDomain {n : ℕ} (D : Listing n) (v : Env n) (i j a : ℕ) : (D.eval v).requestDomain i j a=D.requestDomain.bit (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v))) := rfl
end VariableWL.CircuitCatalog.Program.Listing
namespace VariableWL.CellularCatalog.Data
theorem catalog_validRequest_eq (D : Data) (i : ℕ) : D.catalog.validRequest i=D.validRequest i := rfl
theorem catalog_source_eq (D : Data) (i : ℕ) : D.catalog.source i=D.source i := rfl
theorem catalog_destination_eq (D : Data) (i : ℕ) : D.catalog.destination i=D.destination i := rfl
theorem catalog_destinationForm_eq (D : Data) (i : ℕ) : D.catalog.destinationForm i=D.destinationForm i := rfl
theorem catalog_domain_eq (D : Data) (i j a : ℕ) : D.catalog.domain i j a=D.domain i j a := rfl
theorem catalog_map_eq (D : Data) (i j a : ℕ) : D.catalog.map i j a=D.map i j a := rfl
theorem catalog_requestGate_eq (D : Data) (i : ℕ) : D.catalog.requestGate i=D.requestGate i := rfl
theorem catalog_requestTest_eq (D : Data) (i : ℕ) : D.catalog.requestTest i=D.requestTest i := rfl
theorem catalog_requestDomain_eq (D : Data) (i j a : ℕ) : D.catalog.requestDomain i j a=D.requestDomain i j a := rfl
end VariableWL.CellularCatalog.Data
namespace VariableWL.CellularCatalog.Program.Listing
open Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
variable {n : ℕ} (D : Listing n)
theorem catalog_validRequest_field : D.catalog.validRequest=D.up.validRequest (Computation.Stack.PolyRecipe.input 0) := rfl
theorem catalog_validRequest_eval (v : Env n) (i : ℕ) : (D.catalog.eval v).validRequest i=(D.eval v).catalog.validRequest i := by
  rw [CircuitCatalog.Program.Listing.eval_validRequest,catalog_validRequest_field,Data.catalog_validRequest_eq,validRequest_bit,eval_up]
  simp only [input_number,cons_zero,List.length_replicate]
theorem catalog_source_field : D.catalog.source=D.up.source (Computation.Stack.PolyRecipe.input 0) := rfl
theorem catalog_source_eval (v : Env n) (i : ℕ) : (D.catalog.eval v).source i=(D.eval v).catalog.source i := by
  rw [CircuitCatalog.Program.Listing.eval_source,catalog_source_field,Data.catalog_source_eq,source_number,eval_up]
  simp only [input_number,cons_zero,List.length_replicate]
theorem catalog_destination_field : D.catalog.destination=D.up.destination (Computation.Stack.PolyRecipe.input 0) := rfl
theorem catalog_destination_eval (v : Env n) (i : ℕ) : (D.catalog.eval v).destination i=(D.eval v).catalog.destination i := by
  rw [CircuitCatalog.Program.Listing.eval_destination,catalog_destination_field,Data.catalog_destination_eq,destination_number,eval_up]
  simp only [input_number,cons_zero,List.length_replicate]
theorem catalog_destinationForm_field : D.catalog.destinationForm=D.up.destinationForm (Computation.Stack.PolyRecipe.input 0) := rfl
theorem catalog_destinationForm_eval (v : Env n) (i : ℕ) : (D.catalog.eval v).destinationForm i=(D.eval v).catalog.destinationForm i := by
  rw [CircuitCatalog.Program.Listing.eval_destinationForm,catalog_destinationForm_field,Data.catalog_destinationForm_eq,destinationForm_number,eval_up]
  simp only [input_number,cons_zero,List.length_replicate]
theorem catalog_domain_field : D.catalog.domain=D.up.up.up.domain (Computation.Stack.PolyRecipe.input 0) (Computation.Stack.PolyRecipe.input 1) (Computation.Stack.PolyRecipe.input 2) := rfl
theorem catalog_domain_eval (v : Env n) (i j a : ℕ) : (D.catalog.eval v).domain i j a=(D.eval v).catalog.domain i j a := by
  rw [CircuitCatalog.Program.Listing.eval_domain,catalog_domain_field,Data.catalog_domain_eq,domain_bit,eval_up,eval_up,eval_up]
  simp only [input_number,cons_zero,cons_one,cons_two,List.length_replicate]
theorem catalog_map_field : D.catalog.map=D.up.up.up.map (Computation.Stack.PolyRecipe.input 0) (Computation.Stack.PolyRecipe.input 1) (Computation.Stack.PolyRecipe.input 2) := rfl
theorem catalog_map_eval (v : Env n) (i j a : ℕ) : (D.catalog.eval v).map i j a=(D.eval v).catalog.map i j a := by
  rw [CircuitCatalog.Program.Listing.eval_map,catalog_map_field,Data.catalog_map_eq,map_number,eval_up,eval_up,eval_up]
  simp only [input_number,cons_zero,cons_one,cons_two,List.length_replicate]
theorem catalog_requestGate_field : D.catalog.requestGate=D.up.requestGate (Computation.Stack.PolyRecipe.input 0) := rfl
theorem catalog_requestGate_eval (v : Env n) (i : ℕ) : (D.catalog.eval v).requestGate i=(D.eval v).catalog.requestGate i := by
  rw [CircuitCatalog.Program.Listing.eval_requestGate,catalog_requestGate_field,Data.catalog_requestGate_eq,requestGate_number,eval_up]
  simp only [input_number,cons_zero,List.length_replicate]
theorem catalog_requestTest_field : D.catalog.requestTest=D.up.requestTest (Computation.Stack.PolyRecipe.input 0) := rfl
theorem catalog_requestTest_eval (v : Env n) (i : ℕ) : (D.catalog.eval v).requestTest i=(D.eval v).catalog.requestTest i := by
  rw [CircuitCatalog.Program.Listing.eval_requestTest,catalog_requestTest_field,Data.catalog_requestTest_eq,requestTest_number,eval_up]
  simp only [input_number,cons_zero,List.length_replicate]
theorem catalog_requestDomain_field : D.catalog.requestDomain=D.up.up.up.requestDomain (Computation.Stack.PolyRecipe.input 0) (Computation.Stack.PolyRecipe.input 1) (Computation.Stack.PolyRecipe.input 2) := rfl
theorem catalog_requestDomain_eval (v : Env n) (i j a : ℕ) : (D.catalog.eval v).requestDomain i j a=(D.eval v).catalog.requestDomain i j a := by
  rw [CircuitCatalog.Program.Listing.eval_requestDomain,catalog_requestDomain_field,Data.catalog_requestDomain_eq,requestDomain_bit,eval_up,eval_up,eval_up]
  simp only [input_number,cons_zero,cons_one,cons_two,List.length_replicate]
 theorem catalog_eval (v : Env n) : D.catalog.eval v=(D.eval v).catalog := by
  apply CircuitCatalog.Data.ext_fields
  · exact add_number D.bits D.bits v
  · rfl
  · rfl
  · change (mul D.triples (numeral 2)).number v=(D.eval v).triples*2
    rw [mul_number,triples_number,numeral_number]
  · change (mul D.triples D.kinds).number v=(D.eval v).triples*(D.eval v).kinds
    rw [mul_number,triples_number,kinds_number]
  · change (add D.initialEnd D.letters).number v=(D.eval v).initialEnd+(D.eval v).letters
    rw [add_number,initialEnd_number]; rfl
  · funext i; rfl
  · funext i; rfl
  · funext i; rfl
  · funext i; exact catalog_validRequest_eval D v i
  · funext i; exact catalog_source_eval D v i
  · funext i; exact catalog_destination_eval D v i
  · funext i; exact catalog_destinationForm_eval D v i
  · funext i j a; exact catalog_domain_eval D v i j a
  · funext i j a; exact catalog_map_eval D v i j a
  · funext i; exact catalog_requestGate_eval D v i
  · funext i; exact catalog_requestTest_eval D v i
  · funext i j a; exact catalog_requestDomain_eval D v i j a
  · rfl
  · rfl
end VariableWL.CellularCatalog.Program.Listing

namespace VariableWL.MachineCellular
open MachineOneHead MachineReduction Descriptor Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
attribute [local instance] Classical.propDecidable
variable (M : Machine)
 theorem input_eq (w : Word) : MachineOneHead.input M w=initial M w.reverse := by
  simp only [MachineOneHead.input,Turing.TM2to1.trInit,←List.map_reverse]
  cases w.reverse with
  | nil => rfl
  | cons b bs =>
    change alpha M true b :: ((bs.map (MultiStack.inputSymbol M)).map (fun a => (false,Function.update (fun _ : MultiStack.Slot M=>none) (0,true) (some a)))) = alpha M true b :: bs.map (alpha M false)
    apply congrArg (List.cons (alpha M true b))
    induction bs with
    | nil => rfl
    | cons a bs ih => exact congrArg (List.cons (alpha M false a)) ih
 theorem initial_length (v : Word) : (initial M v).length=1+(v.length-1) := by
  cases v with
  | nil => rfl
  | cons b bs =>
    change (bs.map (alpha M false)).length+1=1+((bs.length+1)-1)
    rw [List.length_map]; omega
 theorem letterInput_eq (v : Word) (j : Fin (initial M v).length) :
    letterInput M v j.val=OneHead.markedInput (oneHead M) (fun i : Fin (initial M v).length => (initial M v)[i]) j := by
  rcases j with ⟨j,hj⟩
  cases v with
  | nil =>
    have he : j=0 := by change j<1 at hj; omega
    subst j
    rfl
  | cons b bs =>
    cases j with
    | zero => rfl
    | succ j =>
      have hj' : j<bs.length := by simpa only [initial,List.length_cons,List.length_map,Nat.succ_lt_succ_iff] using hj
      simp only [letterInput,Nat.succ_ne_zero,ite_false,List.getD_cons_succ,
        List.getD_eq_getElem _ _ hj',tailLetter,OneHead.markedInput,initial,Fin.getElem_fin,List.getElem_cons_succ,List.getElem_map]
 theorem letterInput_original (w : Word) (j : Fin (MachineOneHead.input M w).length) :
    letterInput M w.reverse j.val=OneHead.markedInput (oneHead M) (fun i : Fin (MachineOneHead.input M w).length => (MachineOneHead.input M w)[i]) j := by
  have h:=letterInput_eq M w.reverse ⟨j.val,by rw [←input_eq]; exact j.isLt⟩
  simp only [OneHead.markedInput,Fin.getElem_fin] at h ⊢
  simpa only [input_eq] using h
 theorem cons_one_env1 (a : Word) (v : Env 1) : cons a v (1 : Fin 2)=v 0 := rfl
 theorem inputProgram_number (v : Env 1) (j : ℕ) :
    (inputProgram M).number (cons (List.replicate j true) v)=(presentation M).encode (letterInput M (v 0) j) := by
  simp only [inputProgram,NumericProgram.choose_number,eq_bit,input_number,numeral_number,
    cons_zero,cons_one_env1,List.length_replicate,lookup_bit,Computation.Stack.PolyRecipe.input_value,letterInput,decide_eq_true_eq]
  split_ifs <;> cases hb : (v 0).getD j false <;> simp_all

 theorem fixedPower_number {n : ℕ} (X : Expr n) (k : ℕ) (v : Env n) :
    (fixedPower X k).number v=(X.number v)^k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [fixedPower,mul_number,ih,pow_succ]
 theorem bitProgram_number (c d : ℕ) (v : Env 1) :
    (bitProgram M c d).number v=addressBits M c d (v 0).length := by
  simp only [bitProgram,add_number,mul_number,numeral_number,fixedPower_number,input_number,
    addressBits,simulationExponent,inputExponent]
end VariableWL.MachineCellular

namespace VariableWL.MachineCellular
open MachineOneHead MachineReduction Descriptor Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
attribute [local instance] Classical.propDecidable
variable (M : Machine)
 theorem presentation_valid : (presentation M).valid=fun _=>true := rfl
 theorem ruleCode_encode (a b c : Letter M) :
    ruleCode M ((presentation M).encode a) ((presentation M).encode b) ((presentation M).encode c)=
      (presentation M).encode ((oneHead M).rule a b c) := by
  rw [ruleCode,dite_eq_left ((presentation M).encode_lt a),dite_eq_left ((presentation M).encode_lt b),
    dite_eq_left ((presentation M).encode_lt c)]
  change (presentation M).encode ((oneHead M).rule ((Fintype.equivFin (Letter M)).symm (Fintype.equivFin (Letter M) a)) ((Fintype.equivFin (Letter M)).symm (Fintype.equivFin (Letter M) b)) ((Fintype.equivFin (Letter M)).symm (Fintype.equivFin (Letter M) c)))=_
  simp only [Equiv.symm_apply_apply]
 theorem ruleProgram_number (v : Env 1) (a b c : Letter M) :
    (ruleProgram M).number (cons (List.replicate ((presentation M).encode a) true)
      (cons (List.replicate ((presentation M).encode b) true) (cons (List.replicate ((presentation M).encode c) true) v)))=
    (presentation M).encode ((oneHead M).rule a b c) := by
  rw [ruleProgram,table₃_number]
  simp only [input_number,cons_zero,cons_one,cons_two,List.length_replicate]
  rw [ite_eq_left ⟨(presentation M).encode_lt a,(presentation M).encode_lt b,(presentation M).encode_lt c⟩,
    ruleCode_encode]
 theorem acceptProgram_bit (v : Env 1) (j : ℕ) :
    (acceptProgram M).bit (cons (List.replicate j true) v)=acceptCode M j := by
  rw [acceptProgram,Computation.Stack.PolyRecipe.choose_bit,lt_bit,input_number,cons_zero,List.length_replicate,numeral_number]
  by_cases hj : j<(presentation M).bound
  · rw [ite_eq_left (by simpa using hj),fixedBool_bit _ _ _ _ (by simpa only [input_number,cons_zero,List.length_replicate] using hj)]
    apply congrArg (acceptCode M)
    simp only [input_number,cons_zero,List.length_replicate]
  · rw [ite_eq_right (by simpa using hj)]
    have he : ¬∃f,(presentation M).encode f=j ∧ (oneHead M).acceptingCell f := by
      rintro ⟨f,hf,_⟩
      exact hj (hf ▸ (presentation M).encode_lt f)
    change false=decide _
    exact (decide_eq_false he).symm
 theorem circuit_rule (c d : ℕ) (w : Word) : (MachineReduction.circuit M c d w).rule=(oneHead M).rule := rfl
 theorem circuit_input (c d : ℕ) (w : Word) (j : Fin (MachineOneHead.input M w).length) :
    (MachineReduction.circuit M c d w).input j=OneHead.markedInput (oneHead M) (fun i : Fin (MachineOneHead.input M w).length => (MachineOneHead.input M w)[i]) j := rfl
 theorem circuit_blank (c d : ℕ) (w : Word) : (MachineReduction.circuit M c d w).blank=(default,none) := rfl
 theorem circuit_accepting (c d : ℕ) (w : Word) (f : Letter M) :
    f∈(MachineReduction.circuit M c d w).accepting ↔ (oneHead M).acceptingCell f := Iff.rfl
 theorem listing_good (c d : ℕ) (w : Word) (ε : Affine.Bit) :
    CellularCatalog.Good (n := MachineReduction.internal M c d w) (presentation M)
      (MachineReduction.circuit M c d w) (MachineReduction.marked M c d w) ε
      ((listing M c d ε).eval (fun _=>w.reverse)) := by
  refine ⟨?_,?_,?_,presentation_valid M,?_,?_,?_,?_,?_,?_,?_⟩
  · change (bitProgram M c d).number (fun _=>w.reverse)=MachineReduction.bits M c d w
    rw [bitProgram_number,List.length_reverse]; rfl
  · change (add (numeral 1) (sub (input 0) (numeral 1))).number (fun _=>w.reverse)=(MachineOneHead.input M w).length
    rw [add_number,numeral_number,sub_number,input_number,numeral_number,input_eq,initial_length]
  · exact numeral_number _ _
  · change (mul (numeral 4) (add (add (bitProgram M c d) (bitProgram M c d)) (numeral 1))).number (fun _=>w.reverse)=_
    simp only [mul_number,numeral_number,add_number,bitProgram_number,List.length_reverse,
      MachineReduction.internal,MachineReduction.dimension,MachineReduction.bits]
  · intro a b z
    rw [circuit_rule]
    exact ruleProgram_number M (fun _=>w.reverse) a b z
  · intro j
    change (inputProgram M).number (cons (List.replicate j.val true) (fun _=>w.reverse))=_
    rw [inputProgram_number,letterInput_original,circuit_input]
  · rw [circuit_blank]
    exact numeral_number _ _
  · intro i
    change (acceptProgram M).bit (cons (List.replicate i true) (fun _=>w.reverse))=_
    rw [acceptProgram_bit]
    simp only [acceptCode,circuit_accepting]
  · exact numeral_number _ _
  · exact numeral_number _ _
end VariableWL.MachineCellular

namespace VariableWL
 theorem equivalent_iso_iff {G H G' H' : Graph} (e : G.graph ≃g G'.graph)
    (f : H.graph ≃g H'.graph) (k : ℕ) : Equivalent G H k ↔ Equivalent G' H' k := by
  constructor
  · intro h s
    exact (histogram_iso e k s).trans ((h s).trans (histogram_iso f k s).symm)
  · intro h s
    exact (histogram_iso e k s).symm.trans ((h s).trans (histogram_iso f k s))
 theorem order_eq_of_iso {G H : Graph} (e : G.graph ≃g H.graph) : G.order=H.order := by
  simpa only [Fintype.card_fin] using Fintype.card_congr e.toEquiv
 theorem subcubic_iso_iff {G H : Graph} (e : G.graph ≃g H.graph) : Subcubic G ↔ Subcubic H := by
  classical
  constructor
  · intro h v
    obtain ⟨u,rfl⟩ := e.surjective v
    rw [e.degree_eq u]
    exact h u
  · intro h v
    rw [←e.degree_eq v]
    exact h (e v)
end VariableWL

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Completeness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2

namespace VariableWL.AffineCatalog
open Blocks BlockCoordinates Descriptor VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} [Fintype P] [Fintype E]
variable (PP : Presentation P) (PE : Presentation E) (J : ProductImages.Instance r P E)
variable (hr : 2≤r) (hn : 0<n) (marked : Fin r) {D : Data} {ε₀ : Bit}
variable (h : Good (n := n) PP PE J marked ε₀ D)
include hr hn h in
 theorem compiler_correct [Nonempty P] (hr3 : 3≤r) (hlarge : r+1<n+1) :
    ∃h0 : (D.descriptor 0).Sound,∃h1 : (D.descriptor 1).Sound,
      let G := (D.descriptor 0).graph h0
      let H := (D.descriptor 1).graph h1
      0<G.order ∧ G.order=H.order ∧ G.graph.Connected ∧ H.graph.Connected ∧
        VariableWL.Subcubic G ∧ VariableWL.Subcubic H ∧ (Equivalent G H r ↔ J.Consistent) := by
  let : ∀b : Block (n := n) J,FiniteNumbering (Proper J b) := properNumbering PP PE J hr hn marked h
  let : FiniteNumbering (Block (n := n) J) := (blockPresentation PP PE J marked h).numbering
  let : FiniteNumbering (PrefixParts.Wiring.SortTag (data J hr hn marked)) := (sortPresentation PP PE J hr hn marked h).numbering
  have hsound := descriptor_sound PP PE J hr hn marked h
  let iso := descriptor_iso PP PE J hr hn marked h
  refine ⟨hsound 0,hsound 1,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [order_eq_of_iso (iso 0)]
    exact Subcubic.positive_order J hr hn marked 0
  · rw [order_eq_of_iso (iso 0),order_eq_of_iso (iso 1)]
    exact Subcubic.equal_order J hr hn marked
  · exact (iso 0).connected_iff.mpr (Subcubic.connected J hr hn marked 0)
  · exact (iso 1).connected_iff.mpr (Subcubic.connected J hr hn marked 1)
  · exact (subcubic_iso_iff (iso 0)).mpr (Subcubic.degree_le_three J hr hn marked 0)
  · exact (subcubic_iso_iff (iso 1)).mpr (Subcubic.degree_le_three J hr hn marked 1)
  · exact (equivalent_iso_iff (iso 0) (iso 1) r).trans
      (Subcubic.equivalent_iff_consistent J hr hn marked hr3 hlarge)
end VariableWL.AffineCatalog

namespace VariableWL.AffineCatalog.Program.Listing
open Computation.Stack.PolyRecipe
variable {n : ℕ} (D : Listing n)
 theorem graph_eval (v : Computation.Stack.Recipe.Env n) :
    D.graph.eval v=(D.eval v).core.toPrefix.portData.expanded := by
  rw [graph,PortListing.expanded_eval,PrefixDescriptor.Program.Listing.portListing_eval,
    BlockDescriptor.Program.Listing.prefix_eval,core_eval]
end VariableWL.AffineCatalog.Program.Listing
namespace VariableWL.CellularCatalog.Program.Listing
open Computation.Stack.PolyRecipe
variable {n : ℕ} (D : Listing n)
 theorem graph_eval (v : Computation.Stack.Recipe.Env n) :
    D.graph.eval v=(D.eval v).catalog.affine.core.toPrefix.portData.expanded := by
  rw [graph,AffineCatalog.Program.Listing.graph_eval,CircuitCatalog.Program.Listing.affine_eval,catalog_eval]
end VariableWL.CellularCatalog.Program.Listing
namespace VariableWL.CellularCatalog.Data
 theorem ext_fields {D E : Data}
    (h1 : D.bits=E.bits) (h2 : D.inputLength=E.inputLength) (h3 : D.letters=E.letters)
    (h4 : D.internal=E.internal) (h5 : D.rule=E.rule) (h6 : D.input=E.input)
    (h7 : D.blank=E.blank) (h8 : D.accepting=E.accepting) (h9 : D.marked=E.marked)
    (h10 : D.epsilon=E.epsilon) : D=E := by
  cases D; cases E; congr
 theorem resign_affine (D : Data) (ε : Affine.Bit) :
    (D.resign ε).catalog.affine=D.catalog.affine.resign ε := rfl
end VariableWL.CellularCatalog.Data
namespace VariableWL.MachineCellular
open Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
variable (M : Machine) (c d : ℕ)
 theorem listing_eval_resign (v : Env 1) (ε : Affine.Bit) :
    (listing M c d ε).eval v=((listing M c d 0).eval v).resign ε := by
  apply CellularCatalog.Data.ext_fields <;> try rfl
  exact numeral_number _ _
 theorem graphListing_eval (v : Env 1) (ε : Affine.Bit) :
    (graphListing M c d ε).eval v=(base M c d v).descriptor ε := by
  rw [graphListing,CellularCatalog.Program.Listing.graph_eval,listing_eval_resign,
    CellularCatalog.Data.resign_affine]
  rfl
end VariableWL.MachineCellular

namespace VariableWL.MachineCellular
open Descriptor Computation.Stack.PolyRecipe Computation.Stack.Recipe
attribute [local instance] Classical.propDecidable
variable (M : Machine) (c d : ℕ)
 theorem base_good (w : Word) :
    AffineCatalog.Good (n := MachineReduction.internal M c d w)
      (realPresentation M c d w) (comparisonPresentation M c d w)
      (MachineReduction.imageInstance M c d w) (MachineReduction.marked M c d w) 0
      (base M c d (fun _=>w.reverse)) := by
  have hC := CellularCatalog.catalog_good (presentation M) (MachineReduction.circuit M c d w)
    (MachineReduction.marked M c d w) 0 (listing_good M c d w 0)
  exact CircuitCatalog.affine_good (presentation M) (CellularCatalog.ands (presentation M))
    (CellularCatalog.edge (d := MachineReduction.bits M c d w) (presentation M))
    (CellularCatalog.request (presentation M) (MachineReduction.circuit M c d w))
    (MachineReduction.circuit M c d w).description (MachineReduction.marked M c d w) 0 hC
 theorem compiled_correct (w : Word) :
    ∃h0 : ((graphListing M c d 0).eval (fun _=>w.reverse)).Sound,
    ∃h1 : ((graphListing M c d 1).eval (fun _=>w.reverse)).Sound,
      let G := ((graphListing M c d 0).eval (fun _=>w.reverse)).graph h0
      let H := ((graphListing M c d 1).eval (fun _=>w.reverse)).graph h1
      0<G.order ∧ G.order=H.order ∧ G.graph.Connected ∧ H.graph.Connected ∧
        VariableWL.Subcubic G ∧ VariableWL.Subcubic H ∧
        (Equivalent G H (MachineReduction.dimension M c d w) ↔ (MachineReduction.imageInstance M c d w).Consistent) := by
  have hr := MachineReduction.dimension_large M c d w
  have h := AffineCatalog.compiler_correct (realPresentation M c d w) (comparisonPresentation M c d w)
    (MachineReduction.imageInstance M c d w) (by omega) (MachineReduction.internal_pos M c d w)
    (MachineReduction.marked M c d w) (base_good M c d w) (by omega) (MachineReduction.enough_links M c d w)
  rw [graphListing_eval M c d (fun _=>w.reverse) 0,graphListing_eval M c d (fun _=>w.reverse) 1]
  exact h
 theorem dimensionProgram_number (w : Word) :
    (dimensionProgram M c d).number (fun _=>w.reverse)=MachineReduction.dimension M c d w := by
  rw [dimensionProgram,add_number,bitProgram_number,List.length_reverse]
  rfl
 theorem pairProgram_value (w : Word)
    (h0 : ((graphListing M c d 0).eval (fun _=>w.reverse)).Sound)
    (h1 : ((graphListing M c d 1).eval (fun _=>w.reverse)).Sound) :
    (pairProgram M c d).value (fun _=>w.reverse)=
      pairCode (((graphListing M c d 0).eval (fun _=>w.reverse)).graph h0)
        (((graphListing M c d 1).eval (fun _=>w.reverse)).graph h1) (MachineReduction.dimension M c d w) := by
  rw [pairProgram,append_value,append_value,GraphListing.code_correct _ _ h0,
    GraphListing.code_correct _ _ h1,integerEncode_value,dimensionProgram_number]
  exact (List.append_assoc _ _ _).symm
 theorem reduction_correct (w : Word) (b : Bool)
    (h : OutputsWithin M w [b] (2^(c*(w.length+1)^d))) :
    ((pairProgram M c d).value (fun _=>w.reverse)∈WL ↔ b=true) ∧
    ((pairProgram M c d).value (fun _=>w.reverse)∈SubWL ↔ b=true) := by
  obtain ⟨h0,h1,hpos,horder,hconn0,hconn1,hdeg0,hdeg1,heq⟩ := compiled_correct M c d w
  have hd := MachineReduction.dimension_large M c d w
  have hr : 2≤MachineReduction.dimension M c d w := by omega
  have hc := MachineReduction.consistent_iff_output M c d w b h
  rw [pairProgram_value M c d w h0 h1,Encoding.pair_mem_WL,Encoding.pair_mem_SubWL]
  constructor
  · exact (and_iff_right hr).trans (heq.trans hc)
  · constructor
    · intro hp
      exact (heq.trans hc).mp hp.2.2.2.2.2.2.2
    · intro hb
      exact ⟨hr,hpos,horder,hconn0,hconn1,hdeg0,hdeg1,(heq.trans hc).mpr hb⟩
end VariableWL.MachineCellular
namespace VariableWL
 theorem general_hard_oai : ∀R : Language, InEXPTIME R → PolytimeReduces R WL := by
  rintro R ⟨M,c,d,hM⟩
  apply Computation.Stack.PolyRecipe.reduces (MachineCellular.pairProgram M c d) R WL
  intro w
  obtain ⟨b,hb,ho⟩ := hM w
  exact hb.symm.trans (MachineCellular.reduction_correct M c d w b ho).1.symm
end VariableWL

end OAI
end

theorem solution : type_of% @OAI.VariableWL.general_hard_oai := @OAI.VariableWL.general_hard_oai
