-- Prove2me | solution 1 for StabilityDichotomies.Solvability.sparse_large_diameter_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:06:29.13417+00:00
-- url     : https://prove2.me/submissions/1c3c2294-5741-4ea2-87a0-1e098af31df5

import Mathlib
import Definitions.Def_StabilityDichotomies_Solvability_Incidence
import Definitions.Def_StabilityDichotomies_Solvability_Model
import Definitions.Def_StabilityDichotomies_Solvability_FiniteDuality
import Definitions.Def_StabilityDichotomies_Solvability_LinksSquares
import Theorems.Thm_StabilityDichotomies_Solvability_links_squares_properties

section
set_option autoImplicit false

namespace StabilityDichotomies.Dev.Disagree

open StabilityDichotomies.Solvability
open scoped Classical

variable {Γ : Language} {V : Type}

lemma nodup_of_minUnsat (I : Instance Γ V) (hI : MinimallyUnsatisfiable I) :
    I.constraints.Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  by_contra h
  push_neg at h
  have ha : a ∈ I.constraints := Multiset.count_pos.mp (by omega)
  obtain ⟨z, hz⟩ := hI.2 a ha
  apply hI.1
  refine ⟨z, ?_⟩
  intro d hd
  by_cases hda : d = a
  · subst hda
    apply hz
    show d ∈ I.constraints.erase d
    rw [← Multiset.count_pos, Multiset.count_erase_self]; omega
  · exact hz d ((Multiset.mem_erase_of_ne hda).2 hd)

lemma occ_mem (I : Instance Γ V) (e : Occurrence I) :
    occurrenceConstraint I e ∈ I.constraints :=
  Multiset.mem_toList.mp (List.get_mem _ _)

lemma occ_surj (I : Instance Γ V) {d : Constraint Γ V} (hd : d ∈ I.constraints) :
    ∃ e : Occurrence I, occurrenceConstraint I e = d :=
  List.mem_iff_get.mp (Multiset.mem_toList.mpr hd)

lemma occ_inj (I : Instance Γ V) (hI : MinimallyUnsatisfiable I) :
    Function.Injective (occurrenceConstraint I) := by
  have h1 : I.constraints.toList.Nodup := by
    have := nodup_of_minUnsat I hI
    rw [← Multiset.coe_toList I.constraints] at this
    exact Multiset.coe_nodup.mp this
  exact List.nodup_iff_injective_get.mp h1

lemma mem_delete_iff (I : Instance Γ V) (hI : MinimallyUnsatisfiable I)
    (e f : Occurrence I) (d : Constraint Γ V) (hd : d ∈ I.constraints) (hef : e ≠ f)
    (hde : d = occurrenceConstraint I e) :
    d ∈ (I.delete (occurrenceConstraint I f)).constraints := by
  show d ∈ I.constraints.erase _
  apply (Multiset.mem_erase_of_ne _).2 hd
  rw [hde]; exact fun h => hef (occ_inj I hI h)

/-- reachability from `c` along walks whose variable nodes are in disagreement -/
def Reach (I : Instance Γ V) (x y : V → Bool) (c : Occurrence I) (u : IncidenceVertex I) : Prop :=
  ∃ p : (incidenceGraph I).Walk (.inr c) u, ∀ v : V, Sum.inl v ∈ p.support → x v ≠ y v

lemma reach_step (I : Instance Γ V) (x y : V → Bool) (c : Occurrence I)
    (u w : IncidenceVertex I) (hu : Reach I x y c u) (hadj : (incidenceGraph I).Adj u w)
    (hw : ∀ v, w = Sum.inl v → x v ≠ y v) : Reach I x y c w := by
  obtain ⟨p, hp⟩ := hu
  refine ⟨p.concat hadj, ?_⟩
  intro v hv
  rw [SimpleGraph.Walk.support_concat] at hv
  simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at hv
  rcases hv with hv | hv
  · exact hp v hv
  · exact hw v hv.symm

theorem disagreement (I : Instance Γ V) (hI : MinimallyUnsatisfiable I)
    (c c' : Occurrence I) (hcc' : c ≠ c') (x y : V → Bool)
    (hx : Solution (I.delete (occurrenceConstraint I c)) x)
    (hy : Solution (I.delete (occurrenceConstraint I c')) y) :
    ∃ p : (incidenceGraph I).Walk (.inr c) (.inr c'),
      p.IsPath ∧ ∀ v : V, Sum.inl v ∈ p.support → x v ≠ y v := by
  have key : Reach I x y c (.inr c') := by
    by_contra hnr
    apply hI.1
    refine ⟨fun v => if Reach I x y c (Sum.inl v) then y v else x v, ?_⟩
    intro d hd
    obtain ⟨e, rfl⟩ := occ_surj I hd
    by_cases hre : Reach I x y c (.inr e)
    · have hec' : e ≠ c' := fun h => hnr (h ▸ hre)
      have hsat : (occurrenceConstraint I e).Satisfied y :=
        hy _ (mem_delete_iff I hI e c' _ hd hec' rfl)
      have : (fun i => (if Reach I x y c (Sum.inl ((occurrenceConstraint I e).scope i))
          then y ((occurrenceConstraint I e).scope i)
          else x ((occurrenceConstraint I e).scope i)))
          = fun i => y ((occurrenceConstraint I e).scope i) := by
        funext i
        by_cases hr : Reach I x y c (Sum.inl ((occurrenceConstraint I e).scope i))
        · simp [hr]
        · by_cases hxy : x ((occurrenceConstraint I e).scope i) = y ((occurrenceConstraint I e).scope i)
          · simp [hr, hxy]
          · exfalso; apply hr
            exact reach_step I x y c (.inr e) _ hre ⟨i, rfl⟩
              (fun v hv => by cases hv; exact hxy)
      unfold Constraint.Satisfied
      rw [this]; exact hsat
    · have hec : e ≠ c := fun h => hre (h ▸ ⟨SimpleGraph.Walk.nil, by simp⟩)
      have hsat : (occurrenceConstraint I e).Satisfied x :=
        hx _ (mem_delete_iff I hI e c _ hd hec rfl)
      have : (fun i => (if Reach I x y c (Sum.inl ((occurrenceConstraint I e).scope i))
          then y ((occurrenceConstraint I e).scope i)
          else x ((occurrenceConstraint I e).scope i)))
          = fun i => x ((occurrenceConstraint I e).scope i) := by
        funext i
        by_cases hr : Reach I x y c (Sum.inl ((occurrenceConstraint I e).scope i))
        · exfalso; apply hre
          obtain ⟨p, hp⟩ := hr
          exact reach_step I x y c _ _ ⟨p, hp⟩ ⟨i, rfl⟩ (fun v hv => by cases hv)
        · simp [hr]
      unfold Constraint.Satisfied
      rw [this]; exact hsat
  obtain ⟨p, hp⟩ := key
  refine ⟨p.bypass, SimpleGraph.Walk.bypass_isPath p, ?_⟩
  intro v hv
  exact hp v (SimpleGraph.Walk.support_bypass_subset_support p hv)

end StabilityDichotomies.Dev.Disagree

namespace StabilityDichotomies.Solvability

end StabilityDichotomies.Solvability
end

section
set_option autoImplicit false

namespace StabilityDichotomies.Dev.Sparse

open StabilityDichotomies.Solvability
open scoped Classical

variable {Γ : Language}

/-- Step 1: a minimal unsatisfiable sub-multiset. -/
lemma exists_minUnsat_sub {V : Type} (E : Multiset (Constraint Γ V))
    (h : ¬ Satisfiable (⟨E⟩ : Instance Γ V)) :
    ∃ E' : Multiset (Constraint Γ V), E' ≤ E ∧ MinimallyUnsatisfiable (⟨E'⟩ : Instance Γ V) := by
  induction' hn : Multiset.card E using Nat.strong_induction_on with n ih generalizing E
  by_cases hall : ∀ c ∈ E, Satisfiable (⟨E.erase c⟩ : Instance Γ V)
  · exact ⟨E, le_rfl, h, hall⟩
  · push Not at hall
    obtain ⟨c, hc, hc'⟩ := hall
    obtain ⟨E', hle, hE'⟩ := ih (Multiset.card (E.erase c))
      (by rw [← hn]; exact Multiset.card_erase_lt_of_mem hc) (E.erase c) hc' rfl
    exact ⟨E', hle.trans (Multiset.erase_le _ _), hE'⟩

/-- Relabelling preserves minimal unsatisfiability when injective on used variables. -/
lemma map_minUnsat {V W : Type} (M : Instance Γ V) (f : V → W) (g : W → V)
    (hM : MinimallyUnsatisfiable M)
    (hfg : ∀ c ∈ M.constraints, ∀ i, g (f (c.scope i)) = c.scope i) :
    MinimallyUnsatisfiable (M.map f) := by
  have hnd := Disagree.nodup_of_minUnsat M hM
  have hinj : ∀ a ∈ M.constraints, ∀ b ∈ M.constraints,
      (⟨a.rel, f ∘ a.scope⟩ : Constraint Γ W) = ⟨b.rel, f ∘ b.scope⟩ → a = b := by
    intro a ha b hb hab
    obtain ⟨r, s⟩ := a
    obtain ⟨r', s'⟩ := b
    simp only [Constraint.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    subst h1
    have h3 := eq_of_heq h2
    congr
    funext i
    have e1 := hfg _ ha i
    have e2 := hfg _ hb i
    have : f (s i) = f (s' i) := congrFun h3 i
    simp only at e1 e2
    rw [← e1, ← e2, this]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    apply hM.1
    refine ⟨x ∘ f, ?_⟩
    intro c hc
    exact hx ⟨c.rel, f ∘ c.scope⟩ (Multiset.mem_map.mpr ⟨c, hc, rfl⟩)
  · intro c' hc'
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hc'
    obtain ⟨y, hy⟩ := hM.2 c hc
    refine ⟨y ∘ g, ?_⟩
    have hnd' : (M.constraints.map fun c : Constraint Γ V => (⟨c.rel, f ∘ c.scope⟩ : Constraint Γ W)).Nodup :=
      Multiset.Nodup.map_on (fun a ha b hb h => hinj a ha b hb h) hnd
    intro d' hd'
    change d' ∈ (M.constraints.map fun c : Constraint Γ V => (⟨c.rel, f ∘ c.scope⟩ : Constraint Γ W)).erase _ at hd'
    rw [hnd'.mem_erase_iff] at hd'
    obtain ⟨hne, hmem⟩ := hd'
    obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hmem
    have hdc : d ≠ c := fun h => hne (by rw [h])
    have hsat := hy d ((Multiset.mem_erase_of_ne hdc).2 hd)
    unfold Constraint.Satisfied at hsat ⊢
    have : (fun i => (y ∘ g) ((f ∘ d.scope) i)) = fun i => y (d.scope i) := by
      funext i; exact congrArg y (hfg d hd i)
    simp only [Function.comp] at this ⊢
    rw [this]; exact hsat

/-- Connectedness of the incidence graph of a minimally unsatisfiable instance. -/
lemma connected_of_minUnsat {V : Type} [Fintype V] (I : Instance Γ V)
    (hI : MinimallyUnsatisfiable I)
    (hcov : ∀ v : V, ∃ c ∈ I.constraints, ∃ i, c.scope i = v) :
    (incidenceGraph I).Connected := by
  have hne : Nonempty (Occurrence I) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    apply hI.1
    refine ⟨fun _ => false, ?_⟩
    intro c hc
    obtain ⟨e, _⟩ := Disagree.occ_surj I hc
    exact (hn.false e).elim
  have hvar : ∀ v : V, ∃ e : Occurrence I, (incidenceGraph I).Adj (.inl v) (.inr e) := by
    intro v
    obtain ⟨c, hc, i, hi⟩ := hcov v
    obtain ⟨e, rfl⟩ := Disagree.occ_surj I hc
    exact ⟨e, ⟨i, hi⟩⟩
  have hoo : ∀ e e' : Occurrence I,
      (incidenceGraph I).Reachable (.inr e) (.inr e') := by
    intro e e'
    by_cases h : e = e'
    · subst h; exact SimpleGraph.Reachable.refl _
    · have h1 := hI.2 _ (Disagree.occ_mem I e)
      have h2 := hI.2 _ (Disagree.occ_mem I e')
      obtain ⟨x, hx⟩ := h1
      obtain ⟨y, hy⟩ := h2
      obtain ⟨p, _, _⟩ := Disagree.disagreement I hI e e' h x y hx hy
      exact ⟨p⟩
  have hv : ∀ u : IncidenceVertex I, (incidenceGraph I).Reachable u (.inr hne.some) := by
    intro u
    rcases u with v | e
    · obtain ⟨e, he⟩ := hvar v
      exact (SimpleGraph.Adj.reachable he).trans (hoo e _)
    · exact hoo e _
  have : Nonempty (IncidenceVertex I) := ⟨.inr hne.some⟩
  refine ⟨fun u w => (hv u).trans (hv w).symm⟩

/-- Potential argument: walks are at least as long as the potential difference. -/
lemma walk_length_ge {α : Type} (G : SimpleGraph α) (φ : α → ℤ)
    (h : ∀ u v, G.Adj u v → |φ u - φ v| ≤ 1) :
    ∀ {u v : α} (p : G.Walk u v), |φ u - φ v| ≤ (p.length : ℤ) := by
  intro u v p
  induction p with
  | nil => simp
  | cons hadj q ih =>
    rename_i a b c
    have := h _ _ hadj
    rw [SimpleGraph.Walk.length_cons]
    push_cast
    have e : φ a - φ c = (φ a - φ b) + (φ b - φ c) := by ring
    rw [e]
    calc |(φ a - φ b) + (φ b - φ c)| ≤ |φ a - φ b| + |φ b - φ c| := abs_add_le _ _
      _ ≤ _ := by linarith


lemma card_links (N : ℕ) : (linksSquares Γ N).constraints.card ≤ kappa Γ * N := by
  have : (linksSquares Γ N).constraints.card = kappa Γ * N := by
    unfold linksSquares kappa
    simp only [Multiset.card_bind, Multiset.card_map, Function.comp_def, Finset.card_val,
      Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    simp only [← Finset.sum_eq_multiset_sum, Finset.sum_const, smul_eq_mul]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_mul, ← Finset.sum_coe_sort Γ.relations]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  exact this.le


lemma card_linkVertex (N : ℕ) (hN : 1 ≤ N) : Fintype.card (LinkVertex N) ≤ 4 * N := by
  let F : LinkVertex N → Fin N × Bool × Bool := fun v =>
    if h : v.val.1.val = N then (⟨0, hN⟩, v.val.2.2, true)
    else (⟨v.val.1.val, by have := v.val.1.isLt; omega⟩, v.val.2.1, v.val.2.2)
  have hF : Function.Injective F := by
    rintro ⟨⟨i, a, b⟩, h1, h2⟩ ⟨⟨i', a', b'⟩, h1', h2'⟩ h
    simp only at h1 h2 h1' h2'
    simp only [F] at h
    by_cases hi : i.val = N <;> by_cases hi' : i'.val = N <;> simp only [hi, hi', dite_true, dite_false] at h
    · have e1 : i = i' := Fin.ext (by omega)
      subst e1
      have ha := h2 hi
      have ha' := h2' hi'
      simp only [Prod.mk.injEq, true_and, and_true] at h
      simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
      exact ⟨by rw [ha, ha'], h⟩
    · simp only [Prod.mk.injEq, Fin.mk.injEq] at h
      obtain ⟨h3, h4, h5⟩ := h
      have := h1' (by omega)
      rw [this] at h5
      exact absurd h5 (by simp)
    · simp only [Prod.mk.injEq, Fin.mk.injEq] at h
      obtain ⟨h3, h4, h5⟩ := h
      have := h1 (by omega)
      rw [this] at h5
      exact absurd h5.symm (by simp)
    · simp only [Prod.mk.injEq, Fin.mk.injEq] at h
      obtain ⟨h3, h4, h5⟩ := h
      have e1 : i = i' := Fin.ext h3
      subst e1
      simp [h4, h5]
  have := Fintype.card_le_of_injective F hF
  simpa [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_assoc, mul_comm, mul_left_comm] using this


def lay {N : ℕ} (v : LinkVertex N) : ℕ := v.val.1.val

lemma links_scope_layers (N : ℕ) (c : Constraint Γ (LinkVertex N))
    (hc : c ∈ (linksSquares Γ N).constraints) :
    ∃ j : ℕ, ∀ i, lay (c.scope i) = j ∨ lay (c.scope i) = j + 1 := by
  unfold linksSquares at hc
  simp only [Multiset.mem_bind, Multiset.mem_map] at hc
  obtain ⟨R, _, a, _, b, _, j, _, layers, _, rfl⟩ := hc
  refine ⟨j.val, fun t => ?_⟩
  show (if layers t = true then j.val + 1 else j.val) = j.val ∨
    (if layers t = true then j.val + 1 else j.val) = j.val + 1
  by_cases h : layers t = true <;> simp [h]

lemma sat_of_induce {V : Type} (I : Instance Γ V) (U : Finset V)
    (hs : Satisfiable (I.induce U)) (E : Multiset (Constraint Γ V))
    (hE : ∀ c ∈ E, c ∈ I.constraints ∧ ∀ i, c.scope i ∈ U) :
    Satisfiable (⟨E⟩ : Instance Γ V) := by
  obtain ⟨x, hx⟩ := hs
  refine ⟨fun v => if h : v ∈ U then x ⟨v, h⟩ else false, ?_⟩
  intro c hc
  obtain ⟨hc1, hc2⟩ := hE c hc
  have hmem : (⟨c.rel, fun i => ⟨c.scope i, hc2 i⟩⟩ : Constraint Γ U) ∈ (I.induce U).constraints := by
    unfold Instance.induce
    simp only [Multiset.mem_bind]
    exact ⟨c, hc1, by rw [dif_pos hc2]; simp⟩
  have := hx _ hmem
  unfold Constraint.Satisfied at this ⊢
  convert this using 2
  rename_i i
  simp [hc2 i]

lemma two_mul_le_edist {V : Type} [Fintype V] (I : Instance Γ V) (l : V → ℕ)
    (hl : ∀ c ∈ I.constraints, ∃ j : ℕ, ∀ i, l (c.scope i) = j ∨ l (c.scope i) = j + 1)
    (hconn : (incidenceGraph I).Connected) (N : ℕ) (u v : V) (hu : l u = 0) (hv : l v = N) :
    ((2 * N : ℕ) : ℕ∞) ≤ (incidenceGraph I).edist (.inl u) (.inl v) := by
  let J : Occurrence I → ℕ := fun e =>
    if h : ∃ j : ℕ, ∀ i, l ((occurrenceConstraint I e).scope i) = j ∨
        l ((occurrenceConstraint I e).scope i) = j + 1 then h.choose else 0
  have hJ : ∀ e i, l ((occurrenceConstraint I e).scope i) = J e ∨
      l ((occurrenceConstraint I e).scope i) = J e + 1 := by
    intro e
    have h := hl _ (Disagree.occ_mem I e)
    simp only [J, dif_pos h]
    exact h.choose_spec
  let φ : IncidenceVertex I → ℤ := fun u => match u with
    | .inl w => 2 * (l w : ℤ)
    | .inr e => 2 * (J e : ℤ) + 1
  have hφ : ∀ a b, (incidenceGraph I).Adj a b → |φ a - φ b| ≤ 1 := by
    intro a b hab
    change IncAdjacent I a b at hab
    rcases a with w | e <;> rcases b with w' | e'
    · exact hab.elim
    · obtain ⟨i, hi⟩ := hab
      subst hi
      rcases hJ e' i with h | h <;> simp only [φ, h] <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith
    · obtain ⟨i, hi⟩ := hab
      subst hi
      rcases hJ e i with h | h <;> simp only [φ, h] <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith
    · exact hab.elim
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_edist (.inl u) (.inl v)
  have := walk_length_ge _ φ hφ p
  rw [← hp]
  simp only [φ, hu, hv] at this
  have h2 : 2 * N ≤ p.length := by
    have : |((0 : ℕ) : ℤ) * 2 - 2 * (N : ℤ)| ≤ (p.length : ℤ) := by simpa using this
    rw [abs_le] at this; omega
  exact_mod_cast h2


theorem main (Γ : Language) (hΓ : ¬ FiniteDuality Γ)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (n : ℕ) (F : Instance Γ (Fin n)),
      MinimallyUnsatisfiable F ∧ (incidenceGraph F).Connected ∧
      n ≤ 4 * N ∧ F.constraints.card ≤ kappa Γ * N ∧
      ((2 * N : ℕ) : ℕ∞) ≤ (incidenceGraph F).ediam := by
  obtain ⟨hunsat, hlayers⟩ := links_squares_properties Γ hΓ N hN
  obtain ⟨E, hEle, hmin⟩ := exists_minUnsat_sub (linksSquares Γ N).constraints hunsat
  have hEL : ∀ c ∈ E, c ∈ (linksSquares Γ N).constraints := fun c hc => Multiset.mem_of_le hEle hc
  let T : Finset (LinkVertex N) :=
    (E.bind fun c => (Finset.univ : Finset (Fin c.rel.val.arity)).val.map c.scope).toFinset
  have hT : ∀ v, v ∈ T ↔ ∃ c ∈ E, ∃ i, c.scope i = v := by
    intro v
    simp [T, Multiset.mem_bind, Multiset.mem_map]
  have hEne : E ≠ 0 := by
    rintro rfl
    exact hmin.1 ⟨fun _ => false, fun c hc => by simp at hc⟩
  have hTne : T.Nonempty := by
    obtain ⟨c, hc⟩ := Multiset.exists_mem_of_ne_zero hEne
    exact ⟨c.scope ⟨0, c.rel.val.arity_pos⟩, (hT _).2 ⟨c, hc, _, rfl⟩⟩
  obtain ⟨t0, ht0⟩ := hTne
  let e := T.equivFin
  let f : LinkVertex N → Fin T.card := fun v => if h : v ∈ T then e ⟨v, h⟩ else e ⟨t0, ht0⟩
  let g : Fin T.card → LinkVertex N := fun w => (e.symm w).1
  have hgf : ∀ v ∈ T, g (f v) = v := by
    intro v hv
    simp [f, g, hv]
  have hfg_w : ∀ w, f (g w) = w := by
    intro w
    have : g w ∈ T := (e.symm w).2
    simp [f, g, this]
  have hgT : ∀ w, g w ∈ T := fun w => (e.symm w).2
  have hscopeT : ∀ c ∈ E, ∀ i, c.scope i ∈ T := fun c hc i => (hT _).2 ⟨c, hc, i, rfl⟩
  have hfg : ∀ c ∈ (⟨E⟩ : Instance Γ (LinkVertex N)).constraints, ∀ i,
      g (f (c.scope i)) = c.scope i := fun c hc i => hgf _ (hscopeT c hc i)
  have hFmin := map_minUnsat (⟨E⟩ : Instance Γ (LinkVertex N)) f g hmin hfg
  have hcov : ∀ w : Fin T.card, ∃ c ∈ ((⟨E⟩ : Instance Γ (LinkVertex N)).map f).constraints,
      ∃ i, c.scope i = w := by
    intro w
    obtain ⟨c, hc, i, hi⟩ := (hT _).1 (hgT w)
    refine ⟨⟨c.rel, f ∘ c.scope⟩, Multiset.mem_map.mpr ⟨c, hc, rfl⟩, i, ?_⟩
    simp only [Function.comp, hi, hfg_w]
  have hconn := connected_of_minUnsat _ hFmin hcov
  have hlayer : ∀ k : Fin (N + 1), ∃ v ∈ T, v.val.1 = k := by
    intro k
    by_contra hno
    push Not at hno
    apply hmin.1
    refine sat_of_induce (linksSquares Γ N) (Finset.univ \ linkLayer N k) (hlayers k) E ?_
    intro c hc
    refine ⟨hEL c hc, fun i => ?_⟩
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, linkLayer, Finset.mem_filter, not_and]
    exact fun h => absurd h (hno _ (hscopeT c hc i))
  obtain ⟨v0, hv0T, hv0⟩ := hlayer 0
  obtain ⟨vN, hvNT, hvN⟩ := hlayer (Fin.last N)
  refine ⟨T.card, (⟨E⟩ : Instance Γ (LinkVertex N)).map f, hFmin, hconn, ?_, ?_, ?_⟩
  · exact (Finset.card_le_univ T).trans (card_linkVertex N hN)
  · show (E.map _).card ≤ _
    rw [Multiset.card_map]
    exact (Multiset.card_le_card hEle).trans (card_links N)
  · have hl : ∀ c ∈ ((⟨E⟩ : Instance Γ (LinkVertex N)).map f).constraints,
        ∃ j : ℕ, ∀ i, (fun w => lay (g w)) (c.scope i) = j ∨
          (fun w => lay (g w)) (c.scope i) = j + 1 := by
      intro c' hc'
      obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hc'
      obtain ⟨j, hj⟩ := links_scope_layers N c (hEL c hc)
      refine ⟨j, fun i => ?_⟩
      have := hfg c hc i
      simp only [Function.comp, this]
      exact hj i
    have h1 := two_mul_le_edist _ (fun w => lay (g w)) hl hconn N (f v0) (f vN)
      (by simp only [hgf _ hv0T, lay, hv0]; rfl) (by simp only [hgf _ hvNT, lay, hvN]; rfl)
    exact h1.trans SimpleGraph.edist_le_ediam

end StabilityDichotomies.Dev.Sparse

namespace StabilityDichotomies.Solvability

theorem chk_sparse_large_diameter_obstruction (Γ : Language) (hΓ : ¬ FiniteDuality Γ)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (n : ℕ) (F : Instance Γ (Fin n)),
      MinimallyUnsatisfiable F ∧ (incidenceGraph F).Connected ∧
      n ≤ 4 * N ∧ F.constraints.card ≤ kappa Γ * N ∧
      ((2 * N : ℕ) : ℕ∞) ≤ (incidenceGraph F).ediam :=
  StabilityDichotomies.Dev.Sparse.main Γ hΓ N hN

end StabilityDichotomies.Solvability
end

theorem solution : type_of% @StabilityDichotomies.Solvability.chk_sparse_large_diameter_obstruction := @StabilityDichotomies.Solvability.chk_sparse_large_diameter_obstruction
