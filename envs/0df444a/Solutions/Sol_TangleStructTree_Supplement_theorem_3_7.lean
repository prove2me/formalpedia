-- Prove2me | solution 1 for TangleStructTree.Supplement.theorem_3_7
-- status  : ACCEPTED   (prove)
-- author  : @amenyxia
-- created : 2026-11-16T08:14:09.19514+00:00
-- url     : https://prove2.me/submissions/2156b5b2-e8fb-446b-a06c-35ea0efc4d57

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_Consistent
import Definitions.Def_TangleStructTree_SepTree_IsTST

set_option autoImplicit false

open TangleStructTree

variable {E : Type*} [PartialOrder E] [SepSystem E]

open SepSystem

private def Adm (ℱ : Set (Set E)) (T : SepTree E) (hT : T.IsTST ℱ) (τ : Set E) (v : List E) : Prop := labels v ⊆ τ

private lemma adm_root (ℱ : Set (Set E)) (T : SepTree E) (hT : T.IsTST ℱ) (τ : Set E) : Adm ℱ T hT τ [] := by
  intro y hy
  cases hy

private lemma adm_child (ℱ : Set (Set E)) (T : SepTree E) (hT : T.IsTST ℱ) (τ : Set E) (hτ : IsTangle ℱ τ) (v : List E)
    (hv : v ∈ T.nodes) (hadm : Adm ℱ T hT τ v) (hchild : ∃ x : E, x :: v ∈ T.nodes) :
    ∃! c : List E, c ∈ T.nodes ∧ (∃ x : E, c = x :: v) ∧ Adm ℱ T hT τ c := by
  obtain ⟨s, hsplit, _⟩ := T.split v hv hchild
  have hlabels : ∀ x, labels (x :: v) = insert x (labels v) := by
    intro x
    ext y
    simp [labels, List.mem_cons]
  have hadm_child : ∀ x, Adm ℱ T hT τ (x :: v) ↔ Adm ℱ T hT τ v ∧ x ∈ τ := by
    intro x
    dsimp only [Adm] at hadm ⊢
    rw [hlabels x, Set.insert_subset_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  by_cases hsτ : s ∈ τ
  · refine ⟨s :: v, ⟨hsplit s |>.mpr (Or.inl rfl), ⟨s, rfl⟩, (hadm_child s).mpr ⟨hadm, hsτ⟩⟩, ?_⟩
    intro c hc
    obtain ⟨x, rfl⟩ := hc.2.1
    have hxs : x = s ∨ x = rev s := (hsplit x).mp hc.1
    rcases hxs with (heq | heq)
    · rw [heq]
    · rw [heq] at hc
      rw [heq]
      have hrev : rev s ∈ τ := (hadm_child (rev s)).mp hc.2.2 |>.2
      rw [(hτ.1 s).2 hsτ hrev]
  · have hrsτ : rev s ∈ τ := by
      rcases (hτ.1 (rev s)).1 with (h | h)
      · exact h
      · rw [rev_rev] at h
        contradiction
    refine ⟨rev s :: v, ⟨hsplit (rev s) |>.mpr (Or.inr rfl), ⟨rev s, rfl⟩,
      (hadm_child (rev s)).mpr ⟨hadm, hrsτ⟩⟩, ?_⟩
    intro c hc
    obtain ⟨x, rfl⟩ := hc.2.1
    have hxs : x = s ∨ x = rev s := (hsplit x).mp hc.1
    rcases hxs with (heq | heq)
    · rw [heq] at hc
      rw [heq]
      have hs : s ∈ τ := (hadm_child s).mp hc.2.2 |>.2
      rw [(hτ.1 s).2 hs hrsτ]
    · rw [heq]

private lemma drop_step (l : List E) (k : ℕ) : l.drop (k + 1) = (l.drop k).tail := by
  induction k
  · simp [List.drop]
  · simp_all [List.drop]

private lemma list_nil_or_cons (l : List E) : l = [] ∨ ∃ x, l = x :: l.tail := by
  cases l with
  | nil => simp
  | cons x r => exact Or.inr ⟨x, rfl⟩

private lemma drop_node_adm (ℱ : Set (Set E)) (T : SepTree E) (hT : T.IsTST ℱ) (τ : Set E)
    (ℓ : List E) (hℓ : T.IsLeaf ℓ) (hadm : Adm ℱ T hT τ ℓ) (k : ℕ) :
    ℓ.drop k ∈ T.nodes ∧ Adm ℱ T hT τ (ℓ.drop k) := by
  induction k with
  | zero =>
    rw [List.drop_zero]
    exact ⟨hℓ.1, hadm⟩
  | succ k ih =>
    have ih' : ℓ.drop k ∈ T.nodes ∧ Adm ℱ T hT τ (ℓ.drop k) := ih
    refine ⟨?_, ?_⟩
    · rw [drop_step]
      rcases (list_nil_or_cons (ℓ.drop k)) with (hnil | ⟨x, hwx⟩)
      · rw [hnil, List.tail_nil]
        exact T.root_mem
      · exact T.parent_mem x (ℓ.drop k).tail (hwx.symm ▸ ih'.1)
    · rw [drop_step]
      rcases (list_nil_or_cons (ℓ.drop k)) with (hnil | ⟨x, hwx⟩)
      · rw [hnil, List.tail_nil]
        dsimp only [Adm]
        intro z hz
        cases hz
      · have hsub : labels (ℓ.drop k).tail ⊆ labels (x :: (ℓ.drop k).tail) := by
          intro z hz
          dsimp only [labels] at hz ⊢
          exact List.mem_cons.mpr (Or.inr hz)
        simpa [Adm] using Set.Subset.trans hsub (hwx.symm ▸ ih'.2)

private lemma adm_leaf (ℱ : Set (Set E)) (T : SepTree E) (hT : T.IsTST ℱ) (τ : Set E) (hτ : IsTangle ℱ τ) :
    ∃! ℓ : List E, T.IsLeaf ℓ ∧ Adm ℱ T hT τ ℓ := by
  classical
  let A := T.nodes.filter (fun v => Adm ℱ T hT τ v)
  have hA : A.Nonempty := by
    refine ⟨[], ?_⟩
    dsimp only [A]
    rw [Finset.mem_filter]
    exact ⟨T.root_mem, adm_root ℱ T hT τ⟩
  obtain ⟨ℓ₀, hℓ₀, hmax⟩ := Finset.exists_max_image A (fun v => v.length) hA
  have hℓ₀n : ℓ₀ ∈ T.nodes := (Finset.mem_filter.mp hℓ₀).1
  have hℓ₀a : Adm ℱ T hT τ ℓ₀ := (Finset.mem_filter.mp hℓ₀).2
  have hleaf : T.IsLeaf ℓ₀ := by
    constructor
    · exact hℓ₀n
    · intro x hx
      rcases (adm_child ℱ T hT τ hτ ℓ₀ hℓ₀n hℓ₀a ⟨x, hx⟩) with ⟨w, hw, _⟩
      have hwA : w ∈ A := by
        dsimp only [A]
        rw [Finset.mem_filter]
        exact ⟨hw.1, hw.2.2⟩
      have hlen : ℓ₀.length < w.length := by
        rcases hw.2.1 with ⟨y, rfl⟩
        simp only [List.length_cons]
        exact Nat.lt_succ_self _
      linarith [hmax w hwA]
  have hdropnil (l : List E) (n : ℕ) : l.drop n = [] ↔ n ≥ l.length := by
    induction l with
    | nil => simp
    | cons _ t ih =>
      cases n with
      | zero => simp
      | succ n => simp
  refine ⟨ℓ₀, ⟨hleaf, hℓ₀a⟩, ?_⟩
  intro ℓ' hℓ'
  rcases hℓ' with ⟨hleaf', hadm'⟩
  by_contra hne
  have hdrop₀ : ∀ k, ℓ₀.drop k ∈ T.nodes ∧ Adm ℱ T hT τ (ℓ₀.drop k) :=
    fun k => drop_node_adm ℱ T hT τ ℓ₀ hleaf hℓ₀a k
  have hdrop' : ∀ k, ℓ'.drop k ∈ T.nodes ∧ Adm ℱ T hT τ (ℓ'.drop k) :=
    fun k => drop_node_adm ℱ T hT τ ℓ' hleaf' hadm' k
  let S := (Finset.range (ℓ₀.length + 1)).image (fun k => ℓ₀.drop k) ∩
    (Finset.range (ℓ'.length + 1)).image (fun k => ℓ'.drop k)
  have hS : S.Nonempty := by
    rw [Finset.Nonempty]
    refine ⟨[], ?_⟩
    simp only [S, Finset.mem_inter]
    constructor
    · rw [Finset.mem_image]
      refine ⟨ℓ₀.length, ?_, (hdropnil ℓ₀ ℓ₀.length).mpr (le_refl _)⟩
      simp only [Finset.mem_range]
      exact Nat.lt_succ_self _
    · rw [Finset.mem_image]
      refine ⟨ℓ'.length, ?_, (hdropnil ℓ' ℓ'.length).mpr (le_refl _)⟩
      simp only [Finset.mem_range]
      exact Nat.lt_succ_self _
  obtain ⟨p, hp, hmaxp⟩ := Finset.exists_max_image S (fun v => v.length) hS
  rcases (Finset.mem_inter.mp hp) with ⟨hp₁, hp₂⟩
  rcases (Finset.mem_image.mp hp₁) with ⟨k₀, hrange₀, heq₀⟩
  rcases (Finset.mem_image.mp hp₂) with ⟨k', hrange', heq'⟩
  subst p
  simp only [Finset.mem_range] at hrange₀ hrange'
  have hk₀ : k₀ ≤ ℓ₀.length := by omega
  have hk' : k' ≤ ℓ'.length := by omega
  by_cases hk₀z : k₀ = 0
  · subst k₀
    by_cases hk'z : k' = 0
    · subst k'
      have heq'' : ℓ' = ℓ₀ := by
        simpa [List.drop_zero] using heq'
      exact hne heq''
    · have hk'p : 0 < k' := Nat.pos_of_ne_zero hk'z
      have hℓ₀drop : ℓ'.drop k' = ℓ₀ := by
        simpa [List.drop_zero] using heq'
      have hw'tail : (ℓ'.drop (k' - 1)).tail = ℓ₀ := by
        rw [(drop_step ℓ' (k' - 1)).symm]
        have hk'p' : k' - 1 + 1 = k' := by omega
        rw [hk'p']
        simpa using hℓ₀drop
      have hw'n : ℓ'.drop (k' - 1) ∈ T.nodes := hdrop' (k' - 1) |>.1
      rcases (list_nil_or_cons (ℓ'.drop (k' - 1))) with (hnil | ⟨x, hw'⟩)
      · have hge : k' - 1 ≥ ℓ'.length := (hdropnil ℓ' (k' - 1)).mp hnil
        have hlt : k' - 1 < ℓ'.length := by omega
        omega
      · have h : ℓ'.drop (k' - 1) = x :: ℓ₀ := by
          simpa [hw'tail] using hw'
        have hw'real : x :: ℓ₀ ∈ T.nodes := by
          simpa [h] using hw'n
        exact hleaf.2 x hw'real
  · have hk₀p : 0 < k₀ := Nat.pos_of_ne_zero hk₀z
    by_cases hk'z : k' = 0
    · subst k'
      have hℓ'drop : ℓ' = ℓ₀.drop k₀ := by
        simpa [List.drop_zero] using heq'
      have hw₀n : ℓ₀.drop (k₀ - 1) ∈ T.nodes := hdrop₀ (k₀ - 1) |>.1
      have hw₀tail : (ℓ₀.drop (k₀ - 1)).tail = ℓ₀.drop k₀ := by
        have hk₀p' : k₀ - 1 + 1 = k₀ := by omega
        have hdrop : ℓ₀.drop k₀ = ℓ₀.drop (k₀ - 1 + 1) := by rw [hk₀p']
        rw [hdrop]
        exact (drop_step ℓ₀ (k₀ - 1)).symm
      rcases (list_nil_or_cons (ℓ₀.drop (k₀ - 1))) with (hnil | ⟨x, hw₀⟩)
      · have hge : k₀ - 1 ≥ ℓ₀.length := (hdropnil ℓ₀ (k₀ - 1)).mp hnil
        have hlt : k₀ - 1 < ℓ₀.length := by omega
        omega
      · have h : ℓ₀.drop (k₀ - 1) = x :: ℓ' := by
          simpa [hw₀tail, hℓ'drop] using hw₀
        have hw'real : x :: ℓ' ∈ T.nodes := by
          simpa [h] using hw₀n
        exact hleaf'.2 x hw'real
    · have hk'p : 0 < k' := Nat.pos_of_ne_zero hk'z
      have hw₀n : ℓ₀.drop (k₀ - 1) ∈ T.nodes := hdrop₀ (k₀ - 1) |>.1
      have hw₀a : Adm ℱ T hT τ (ℓ₀.drop (k₀ - 1)) := hdrop₀ (k₀ - 1) |>.2
      have hw'n : ℓ'.drop (k' - 1) ∈ T.nodes := hdrop' (k' - 1) |>.1
      have hw'a : Adm ℱ T hT τ (ℓ'.drop (k' - 1)) := hdrop' (k' - 1) |>.2
      have hptail : (ℓ₀.drop (k₀ - 1)).tail = ℓ₀.drop k₀ := by
        have hk₀p' : k₀ - 1 + 1 = k₀ := by omega
        have hdrop : ℓ₀.drop k₀ = ℓ₀.drop (k₀ - 1 + 1) := by rw [hk₀p']
        rw [hdrop]
        exact (drop_step ℓ₀ (k₀ - 1)).symm
      have hptail' : (ℓ'.drop (k' - 1)).tail = ℓ'.drop k' := by
        have hk'p' : k' - 1 + 1 = k' := by omega
        have hdrop' : ℓ'.drop k' = ℓ'.drop (k' - 1 + 1) := by rw [hk'p']
        rw [hdrop']
        exact (drop_step ℓ' (k' - 1)).symm
      rcases (list_nil_or_cons (ℓ₀.drop (k₀ - 1))) with (hnil | ⟨x, hwx⟩)
      · have hge : k₀ - 1 ≥ ℓ₀.length := (hdropnil ℓ₀ (k₀ - 1)).mp hnil
        have hlt : k₀ - 1 < ℓ₀.length := by omega
        omega
      · have hwx' : ℓ₀.drop (k₀ - 1) = x :: (ℓ₀.drop k₀) := by
          rw [hwx, hptail]
        have hw₀x : x :: (ℓ₀.drop k₀) ∈ T.nodes := by
          simpa [hwx'] using hw₀n
        rcases (list_nil_or_cons (ℓ'.drop (k' - 1))) with (hnil | ⟨y, hwy⟩)
        · have hge : k' - 1 ≥ ℓ'.length := (hdropnil ℓ' (k' - 1)).mp hnil
          have hlt : k' - 1 < ℓ'.length := by omega
          omega
        · have hwy' : ℓ'.drop (k' - 1) = y :: (ℓ'.drop k') := by
            rw [hwy, hptail']
          have hw'y : y :: (ℓ'.drop k') ∈ T.nodes := by
            simpa [hwy'] using hw'n
          have hpn : ℓ₀.drop k₀ ∈ T.nodes := hdrop₀ k₀ |>.1
          have hpa : Adm ℱ T hT τ (ℓ₀.drop k₀) := hdrop₀ k₀ |>.2
          have hchild₀ : ∃ z, z :: ℓ₀.drop k₀ ∈ T.nodes := ⟨x, hw₀x⟩
          rcases (adm_child ℱ T hT τ hτ (ℓ₀.drop k₀) hpn hpa hchild₀) with ⟨c, hc, hu⟩
          have h₁ : x :: ℓ₀.drop k₀ ∈ T.nodes ∧ (∃ z, x :: ℓ₀.drop k₀ = z :: ℓ₀.drop k₀) ∧
              Adm ℱ T hT τ (x :: ℓ₀.drop k₀) :=
            ⟨hw₀x, ⟨x, rfl⟩, hwx'.symm ▸ hw₀a⟩
          have h₂ : y :: ℓ'.drop k' ∈ T.nodes ∧ (∃ z, y :: ℓ'.drop k' = z :: ℓ₀.drop k₀) ∧
              Adm ℱ T hT τ (y :: ℓ'.drop k') :=
            ⟨hw'y, ⟨y, by simpa [heq']⟩, hwy'.symm ▸ hw'a⟩
          have hweq : x :: ℓ₀.drop k₀ = y :: ℓ'.drop k' :=
            (hu (x :: ℓ₀.drop k₀) h₁).trans (hu (y :: ℓ'.drop k') h₂).symm
          have hq : ℓ₀.drop (k₀ - 1) = ℓ'.drop (k' - 1) := by
            simpa [hwx', hwy'] using hweq
          have hqS : ℓ₀.drop (k₀ - 1) ∈ S := by
            dsimp only [S]
            rw [Finset.mem_inter]
            constructor
            · rw [Finset.mem_image]
              refine ⟨k₀ - 1, ?_, rfl⟩
              exact Finset.mem_range.mpr (by omega)
            · rw [Finset.mem_image]
              refine ⟨k' - 1, ?_, hq.symm⟩
              exact Finset.mem_range.mpr (by omega)
          have hqmax : (ℓ₀.drop (k₀ - 1)).length ≤ (ℓ₀.drop k₀).length :=
            hmaxp (ℓ₀.drop (k₀ - 1)) hqS
          have hqlen : (ℓ₀.drop k₀).length < (ℓ₀.drop (k₀ - 1)).length := by
            rw [hwx']
            simp only [List.length_cons]
            exact Nat.lt_succ_self _
          omega

private lemma leaf_tangle (ℱ : Set (Set E)) (T : SepTree E) (hT : T.IsTST ℱ) (τ : Set E) (hτ : IsTangle ℱ τ) (ℓ : List E)
    (hℓ : T.IsLeaf ℓ ∧ Adm ℱ T hT τ ℓ) : T.IsTangleLeaf ℱ ℓ := by
  rcases (hT.2.1 ℓ hℓ.1) with (ht | hf)
  · exact ht
  · have hnot : ¬ Avoids ℱ (labels ℓ) := hf.2
    have hsub : ∃ σ₀ ∈ ℱ, σ₀ ⊆ labels ℓ := by
      by_contra hno
      have havoid : Avoids ℱ (labels ℓ) := by
        intro σ hσ
        push Not at hno
        exact hno σ hσ
      contradiction
    rcases hsub with ⟨σ₀, hσ₀, hsub₀⟩
    exact False.elim ((hτ.2.2 σ₀ hσ₀) (Set.Subset.trans hsub₀ hℓ.2))

private lemma closure_sub (ℱ : Set (Set E)) (T : SepTree E) (hT : T.IsTST ℱ) (τ : Set E) (hτ : IsTangle ℱ τ) (ℓ : List E)
    (hℓ : T.IsLeaf ℓ ∧ Adm ℱ T hT τ ℓ) : sepClosure (labels ℓ) ⊆ τ := by
  intro x hx
  dsimp only [sepClosure] at hx
  rw [Set.mem_union] at hx
  rcases hx with (hxl | ⟨hxn, hinc⟩)
  · exact hℓ.2 hxl
  · by_cases hrx : rev x ∈ τ
    · have hsub : insert (rev x) (labels ℓ) ⊆ τ := by
        intro y hy
        rcases (@Set.mem_insert_iff E y (rev x) (labels ℓ)).mp hy with (hyeq | hyl)
        · exact hyeq ▸ hrx
        · exact hℓ.2 hyl
      have hcons : IsConsistent (insert (rev x) (labels ℓ)) := by
        intro y hy z hz hyz hyr
        exact hτ.2.1 y (hsub hy) z (hsub hz) hyz hyr
      exact False.elim (hinc hcons)
    · have ho : Orients τ x := (hτ.1 x).1
      rcases ho with (hxt | hrx2)
      · exact hxt
      · contradiction

private lemma sub_closure (ℱ : Set (Set E)) (T : SepTree E) (hT : T.IsTST ℱ) (τ : Set E) (hτ : IsTangle ℱ τ) (ℓ : List E)
    (hℓ : T.IsLeaf ℓ ∧ Adm ℱ T hT τ ℓ) : τ ⊆ sepClosure (labels ℓ) := by
  intro x hx
  by_cases hxl : x ∈ labels ℓ
  · dsimp only [sepClosure]
    exact (Set.mem_union x (labels ℓ) {y | Requires (labels ℓ) y}).mpr (Or.inl hxl)
  · have hreq : Requires (labels ℓ) x := by
      constructor
      · exact hxl
      · by_contra hcons
        have ho : Orients (sepClosure (labels ℓ)) x := ((leaf_tangle ℱ T hT τ hτ ℓ hℓ).2.1 x).1
        rcases ho with (hsx | hrsx)
        · have hxs : x ∈ sepClosure (labels ℓ) := hsx
          have hmem : x ∈ labels ℓ ∨ x ∈ {y | Requires (labels ℓ) y} := by
            dsimp only [sepClosure] at hxs
            rw [Set.mem_union] at hxs
            exact hxs
          rcases hmem with (hyl | ⟨_, hyr2⟩)
          · contradiction
          · exact hyr2 hcons
        · have hcsub : sepClosure (labels ℓ) ⊆ τ := closure_sub ℱ T hT τ hτ ℓ hℓ
          have hrevτ : rev x ∈ τ := hcsub hrsx
          have heq : rev x = x := (hτ.1 x).2 hx hrevτ
          have hxs : x ∈ sepClosure (labels ℓ) := heq ▸ hrsx
          have hmem : x ∈ labels ℓ ∨ x ∈ {y | Requires (labels ℓ) y} := by
            dsimp only [sepClosure] at hxs
            rw [Set.mem_union] at hxs
            exact hxs
          rcases hmem with (hyl | ⟨_, hyr2⟩)
          · contradiction
          · exact hyr2 hcons
    dsimp only [sepClosure]
    exact (Set.mem_union x (labels ℓ) {y | Requires (labels ℓ) y}).mpr (Or.inr (by simpa using hreq))

theorem solution (ℱ : Set (Set E)) (T : SepTree E) (hT : T.IsTST ℱ) :
    (∀ τ : Set E, IsTangle ℱ τ → ∃! ℓ : List E, T.IsLeaf ℓ ∧ sepClosure (labels ℓ) = τ) ∧
      ((∀ ℓ : List E, T.IsLeaf ℓ → T.IsForbiddenLeaf ℱ ℓ) → ¬ ∃ τ : Set E, IsTangle ℱ τ) := by
  constructor
  · intro τ hτ
    obtain ⟨ℓ, ⟨hleaf, hadm⟩, hu⟩ := adm_leaf ℱ T hT τ hτ
    have hs : sepClosure (labels ℓ) = τ :=
      Set.Subset.antisymm (closure_sub ℱ T hT τ hτ ℓ ⟨hleaf, hadm⟩)
                           (sub_closure ℱ T hT τ hτ ℓ ⟨hleaf, hadm⟩)
    refine ⟨ℓ, ⟨hleaf, hs⟩, ?_⟩
    intro ℓ' h'
    have hsub : labels ℓ' ⊆ τ := by
      have : labels ℓ' ⊆ sepClosure (labels ℓ') := by
        rintro y hy
        rw [sepClosure]
        exact Or.inl hy
      rw [h'.2.symm]
      exact this
    have hadm' : Adm ℱ T hT τ ℓ' := hsub
    exact hu ℓ' ⟨h'.1, hadm'⟩
  · intro hforb
    intro hex
    obtain ⟨τ, hτ⟩ := hex
    obtain ⟨ℓ, ⟨hleaf, hadm⟩, _⟩ := adm_leaf ℱ T hT τ hτ
    have htl := leaf_tangle ℱ T hT τ hτ ℓ ⟨hleaf, hadm⟩
    have havoid : Avoids ℱ (labels ℓ) := by
      have htau : IsTangle ℱ (sepClosure (labels ℓ)) := by
        dsimp only [SepTree.IsTangleLeaf] at htl
        exact htl.2
      have : labels ℓ ⊆ sepClosure (labels ℓ) := by
        rintro y hy
        rw [sepClosure]
        exact Or.inl hy
      intro σ₀ hσ₀ hsub0
      exact htau.2.2 σ₀ hσ₀ (Set.Subset.trans hsub0 this)
    have hfb := hforb ℓ hleaf
    dsimp only [SepTree.IsForbiddenLeaf] at hfb
    exact hfb.2 havoid
