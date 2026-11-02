-- Prove2me | solution 1 for RainbowEFX.Sublinear.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:00:25.671379+00:00
-- url     : https://prove2.me/submissions/eec2e9be-5823-429b-b6d3-3415525a9f69

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

open LittleCharity.EFX RainbowEFX.Sublinear

/-- A walk extracted from `TransGen`, as an ℕ-indexed sequence. -/
theorem REFX_walk_of_transGen' {α : Type} (E : α → α → Prop) {i j : α}
    (h : Relation.TransGen E i j) :
    ∃ (r : ℕ) (c : ℕ → α), c 0 = i ∧ c (r + 1) = j ∧ ∀ k ≤ r, E (c k) (c (k + 1)) := by
  classical
  induction h with
  | single hb =>
    rename_i b
    exact ⟨0, fun k => if k = 0 then i else b, by simp, by simp, by
      intro k hk; have : k = 0 := by omega
      subst this; simpa using hb⟩
  | @tail b c' _ hbc ih =>
    obtain ⟨r, c, h0, hr, hE⟩ := ih
    refine ⟨r + 1, fun k => if k ≤ r + 1 then c k else c', by simp [h0], by simp, ?_⟩
    intro k hk
    by_cases hk' : k ≤ r
    · simp only [show k ≤ r + 1 by omega, show k + 1 ≤ r + 1 by omega, if_true]
      exact hE k hk'
    · have : k = r + 1 := by omega
      subst this
      simp only [le_refl, if_true, show ¬ (r + 1 + 1 ≤ r + 1) by omega, if_false, hr]
      exact hbc

/-- A closed walk through a vertex satisfying `P` yields an injective cycle
`d : Fin (r+1) → α` whose vertex `d 0` satisfies `P`. -/
theorem REFX_simple_cycle_P {α : Type} (E : α → α → Prop) (P : α → Prop) {i : α}
    (hP : P i) (h : Relation.TransGen E i i) :
    ∃ (r : ℕ) (d : Fin (r + 1) → α), Function.Injective d ∧ P (d 0) ∧
      ∀ k, E (d k) (d (finRotate (r + 1) k)) := by
  classical
  have hex : ∃ r, ∃ c : ℕ → α, P (c 0) ∧ c (r + 1) = c 0 ∧ ∀ k ≤ r, E (c k) (c (k + 1)) := by
    obtain ⟨r, c, h0, hr, hE⟩ := REFX_walk_of_transGen' E h
    exact ⟨r, c, h0 ▸ hP, by rw [hr, h0], hE⟩
  set r := Nat.find hex with hrdef
  obtain ⟨c, hcP, hcr, hE⟩ := Nat.find_spec hex
  have hmin : ∀ r' < r, ¬ ∃ c : ℕ → α, P (c 0) ∧ c (r' + 1) = c 0 ∧
      ∀ k ≤ r', E (c k) (c (k + 1)) :=
    fun r' hr' => Nat.find_min hex hr'
  have hinj : ∀ a b, a < b → b ≤ r → c a ≠ c b := by
    intro a b hab hb heq
    apply hmin (r - (b - a)) (by omega)
    refine ⟨fun k => if k ≤ a then c k else c (k + (b - a)), ?_, ?_, ?_⟩
    · simpa using hcP
    · simp only [Nat.zero_le, if_true, show ¬ (r - (b - a) + 1 ≤ a) by omega, if_false]
      rw [show r - (b - a) + 1 + (b - a) = r + 1 by omega]; exact hcr
    · intro k hk
      by_cases hka : k < a
      · simp only [show k ≤ a by omega, show k + 1 ≤ a by omega, if_true]
        exact hE k (by omega)
      · by_cases hka' : k = a
        · subst hka'
          simp only [le_refl, if_true, show ¬ (k + 1 ≤ k) by omega, if_false]
          rw [heq, show k + 1 + (b - k) = b + 1 by omega]
          exact hE b hb
        · simp only [show ¬ k ≤ a by omega, show ¬ (k + 1 ≤ a) by omega, if_false]
          rw [show k + 1 + (b - a) = k + (b - a) + 1 by omega]
          exact hE _ (by omega)
  refine ⟨r, fun k => c k.val, ?_, by simpa using hcP, ?_⟩
  · intro a b hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
    · exact hinj a b h (by omega) hab
    · exact hinj b a h (by omega) hab.symm
  · intro k
    have := hE k.val (by omega)
    show E (c k.val) (c (finRotate (r + 1) k).val)
    rw [coe_finRotate]
    by_cases hk : k = Fin.last r
    · rw [if_pos hk]
      have hk' : k.val = r := by rw [hk]; simp
      rw [hk'] at this ⊢
      rw [hcr] at this
      exact this
    · rw [if_neg hk]
      exact this

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (s : Fin ℓ → Fin n) (g : Fin ℓ → Fin m) (t : Fin ℓ → Fin n)
    (hs_inj : Function.Injective s) (hg_inj : Function.Injective g)
    (ht_inj : Function.Injective t)
    (hs : ∀ i, IsSource v X (s i)) (hg : ∀ i, g i ∈ pool X)
    (hreach : ∀ i, Reach v X (s i) (t i))
    (hchamp : ∀ i, IsMostEnviousAgent ε v X
      (insert (g (finRotate ℓ i)) (X (s (finRotate ℓ i)))) (t i)) :
    ∃ X' : Fin n → Finset (Fin m), IsPartialAllocation X' ∧ IsAlphaEFX (1 - ε) v X' ∧
      StronglyParetoDominates ε v X' X := by
  classical
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + 1 := ⟨ℓ - 1, by omega⟩
  choose Z hZ using hchamp
  have hgX : ∀ i j, g i ∉ X j := by
    intro i j hj
    have := hg i
    simp only [pool, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion,
      not_exists] at this
    exact this j hj
  -- the augmented graph: envy edges plus champion edges `t i → s (i+1)`
  let Aug : Fin n → Fin n → Prop := fun u w =>
    Envies v X u w ∨ ∃ i, t i = u ∧ s (finRotate (L + 1) i) = w
  have hstep : ∀ i, Relation.TransGen Aug (s i) (s (finRotate (L + 1) i)) := by
    intro i
    have h1 : Relation.ReflTransGen Aug (s i) (t i) := by
      have key : ∀ a b, Relation.ReflTransGen (Envies v X) a b →
          Relation.ReflTransGen Aug a b := by
        intro a b hr
        induction hr with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hbc ih => exact ih.tail (Or.inl hbc)
      exact key _ _ (hreach i)
    exact Relation.TransGen.tail' h1 (Or.inr ⟨i, rfl, rfl⟩)
  have hrot : ∀ j (hj : j + 1 < L + 1),
      finRotate (L + 1) ⟨j, by omega⟩ = ⟨j + 1, hj⟩ := by
    intro j hj
    apply Fin.ext
    rw [coe_finRotate_of_ne_last]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hchain : ∀ j (hj : j < L + 1),
      Relation.TransGen Aug (s 0) (s (finRotate (L + 1) ⟨j, hj⟩)) := by
    intro j
    induction j with
    | zero => intro hj; exact hstep 0
    | succ j ih =>
      intro hj
      have := ih (by omega)
      rw [hrot j hj] at this
      exact this.trans (hstep _)
  have hcyc : Relation.TransGen Aug (s 0) (s 0) := by
    have := hchain L (by omega)
    rwa [show (⟨L, by omega⟩ : Fin (L + 1)) = Fin.last L from rfl, finRotate_last] at this
  obtain ⟨r, d, hdinj, hd0, hdE⟩ := REFX_simple_cycle_P Aug (IsSource v X) (hs 0) hcyc
  -- rotate along the cycle
  set σ : Equiv.Perm (Fin n) :=
    (finRotate (r + 1)).extendDomain (Equiv.ofInjective d hdinj) with hσ
  have hσd : ∀ k, σ (d k) = d (finRotate (r + 1) k) := by
    intro k
    have := Equiv.Perm.extendDomain_apply_image (finRotate (r + 1))
      (Equiv.ofInjective d hdinj) k
    simpa using this
  have hσout : ∀ j, (¬ ∃ k, d k = j) → σ j = j := by
    intro j hj
    apply Equiv.Perm.extendDomain_apply_not_subtype
    simpa [Set.mem_range] using hj
  let sp : Fin n → Prop := fun u =>
    (∃ i, t i = u ∧ s (finRotate (L + 1) i) = σ u) ∧ ∃ k, d k = u
  let X' : Fin n → Finset (Fin m) := fun u =>
    if h : sp u then Z (Classical.choose h.1) else X (σ u)
  have hX'sp : ∀ u (h : sp u), X' u = Z (Classical.choose h.1) := fun u h => dif_pos h
  have hX'n : ∀ u, ¬ sp u → X' u = X (σ u) := fun u h => dif_neg h
  have hspt : ∀ u (h : sp u), t (Classical.choose h.1) = u := fun u h =>
    (Classical.choose_spec h.1).1
  have hsps : ∀ u (h : sp u), s (finRotate (L + 1) (Classical.choose h.1)) = σ u :=
    fun u h => (Classical.choose_spec h.1).2
  have hZsub : ∀ u (h : sp u), Z (Classical.choose h.1) ⊆
      insert (g (finRotate (L + 1) (Classical.choose h.1))) (X (σ u)) := by
    intro u h
    have := (hZ (Classical.choose h.1)).1
    rwa [hsps u h] at this
  have hheavy : ∀ u (h : sp u), v u (X u) < (1 - ε) * v u (Z (Classical.choose h.1)) := by
    intro u h
    have := (hZ (Classical.choose h.1)).2.1
    unfold HeavilyEnvies at this
    rwa [hspt u h] at this
  have hge : ∀ u, v u (X u) ≤ v u (X' u) := by
    intro u
    by_cases h : sp u
    · rw [hX'sp u h]
      have h1 := hheavy u h
      have h0 : 0 ≤ v u (Z (Classical.choose h.1)) := hv.2 _ _
      nlinarith
    · rw [hX'n u h]
      by_cases hon : ∃ k, d k = u
      · obtain ⟨k, rfl⟩ := hon
        rcases hdE k with he | ⟨i, hi1, hi2⟩
        · rw [hσd]; exact he.le
        · exact absurd ⟨⟨i, hi1, by rw [hσd]; exact hi2⟩, k, rfl⟩ h
      · rw [hσout u hon]
  refine ⟨X', ?_, ?_, ⟨hge, ?_⟩⟩
  · -- disjointness
    intro u u' huu
    have hσne : σ u ≠ σ u' := fun h => huu (σ.injective h)
    have hXd : Disjoint (X (σ u)) (X (σ u')) := hX hσne
    by_cases h : sp u <;> by_cases h' : sp u'
    · rw [hX'sp u h, hX'sp u' h']
      refine Disjoint.mono (hZsub u h) (hZsub u' h') ?_
      have hii : Classical.choose h.1 ≠ Classical.choose h'.1 := by
        intro heq
        apply huu
        rw [← hspt u h, ← hspt u' h', heq]
      have hgne : g (finRotate (L + 1) (Classical.choose h.1)) ≠
          g (finRotate (L + 1) (Classical.choose h'.1)) :=
        fun he => hii ((finRotate (L + 1)).injective (hg_inj he))
      rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
      refine ⟨?_, hgX _ _, hXd⟩
      rw [Finset.mem_insert, not_or]
      exact ⟨hgne, hgX _ _⟩
    · rw [hX'sp u h, hX'n u' h']
      refine Disjoint.mono_left (hZsub u h) ?_
      rw [Finset.disjoint_insert_left]
      exact ⟨hgX _ _, hXd⟩
    · rw [hX'n u h, hX'sp u' h']
      refine Disjoint.mono_right (hZsub u' h') ?_
      rw [Finset.disjoint_insert_right]
      exact ⟨hgX _ _, hXd⟩
    · rw [hX'n u h, hX'n u' h']
      exact hXd
  · -- (1 - ε)-EFX
    intro a b x hx
    by_cases h : sp b
    · rw [hX'sp b h] at hx ⊢
      have hlt := Finset.erase_ssubset hx
      have := (hZ (Classical.choose h.1)).2.2 a
      simp only [StronglyEnvies, HeavilyEnvies, not_exists, not_and, not_lt] at this
      exact (this _ hlt).trans (hge a)
    · rw [hX'n b h] at hx ⊢
      exact (hEFX a (σ b) x hx).trans (hge a)
  · -- the predecessor of the source `d 0` improves by the factor `1 - ε`
    set k0 := (finRotate (r + 1)).symm 0 with hk0
    have hrk0 : finRotate (r + 1) k0 = 0 := by simp [hk0]
    have hsp0 : sp (d k0) := by
      rcases hdE k0 with he | ⟨i, hi1, hi2⟩
      · rw [hrk0] at he
        exact absurd he (hd0 (d k0))
      · exact ⟨⟨i, hi1, by rw [hσd]; exact hi2⟩, k0, rfl⟩
    refine ⟨d k0, ?_⟩
    rw [hX'sp _ hsp0]
    exact hheavy _ hsp0
