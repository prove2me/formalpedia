-- Prove2me | solution 1 for Rado.rado_defect
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:29:56.554016+00:00
-- url     : https://prove2.me/submissions/633246e6-24eb-427a-8abb-6830eca811d5

import Mathlib
import Theorems.Thm_Rado_rado_defect_le

set_option autoImplicit false

namespace Rado

open Module Submodule

section Core

variable {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V]

noncomputable def pk_rk (k : Type*) {V : Type*} [Field k] [AddCommGroup V] [Module k V] (X : Set V) : ℕ :=
  finrank k (span k X)

lemma pk_rk_mono {X Y : Set V} (hY : Y.Finite) (h : X ⊆ Y) : pk_rk k X ≤ pk_rk k Y := by
  have : FiniteDimensional k (span k Y) := FiniteDimensional.span_of_finite k hY
  exact Submodule.finrank_mono (span_mono h)

lemma pk_rk_submod {X Y : Set V} (hX : X.Finite) (hY : Y.Finite) :
    pk_rk k (X ∪ Y) + pk_rk k (X ∩ Y) ≤ pk_rk k X + pk_rk k Y := by
  have : FiniteDimensional k (span k X) := FiniteDimensional.span_of_finite k hX
  have : FiniteDimensional k (span k Y) := FiniteDimensional.span_of_finite k hY
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (span k X) (span k Y)
  have h2 : span k (X ∩ Y) ≤ (span k X ⊓ span k Y : Submodule k V) :=
    le_inf (span_mono Set.inter_subset_left) (span_mono Set.inter_subset_right)
  have h3 : finrank k (span k (X ∩ Y)) ≤ finrank k (↥(span k X ⊓ span k Y : Submodule k V)) :=
    Submodule.finrank_mono h2
  rw [pk_rk, pk_rk, pk_rk, pk_rk, span_union]
  omega

variable [Fintype ι] [DecidableEq ι]

/-- f_A(S) = |S^c| + rank of the union of the sets indexed by S -/
noncomputable def pk_f (A : ι → Set V) (S : Finset ι) : ℕ := Sᶜ.card + pk_rk k (⋃ i ∈ S, A i)

/-- the shrinking lemma, abstract in the ranks -/
lemma pk_shrink (A A' A'' : ι → Set V) (hA : ∀ i, (A i).Finite) (i₀ : ι) (x y : V) (hxy : x ≠ y)
    (hx : x ∈ A i₀) (hy : y ∈ A i₀)
    (hA' : ∀ i, i ≠ i₀ → A' i = A i) (hA'0 : A' i₀ = A i₀ \ {x})
    (hA'' : ∀ i, i ≠ i₀ → A'' i = A i) (hA''0 : A'' i₀ = A i₀ \ {y})
    (δ : ℕ) (hδ : ∀ S, δ ≤ pk_f (k := k) A S) :
    (∀ S, δ ≤ pk_f (k := k) A' S) ∨ (∀ S, δ ≤ pk_f (k := k) A'' S) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨S₁, h₁⟩, ⟨S₂, h₂⟩⟩ := hcon
  have fin : ∀ (B : ι → Set V), (∀ i, (B i).Finite) → ∀ S : Finset ι, (⋃ i ∈ S, B i).Finite := by
    intro B hB S
    exact Set.Finite.biUnion S.finite_toSet (fun i _ => hB i)
  have hA'fin : ∀ i, (A' i).Finite := by
    intro i; by_cases h : i = i₀
    · subst h; rw [hA'0]; exact (hA _).subset Set.sdiff_subset
    · rw [hA' i h]; exact hA i
  have hA''fin : ∀ i, (A'' i).Finite := by
    intro i; by_cases h : i = i₀
    · subst h; rw [hA''0]; exact (hA _).subset Set.sdiff_subset
    · rw [hA'' i h]; exact hA i
  -- i₀ ∈ S₁ and i₀ ∈ S₂
  have hi1 : i₀ ∈ S₁ := by
    by_contra hn
    have : (⋃ i ∈ S₁, A' i) = ⋃ i ∈ S₁, A i := by
      apply Set.iUnion₂_congr; intro i hi
      exact hA' i (fun h => hn (h ▸ hi))
    apply absurd h₁; unfold pk_f; rw [this]; exact not_lt.2 (hδ S₁)
  have hi2 : i₀ ∈ S₂ := by
    by_contra hn
    have : (⋃ i ∈ S₂, A'' i) = ⋃ i ∈ S₂, A i := by
      apply Set.iUnion₂_congr; intro i hi
      exact hA'' i (fun h => hn (h ▸ hi))
    apply absurd h₂; unfold pk_f; rw [this]; exact not_lt.2 (hδ S₂)
  unfold pk_f at h₁ h₂
  set X : Set V := ⋃ i ∈ S₁, A' i with hX
  set Y : Set V := ⋃ i ∈ S₂, A'' i with hY
  set T₀ : Finset ι := (S₁ ∩ S₂).erase i₀ with hT₀
  -- containments
  have hU : (⋃ i ∈ S₁ ∪ S₂, A i) ⊆ X ∪ Y := by
    intro z hz
    simp only [Set.mem_iUnion, Finset.mem_union] at hz
    obtain ⟨i, hi, hzi⟩ := hz
    by_cases hii : i = i₀
    · subst hii
      by_cases hzx : z = x
      · right; subst hzx; simp only [hY, Set.mem_iUnion]; exact ⟨i, hi2, by rw [hA''0]; exact ⟨hzi, hxy⟩⟩
      · left; simp only [hX, Set.mem_iUnion]; exact ⟨i, hi1, by rw [hA'0]; exact ⟨hzi, hzx⟩⟩
    · rcases hi with hi | hi
      · left; simp only [hX, Set.mem_iUnion]; exact ⟨i, hi, by rw [hA' i hii]; exact hzi⟩
      · right; simp only [hY, Set.mem_iUnion]; exact ⟨i, hi, by rw [hA'' i hii]; exact hzi⟩
  have hI : (⋃ i ∈ T₀, A i) ⊆ X ∩ Y := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨i, hi, hzi⟩ := hz
    rw [hT₀, Finset.mem_erase, Finset.mem_inter] at hi
    refine ⟨?_, ?_⟩
    · simp only [hX, Set.mem_iUnion]; exact ⟨i, hi.2.1, by rw [hA' i hi.1]; exact hzi⟩
    · simp only [hY, Set.mem_iUnion]; exact ⟨i, hi.2.2, by rw [hA'' i hi.1]; exact hzi⟩
  have hXfin : X.Finite := fin A' hA'fin S₁
  have hYfin : Y.Finite := fin A'' hA''fin S₂
  have s1 := pk_rk_submod (k := k) hXfin hYfin
  have m1 : pk_rk k (⋃ i ∈ S₁ ∪ S₂, A i) ≤ pk_rk k (X ∪ Y) := pk_rk_mono (hXfin.union hYfin) hU
  have m2 : pk_rk k (⋃ i ∈ T₀, A i) ≤ pk_rk k (X ∩ Y) := pk_rk_mono (hXfin.inter_of_left _) hI
  have d1 := hδ (S₁ ∪ S₂)
  have d2 := hδ T₀
  unfold pk_f at d1 d2
  -- cardinalities
  have c1 : (S₁ ∪ S₂)ᶜ.card + T₀ᶜ.card = S₁ᶜ.card + S₂ᶜ.card + 1 := by
    have hmem : i₀ ∈ S₁ ∩ S₂ := Finset.mem_inter.2 ⟨hi1, hi2⟩
    have e1 := Finset.card_union_add_card_inter S₁ S₂
    have e2 : T₀.card + 1 = (S₁ ∩ S₂).card := by
      rw [hT₀, Finset.card_erase_of_mem hmem]
      have : 0 < (S₁ ∩ S₂).card := Finset.card_pos.2 ⟨i₀, hmem⟩
      omega
    have b1 := Finset.card_le_univ S₁
    have b2 := Finset.card_le_univ S₂
    have b3 := Finset.card_le_univ (S₁ ∪ S₂)
    have b4 := Finset.card_le_univ T₀
    simp only [Finset.card_compl]
    omega
  omega

end Core

/-- Base case of Rado's induction: every `A i` has at most one element. -/
lemma pk_base {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    [DecidableEq ι] (A : ι → Set V) (hA : ∀ i, (A i).Finite) (h1 : ∀ i, (A i).ncard ≤ 1) :
    ∃ (J : Finset ι) (v : ι → V) (S : Finset ι),
      (∀ j ∈ J, v j ∈ A j) ∧ LinearIndepOn k v (J : Set ι) ∧
      J.card = Sᶜ.card + Module.finrank k (Submodule.span k (⋃ i ∈ S, A i)) := by
  classical
  let u : ι → V := fun i => if h : (A i).Nonempty then h.some else 0
  have hmem : ∀ i, (A i).Nonempty → u i ∈ A i := fun i h => by
    simp only [u, dif_pos h]; exact h.some_mem
  have hu : ∀ i (z : V), z ∈ A i → z = u i := fun i z hz =>
    (Set.ncard_le_one (hA i)).1 (h1 i) z hz (u i) (hmem i ⟨z, hz⟩)
  obtain ⟨I, hI, hmax⟩ := exists_maximal_linearIndepOn k u
  set J : Finset ι := Finset.univ.filter (fun i => i ∈ I) with hJdef
  have hJ : (J : Set ι) = I := by ext i; simp [hJdef]
  have hI' : LinearIndepOn k u (J : Set ι) := by rw [hJ]; exact hI
  have hspan : ∀ i, u i ∈ span k (u '' (J : Set ι)) := by
    intro i
    rw [hJ]
    by_cases hi : i ∈ I
    · exact subset_span ⟨i, hi, rfl⟩
    · obtain ⟨a, ha, h⟩ := hmax i hi
      have := (span k (u '' I)).smul_mem a⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
  have hnonempty : ∀ j ∈ J, (A j).Nonempty := by
    intro j hj
    by_contra hne
    have : u j = 0 := by simp only [u, dif_neg hne]
    exact hI'.ne_zero hj this
  refine ⟨J, u, Finset.univ, fun j hj => hmem j (hnonempty j hj), hI', ?_⟩
  have hspaneq : span k (⋃ i ∈ (Finset.univ : Finset ι), A i) = span k (u '' (J : Set ι)) := by
    refine le_antisymm (span_le.2 ?_) (span_mono ?_)
    · intro z hz
      obtain ⟨i, -, hzi⟩ := Set.mem_iUnion₂.1 hz
      rw [hu i z hzi]
      exact hspan i
    · rintro _ ⟨j, hj, rfl⟩
      exact Set.mem_iUnion₂.2 ⟨j, Finset.mem_univ j, hmem j (hnonempty j hj)⟩
  have hrank : finrank k (span k (u '' (J : Set ι))) = J.card := by
    have := finrank_span_eq_card hI'
    rw [← Set.image_eq_range] at this
    simpa using this
  rw [hspaneq, hrank]
  simp

/-- Rado's induction, measured by the total number of vectors. -/
lemma pk_main {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    [DecidableEq ι] :
    ∀ (n : ℕ) (A : ι → Set V), (∀ i, (A i).Finite) → ∑ i, (A i).ncard ≤ n →
      ∃ (J : Finset ι) (v : ι → V) (S : Finset ι),
        (∀ j ∈ J, v j ∈ A j) ∧ LinearIndepOn k v (J : Set ι) ∧
        J.card = Sᶜ.card + Module.finrank k (Submodule.span k (⋃ i ∈ S, A i)) := by
  intro n
  induction n with
  | zero =>
    intro A hA hn
    refine pk_base A hA (fun i => ?_)
    have : (A i).ncard ≤ ∑ j, (A j).ncard :=
      Finset.single_le_sum (f := fun j => (A j).ncard) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  | succ n ih =>
    intro A hA hn
    by_cases hbase : ∀ i, (A i).ncard ≤ 1
    · exact pk_base A hA hbase
    rw [not_forall] at hbase
    obtain ⟨i₀, hi₀⟩ := hbase
    rw [not_le] at hi₀
    obtain ⟨x, hx, y, hy, hxy⟩ := (Set.one_lt_ncard (hA i₀)).1 hi₀
    -- the two shrunken families
    have hshr : ∀ z ∈ A i₀,
        (∀ i, (Function.update A i₀ (A i₀ \ {z}) i).Finite) ∧
        ∑ i, (Function.update A i₀ (A i₀ \ {z}) i).ncard ≤ n := by
      intro z hz
      have hfin : ∀ i, (Function.update A i₀ (A i₀ \ {z}) i).Finite := by
        intro i
        by_cases hi : i = i₀
        · subst hi; rw [Function.update_self]; exact (hA _).subset Set.sdiff_subset
        · rw [Function.update_of_ne hi]; exact hA i
      refine ⟨hfin, ?_⟩
      have e1 := Finset.add_sum_erase Finset.univ
        (fun i => (Function.update A i₀ (A i₀ \ {z}) i).ncard) (Finset.mem_univ i₀)
      have e2 := Finset.add_sum_erase Finset.univ (fun i => (A i).ncard) (Finset.mem_univ i₀)
      have e3 : ∑ i ∈ Finset.univ.erase i₀, (Function.update A i₀ (A i₀ \ {z}) i).ncard =
          ∑ i ∈ Finset.univ.erase i₀, (A i).ncard :=
        Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      have e4 : (A i₀ \ {z}).ncard = (A i₀).ncard - 1 := Set.ncard_sdiff_singleton_of_mem hz
      simp only [Function.update_self] at e1
      omega
    obtain ⟨hfin', hsum'⟩ := hshr x hx
    obtain ⟨hfin'', hsum''⟩ := hshr y hy
    obtain ⟨S₀, -, hS₀⟩ := Finset.exists_min_image Finset.univ (pk_f (k := k) A) ⟨∅, Finset.mem_univ _⟩
    have hδ : ∀ S, pk_f (k := k) A S₀ ≤ pk_f (k := k) A S := fun S => hS₀ S (Finset.mem_univ S)
    have hshrink := pk_shrink (k := k) A (Function.update A i₀ (A i₀ \ {x}))
      (Function.update A i₀ (A i₀ \ {y})) hA i₀ x y hxy hx hy
      (fun i hi => Function.update_of_ne hi _ _) (Function.update_self ..)
      (fun i hi => Function.update_of_ne hi _ _) (Function.update_self ..) _ hδ
    -- a tight transversal of a shrunken family is tight for `A`
    have hlift : ∀ z (B : ι → Set V), B = Function.update A i₀ (A i₀ \ {z}) →
        (∀ i, (B i).Finite) → ∑ i, (B i).ncard ≤ n →
        (∀ S, pk_f (k := k) A S₀ ≤ pk_f (k := k) B S) →
        ∃ (J : Finset ι) (v : ι → V) (S : Finset ι),
          (∀ j ∈ J, v j ∈ A j) ∧ LinearIndepOn k v (J : Set ι) ∧
          J.card = Sᶜ.card + Module.finrank k (Submodule.span k (⋃ i ∈ S, A i)) := by
      intro z B hB hBfin hBsum hBS
      obtain ⟨J, v, S, hv, hind, hcard⟩ := ih B hBfin hBsum
      have hsub : ∀ i, B i ⊆ A i := by
        intro i
        by_cases hi : i = i₀
        · subst hi; rw [hB, Function.update_self]; exact Set.sdiff_subset
        · rw [hB, Function.update_of_ne hi]
      have hv' : ∀ j ∈ J, v j ∈ A j := fun j hj => hsub j (hv j hj)
      have hle := rado_defect_le A hA J v hv' hind S₀
      have hge := hBS S
      unfold pk_f pk_rk at hge hδ
      refine ⟨J, v, S₀, hv', hind, ?_⟩
      omega
    rcases hshrink with h | h
    · exact hlift x _ rfl hfin' hsum' h
    · exact hlift y _ rfl hfin'' hsum'' h

end Rado

open Rado

theorem solution {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    [DecidableEq ι] (A : ι → Set V) (hA : ∀ i, (A i).Finite) :
    ∃ (J : Finset ι) (v : ι → V) (S : Finset ι),
      (∀ j ∈ J, v j ∈ A j) ∧ LinearIndepOn k v (J : Set ι) ∧
      J.card = Sᶜ.card + Module.finrank k (Submodule.span k (⋃ i ∈ S, A i)) :=
  pk_main _ A hA le_rfl

#print axioms solution
