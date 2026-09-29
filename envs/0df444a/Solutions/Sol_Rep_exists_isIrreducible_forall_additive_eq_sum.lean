-- Prove2me | solution 1 for Rep.exists_isIrreducible_forall_additive_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9b339e4b-d4b3-5ed0-9381-005e9c36903c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_isIrreducible_forall_additive_eq_sum

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical

namespace ArtIndJH

variable {k : Type} [Field k] {G : Type} [Group G]

def Additive (φ : Rep.{0} k G → ℤ) : Prop :=
  ∀ X : ShortComplex (Rep.{0} k G), X.ShortExact → FiniteDimensional k X.X₂ → φ X.X₂ = φ X.X₁ + φ X.X₃

lemma shortExact_of {A B C : Rep.{0} k G} (f : A ⟶ B) (g : B ⟶ C)
    (hinj : Function.Injective f.hom) (hsurj : Function.Surjective g.hom)
    (hrk : LinearMap.range f.hom.toLinearMap = LinearMap.ker g.hom.toLinearMap) :
    ∃ hfg : f ≫ g = 0, (ShortComplex.mk f g hfg).ShortExact := by
  have hfg : f ≫ g = 0 := by
    ext a
    have : f.hom a ∈ LinearMap.ker g.hom.toLinearMap := by rw [← hrk]; exact ⟨a, rfl⟩
    simpa using this
  refine ⟨hfg, ?_⟩
  haveI : Mono f := (Rep.mono_iff_injective f).2 hinj
  haveI : Epi g := (Rep.epi_iff_surjective g).2 hsurj
  have hex : (ShortComplex.mk f g hfg).Exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact hrk
  exact ShortComplex.ShortExact.mk' hex inferInstance inferInstance

lemma additive_eq_zero_of_subsingleton {φ : Rep.{0} k G → ℤ} (hφ : Additive φ) (X : Rep.{0} k G)
    [FiniteDimensional k X] [Subsingleton X] : φ X = 0 := by
  obtain ⟨hfg, hX⟩ := shortExact_of (𝟙 X) (0 : X ⟶ X) (fun a b h => h) (fun x => ⟨0, Subsingleton.elim _ _⟩)
    (by ext x; simp [Subsingleton.elim x 0])
  have := hφ _ hX ‹_›
  simp only at this
  omega

lemma additive_subrep {φ : Rep.{0} k G → ℤ} (hφ : Additive φ) (X : Rep.{0} k G) [FiniteDimensional k X]
    (W : Submodule k X) (hW : ∀ g, W ≤ W.comap (X.ρ g)) :
    φ X = φ (Rep.subrepresentation X W hW) + φ (Rep.quotient X W hW) := by
  obtain ⟨hfg, hX⟩ := shortExact_of (Rep.subtype X W hW) (Rep.mkQ X W hW)
    (fun a b h => Subtype.ext h) (Submodule.mkQ_surjective W)
    (by
      show LinearMap.range W.subtype = LinearMap.ker W.mkQ
      rw [Submodule.ker_mkQ, Submodule.range_subtype])
  exact hφ _ hX ‹_›

lemma isIrreducible_subrepresentation_of_minimal (X : Rep.{0} k G) [FiniteDimensional k X]
    (W : Submodule k X) (hW : ∀ g, W ≤ W.comap (X.ρ g)) (hW0 : W ≠ ⊥)
    (hmin : ∀ U : Submodule k X, (∀ g, U ≤ U.comap (X.ρ g)) → U ≠ ⊥ → Module.finrank k W ≤ Module.finrank k U) :
    (X.ρ.subrepresentation W hW).IsIrreducible := by

  have hWnt : Nontrivial W := by
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).1 hW0
    exact ⟨⟨⟨w, hw⟩, 0, fun h => hw0 (congrArg Subtype.val h)⟩⟩
  haveI : Nontrivial (Subrepresentation (X.ρ.subrepresentation W hW)) := by
    refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have : w ∈ (⊤ : Subrepresentation (X.ρ.subrepresentation W hW)) := trivial
    rw [← h] at this
    exact hw this
  refine ⟨fun U => ?_⟩

  let U' : Submodule k X := U.toSubmodule.map W.subtype
  have hU' : ∀ g, U' ≤ U'.comap (X.ρ g) := by
    rintro g _ ⟨u, hu, rfl⟩
    refine ⟨(X.ρ.subrepresentation W hW) g u, U.apply_mem_toSubmodule g hu, ?_⟩
    rfl
  by_cases hUbot : U' = ⊥
  · left
    apply le_antisymm _ bot_le
    intro u hu
    have : W.subtype u ∈ U' := ⟨u, hu, rfl⟩
    rw [hUbot, Submodule.mem_bot] at this
    have hu0 : u = 0 := Subtype.ext this
    rw [hu0]
    exact (⊥ : Subrepresentation (X.ρ.subrepresentation W hW)).toSubmodule.zero_mem
  · right
    have hle : U' ≤ W := by
      rintro _ ⟨u, -, rfl⟩; exact u.2
    have hfin : Module.finrank k W ≤ Module.finrank k U' := hmin U' hU' hUbot
    have hUeq : U' = W := Submodule.eq_of_le_of_finrank_le hle hfin
    apply le_antisymm le_top
    intro u _
    have : W.subtype u ∈ U' := by rw [hUeq]; exact u.2
    obtain ⟨u', hu', he⟩ := this
    have : u' = u := Subtype.ext (by simpa using he)
    rw [← this]
    exact hu'

theorem exists_list (X : Rep.{0} k G) [FiniteDimensional k X] :
    ∃ L : List (Rep.{0} k G), (∀ S ∈ L, FiniteDimensional k S ∧ S.ρ.IsIrreducible) ∧
      ∀ φ : Rep.{0} k G → ℤ, Additive φ → φ X = (L.map φ).sum := by
  suffices key : ∀ (n : ℕ) (X : Rep.{0} k G) [FiniteDimensional k X], Module.finrank k X = n →
      ∃ L : List (Rep.{0} k G), (∀ S ∈ L, FiniteDimensional k S ∧ S.ρ.IsIrreducible) ∧
        ∀ φ : Rep.{0} k G → ℤ, Additive φ → φ X = (L.map φ).sum from key _ X rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ hn
    by_cases hX : Subsingleton X
    · exact ⟨[], by simp, fun φ hφ => by simp [additive_eq_zero_of_subsingleton hφ X]⟩
    · rw [not_subsingleton_iff_nontrivial] at hX

      let P : ℕ → Prop := fun m => ∃ W : Submodule k X, (∀ g, W ≤ W.comap (X.ρ g)) ∧ W ≠ ⊥ ∧ Module.finrank k W = m
      have hP : ∃ m, P m := ⟨_, ⊤, fun g => by simp, top_ne_bot, rfl⟩
      obtain ⟨W, hW, hW0, hWm⟩ := Nat.find_spec hP
      have hmin : ∀ U : Submodule k X, (∀ g, U ≤ U.comap (X.ρ g)) → U ≠ ⊥ →
          Module.finrank k W ≤ Module.finrank k U := fun U hU hU0 => by
        rw [hWm]; exact Nat.find_min' hP ⟨U, hU, hU0, rfl⟩
      have hirr := isIrreducible_subrepresentation_of_minimal X W hW hW0 hmin

      have hlt : Module.finrank k (X ⧸ W) < n := by
        have h1 := Submodule.finrank_quotient_add_finrank W
        have h2 : 0 < Module.finrank k W := by
          rw [Module.finrank_pos_iff_exists_ne_zero]
          obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).1 hW0
          exact ⟨⟨w, hw⟩, fun h => hw0 (congrArg Subtype.val h)⟩
        omega
      obtain ⟨L, hL, hLφ⟩ := ih _ hlt (Rep.quotient X W hW) rfl
      refine ⟨Rep.subrepresentation X W hW :: L, ?_, fun φ hφ => ?_⟩
      · intro S hS
        rcases List.mem_cons.1 hS with rfl | hS
        · exact ⟨inferInstanceAs (FiniteDimensional k W), hirr⟩
        · exact hL S hS
      · rw [List.map_cons, List.sum_cons, additive_subrep hφ X W hW, hLφ φ hφ]

lemma additive_iso {φ : Rep.{0} k G → ℤ} (hφ : Additive φ) {X Y : Rep.{0} k G} (e : X ≅ Y)
    [FiniteDimensional k Y] : φ X = φ Y := by
  have hinj : Function.Injective e.hom.hom := fun a b h => by
    simpa using congrArg e.inv.hom h
  have hsurj : Function.Surjective e.hom.hom := fun y => ⟨e.inv.hom y, by simp⟩
  have htop : ∀ g, (⊤ : Submodule k Y) ≤ (⊤ : Submodule k Y).comap (Y.ρ g) := fun g => by
    rw [Submodule.comap_top]
  obtain ⟨hfg, hX⟩ := shortExact_of e.hom (Rep.mkQ Y ⊤ htop) hinj (Submodule.mkQ_surjective _)
    (by
      show LinearMap.range e.hom.hom.toLinearMap = LinearMap.ker (⊤ : Submodule k Y).mkQ
      rw [Submodule.ker_mkQ, LinearMap.range_eq_top]
      exact hsurj)
  have h := hφ _ hX ‹_›
  haveI : Subsingleton (Rep.quotient Y ⊤ htop) :=
    inferInstanceAs (Subsingleton (Y ⧸ (⊤ : Submodule k Y)))
  have h0 := additive_eq_zero_of_subsingleton hφ (Rep.quotient Y ⊤ htop)
  simp only at h
  omega

lemma exists_cover (L : List (Rep.{0} k G)) :
    ∃ R : List (Rep.{0} k G), (∀ S ∈ R, S ∈ L) ∧ R.Pairwise (fun X Y => IsEmpty (X ≅ Y)) ∧
      ∀ X ∈ L, ∃ Y ∈ R, Nonempty (X ≅ Y) := by
  induction L with
  | nil => exact ⟨[], by simp, List.Pairwise.nil, by simp⟩
  | cons X L ih =>
    obtain ⟨R, hRL, hRp, hcov⟩ := ih
    by_cases h : ∃ Y ∈ R, Nonempty (X ≅ Y)
    · refine ⟨R, fun S hS => List.mem_cons_of_mem _ (hRL S hS), hRp, fun Z hZ => ?_⟩
      rcases List.mem_cons.1 hZ with rfl | hZ
      · exact h
      · exact hcov Z hZ
    · refine ⟨X :: R, fun S hS => ?_, ?_, fun Z hZ => ?_⟩
      · rcases List.mem_cons.1 hS with rfl | hS
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hRL S hS)
      · refine List.Pairwise.cons (fun Y hY => ⟨fun e => h ⟨Y, hY, ⟨e⟩⟩⟩) hRp
      · rcases List.mem_cons.1 hZ with rfl | hZ
        · exact ⟨Z, List.mem_cons_self, ⟨Iso.refl _⟩⟩
        · obtain ⟨Y, hY, e⟩ := hcov Z hZ
          exact ⟨Y, List.mem_cons_of_mem _ hY, e⟩

noncomputable def cnt (L : List (Rep.{0} k G)) (S : Rep.{0} k G) : ℕ :=
  (L.filter fun X => decide (Nonempty (X ≅ S))).length

lemma cnt_nil (S : Rep.{0} k G) : cnt ([] : List (Rep.{0} k G)) S = 0 := rfl

lemma cnt_cons (X : Rep.{0} k G) (L : List (Rep.{0} k G)) (S : Rep.{0} k G) :
    cnt (X :: L) S = cnt L S + (if Nonempty (X ≅ S) then 1 else 0) := by
  unfold cnt
  rw [List.filter_cons]
  split_ifs with h <;> simp_all

lemma sum_map_eq_sum_cnt {φ : Rep.{0} k G → ℤ} (hφ : Additive φ) {r : ℕ} (S : Fin r → Rep.{0} k G)
    (hfd : ∀ i, FiniteDimensional k (S i)) (hij : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (L : List (Rep.{0} k G)) (hcov : ∀ X ∈ L, ∃ i, Nonempty (X ≅ S i)) :
    (L.map φ).sum = ∑ i, (cnt L (S i) : ℤ) * φ (S i) := by
  induction L with
  | nil => simp [cnt_nil]
  | cons X L ih =>
    have hcovL : ∀ Y ∈ L, ∃ i, Nonempty (Y ≅ S i) := fun Y hY => hcov Y (List.mem_cons_of_mem _ hY)
    obtain ⟨i0, ⟨e0⟩⟩ := hcov X List.mem_cons_self
    rw [List.map_cons, List.sum_cons, ih hcovL]
    simp only [cnt_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, add_mul, Finset.sum_add_distrib,
      ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hfilt : (Finset.univ.filter fun i => Nonempty (X ≅ S i)) = {i0} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨e⟩; exact hij i i0 ⟨e.symm ≪≫ e0⟩
      · rintro rfl; exact ⟨e0⟩
    rw [hfilt, Finset.sum_singleton]
    haveI := hfd i0
    rw [additive_iso hφ e0]
    ring

end ArtIndJH

open ArtIndJH in
theorem solution
    {k : Type} [Field k] {G : Type} [Group G]
    (A B : Rep.{0} k G) [FiniteDimensional k A] [FiniteDimensional k B] :
    ∃ (r : ℕ) (S : Fin r → Rep.{0} k G) (a b : Fin r → ℕ),
      (∀ i, FiniteDimensional k (S i) ∧ (S i).ρ.IsIrreducible) ∧
      (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
      ∀ φ : Rep.{0} k G → ℤ,
        (∀ X : ShortComplex (Rep.{0} k G), X.ShortExact → FiniteDimensional k X.X₂ →
          φ X.X₂ = φ X.X₁ + φ X.X₃) →
        φ A = ∑ i, (a i : ℤ) * φ (S i) ∧ φ B = ∑ i, (b i : ℤ) * φ (S i) := by
  obtain ⟨LA, hLA, hLAφ⟩ := exists_list A
  obtain ⟨LB, hLB, hLBφ⟩ := exists_list B
  obtain ⟨R, hRL, hRp, hcov⟩ := exists_cover (LA ++ LB)
  refine ⟨R.length, fun i => R.get i, fun i => cnt LA (R.get i), fun i => cnt LB (R.get i), fun i => ?_, ?_, fun φ hφ => ?_⟩
  · have hi : R.get i ∈ LA ++ LB := hRL _ (List.get_mem R i)
    rcases List.mem_append.1 hi with hi | hi
    · exact hLA _ hi
    · exact hLB _ hi
  · intro i j hne
    by_contra hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact (List.pairwise_iff_get.1 hRp i j h).false hne.some
    · exact (List.pairwise_iff_get.1 hRp j i h).false hne.some.symm
  · have hfd : ∀ i, FiniteDimensional k (R.get i) := fun i => by
      have hi : R.get i ∈ LA ++ LB := hRL _ (List.get_mem R i)
      rcases List.mem_append.1 hi with hi | hi
      · exact (hLA _ hi).1
      · exact (hLB _ hi).1
    have hij : ∀ i j, Nonempty (R.get i ≅ R.get j) → i = j := by
      intro i j hne
      by_contra hij
      rcases lt_or_gt_of_ne hij with h | h
      · exact (List.pairwise_iff_get.1 hRp i j h).false hne.some
      · exact (List.pairwise_iff_get.1 hRp j i h).false hne.some.symm
    have hcov' : ∀ X ∈ LA ++ LB, ∃ i, Nonempty (X ≅ R.get i) := fun X hX => by
      obtain ⟨Y, hY, e⟩ := hcov X hX
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hY
      exact ⟨i, e⟩
    constructor
    · rw [hLAφ φ hφ]
      exact sum_map_eq_sum_cnt hφ _ hfd hij LA (fun X hX => hcov' X (List.mem_append_left _ hX))
    · rw [hLBφ φ hφ]
      exact sum_map_eq_sum_cnt hφ _ hfd hij LB (fun X hX => hcov' X (List.mem_append_right _ hX))

end S_Rep_exists_isIrreducible_forall_additive_eq_sum
end P2MW
export P2MW.S_Rep_exists_isIrreducible_forall_additive_eq_sum (solution)
