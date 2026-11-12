-- Prove2me | solution 1 for WeakEpsNets.LowerBound.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:01:32.803031+00:00
-- url     : https://prove2.me/submissions/cb46d000-b9c1-4734-b3f1-9fa2ed6890f7

import Mathlib
import Definitions.Def_WeakEpsNets_LowerBound_Parameters
import Definitions.Def_WeakEpsNets_LowerBound_Construction
import Definitions.Def_WeakEpsNets_LowerBound_Nets
import Theorems.Thm_WeakEpsNets_LowerBound_lemma_1

section
set_option autoImplicit false

namespace WeakEpsNets.Dev

open WeakEpsNets.LowerBound

/-- The `(s+1) × (s+1)` symmetric matrix of the quadratic coordinates of `z`
(`Z i j = z_{min(i,j), max(i,j)}`). -/
noncomputable def Zmat (s : ℕ) (z : LiftSpace s) : Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ :=
  fun i j => if h : i ≤ j then z (Sum.inr ⟨(i, j), h⟩) else z (Sum.inr ⟨(j, i), le_of_not_ge h⟩)

/-- `F_z = (ker Z)^⊥`. -/
def Fspace (s : ℕ) (z : LiftSpace s) : Set (Fin (s + 1) → ℝ) :=
  {p | ∀ u : Fin (s + 1) → ℝ, (Zmat s z).mulVec u = 0 → u ⬝ᵥ p = 0}

/-- `h` is compatible with `z`: some member of the hull family of `h` contains `z`. -/
def Compat (s q : ℕ) (z : LiftSpace s) (h : HyperplaneIndex s q) : Prop :=
  ∃ C ∈ hullFamily s q h, z ∈ C

/-- Grid points of the block of `h` lying in `F_z`. -/
noncomputable def blockF (s q : ℕ) (z : LiftSpace s) (h : HyperplaneIndex s q) :
    Finset (Fin (s + 1) → ℝ) := by
  classical
  exact (block s q h).filter (fun p => p ∈ Fspace s z)

end WeakEpsNets.Dev
end

section
set_option autoImplicit false

namespace WeakEpsNets.Dev

open WeakEpsNets.LowerBound

/-- Convex-combination representation of `z ∈ conv φ(S0)` by points of the block,
with the extra information that each used point lifts into `C`. -/
theorem rep_sub (s q : ℕ) (z : LiftSpace s) (h : HyperplaneIndex s q) (C : Set (LiftSpace s))
    (hC : C ∈ hullFamily s q h) (hz : z ∈ C) :
    ∃ (S : Finset (Fin (s + 1) → ℝ)) (w : (Fin (s + 1) → ℝ) → ℝ),
      S ⊆ block s q h ∧ (∀ p ∈ S, 0 < w p) ∧ ∑ p ∈ S, w p = 1 ∧
      (∀ i : LiftIndex s, ∑ p ∈ S, w p * phi s p i = z i) ∧ (∀ p ∈ S, phi s p ∈ C) := by
  classical
  obtain ⟨S0, hS0, -, rfl⟩ := hC
  obtain ⟨w, hw0, hw1, hwz⟩ := Finset.mem_convexHull'.mp hz
  set T : Finset (LiftSpace s) := S0.image (phi s) with hT
  have hg : ∀ y ∈ T, ∃ p ∈ S0, phi s p = y := by
    intro y hy; simpa [hT] using hy
  choose! g hgS hgp using hg
  set Tf := T.filter (fun y => 0 < w y) with hTf
  have hginj : Set.InjOn g (Tf : Set (LiftSpace s)) := by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).1
    have hb' := (Finset.mem_filter.mp hb).1
    rw [← hgp a ha', ← hgp b hb', hab]
  have hsum : ∀ f : LiftSpace s → ℝ, (∑ y ∈ T, w y * f y) = ∑ y ∈ Tf, w y * f y := by
    intro f
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro y hy hn
    have : ¬ 0 < w y := fun h' => hn (Finset.mem_filter.mpr ⟨hy, h'⟩)
    have : w y = 0 := le_antisymm (not_lt.mp this) (hw0 y hy)
    simp [this]
  refine ⟨Tf.image g, fun p => w (phi s p), ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
    exact hS0 (hgS y (Finset.mem_filter.mp hy).1)
  · intro p hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
    show 0 < w (phi s (g y))
    rw [hgp y (Finset.mem_filter.mp hy).1]
    exact (Finset.mem_filter.mp hy).2
  · rw [Finset.sum_image hginj]
    have := hsum (fun _ => 1)
    simp only [mul_one] at this
    rw [← hw1, this]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hgp y (Finset.mem_filter.mp hy).1]
  · intro i
    rw [Finset.sum_image hginj]
    have e := congrFun hwz i
    have := hsum (fun y => y i)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e
    rw [← e, this]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp only
    rw [hgp y (Finset.mem_filter.mp hy).1]
  · intro p hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
    rw [hgp y (Finset.mem_filter.mp hy).1]
    exact subset_convexHull ℝ _ (by simpa [hT] using (Finset.mem_filter.mp hy).1)

/-- Convex-combination representation of `z ∈ conv φ(S0)` by points of the block. -/
theorem rep (s q : ℕ) (z : LiftSpace s) (h : HyperplaneIndex s q) (C : Set (LiftSpace s))
    (hC : C ∈ hullFamily s q h) (hz : z ∈ C) :
    ∃ (S : Finset (Fin (s + 1) → ℝ)) (w : (Fin (s + 1) → ℝ) → ℝ),
      S ⊆ block s q h ∧ (∀ p ∈ S, 0 < w p) ∧ ∑ p ∈ S, w p = 1 ∧
      ∀ i : LiftIndex s, ∑ p ∈ S, w p * phi s p i = z i := by
  obtain ⟨S, w, h1, h2, h3, h4, -⟩ := rep_sub s q z h C hC hz
  exact ⟨S, w, h1, h2, h3, h4⟩

end WeakEpsNets.Dev
end

section
set_option autoImplicit false

namespace WeakEpsNets.Dev

open WeakEpsNets.LowerBound

theorem Zmat_rep (s : ℕ) (z : LiftSpace s) (S : Finset (Fin (s + 1) → ℝ))
    (w : (Fin (s + 1) → ℝ) → ℝ)
    (hcoord : ∀ i : LiftIndex s, ∑ p ∈ S, w p * phi s p i = z i) (i j : Fin (s + 1)) :
    Zmat s z i j = ∑ p ∈ S, w p * (p i * p j) := by
  unfold Zmat
  split_ifs with hij
  · rw [← hcoord (Sum.inr ⟨(i, j), hij⟩)]
    rfl
  · rw [← hcoord (Sum.inr ⟨(j, i), le_of_not_ge hij⟩)]
    apply Finset.sum_congr rfl
    intro p _
    simp only [phi]
    ring

theorem quad_form_rep (s : ℕ) (z : LiftSpace s) (S : Finset (Fin (s + 1) → ℝ))
    (w : (Fin (s + 1) → ℝ) → ℝ)
    (hcoord : ∀ i : LiftIndex s, ∑ p ∈ S, w p * phi s p i = z i)
    (u v : Fin (s + 1) → ℝ) :
    u ⬝ᵥ (Zmat s z).mulVec v = ∑ p ∈ S, w p * ((u ⬝ᵥ p) * (v ⬝ᵥ p)) := by
  simp only [dotProduct, Matrix.mulVec, Zmat_rep s z S w hcoord, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem piercing (s q : ℕ) (z : LiftSpace s) (h : HyperplaneIndex s q) (_hc : Compat s q z h)
    (C : Set (LiftSpace s)) (hC : C ∈ hullFamily s q h) (hz : z ∈ C) :
    ∃ p ∈ blockF s q z h, phi s p ∈ C := by
  classical
  obtain ⟨S, w, hSb, hw, hw1, hcoord, hSC⟩ := rep_sub s q z h C hC hz
  have hne : S.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    simp [hn] at hw1
  obtain ⟨p, hp⟩ := hne
  refine ⟨p, ?_, hSC p hp⟩
  unfold blockF
  rw [Finset.mem_filter]
  refine ⟨hSb hp, ?_⟩
  intro u hu
  have hq := quad_form_rep s z S w hcoord u u
  rw [hu, dotProduct_zero] at hq
  have hnn : ∀ r ∈ S, 0 ≤ w r * ((u ⬝ᵥ r) * (u ⬝ᵥ r)) := fun r hr =>
    mul_nonneg (hw r hr).le (mul_self_nonneg _)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hq.symm p hp
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 (hw p hp).ne'
  · exact mul_self_eq_zero.mp h0

end WeakEpsNets.Dev
end

section
set_option autoImplicit false

namespace WeakEpsNets.Dev.Latt

open Module

theorem pivot_exists (n : ℕ) (U : Submodule ℝ (Fin n → ℝ)) :
    ∃ J : Finset (Fin n), J.card ≤ finrank ℝ U ∧
      ∀ u ∈ U, (∀ j ∈ J, u j = 0) → u = 0 := by
  classical
  let v : Fin n → Dual ℝ U := fun i => (LinearMap.proj i).comp U.subtype
  obtain ⟨κ, a, hainj, hspan, hli⟩ := exists_linearIndependent' ℝ v
  have : Finite κ := hli.finite
  let _inst : Fintype κ := Fintype.ofFinite κ
  refine ⟨Finset.univ.image a, ?_, ?_⟩
  · calc (Finset.univ.image a).card ≤ (Finset.univ : Finset κ).card := Finset.card_image_le
      _ = Fintype.card κ := Finset.card_univ
      _ ≤ finrank ℝ (Dual ℝ U) := hli.fintype_card_le_finrank
      _ = finrank ℝ U := Subspace.dual_finrank_eq
  · intro u hu hz
    have h1 : ∀ k : κ, (v (a k)) ⟨u, hu⟩ = 0 := fun k => hz _ (Finset.mem_image_of_mem a (Finset.mem_univ k))
    have h2 : ∀ f ∈ Submodule.span ℝ (Set.range v), f ⟨u, hu⟩ = 0 := by
      intro f hf
      rw [← hspan] at hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact h1 k
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul c x _ hx => simp [hx]
    funext i
    simpa [v] using h2 (v i) (Submodule.subset_span ⟨i, rfl⟩)

theorem box_card_le (n q : ℕ) (U : Submodule ℝ (Fin n → ℝ)) (t0 : Fin n → ℝ)
    (T : Finset (Fin n → ℝ))
    (hbox : ∀ t ∈ T, ∀ i, ∃ k : ℕ, 1 ≤ k ∧ k ≤ q ∧ t i = (k : ℝ))
    (hmem : ∀ t ∈ T, t - t0 ∈ U) :
    T.card ≤ q ^ Module.finrank ℝ U := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (Fin 0 → ℝ) := inferInstance
    have h0 : finrank ℝ U = 0 := finrank_zero_of_subsingleton
    rw [h0]
    simpa using Finset.card_le_one_of_subsingleton T
  rcases T.eq_empty_or_nonempty with rfl | ⟨t1, ht1⟩
  · simp
  have hq : 1 ≤ q := by
    obtain ⟨k, hk1, hkq, _⟩ := hbox t1 ht1 ⟨0, hn⟩
    omega
  obtain ⟨J, hJ, hinj⟩ := pivot_exists n U
  let f : (Fin n → ℝ) → (J → ℕ) := fun t j => ⌊t j⌋₊
  have hmaps : ∀ t ∈ T, f t ∈ Fintype.piFinset (fun _ : J => Finset.Icc 1 q) := by
    intro t ht
    rw [Fintype.mem_piFinset]
    intro j
    obtain ⟨k, hk1, hkq, hk⟩ := hbox t ht j
    simp [f, hk, Finset.mem_Icc, hk1, hkq]
  have hinjOn : Set.InjOn f T := by
    intro t ht t' ht' h
    have h1 : t - t' ∈ U := by
      have := U.sub_mem (hmem t ht) (hmem t' ht')
      simpa using this
    have h2 : t - t' = 0 := by
      apply hinj _ h1
      intro j hj
      obtain ⟨k, _, _, hk⟩ := hbox t ht j
      obtain ⟨k', _, _, hk'⟩ := hbox t' ht' j
      have := congrFun h ⟨j, hj⟩
      simp only [f, hk, hk', Nat.floor_natCast] at this
      simp [hk, hk', this]
    exact sub_eq_zero.mp h2
  calc T.card ≤ (Fintype.piFinset (fun _ : J => Finset.Icc 1 q)).card :=
        Finset.card_le_card_of_injOn f hmaps hinjOn
    _ = q ^ J.card := by simp
    _ ≤ q ^ finrank ℝ U := Nat.pow_le_pow_right hq hJ

/-- vectors orthogonal to every element of `S` -/
def orth (s : ℕ) (S : Set (Fin s → ℝ)) : Submodule ℝ (Fin s → ℝ) where
  carrier := {v | ∀ u ∈ S, v ⬝ᵥ u = 0}
  zero_mem' := by intro u _; simp
  add_mem' := by
    intro a b ha hb u hu
    simp [add_dotProduct, ha u hu, hb u hu]
  smul_mem' := by
    intro c a ha u hu
    simp [smul_dotProduct, ha u hu]

theorem orth_span (s : ℕ) (S : Set (Fin s → ℝ)) (v : Fin s → ℝ) (hv : v ∈ orth s S)
    (u : Fin s → ℝ) (hu : u ∈ Submodule.span ℝ S) : v ⬝ᵥ u = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx => exact hv x hx
  | zero => simp
  | add x y _ _ hx hy => simp [dotProduct_add, hx, hy]
  | smul c x _ hx => simp [dotProduct_smul, hx]

theorem dim_le (s : ℕ) (S : Set (Fin s → ℝ)) :
    finrank ℝ (Submodule.span ℝ S) + finrank ℝ (orth s S) ≤ s := by
  have hdisj : Submodule.span ℝ S ⊓ orth s S = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have h := orth_span s S u hu.2 u hu.1
    have : u = 0 := dotProduct_self_eq_zero.mp h
    simp [this]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span ℝ S) (orth s S)
  rw [hdisj] at h
  simp only [finrank_bot, add_zero] at h
  have h2 := Submodule.finrank_le (Submodule.span ℝ S ⊔ orth s S)
  simp at h2
  omega

theorem incidence_card_le (s q : ℕ) (X A : Finset (Fin s → ℝ)) (y c : (Fin s → ℝ) → ℝ)
    (hX : ∀ x ∈ X, ∀ i, ∃ k : ℕ, 1 ≤ k ∧ k ≤ q ∧ x i = (k : ℝ))
    (hA : ∀ a ∈ A, ∀ i, ∃ k : ℕ, 1 ≤ k ∧ k ≤ q ∧ a i = (k : ℝ))
    (hinc : ∀ x ∈ X, ∀ a ∈ A, a ⬝ᵥ x + c a = y x) :
    X.card * A.card ≤ q ^ s := by
  rcases X.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · simp
  rcases A.eq_empty_or_nonempty with rfl | ⟨a0, ha0⟩
  · simp
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have h1 := Finset.card_le_one_of_subsingleton X
    have h2 := Finset.card_le_one_of_subsingleton A
    simpa using Nat.mul_le_mul h1 h2
  let S : Set (Fin s → ℝ) := (fun x => x - x0) '' (X : Set (Fin s → ℝ))
  have hperp : ∀ x ∈ X, ∀ a ∈ A, (a - a0) ⬝ᵥ (x - x0) = 0 := by
    intro x hx a ha
    have e1 := hinc x hx a ha
    have e2 := hinc x hx a0 ha0
    have e3 := hinc x0 hx0 a ha
    have e4 := hinc x0 hx0 a0 ha0
    simp only [sub_dotProduct, dotProduct_sub]
    linarith
  have h1 : X.card ≤ q ^ finrank ℝ (Submodule.span ℝ S) := by
    apply box_card_le s q _ x0 X hX
    intro t ht
    exact Submodule.subset_span ⟨t, ht, rfl⟩
  have h2 : A.card ≤ q ^ finrank ℝ (orth s S) := by
    apply box_card_le s q _ a0 A hA
    intro a ha u hu
    obtain ⟨x, hx, rfl⟩ := hu
    exact hperp x hx a ha
  have hq : 1 ≤ q := by
    obtain ⟨k, hk1, hkq, _⟩ := hX x0 hx0 ⟨0, hs⟩
    omega
  calc X.card * A.card ≤ q ^ finrank ℝ (Submodule.span ℝ S) * q ^ finrank ℝ (orth s S) :=
        Nat.mul_le_mul h1 h2
    _ = q ^ (finrank ℝ (Submodule.span ℝ S) + finrank ℝ (orth s S)) := (pow_add _ _ _).symm
    _ ≤ q ^ s := Nat.pow_le_pow_right hq (dim_le s S)

end WeakEpsNets.Dev.Latt
end

section
set_option autoImplicit false

namespace WeakEpsNets.Dev.Core1

open WeakEpsNets.LowerBound WeakEpsNets.Dev

/-- normal vector `u_h = (-a_1, ..., -a_s, 1)` -/
noncomputable def uh (s q : ℕ) (h : HyperplaneIndex s q) : Fin (s + 1) → ℝ :=
  fun i => if hi : i.val < s then -(((h.1 ⟨i.val, hi⟩).val + 1 : ℕ) : ℝ) else 1

/-- the right-hand side `c_h = b + tau` -/
noncomputable def ch (s q : ℕ) (h : HyperplaneIndex s q) : ℝ :=
  ((h.2.val + 1 : ℕ) : ℝ) + tau q

lemma ch_pos (s q : ℕ) (hq : 2 ≤ q) (h : HyperplaneIndex s q) : 0 < ch s q h := by
  unfold ch tau
  have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  positivity

lemma uh_dot (s q : ℕ) (h : HyperplaneIndex s q) (p : Fin (s + 1) → ℝ) :
    uh s q h ⬝ᵥ p = p (Fin.last s) - ∑ i : Fin s, (((h.1 i).val + 1 : ℕ) : ℝ) * p i.castSucc := by
  rw [dotProduct, Fin.sum_univ_castSucc]
  have h1 : ∀ i : Fin s, uh s q h i.castSucc * p i.castSucc =
      -((((h.1 i).val + 1 : ℕ) : ℝ) * p i.castSucc) := by
    intro i; simp [uh]; ring
  have h2 : uh s q h (Fin.last s) = 1 := by simp [uh]
  simp only [h1, h2, Finset.sum_neg_distrib]
  ring

lemma mem_hyperplane_iff (s q : ℕ) (h : HyperplaneIndex s q) (p : Fin (s + 1) → ℝ) :
    p ∈ hyperplane s q h ↔ uh s q h ⬝ᵥ p = ch s q h := by
  rw [uh_dot]
  unfold hyperplane ch
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro H <;> linarith

/-- unit vector -/
def ev1 (s : ℕ) (i : Fin (s + 1)) : Fin (s + 1) → ℝ := fun j => if i = j then 1 else 0

lemma ev1_dot (s : ℕ) (i : Fin (s + 1)) (p : Fin (s + 1) → ℝ) : ev1 s i ⬝ᵥ p = p i := by
  simp [ev1, dotProduct]

lemma Zmat_eq (s : ℕ) (z : LiftSpace s) (S : Finset (Fin (s + 1) → ℝ)) (w : (Fin (s + 1) → ℝ) → ℝ)
    (hz : ∀ i : LiftIndex s, ∑ p ∈ S, w p * phi s p i = z i) (i j : Fin (s + 1)) :
    Zmat s z i j = ∑ p ∈ S, w p * (p i * p j) := by
  unfold Zmat
  by_cases hij : i ≤ j
  · simp only [hij, dite_true]
    rw [← hz]; simp [phi]
  · simp only [hij, dite_false]
    rw [← hz]; simp [phi]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring

lemma gram_eq (s : ℕ) (z : LiftSpace s) (S : Finset (Fin (s + 1) → ℝ)) (w : (Fin (s + 1) → ℝ) → ℝ)
    (hz : ∀ i : LiftIndex s, ∑ p ∈ S, w p * phi s p i = z i) (u v : Fin (s + 1) → ℝ) :
    u ⬝ᵥ (Zmat s z).mulVec v = ∑ p ∈ S, w p * ((u ⬝ᵥ p) * (v ⬝ᵥ p)) := by
  simp only [dotProduct, Matrix.mulVec, Zmat_eq s z S w hz, Finset.mul_sum, Finset.sum_mul]
  have e1 : ∀ x : Fin (s + 1), ∑ x_1 : Fin (s + 1), ∑ i ∈ S, u x * (w i * (i x * i x_1) * v x_1) =
      ∑ i ∈ S, ∑ x_1 : Fin (s + 1), u x * (w i * (i x * i x_1) * v x_1) :=
    fun x => Finset.sum_comm
  have e2 : ∀ x ∈ S, ∑ x_1 : Fin (s + 1), ∑ i : Fin (s + 1), w x * (u i * x i * (v x_1 * x x_1)) =
      ∑ i : Fin (s + 1), ∑ x_1 : Fin (s + 1), w x * (u i * x i * (v x_1 * x x_1)) :=
    fun x _ => Finset.sum_comm
  simp only [e1]
  rw [Finset.sum_comm, Finset.sum_congr rfl e2]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring


lemma facts (s q : ℕ) (hq : 2 ≤ q) (z : LiftSpace s) (h : HyperplaneIndex s q)
    (hc : Compat s q z h) :
    uh s q h ⬝ᵥ (Zmat s z).mulVec (uh s q h) = ch s q h ^ 2 ∧
    ∀ j : Fin (s - 1), ev1 s ⟨j.val, by omega⟩ ⬝ᵥ (Zmat s z).mulVec (uh s q h)
      = ch s q h * z (Sum.inl j) := by
  obtain ⟨C, hC, hzC⟩ := hc
  obtain ⟨S, w, hS, hw, hw1, hz⟩ := rep s q z h C hC hzC
  have hu : ∀ p ∈ S, uh s q h ⬝ᵥ p = ch s q h := by
    intro p hp
    classical
    have := hS hp
    unfold block at this
    rw [Finset.mem_filter] at this
    exact (mem_hyperplane_iff s q h p).1 this.2
  refine ⟨?_, ?_⟩
  · rw [gram_eq s z S w hz]
    rw [Finset.sum_congr rfl (g := fun p => w p * (ch s q h * ch s q h))
      (fun p hp => by rw [hu p hp])]
    rw [← Finset.sum_mul, hw1]; ring
  · intro j
    rw [gram_eq s z S w hz, ← hz (Sum.inl j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hu p hp, ev1_dot]
    simp [phi]
    ring

lemma gramE (s : ℕ) (z : LiftSpace s) (S : Finset (Fin (s + 1) → ℝ)) (w : (Fin (s + 1) → ℝ) → ℝ)
    (hw : ∀ p ∈ S, 0 < w p)
    (hz : ∀ i : LiftIndex s, ∑ p ∈ S, w p * phi s p i = z i) :
    ∃ ev : (Fin (s + 1) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ S,
      ∀ u v, inner ℝ (ev u) (ev v) = u ⬝ᵥ (Zmat s z).mulVec v := by
  refine ⟨{ toFun := fun u => WithLp.toLp 2 (fun p : S => Real.sqrt (w p) * (u ⬝ᵥ (p : Fin (s + 1) → ℝ)))
            map_add' := ?_
            map_smul' := ?_ }, ?_⟩
  · intro u v
    ext p
    simp [add_dotProduct]; ring
  · intro c u
    ext p
    simp [smul_dotProduct]; ring
  · intro u v
    rw [gram_eq s z S w hz]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply]
    rw [← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun p _ => ?_
    have := hw p p.2
    have h2 := Real.mul_self_sqrt this.le
    simp
    linear_combination (u ⬝ᵥ (p : Fin (s + 1) → ℝ)) * (v ⬝ᵥ (p : Fin (s + 1) → ℝ)) * h2

end WeakEpsNets.Dev.Core1
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WeakEpsNets.Dev.Core2

open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type}

lemma eq_zero_of_mem_span (f : ι → E) (x : E) (hx : x ∈ Submodule.span ℝ (Set.range f))
    (h : ∀ i, ⟪f i, x⟫ = 0) : x = 0 := by
  have key : ∀ y ∈ Submodule.span ℝ (Set.range f), ⟪y, x⟫ = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h i
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb]; simp
    | smul c a _ ha => rw [real_inner_smul_left, ha]; simp
  have := key x hx
  simpa using this

lemma inner_proj_eq (W : Submodule ℝ E) (v w : E) (hw : w ∈ W) :
    ⟪w, W.starProjection v⟫ = ⟪w, v⟫ := by
  have h := Submodule.starProjection_inner_eq_zero (K := W) v w hw
  rw [inner_sub_left] at h
  have a := real_inner_comm w (W.starProjection v)
  have b := real_inner_comm w v
  linarith

lemma proj_unique (f : ι → E) (v v' : E) (h : ∀ i, ⟪f i, v⟫ = ⟪f i, v'⟫) :
    (Submodule.span ℝ (Set.range f)).starProjection v =
      (Submodule.span ℝ (Set.range f)).starProjection v' := by
  set W := Submodule.span ℝ (Set.range f)
  have hmem : ∀ i, f i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hd : W.starProjection v - W.starProjection v' ∈ W :=
    W.sub_mem (Submodule.starProjection_apply_mem _ _) (Submodule.starProjection_apply_mem _ _)
  have := eq_zero_of_mem_span f _ hd (fun i => by
    rw [inner_sub_right, inner_proj_eq W v _ (hmem i), inner_proj_eq W v' _ (hmem i), h i]; simp)
  exact sub_eq_zero.1 this

lemma norm_sq_sub_proj (W : Submodule ℝ E) (v : E) :
    ‖v - W.starProjection v‖ ^ 2 = ‖v‖ ^ 2 - ‖W.starProjection v‖ ^ 2 := by
  have h0 : ⟪v - W.starProjection v, W.starProjection v⟫ = 0 :=
    Submodule.starProjection_inner_eq_zero v _ (Submodule.starProjection_apply_mem _ _)
  have := norm_add_sq_real (v - W.starProjection v) (W.starProjection v)
  rw [h0] at this
  simp at this
  linarith

end WeakEpsNets.Dev.Core2
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace WeakEpsNets.Dev.Core3

open WeakEpsNets.LowerBound WeakEpsNets.Dev WeakEpsNets.Dev.Core1 WeakEpsNets.Dev.Core2
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- the known linear directions inside `E` -/
noncomputable def fW (s : ℕ) (ev : (Fin (s + 1) → ℝ) →ₗ[ℝ] E) (j : Fin (s - 1)) : E :=
  ev (ev1 s ⟨j.val, by omega⟩)

noncomputable def WW (s : ℕ) (ev : (Fin (s + 1) → ℝ) →ₗ[ℝ] E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fW s ev))

noncomputable def vh (s q : ℕ) (ev : (Fin (s + 1) → ℝ) →ₗ[ℝ] E) (h : HyperplaneIndex s q) : E :=
  (ch s q h)⁻¹ • ev (uh s q h)

noncomputable def yh (s q : ℕ) (ev : (Fin (s + 1) → ℝ) →ₗ[ℝ] E) (h : HyperplaneIndex s q) : E :=
  vh s q ev h - (WW s ev).starProjection (vh s q ev h)

section
variable (s q : ℕ) (hq : 2 ≤ q) (z : LiftSpace s) (ev : (Fin (s + 1) → ℝ) →ₗ[ℝ] E)
  (hev : ∀ u v, ⟪ev u, ev v⟫ = u ⬝ᵥ (Zmat s z).mulVec v)
include hq hev

lemma inner_fW_vh (h : HyperplaneIndex s q) (hc : Compat s q z h) (j : Fin (s - 1)) :
    ⟪fW s ev j, vh s q ev h⟫ = z (Sum.inl j) := by
  have hpos := ch_pos s q hq h
  have := (facts s q hq z h hc).2 j
  unfold fW vh
  rw [real_inner_smul_right, hev, this]
  field_simp

lemma norm_vh (h : HyperplaneIndex s q) (hc : Compat s q z h) : ‖vh s q ev h‖ ^ 2 = 1 := by
  have hpos := ch_pos s q hq h
  have := (facts s q hq z h hc).1
  rw [← real_inner_self_eq_norm_sq]
  unfold vh
  rw [real_inner_smul_left, real_inner_smul_right, hev, this]
  field_simp

lemma proj_vh_eq (h h' : HyperplaneIndex s q) (hc : Compat s q z h) (hc' : Compat s q z h') :
    (WW s ev).starProjection (vh s q ev h) = (WW s ev).starProjection (vh s q ev h') :=
  proj_unique (fW s ev) _ _ (fun j => by
    rw [inner_fW_vh s q hq z ev hev h hc, inner_fW_vh s q hq z ev hev h' hc'])

lemma norm_yh_eq (h h' : HyperplaneIndex s q) (hc : Compat s q z h) (hc' : Compat s q z h') :
    ‖yh s q ev h‖ ^ 2 = ‖yh s q ev h'‖ ^ 2 := by
  unfold yh
  rw [norm_sq_sub_proj, norm_sq_sub_proj, norm_vh s q hq z ev hev h hc,
    norm_vh s q hq z ev hev h' hc', proj_vh_eq s q hq z ev hev h h' hc hc']

lemma vh_eq_of_yh_eq (h h' : HyperplaneIndex s q) (hc : Compat s q z h) (hc' : Compat s q z h')
    (hy : yh s q ev h = yh s q ev h') : vh s q ev h = vh s q ev h' := by
  have e1 : vh s q ev h = yh s q ev h + (WW s ev).starProjection (vh s q ev h) := by
    unfold yh; abel
  have e2 : vh s q ev h' = yh s q ev h' + (WW s ev).starProjection (vh s q ev h') := by
    unfold yh; abel
  rw [e1, e2, hy, proj_vh_eq s q hq z ev hev h h' hc hc']

end


noncomputable def Ek (s : ℕ) (ev : (Fin (s + 1) → ℝ) →ₗ[ℝ] E) (i : Fin (s + 1)) : E :=
  ev (ev1 s i) - (WW s ev).starProjection (ev (ev1 s i))

lemma Ek_zero (s : ℕ) (ev : (Fin (s + 1) → ℝ) →ₗ[ℝ] E) (i : Fin (s + 1)) (hi : i.val < s - 1) :
    Ek s ev i = 0 := by
  have hm : ev (ev1 s i) ∈ WW s ev :=
    Submodule.subset_span ⟨⟨i.val, hi⟩, rfl⟩
  unfold Ek
  rw [(Submodule.starProjection_eq_self_iff).2 hm]; simp

lemma ev_sub_proj (s : ℕ) (ev : (Fin (s + 1) → ℝ) →ₗ[ℝ] E) (u : Fin (s + 1) → ℝ) :
    ev u - (WW s ev).starProjection (ev u) = ∑ i, u i • Ek s ev i := by
  have h1 : ev u = ∑ i, u i • ev (ev1 s i) := LinearMap.pi_apply_eq_sum_univ ev u
  conv_lhs => rw [h1]
  rw [map_sum]
  simp only [map_smul, Ek, smul_sub, Finset.sum_sub_distrib]

lemma yh_eq (s q : ℕ) (hs : 1 ≤ s) (ev : (Fin (s + 1) → ℝ) →ₗ[ℝ] E) (h : HyperplaneIndex s q) :
    yh s q ev h = (ch s q h)⁻¹ •
      (Ek s ev (Fin.last s) - ((((h.1 ⟨s - 1, by omega⟩).val + 1 : ℕ) : ℝ)) • Ek s ev ⟨s - 1, by omega⟩) := by
  have e1 : yh s q ev h = (ch s q h)⁻¹ • (ev (uh s q h) - (WW s ev).starProjection (ev (uh s q h))) := by
    unfold yh vh
    rw [map_smul, smul_sub]
  rw [e1, ev_sub_proj]
  congr 1
  have hne : (Fin.last s : Fin (s + 1)) ≠ ⟨s - 1, by omega⟩ := by
    intro H; have := congrArg Fin.val H; simp at this; omega
  rw [Finset.sum_eq_add (Fin.last s) ⟨s - 1, by omega⟩ hne]
  · have a1 : uh s q h (Fin.last s) = 1 := by simp [uh]
    have a2 : uh s q h ⟨s - 1, by omega⟩ = -((((h.1 ⟨s - 1, by omega⟩).val + 1 : ℕ) : ℝ)) := by
      simp [uh, show s - 1 < s by omega]
    rw [a1, a2]; simp only [one_smul, neg_smul]; abel
  · intro c _ hc
    have hc1 : c.val < s - 1 := by
      have h1 : c ≠ Fin.last s := hc.1
      have h2 : c.val ≠ s - 1 := fun H => hc.2 (Fin.ext H)
      have h3 : c.val ≠ s := fun H => h1 (Fin.ext (by simpa using H))
      omega
    rw [Ek_zero s ev c hc1]; simp
  · intro H; exact absurd (Finset.mem_univ _) H
  · intro H; exact absurd (Finset.mem_univ _) H

end WeakEpsNets.Dev.Core3
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace WeakEpsNets.Dev.Core4

open WeakEpsNets.LowerBound WeakEpsNets.Dev WeakEpsNets.Dev.Core1 WeakEpsNets.Dev.Core2
  WeakEpsNets.Dev.Core3
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma norm_sq_comb (a b : E) (t : ℝ) :
    ‖a - t • b‖ ^ 2 = ‖a‖ ^ 2 - 2 * t * ⟪a, b⟫ + t ^ 2 * ‖b‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow]
  simp; ring

/-- the pair `(t_h, b_h)` -/
def pairOf (s q : ℕ) (hs : 1 ≤ s) (h : HyperplaneIndex s q) : ℕ × ℕ :=
  ((h.1 ⟨s - 1, by omega⟩).val + 1, h.2.val + 1)

noncomputable def fOf (s q : ℕ) (ev : (Fin (s + 1) → ℝ) →ₗ[ℝ] E) (hs : 1 ≤ s) (ab : ℕ × ℕ) : E :=
  (((ab.2 : ℝ) + tau q))⁻¹ • (Ek s ev (Fin.last s) - (ab.1 : ℝ) • Ek s ev ⟨s - 1, by omega⟩)

lemma yh_eq_fOf (s q : ℕ) (hs : 1 ≤ s) (ev : (Fin (s + 1) → ℝ) →ₗ[ℝ] E)
    (h : HyperplaneIndex s q) : yh s q ev h = fOf s q ev hs (pairOf s q hs h) := by
  rw [yh_eq s q hs ev h]; rfl

section
variable (s q : ℕ) (hs : 1 ≤ s) (hq : 2 ≤ q) (heven : Even q) (z : LiftSpace s)
  (ev : (Fin (s + 1) → ℝ) →ₗ[ℝ] E)
  (hev : ∀ u v, ⟪ev u, ev v⟫ = u ⬝ᵥ (Zmat s z).mulVec v)
include hs hq heven hev

/-- the key quadratic identity -/
lemma key_identity (h0 : HyperplaneIndex s q) (hc0 : Compat s q z h0)
    (h : HyperplaneIndex s q) (hc : Compat s q z h) :
    ‖Ek s ev (Fin.last s)‖ ^ 2
      - 2 * (((pairOf s q hs h).1 : ℕ) : ℝ) * ⟪Ek s ev (Fin.last s), Ek s ev ⟨s - 1, by omega⟩⟫
      + (((pairOf s q hs h).1 : ℕ) : ℝ) ^ 2 * ‖Ek s ev ⟨s - 1, by omega⟩‖ ^ 2
      = ‖yh s q ev h0‖ ^ 2 * (((pairOf s q hs h).2 : ℕ) + tau q) ^ 2 := by
  have hpos := ch_pos s q hq h
  rw [← norm_sq_comb, ← norm_yh_eq s q hq z ev hev h h0 hc hc0]
  have e : yh s q ev h = (ch s q h)⁻¹ • (Ek s ev (Fin.last s)
      - (((pairOf s q hs h).1 : ℕ) : ℝ) • Ek s ev ⟨s - 1, by omega⟩) := yh_eq s q hs ev h
  have e2 : ch s q h = (((pairOf s q hs h).2 : ℕ) : ℝ) + tau q := rfl
  rw [e, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, e2]
  rw [e2] at hpos
  field_simp

lemma exists_T (h0 : HyperplaneIndex s q) (hc0 : Compat s q z h0) :
    ∃ T : Finset E, T.card ≤ 4 ∧ ∀ h, Compat s q z h → yh s q ev h ∈ T := by
  classical
  have key := key_identity s q hs hq heven z ev hev h0 hc0
  set El := Ek s ev (Fin.last s) with hEl
  set Es := Ek s ev ⟨s - 1, by omega⟩ with hEs
  set ρ2 := ‖yh s q ev h0‖ ^ 2 with hρ
  have yeq : ∀ h, yh s q ev h = (ch s q h)⁻¹ • (El - (((pairOf s q hs h).1 : ℕ) : ℝ) • Es) :=
    fun h => yh_eq s q hs ev h
  have hnorm : ∀ h, Compat s q z h → ‖yh s q ev h‖ ^ 2 = ρ2 :=
    fun h hc => norm_yh_eq s q hq z ev hev h h0 hc hc0
  set pairs : Finset (ℕ × ℕ) :=
    (Finset.univ.filter (fun h => Compat s q z h)).image (pairOf s q hs) with hpairs
  have hmem : ∀ h, Compat s q z h → pairOf s q hs h ∈ pairs := fun h hc =>
    Finset.mem_image_of_mem _ (by simp [hc])
  by_cases hcard : pairs.card ≤ 4
  · refine ⟨pairs.image (fOf s q ev hs), ?_, fun h hc => ?_⟩
    · exact (Finset.card_image_le).trans hcard
    · rw [yh_eq_fOf s q hs ev h]
      exact Finset.mem_image_of_mem _ (hmem h hc)
  push_neg at hcard
  by_cases hρ0 : ρ2 = 0
  · refine ⟨{0}, by simp, fun h hc => ?_⟩
    have := hnorm h hc
    rw [hρ0] at this
    simp only [Finset.mem_singleton]
    exact norm_eq_zero.1 (by simpa using this)
  by_cases hEs0 : ‖Es‖ ^ 2 = 0
  · refine ⟨{yh s q ev h0}, by simp, fun h hc => ?_⟩
    simp only [Finset.mem_singleton]
    have hEs' : Es = 0 := by simpa using hEs0
    have k1 := key h hc
    have k0 := key h0 hc0
    have hp1 := ch_pos s q hq h
    have hp0 := ch_pos s q hq h0
    have e1 : yh s q ev h = (ch s q h)⁻¹ • El := by rw [yeq h]; simp [hEs']
    have e0 : yh s q ev h0 = (ch s q h0)⁻¹ • El := by rw [yeq h0]; simp [hEs']
    have hsq : ch s q h ^ 2 = ch s q h0 ^ 2 := by
      have a1 : ‖El‖ ^ 2 = ρ2 * ch s q h ^ 2 := by
        have : ch s q h = (((pairOf s q hs h).2 : ℕ) : ℝ) + tau q := rfl
        rw [this]; simpa [hEs'] using k1
      have a0 : ‖El‖ ^ 2 = ρ2 * ch s q h0 ^ 2 := by
        have : ch s q h0 = (((pairOf s q hs h0).2 : ℕ) : ℝ) + tau q := rfl
        rw [this]; simpa [hEs'] using k0
      exact mul_left_cancel₀ hρ0 (a1.symm.trans a0)
    have hceq : ch s q h = ch s q h0 := (sq_eq_sq₀ hp1.le hp0.le).1 hsq
    rw [e1, e0, hceq]
  · have hρpos : 0 < ρ2 := lt_of_le_of_ne (by positivity) (Ne.symm hρ0)
    have hEspos : 0 < ‖Es‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hEs0)
    set G : Polynomial ℝ := Polynomial.C (ρ2⁻¹ * ‖Es‖ ^ 2) * Polynomial.X ^ 2
      + Polynomial.C (ρ2⁻¹ * (-2 * ⟪El, Es⟫)) * Polynomial.X + Polynomial.C (ρ2⁻¹ * ‖El‖ ^ 2) with hG
    have hGdeg : G.natDegree = 2 := Polynomial.natDegree_quadratic (by positivity)
    have hGeval : ∀ x : ℝ, G.eval x = ρ2⁻¹ * (‖El‖ ^ 2 - 2 * x * ⟪El, Es⟫ + x ^ 2 * ‖Es‖ ^ 2) := by
      intro x; simp [hG]; ring
    have hvals : ∀ ab ∈ pairs, G.eval (ab.1 : ℝ) = ((ab.2 : ℝ) + tau q) ^ 2 := by
      intro ab hab
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hab
      have hc : Compat s q z h := by simpa using hh
      rw [hGeval, key h hc]
      field_simp
    have hgrid : pairs ⊆ (positiveInterval q).product (positiveInterval (q ^ 2)) := by
      intro ab hab
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hab
      have h1 := (h.1 ⟨s - 1, by omega⟩).2
      have h2 := h.2.2
      rw [Finset.product_eq_sprod, Finset.mem_product]
      simp only [positiveInterval, Finset.mem_Icc, pairOf]
      omega
    obtain ⟨α, t0, hGeq⟩ := WeakEpsNets.LowerBound.lemma_1 q hq heven G hGdeg pairs hgrid
      (by omega) hvals
    have hG0 : G.eval t0 = 0 := by rw [hGeq]; simp
    rw [hGeval] at hG0
    have hElt : El = t0 • Es := by
      have : ‖El - t0 • Es‖ ^ 2 = 0 := by
        rw [norm_sq_comb]
        have := mul_eq_zero.1 hG0
        rcases this with h | h
        · exact absurd h (by positivity)
        · linarith
      have h2 : El - t0 • Es = 0 := by simpa using this
      exact sub_eq_zero.1 h2
    set r0 : ℝ := Real.sqrt (ρ2 / ‖Es‖ ^ 2) with hr0
    refine ⟨{r0 • Es, (-r0) • Es}, Finset.card_le_two.trans (by norm_num), fun h hc => ?_⟩
    have hp := ch_pos s q hq h
    set r : ℝ := (ch s q h)⁻¹ * (t0 - (((pairOf s q hs h).1 : ℕ) : ℝ)) with hr
    have e : yh s q ev h = r • Es := by
      rw [yeq h, hElt, hr, ← sub_smul, smul_smul]
    have hn := hnorm h hc
    rw [e, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hn
    have hr2 : r ^ 2 = r0 ^ 2 := by
      rw [hr0, Real.sq_sqrt (by positivity)]
      exact (eq_div_iff hEs0).2 hn
    rw [e]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hr2 with h1 | h1
    · simp [h1]
    · simp [h1]

end

end WeakEpsNets.Dev.Core4
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace WeakEpsNets.Dev

open WeakEpsNets.LowerBound WeakEpsNets.Dev.Core1 WeakEpsNets.Dev.Core2 WeakEpsNets.Dev.Core3
  WeakEpsNets.Dev.Core4
open scoped RealInnerProductSpace

namespace Core5

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma exists_cls (T : Finset E) (hT : T.card ≤ 4) :
    ∃ f : E → Fin 4, ∀ x ∈ T, ∀ y ∈ T, f x = f y → x = y := by
  classical
  refine ⟨fun x => if hx : x ∈ T then Fin.castLE hT (T.equivFin ⟨x, hx⟩) else 0, ?_⟩
  intro x hx y hy hxy
  simp only [hx, hy, dite_true] at hxy
  have := (T.equivFin).injective (Fin.castLE_injective hT hxy)
  exact congrArg Subtype.val this

lemma blockF_eq (s q : ℕ) (hq : 2 ≤ q) (z : LiftSpace s) (ev : (Fin (s + 1) → ℝ) →ₗ[ℝ] E)
    (hev : ∀ u v, ⟪ev u, ev v⟫ = u ⬝ᵥ (Zmat s z).mulVec v)
    (h h' : HyperplaneIndex s q) (hc : Compat s q z h) (hc' : Compat s q z h')
    (hy : yh s q ev h = yh s q ev h') : blockF s q z h = blockF s q z h' := by
  classical
  have hv := vh_eq_of_yh_eq s q hq z ev hev h h' hc hc' hy
  have hp := ch_pos s q hq h
  have hp' := ch_pos s q hq h'
  set d : Fin (s + 1) → ℝ := (ch s q h)⁻¹ • uh s q h - (ch s q h')⁻¹ • uh s q h' with hd
  have hevd : ev d = 0 := by
    rw [hd, map_sub, map_smul, map_smul]
    exact sub_eq_zero.2 hv
  have hZ : (Zmat s z).mulVec d = 0 := by
    have : ∀ u, u ⬝ᵥ (Zmat s z).mulVec d = 0 := fun u => by
      rw [← hev, hevd]; simp
    exact dotProduct_self_eq_zero.1 (this _)
  have hF : ∀ p ∈ Fspace s z, (ch s q h)⁻¹ * (uh s q h ⬝ᵥ p) = (ch s q h')⁻¹ * (uh s q h' ⬝ᵥ p) := by
    intro p hpF
    have := hpF d hZ
    rw [hd, sub_dotProduct, smul_dotProduct, smul_dotProduct] at this
    simpa [sub_eq_zero] using this
  ext p
  unfold blockF block
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hg, hh⟩, hpF⟩
    refine ⟨⟨hg, ?_⟩, hpF⟩
    rw [mem_hyperplane_iff] at hh ⊢
    have := hF p hpF
    rw [hh, inv_mul_cancel₀ hp.ne'] at this
    exact ((inv_mul_eq_one₀ hp'.ne').1 this.symm).symm
  · rintro ⟨⟨hg, hh⟩, hpF⟩
    refine ⟨⟨hg, ?_⟩, hpF⟩
    rw [mem_hyperplane_iff] at hh ⊢
    have := hF p hpF
    rw [hh, inv_mul_cancel₀ hp'.ne'] at this
    exact ((inv_mul_eq_one₀ hp.ne').1 this).symm

end Core5

theorem core (s q : ℕ) (hs : 1 ≤ s) (hq : 2 ≤ q) (heven : Even q) (z : LiftSpace s) :
    ∃ cls : HyperplaneIndex s q → Fin 4, ∀ h h' : HyperplaneIndex s q,
      Compat s q z h → Compat s q z h' → cls h = cls h' → blockF s q z h = blockF s q z h' := by
  classical
  by_cases hex : ∃ h0, Compat s q z h0
  · obtain ⟨h0, hc0⟩ := hex
    obtain ⟨C, hC, hzC⟩ := hc0
    obtain ⟨S, w, hS, hw, hw1, hz⟩ := rep s q z h0 C hC hzC
    obtain ⟨ev, hev⟩ := gramE s z S w hw hz
    have hc0 : Compat s q z h0 := ⟨C, hC, hzC⟩
    obtain ⟨T, hT, hTm⟩ := exists_T s q hs hq heven z ev hev h0 hc0
    obtain ⟨f, hf⟩ := Core5.exists_cls T hT
    refine ⟨fun h => f (yh s q ev h), fun h h' hc hc' hcls => ?_⟩
    exact Core5.blockF_eq s q hq z ev hev h h' hc hc' (hf _ (hTm h hc) _ (hTm h' hc') hcls)
  · exact ⟨fun _ => 0, fun h h' hc _ _ => absurd ⟨h, hc⟩ hex⟩

end WeakEpsNets.Dev
end

section
set_option autoImplicit false

open scoped BigOperators

namespace WeakEpsNets.Dev

open WeakEpsNets.LowerBound

theorem block_grid (s q : ℕ) (h : HyperplaneIndex s q) (p : Fin (s + 1) → ℝ)
    (hp : p ∈ block s q h) (i : Fin s) : ∃ k : ℕ, 1 ≤ k ∧ k ≤ q ∧ p i.castSucc = (k : ℝ) := by
  classical
  unfold block at hp
  rw [Finset.mem_filter] at hp
  have hg := hp.1
  unfold shiftedGrid at hg
  rw [Finset.mem_image] at hg
  obtain ⟨t, -, rfl⟩ := hg
  refine ⟨(t.1 ⟨i.val, i.isLt⟩).val + 1, by omega, ?_, ?_⟩
  · have := (t.1 ⟨i.val, i.isLt⟩).isLt
    omega
  · simp [i.isLt]

theorem block_last (s q : ℕ) (h : HyperplaneIndex s q) (p : Fin (s + 1) → ℝ)
    (hp : p ∈ block s q h) :
    p (Fin.last s) = (fun i : Fin s => (((h.1 i).val + 1 : ℕ) : ℝ)) ⬝ᵥ (fun i : Fin s => p i.castSucc)
      + (((h.2.val + 1 : ℕ) : ℝ) + tau q) := by
  classical
  unfold block at hp
  rw [Finset.mem_filter] at hp
  have := hp.2
  simp only [hyperplane, Set.mem_ofPred_eq] at this
  rw [this]
  simp only [dotProduct]
  ring

theorem fibre_bound (s q : ℕ) (z : LiftSpace s) (F : Finset (HyperplaneIndex s q))
    (T : Finset (Fin (s + 1) → ℝ))
    (hF : ∀ h ∈ F, Compat s q z h ∧ blockF s q z h = T) : F.card * T.card ≤ q ^ s := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | ⟨h0, hh0⟩
  · simp
  obtain ⟨hc0, hT0⟩ := hF h0 hh0
  obtain ⟨C0, hC0, hz0⟩ := hc0
  obtain ⟨p0, hp0, -⟩ := piercing s q z h0 ⟨C0, hC0, hz0⟩ C0 hC0 hz0
  rw [hT0] at hp0
  have hTb : ∀ h ∈ F, ∀ p ∈ T, p ∈ block s q h := by
    intro h hh p hp
    rw [← (hF h hh).2] at hp
    exact (Finset.mem_filter.mp hp).1
  let xp : (Fin (s + 1) → ℝ) → (Fin s → ℝ) := fun p i => p i.castSucc
  let ap : HyperplaneIndex s q → (Fin s → ℝ) := fun h i => (((h.1 i).val + 1 : ℕ) : ℝ)
  have hxinj : Set.InjOn xp (T : Set (Fin (s + 1) → ℝ)) := by
    intro p hp p' hp' hpp
    have e1 := block_last s q h0 p (hTb h0 hh0 p hp)
    have e2 := block_last s q h0 p' (hTb h0 hh0 p' hp')
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [e1, e2]
      change _ ⬝ᵥ xp p + _ = _ ⬝ᵥ xp p' + _
      rw [hpp]
    · exact congrFun hpp j
  have hainj : Set.InjOn ap (F : Set (HyperplaneIndex s q)) := by
    intro h hh h' hh' hhh
    have e1 := block_last s q h p0 (hTb h hh p0 hp0)
    have e2 := block_last s q h' p0 (hTb h' hh' p0 hp0)
    have e1 : p0 (Fin.last s) = ap h ⬝ᵥ xp p0 + (((h.2.val + 1 : ℕ) : ℝ) + tau q) := e1
    have e2 : p0 (Fin.last s) = ap h' ⬝ᵥ xp p0 + (((h'.2.val + 1 : ℕ) : ℝ) + tau q) := e2
    rw [hhh] at e1
    have hb : (((h.2.val + 1 : ℕ) : ℝ)) = (((h'.2.val + 1 : ℕ) : ℝ)) := by linarith
    have hb' : h.2.val = h'.2.val := by
      have := Nat.cast_injective (R := ℝ) hb
      omega
    refine Prod.ext ?_ (Fin.ext hb')
    funext i
    have := congrFun hhh i
    simp only [ap] at this
    exact Fin.ext (by have := Nat.cast_injective (R := ℝ) this; omega)
  let y : (Fin s → ℝ) → ℝ := fun x =>
    (fun i : Fin s => (((h0.1 i).val + 1 : ℕ) : ℝ)) ⬝ᵥ x + (((h0.2.val + 1 : ℕ) : ℝ) + tau q)
  let c : (Fin s → ℝ) → ℝ := fun a => y (xp p0) - a ⬝ᵥ xp p0
  have hinc := Latt.incidence_card_le s q (T.image xp) (F.image ap) y c
    (by
      intro x hx i
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact block_grid s q h0 p (hTb h0 hh0 p hp) i)
    (by
      intro a ha i
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp ha
      exact ⟨(h.1 i).val + 1, by omega, by have := (h.1 i).isLt; omega, rfl⟩)
    (by
      intro x hx a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp ha
      have e1 := block_last s q h p (hTb h hh p hp)
      have e2 := block_last s q h p0 (hTb h hh p0 hp0)
      have e3 := block_last s q h0 p (hTb h0 hh0 p hp)
      have e4 := block_last s q h0 p0 (hTb h0 hh0 p0 hp0)
      have e1 : p (Fin.last s) = ap h ⬝ᵥ xp p + (((h.2.val + 1 : ℕ) : ℝ) + tau q) := e1
      have e2 : p0 (Fin.last s) = ap h ⬝ᵥ xp p0 + (((h.2.val + 1 : ℕ) : ℝ) + tau q) := e2
      have e3 : y (xp p) = p (Fin.last s) := e3.symm
      have e4 : y (xp p0) = p0 (Fin.last s) := e4.symm
      show ap h ⬝ᵥ xp p + (y (xp p0) - ap h ⬝ᵥ xp p0) = y (xp p)
      linarith)
  rw [Finset.card_image_of_injOn hxinj, Finset.card_image_of_injOn hainj] at hinc
  rw [mul_comm]
  exact hinc

end WeakEpsNets.Dev

namespace WeakEpsNets.LowerBound

open WeakEpsNets.Dev in
theorem chk_lemma_2 (s q : ℕ) (hs : 1 ≤ s) (hq : 2 ≤ q) (heven : Even q)
    (z : LiftSpace s) :
    ∃ Q : HyperplaneIndex s q → Finset (LiftSpace s),
      (∀ h, Q h ⊆ liftedBlock s q h) ∧
      (∀ h, ∀ C ∈ hullFamily s q h, z ∈ C → ∃ x ∈ Q h, x ∈ C) ∧
      (∑ h : HyperplaneIndex s q, (Q h).card) ≤ 4 * q ^ s := by
  classical
  obtain ⟨cls, hcls⟩ := core s q hs hq heven z
  refine ⟨fun h => if Compat s q z h then (blockF s q z h).image (phi s) else ∅, ?_, ?_, ?_⟩
  · intro h
    dsimp only
    split_ifs
    · unfold liftedBlock
      exact Finset.image_subset_image (Finset.filter_subset _ _)
    · exact Finset.empty_subset _
  · intro h C hC hz
    have hc : Compat s q z h := ⟨C, hC, hz⟩
    obtain ⟨p, hp, hpC⟩ := piercing s q z h hc C hC hz
    refine ⟨phi s p, ?_, hpC⟩
    simp only [hc, if_true]
    exact Finset.mem_image_of_mem _ hp
  · rw [← Finset.sum_fiberwise Finset.univ cls]
    have hk : ∀ k : Fin 4, ∑ h ∈ Finset.univ.filter (fun h => cls h = k),
        (if Compat s q z h then (blockF s q z h).image (phi s) else ∅).card ≤ q ^ s := by
      intro k
      set F := (Finset.univ.filter (fun h => cls h = k)).filter (fun h => Compat s q z h) with hFdef
      have hsub : ∑ h ∈ Finset.univ.filter (fun h => cls h = k),
          (if Compat s q z h then (blockF s q z h).image (phi s) else ∅).card
          = ∑ h ∈ F, ((blockF s q z h).image (phi s)).card := by
        rw [hFdef, Finset.sum_filter (s := Finset.univ.filter (fun h => cls h = k))]
        apply Finset.sum_congr rfl
        intro h _
        split_ifs <;> simp
      rw [hsub]
      rcases F.eq_empty_or_nonempty with hF | ⟨h0, hh0⟩
      · simp [hF]
      have hF : ∀ h ∈ F, Compat s q z h ∧ blockF s q z h = blockF s q z h0 := by
        intro h hh
        simp only [hFdef, Finset.mem_filter, Finset.mem_univ, true_and] at hh hh0
        exact ⟨hh.2, hcls h h0 hh.2 hh0.2 (hh.1.trans hh0.1.symm)⟩
      calc ∑ h ∈ F, ((blockF s q z h).image (phi s)).card
          ≤ ∑ h ∈ F, (blockF s q z h0).card := by
            apply Finset.sum_le_sum
            intro h hh
            rw [(hF h hh).2]
            exact Finset.card_image_le
        _ = F.card * (blockF s q z h0).card := by simp
        _ ≤ q ^ s := fibre_bound s q z F _ hF
    calc ∑ k : Fin 4, ∑ h ∈ Finset.univ.filter (fun h => cls h = k),
          (if Compat s q z h then (blockF s q z h).image (phi s) else ∅).card
        ≤ ∑ _k : Fin 4, q ^ s := Finset.sum_le_sum (fun k _ => hk k)
      _ = 4 * q ^ s := by simp

end WeakEpsNets.LowerBound
end

theorem solution : type_of% @WeakEpsNets.LowerBound.chk_lemma_2 := @WeakEpsNets.LowerBound.chk_lemma_2
