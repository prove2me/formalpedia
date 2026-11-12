-- Prove2me | solution 1 for OddOrder.Isaacs.Ch04.prime_dvd_card_of_faithful_iterCommutator_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:18:32.354514+00:00
-- url     : https://prove2.me/submissions/a1d01b95-cbd1-4721-9f74-84d70a5f665f

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch04_Commutators/Main/ThreeSubgroupsCoprime.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime

-- ===== OddOrder/Isaacs/Ch04_Commutators/Main/ThreeSubgroupsCoprime.lean =====
namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

variable {G : Type*} [Group G]

section

/-- **Bridge lemma** (semidirect product): `K ≤ φ.ker` iff `⁅K.map inr, inl(G).range⁆ = ⊥`
in `Γ = G ⋊[φ] A`. つまり `K ≤ A` が trivial action ↔ `inr(K)` と `inl(G)` が可換.

**証明**: `Subgroup.commutator_eq_bot_iff_le_centralizer` で commutator = ⊥ ↔ centralizer
包含, さらに semidirect product の `inl_aut` (`inl ((φ a) g) = inr a * inl g * inr a⁻¹`)
で `inr(k)` と `inl(g)` が可換 ↔ `(φ k) g = g`. -/
theorem _root_.SemidirectProduct.commutator_inr_inl_range_eq_bot_iff_le_ker
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G} (K : Subgroup A) :
    ⁅K.map (SemidirectProduct.inr : A →* G ⋊[φ] A),
      (SemidirectProduct.inl : G →* G ⋊[φ] A).range⁆ = ⊥ ↔ K ≤ φ.ker := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  constructor
  · -- K.map inr ≤ centralizer inl.range ⇒ K ≤ ker φ
    intro h k hk
    -- k ∈ K. Want φ k = 1, i.e., (φ k) g = g for all g.
    rw [MonoidHom.mem_ker]
    -- Use MulEquiv.ext for (φ k) = 1
    refine MulEquiv.ext fun g => ?_
    -- Goal: (φ k) g = (1 : MulAut G) g = g
    rw [MulAut.one_apply]
    have h_mem : (SemidirectProduct.inr k : G ⋊[φ] A) ∈
        K.map (SemidirectProduct.inr : A →* G ⋊[φ] A) := ⟨k, hk, rfl⟩
    have h_centr := h h_mem
    rw [Subgroup.mem_centralizer_iff] at h_centr
    have h_comm := h_centr (SemidirectProduct.inl g : G ⋊[φ] A) ⟨g, rfl⟩
    -- h_comm : inl g * inr k = inr k * inl g
    have h_aut : (SemidirectProduct.inr k : G ⋊[φ] A) * SemidirectProduct.inl g =
        (SemidirectProduct.inl ((φ k) g) : G ⋊[φ] A) * SemidirectProduct.inr k := by
      have hi := SemidirectProduct.inl_aut (φ := φ) k g
      have h_inv : (SemidirectProduct.inr k⁻¹ : G ⋊[φ] A) = (SemidirectProduct.inr k)⁻¹ :=
        map_inv SemidirectProduct.inr k
      rw [hi, h_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [h_aut] at h_comm
    -- h_comm : inl g * inr k = inl ((φ k) g) * inr k
    have h_eq : (SemidirectProduct.inl g : G ⋊[φ] A) = SemidirectProduct.inl ((φ k) g) :=
      mul_right_cancel h_comm
    exact (SemidirectProduct.inl_injective h_eq).symm
  · -- K ≤ ker φ ⇒ K.map inr ≤ centralizer inl.range
    intro h y hy
    rw [Subgroup.mem_centralizer_iff]
    obtain ⟨k, hk, rfl⟩ := hy
    have h_fix : φ k = 1 := h hk
    intro x hx
    obtain ⟨g, rfl⟩ := hx
    -- Goal: inl g * inr k = inr k * inl g
    have h_aut : (SemidirectProduct.inr k : G ⋊[φ] A) * SemidirectProduct.inl g =
        (SemidirectProduct.inl ((φ k) g) : G ⋊[φ] A) * SemidirectProduct.inr k := by
      have hi := SemidirectProduct.inl_aut (φ := φ) k g
      have h_inv : (SemidirectProduct.inr k⁻¹ : G ⋊[φ] A) = (SemidirectProduct.inr k)⁻¹ :=
        map_inv SemidirectProduct.inr k
      rw [hi, h_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [h_aut, h_fix, MulAut.one_apply]

private lemma iterCommutator_eq_one_of_two_eq_one
    {E F : Subgroup G}
    (h : iterCommutator E F 2 = iterCommutator E F 1) :
    ∀ {m : ℕ}, 1 ≤ m → iterCommutator E F m = iterCommutator E F 1 := by
  intro m hm
  induction m with
  | zero => omega
  | succ n ih =>
      rcases n with _ | n
      · rfl
      · have hn : 1 ≤ n + 1 := by omega
        rw [iterCommutator_succ, ih hn]
        simpa [iterCommutator_succ] using h

theorem iterCommutator_inl_inr_restrict_eq_bot
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    (P : Subgroup A) {m : ℕ}
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥) :
    let ψ : P →* MulAut G := φ.comp P.subtype
    iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
        (SemidirectProduct.inr : P →* G ⋊[ψ] P).range m = ⊥ := by
  dsimp
  let ψ : P →* MulAut G := φ.comp P.subtype
  let F : G ⋊[ψ] P →* G ⋊[φ] A :=
    SemidirectProduct.map (MonoidHom.id G) P.subtype (fun p => by
      ext g
      rfl)
  let XGP : Subgroup (G ⋊[ψ] P) := (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
  let YPP : Subgroup (G ⋊[ψ] P) := (SemidirectProduct.inr : P →* G ⋊[ψ] P).range
  let XGA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  let YAA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  have hF_inj : Function.Injective F := by
    intro x y hxy
    ext
    · simpa [F] using congrArg (fun z : G ⋊[φ] A => z.left) hxy
    · simpa [F] using congrArg (fun z : G ⋊[φ] A => z.right) hxy
  have h_map_X : XGP.map F = XGA := by
    ext x
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, by simp [F]⟩
    · rintro ⟨g, rfl⟩
      refine ⟨(SemidirectProduct.inl : G →* G ⋊[ψ] P) g, ⟨g, rfl⟩, ?_⟩
      simp [F]
  have h_map_Y : YPP.map F ≤ YAA := by
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    exact ⟨p.1, by simp [F]⟩
  have h_map_iter_all :
      ∀ n : ℕ, (iterCommutator XGP YPP n).map F ≤ iterCommutator XGA YAA n := by
    intro n
    induction n with
    | zero =>
        simpa [iterCommutator_zero] using h_map_X.le
    | succ n ih =>
        rw [iterCommutator_succ, iterCommutator_succ, Subgroup.map_commutator]
        exact Subgroup.commutator_mono ih h_map_Y
  have h_map_bot : (iterCommutator XGP YPP m).map F = ⊥ := by
    refine le_antisymm ?_ bot_le
    exact (h_map_iter_all m).trans (le_of_eq h_iter)
  exact (Subgroup.map_eq_bot_iff_of_injective (iterCommutator XGP YPP m) hF_inj).mp h_map_bot

/-- **Isaacs Corollary 4.30**:
Let `A` act faithfully on the finite group `G`. If an iterated commutator
`[G, A, ..., A]` is trivial, then every prime divisor of `|A|` divides `|G|`.

Proof: for a prime `p ∤ |G|`, restrict the action to a Sylow `p`-subgroup `P ≤ A`.
The restricted action is coprime, and the chain hypothesis restricts from `A` to `P`.
Lemma 4.29 collapses the restricted iterated commutator to `[G, P] = 1`, so `P`
acts trivially. Faithfulness forces `P = 1`, hence `p ∤ |A|`. -/
theorem _root_.solution
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    (φ : A →* MulAut G) (h_inj : Function.Injective φ)
    {m : ℕ} (hm : 1 ≤ m)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥)
    {p : ℕ} (hp : p.Prime) (hpA : p ∣ Nat.card A) :
    p ∣ Nat.card G := by
  by_contra hpG
  have : Fact p.Prime := ⟨hp⟩
  let P : Sylow p A := default
  let ψ : P →* MulAut G := φ.comp (P : Subgroup A).subtype
  have h_iter_P :
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
          (SemidirectProduct.inr : P →* G ⋊[ψ] P).range m = ⊥ := by
    simpa [ψ] using
      iterCommutator_inl_inr_restrict_eq_bot (φ := φ) (P : Subgroup A) h_iter
  have hCop_PG : Nat.Coprime (Nat.card P) (Nat.card G) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpG)
  have hSolv : Group.IsSolvable P ∨ Group.IsSolvable G := by
    left
    have : Group.IsNilpotent P := P.isPGroup'.isNilpotent
    infer_instance
  have h_two :
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
          (SemidirectProduct.inr : P →* G ⋊[ψ] P).range 2 =
        iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
          (SemidirectProduct.inr : P →* G ⋊[ψ] P).range 1 :=
    iterCommutator_inl_inr_two_eq_one (φ := ψ) hCop_PG hSolv
  have h_iter_one :
      iterCommutator (SemidirectProduct.inl : G →* G ⋊[ψ] P).range
          (SemidirectProduct.inr : P →* G ⋊[ψ] P).range 1 = ⊥ := by
    have h_m := iterCommutator_eq_one_of_two_eq_one h_two hm
    rw [h_m] at h_iter_P
    exact h_iter_P
  have hP_le_ker : (⊤ : Subgroup P) ≤ ψ.ker := by
    rw [← SemidirectProduct.commutator_inr_inl_range_eq_bot_iff_le_ker]
    rw [show (⊤ : Subgroup P).map (SemidirectProduct.inr : P →* G ⋊[ψ] P) =
        (SemidirectProduct.inr : P →* G ⋊[ψ] P).range from
        (MonoidHom.range_eq_map _).symm]
    rw [Subgroup.commutator_comm]
    exact h_iter_one
  have hP_bot : (P : Subgroup A) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    let x : P := ⟨a, ha⟩
    have hx_ker : x ∈ ψ.ker := hP_le_ker (Subgroup.mem_top x)
    rw [MonoidHom.mem_ker] at hx_ker
    have hφa : φ a = 1 := by
      -- `ψ x = φ ((↑P).subtype ⟨a, ha⟩)` is definitionally `φ a`.
      exact hx_ker
    exact h_inj (by simpa using hφa)
  exact (P.ne_bot_of_dvd_card hpA) hP_bot

end

end OddOrder.Isaacs.Ch04
