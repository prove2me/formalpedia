-- Prove2me | solution 1 for SCCThm8.power_deg_card_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:08:33.269032+00:00
-- url     : https://prove2.me/submissions/93d2ee7f-9a11-43a6-b23b-6989cd077759

module
public import Definitions.Def_SCCThm8_PowerRigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Degeneration
public import Definitions.Def_SCCThm8_PowerDegeneration
public import Theorems.Thm_SCCThm8_psiP_add
public import Theorems.Thm_SCCThm8_toAdd_psiP
public import Theorems.Thm_SCCThm8_mult_eq_one_of_disj
public import Theorems.Thm_SCCThm8_power_rigidity
public import Theorems.Thm_SCCThm8_realizable
public import Theorems.Thm_SCCThm8_sum_ind


set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {G : Type*} [Group G] [Fintype G] (k m : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G) (a b c : (Fin m → Finset (Fin (3 * k))) → ℤ)
    (hpart : ∀ A B C : Fin m → Finset (Fin (3 * k)),
      (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
      (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) →
        f₁ A * f₂ B * f₃ C = 1 ∧ a A + b B + c C = 0)
    (hnon : ∀ A B C : Fin m → Finset (Fin (3 * k)),
      (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
      ¬ (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) →
        f₁ A * f₂ B * f₃ C = 1 → 0 < a A + b B + c C) :
    Nat.choose (3 * k) (3 * k / 2) ^ m ≤ Fintype.card G := by
  -- Step 1: rigidity in `G`.
  obtain ⟨g, hc, hprod⟩ := power_rigidity k m hk f₁ f₂ f₃ (fun A B C hA hB hC hd =>
    (hpart A B C hA hB hC hd).1)
  -- Step 2: rigidity in `Multiplicative ℤ` for the weights.
  obtain ⟨u, -, hw⟩ := power_rigidity (G := Multiplicative ℤ) k m hk
    (fun A => Multiplicative.ofAdd (a A)) (fun B => Multiplicative.ofAdd (b B))
    (fun C => Multiplicative.ofAdd (c C)) (fun A B C hA hB hC hd => by
      have := (hpart A B C hA hB hC hd).2
      rw [← ofAdd_add, ← ofAdd_add, this, ofAdd_zero])
  set W : (Fin m → Fin (3 * k) → ℤ) → ℤ :=
    fun e => ∑ j, ∑ i, e j i * Multiplicative.toAdd (u j i) with hW
  have hweight : ∀ A B C : Fin m → Finset (Fin (3 * k)),
      (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
      a A + b B + c C = W (fun j i => multP A B C j i - 1) := by
    intro A B C hA hB hC
    have := congrArg Multiplicative.toAdd (hw A B C hA hB hC)
    rw [toAdd_psiP] at this
    simpa [toAdd_mul] using this
  -- Step 3: a nonzero blockwise-balanced `{-1,0,1}` array killed by `psiP g` has positive weight.
  have key : ∀ d : Fin m → Fin (3 * k) → ℤ, (∀ j i, -1 ≤ d j i ∧ d j i ≤ 1) →
      (∀ j, ∑ i, d j i = 0) → d ≠ 0 → psiP g d = 1 → 0 < W d := by
    intro d hd hs hne h1
    have hr : ∀ j, ∃ A B C : Finset (Fin (3 * k)), A.card = k ∧ B.card = k ∧ C.card = k ∧
        ∀ i, mult A B C i = d j i + 1 := fun j =>
      realizable k (fun i => d j i + 1)
        (fun i => by have := hd j i; constructor <;> omega)
        (by rw [sum_add_distrib, hs j]; simp)
    choose A B C hA hB hC hm using hr
    have hmd : (fun j i => multP A B C j i - 1) = d := by
      funext j i; simp only [multP]; rw [hm j i]; ring
    have hone : f₁ A * f₂ B * f₃ C = 1 := by
      rw [hprod A B C hA hB hC, hmd]; exact h1
    have hnp : ¬ (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) := by
      intro hdisj
      apply hne
      funext j i
      have := mult_eq_one_of_disj k (A j) (B j) (C j) (hA j) (hB j) (hC j)
        (hdisj j).1 (hdisj j).2.1 (hdisj j).2.2 i
      rw [hm j i] at this
      simp only [Pi.zero_apply]
      omega
    have := hnon A B C hA hB hC hnp hone
    rwa [hweight A B C hA hB hC, hmd] at this
  -- Step 4: injectivity on `m`-tuples of `(3k/2)`-subsets.
  have hinj : Set.InjOn (fun X : Fin m → Finset (Fin (3 * k)) => psiP g (fun j => ind (X j)))
      ↑(Fintype.piFinset fun _ : Fin m =>
        powersetCard (3 * k / 2) (univ : Finset (Fin (3 * k)))) := by
    intro X hX X' hX' heq
    rw [mem_coe, Fintype.mem_piFinset] at hX hX'
    simp only at heq
    by_contra hne
    set d : Fin m → Fin (3 * k) → ℤ := fun j i => ind (X j) i - ind (X' j) i with hd
    have e1 : psiP g (fun j => ind (X j)) = psiP g d * psiP g (fun j => ind (X' j)) := by
      rw [← psiP_add g hc]; congr 1; funext j i; simp [hd]
    have e2 : psiP g (fun j => ind (X' j)) = psiP g (-d) * psiP g (fun j => ind (X j)) := by
      rw [← psiP_add g hc]; congr 1; funext j i; simp [hd]
    have hd1 : psiP g d = 1 := mul_eq_right.mp (e1.symm.trans heq)
    have hd2 : psiP g (-d) = 1 := mul_eq_right.mp (e2.symm.trans heq.symm)
    have hb : ∀ j i, -1 ≤ d j i ∧ d j i ≤ 1 := by
      intro j i; simp only [hd, ind]; split_ifs <;> norm_num
    have hs : ∀ j, ∑ i, d j i = 0 := by
      intro j
      have h1 := (mem_powersetCard.mp (hX j)).2
      have h2 := (mem_powersetCard.mp (hX' j)).2
      simp only [hd]; rw [sum_sub_distrib, sum_ind, sum_ind, h1, h2, sub_self]
    have hne0 : d ≠ 0 := by
      intro h0
      apply hne
      funext j
      ext i
      have := congrFun (congrFun h0 j) i
      simp only [hd, ind, Pi.zero_apply] at this
      by_cases h1 : i ∈ X j <;> by_cases h2 : i ∈ X' j <;> simp [h1, h2] at this ⊢
    have p1 := key d hb hs hne0 hd1
    have p2 := key (-d)
      (fun j i => by have := hb j i; simp only [Pi.neg_apply]; constructor <;> omega)
      (fun j => by simp [sum_neg_distrib, hs j]) (neg_ne_zero.mpr hne0) hd2
    have : W (-d) = - W d := by simp [hW, sum_neg_distrib]
    omega
  have := card_le_card_of_injOn (t := (univ : Finset G)) _
    (fun _ _ => mem_coe.mpr (mem_univ _)) hinj
  simpa [Fintype.card_piFinset, card_powersetCard] using this
end SCCThm8
