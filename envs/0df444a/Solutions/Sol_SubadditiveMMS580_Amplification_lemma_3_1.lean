-- Prove2me | solution 1 for SubadditiveMMS580.Amplification.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:28:42.66277+00:00
-- url     : https://prove2.me/submissions/a541e2a7-ee78-43da-97dc-2ddb425b00bc

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_SubmodOrder_Subadditive
import Theorems.Thm_AGT_zero_sum_minimax

section
set_option autoImplicit false

namespace SubadditiveMMS580.Amplification.Dev.FD

open SubadditiveMMS580.Amplification

/-- Push a finitely supported distribution forward along a map. -/
noncomputable def map {α β : Type*} [DecidableEq β] (σ : FinDist α) (f : α → β) : FinDist β where
  support := σ.support.image f
  weight := fun y => ∑ x ∈ σ.support.filter (fun x => f x = y), σ.weight x
  weight_pos := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    refine Finset.sum_pos (fun x hx => σ.weight_pos x (Finset.mem_filter.1 hx).1) ⟨x, ?_⟩
    simp [hx]
  sum_weight := by
    rw [Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem f hx)]
    exact σ.sum_weight

theorem prob_map {α β : Type*} [DecidableEq β] (σ : FinDist α) (f : α → β) (E : β → Prop) :
    (map σ f).prob E = σ.prob (fun x => E (f x)) := by
  classical
  unfold FinDist.prob
  show ∑ y ∈ (σ.support.image f).filter E,
      ∑ x ∈ σ.support.filter (fun x => f x = y), σ.weight x = _
  have h1 : ∀ y ∈ (σ.support.image f).filter E,
      ∑ x ∈ σ.support.filter (fun x => f x = y), σ.weight x =
      ∑ x ∈ (σ.support.filter (fun x => E (f x))).filter (fun x => f x = y), σ.weight x := by
    intro y hy
    have hEy := (Finset.mem_filter.1 hy).2
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hxy⟩; exact ⟨⟨hx, hxy ▸ hEy⟩, hxy⟩
    · rintro ⟨⟨hx, _⟩, hxy⟩; exact ⟨hx, hxy⟩
  rw [Finset.sum_congr rfl h1]
  exact Finset.sum_fiberwise_of_maps_to (fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_image_of_mem f hx.1, hx.2⟩) _

/-- The distribution with weights given by a point of the standard simplex. -/
noncomputable def ofSimplex {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : p ∈ stdSimplex ℝ ι) :
    FinDist ι where
  support := Finset.univ.filter (fun i => 0 < p i)
  weight := p
  weight_pos := by intro x hx; simpa using hx
  sum_weight := by
    rw [Finset.sum_filter_of_ne (fun i _ hne => lt_of_le_of_ne (hp.1 i) (Ne.symm hne))]
    exact hp.2

open Classical in
theorem prob_ofSimplex {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : p ∈ stdSimplex ℝ ι)
    (E : ι → Prop) :
    (ofSimplex p hp).prob E = ∑ i, if E i then p i else 0 := by
  unfold FinDist.prob
  show ∑ i ∈ (Finset.univ.filter (fun i => 0 < p i)).filter E, p i = _
  rw [Finset.filter_comm, Finset.sum_filter_of_ne, Finset.sum_filter]
  intro i _ hne
  exact lt_of_le_of_ne (hp.1 i) (Ne.symm hne)

end SubadditiveMMS580.Amplification.Dev.FD
end

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Dev.L31

open SubadditiveMMS580.Amplification.Dev.FD

open Classical in
/-- weak-win payoff -/
noncomputable def Hf {s : ℕ} (v : Finset (Fin s) → ℝ) (z y : Fin s → ℕ) : ℝ :=
  if v Finset.univ / 2 ≤ v (Finset.univ.filter (fun g => y g ≤ z g)) then 1 else 0

theorem Hf_add_ge {s : ℕ} (v : Finset (Fin s) → ℝ) (hsub : SubmodOrder.Subadditive v)
    (z y : Fin s → ℕ) : 1 ≤ Hf v z y + Hf v y z := by
  classical
  have hcov : (Finset.univ.filter (fun g => y g ≤ z g)) ∪
      (Finset.univ.filter (fun g => z g ≤ y g)) = Finset.univ := by
    ext g; simp [le_total]
  have h := hsub (Finset.univ.filter (fun g => y g ≤ z g)) (Finset.univ.filter (fun g => z g ≤ y g))
  rw [hcov] at h
  unfold Hf
  by_cases h1 : v Finset.univ / 2 ≤ v (Finset.univ.filter (fun g => y g ≤ z g))
  · rw [if_pos h1]
    have : (0 : ℝ) ≤ (if v Finset.univ / 2 ≤ v (Finset.univ.filter (fun g => z g ≤ y g)) then 1 else 0) := by
      split_ifs <;> norm_num
    linarith
  · rw [if_neg h1]
    have h2 : v Finset.univ / 2 ≤ v (Finset.univ.filter (fun g => z g ≤ y g)) := by
      by_contra h2; push Not at h1 h2; linarith
    rw [if_pos h2]; norm_num

end SubadditiveMMS580.Amplification.Dev.L31

namespace SubadditiveMMS580.Amplification.Dev.L31

open SubadditiveMMS580.Amplification.Dev.FD

theorem exists_simplex_half {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : ∀ a b, 1 ≤ A a b + A b a) :
    ∃ p ∈ stdSimplex ℝ (Fin (N + 1)), ∀ b, (1 : ℝ) / 2 ≤ ∑ a, p a * A a b := by
  obtain ⟨p, hp, q, hq, hrow, hcol, -⟩ := AGT.zero_sum_minimax A
  refine ⟨p, hp, fun b => ?_⟩
  have hqq : (1 : ℝ) / 2 ≤ q ⬝ᵥ A.mulVec q := by
    have hT : q ⬝ᵥ A.mulVec q = ∑ a, ∑ b, q a * A a b * q b := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have hT' : ∑ a, ∑ b, q a * A b a * q b = ∑ a, ∑ b, q a * A a b * q b := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have hsum : ∑ a, ∑ b, q a * q b = 1 := by
      have := hq.2
      calc ∑ a, ∑ b, q a * q b = (∑ a, q a) * (∑ b, q b) := by rw [Finset.sum_mul_sum]
        _ = 1 := by rw [this]; norm_num
    have hge : ∑ a, ∑ b, q a * q b ≤ ∑ a, ∑ b, (q a * A a b * q b + q a * A b a * q b) := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro b _
      have := hq.1 a; have := hq.1 b
      have h3 := hA a b
      have hpos : 0 ≤ q a * q b := by positivity
      nlinarith
    simp only [Finset.sum_add_distrib] at hge
    rw [hT]
    linarith
  have h1 := hrow q hq
  have h2 := hcol (Pi.single b 1) (by
    refine ⟨fun i => ?_, ?_⟩
    · by_cases h : i = b <;> simp [Pi.single_apply, h]
    · simp)
  have h3 : p ⬝ᵥ A.mulVec (Pi.single b 1) = ∑ a, p a * A a b := by
    simp [dotProduct, Matrix.mulVec, Pi.single_apply]
  linarith

end SubadditiveMMS580.Amplification.Dev.L31
end

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification
open SubadditiveMMS580.Amplification.Dev.L31 SubadditiveMMS580.Amplification.Dev.FD in
theorem chk_lemma_3_1 (s : ℕ) (hs : 0 < s) (v : Finset (Fin s) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotone v) (hsub : SubmodOrder.Subadditive v)
    (B : ℝ) (hB : 0 < B) :
    ∃ σ : FinDist (Fin s → ℝ),
      (∀ b ∈ σ.support, (∀ g, 0 ≤ b g) ∧ ∑ g, b g ≤ B) ∧
      ∀ c : Fin s → ℝ, (∀ g, 0 ≤ c g) → ∑ g, c g ≤ B / 2 →
        (1 : ℝ) / 2 ≤
          σ.prob (fun b =>
            v Finset.univ / 2 ≤ v (Finset.univ.filter (fun g => c g < b g))) := by
  classical
  set h : ℝ := B / (2 * s) with hh
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hhpos : 0 < h := by positivity
  have hsh : h * (2 * s) = B := by rw [hh]; field_simp
  let Kset : Finset (Fin s → ℕ) :=
    (Fintype.piFinset fun _ : Fin s => Finset.range (s + 1)).filter (fun z => ∑ g, z g ≤ s)
  have hK : ∀ z : Fin s → ℕ, z ∈ Kset ↔ ∑ g, z g ≤ s := by
    intro z
    simp only [Kset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro hz
      refine ⟨fun g => ?_, hz⟩
      have := Finset.single_le_sum (f := z) (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
      omega
  have hzero : (fun _ : Fin s => (0 : ℕ)) ∈ Kset := (hK _).2 (by simp)
  obtain ⟨N, hN⟩ : ∃ N, Kset.card = N + 1 :=
    ⟨Kset.card - 1, by have := Finset.card_pos.2 ⟨_, hzero⟩; omega⟩
  let e : Kset ≃ Fin (N + 1) := Finset.equivFinOfCardEq hN
  let zv : Fin (N + 1) → (Fin s → ℕ) := fun a => (e.symm a).1
  have hzv : ∀ a, ∑ g, zv a g ≤ s := fun a => (hK _).1 (e.symm a).2
  let A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := fun a b => Hf v (zv a) (zv b)
  obtain ⟨p, hp, hpv⟩ := exists_simplex_half A (fun a b => Hf_add_ge v hsub _ _)
  let bvec : Fin (N + 1) → (Fin s → ℝ) := fun a g => h * ((zv a g : ℝ) + 1)
  let π := ofSimplex p hp
  refine ⟨map π bvec, ?_, ?_⟩
  · intro b hb
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hb
    refine ⟨fun g => by positivity, ?_⟩
    have h1 : ∑ g, bvec a g = h * ((∑ g, (zv a g : ℝ)) + s) := by
      simp only [bvec, ← Finset.mul_sum, Finset.sum_add_distrib]
      simp
    rw [h1]
    have h2 : (∑ g, (zv a g : ℝ)) ≤ s := by exact_mod_cast hzv a
    nlinarith
  · intro c hc0 hcB
    let y : Fin s → ℕ := fun g => ⌊c g / h⌋₊
    have hyle : ∀ g, (y g : ℝ) * h ≤ c g := by
      intro g
      have := Nat.floor_le (show 0 ≤ c g / h by have := hc0 g; positivity)
      calc (y g : ℝ) * h ≤ c g / h * h := by gcongr
        _ = c g := by field_simp
    have hylt : ∀ g, c g < h * ((y g : ℝ) + 1) := by
      intro g
      have := Nat.lt_floor_add_one (c g / h)
      have h3 : c g / h * h < ((y g : ℝ) + 1) * h := by gcongr
      calc c g = c g / h * h := by field_simp
        _ < ((y g : ℝ) + 1) * h := h3
        _ = h * ((y g : ℝ) + 1) := by ring
    have hyK : y ∈ Kset := by
      rw [hK]
      have : (∑ g, (y g : ℝ)) * h ≤ B / 2 := by
        calc (∑ g, (y g : ℝ)) * h = ∑ g, (y g : ℝ) * h := by rw [Finset.sum_mul]
          _ ≤ ∑ g, c g := Finset.sum_le_sum fun g _ => hyle g
          _ ≤ B / 2 := hcB
      have h4 : (∑ g, (y g : ℝ)) ≤ s := by
        have : (∑ g, (y g : ℝ)) * h ≤ s * h := by nlinarith
        exact le_of_mul_le_mul_right this hhpos
      exact_mod_cast h4
    let a0 : Fin (N + 1) := e ⟨y, hyK⟩
    have hza0 : zv a0 = y := by simp [zv, a0]
    rw [prob_map]
    rw [prob_ofSimplex]
    refine le_trans (hpv a0) ?_
    apply Finset.sum_le_sum
    intro a _
    have hpa := hp.1 a
    by_cases hH : v Finset.univ / 2 ≤ v (Finset.univ.filter (fun g => y g ≤ zv a g))
    · have hE : v Finset.univ / 2 ≤ v (Finset.univ.filter (fun g => c g < bvec a g)) := by
        refine le_trans hH (hmono _ _ ?_)
        intro g hg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
        have hz : (y g : ℝ) ≤ zv a g := by exact_mod_cast hg
        calc c g < h * ((y g : ℝ) + 1) := hylt g
          _ ≤ h * ((zv a g : ℝ) + 1) := by gcongr
      have hA : A a a0 = 1 := by
        show Hf v (zv a) (zv a0) = 1
        rw [hza0]; unfold Hf; rw [if_pos hH]
      rw [hA, if_pos hE]; simp
    · have hA : A a a0 = 0 := by
        show Hf v (zv a) (zv a0) = 0
        rw [hza0]; unfold Hf; rw [if_neg hH]
      rw [hA]
      split_ifs <;> simp [hpa]

end SubadditiveMMS580.Amplification
end

theorem solution : type_of% @SubadditiveMMS580.Amplification.chk_lemma_3_1 := @SubadditiveMMS580.Amplification.chk_lemma_3_1
