-- Prove2me | solution 1 for Supermodularity.Matching.exists_increasing_optimal_matching_and_tight_optimality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:46:24.37196+00:00
-- url     : https://prove2.me/submissions/e2d7f1aa-9d81-4ed3-b847-e8aa1c6db1e4

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Matching_IsOptimalMatching
import Definitions.Def_Supermodularity_Matching_IsIncreasingMatching
import Definitions.Def_Supermodularity_Matching_IsTightMatching



namespace Supermodularity.Matching

open Classical

theorem mt_sum_two {m : ℕ} {M : Type*} [AddCommMonoid M] (F G : Fin m → M) (j j' : Fin m)
    (hne : j ≠ j') (h : ∀ t, t ≠ j → t ≠ j' → F t = G t) :
    ∃ R, ∑ t, F t = F j + F j' + R ∧ ∑ t, G t = G j + G j' + R := by
  have hj' : j' ∈ (Finset.univ : Finset (Fin m)).erase j := by simp [Ne.symm hne]
  refine ⟨∑ t ∈ ((Finset.univ : Finset (Fin m)).erase j).erase j', F t, ?_, ?_⟩
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _ hj', add_assoc]
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _ hj', add_assoc]
    congr 2
    refine Finset.sum_congr rfl (fun t ht => ?_)
    simp only [Finset.mem_erase] at ht
    exact (h t ht.2.1 ht.1).symm

theorem mt_perm_id {m : ℕ} (s : Fin m → Fin m) (hs : Function.Bijective s) (hm : Monotone s) :
    s = id := by
  have h1 : StrictMono s := hm.strictMono_of_injective hs.1
  have h2 : Set.range s = Set.range (id : Fin m → Fin m) := by
    rw [hs.2.range_eq, Set.range_id]
  exact (StrictMono.range_inj h1 strictMono_id).1 h2

def mtP {n m : ℕ} (σ : Fin m → Fin n → Fin m) : ℕ := ∑ i : Fin n, ∑ j : Fin m, (j : ℕ) * (σ j i : ℕ)

theorem mt_P_le {n m : ℕ} (σ : Fin m → Fin n → Fin m) : mtP σ ≤ n * (m * (m * m)) := by
  unfold mtP
  calc ∑ i, ∑ j : Fin m, (j : ℕ) * (σ j i : ℕ) ≤ ∑ _i : Fin n, ∑ _j : Fin m, m * m := by
        apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
        exact Nat.mul_le_mul j.isLt.le (σ j i).isLt.le
    _ = n * (m * (m * m)) := by simp

theorem mt_core {n m : ℕ} (g : (Fin n → Fin m) → Fin m → ℝ)
    (hg : ∀ k k' j j', g k j + g k' j' ≤ g (k ⊔ k') (j ⊔ j') + g (k ⊓ k') (j ⊓ j')) :
    ∀ d, ∀ σ : Fin m → Fin n → Fin m, n * (m * (m * m)) - mtP σ = d →
      (∀ i, Function.Bijective (fun j => σ j i)) →
      ∑ j, g (σ j) j ≤ ∑ j, g (fun _ => j) j := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro σ hd hbij
  by_cases hmono : ∀ j j', j ≤ j' → σ j ≤ σ j'
  · have : ∀ j, σ j = fun _ => j := by
      intro j; funext i
      have := mt_perm_id (fun j => σ j i) (hbij i) (fun a b hab => hmono a b hab i)
      exact congrFun this j
    simp [this]
  push_neg at hmono
  obtain ⟨j, j', hjj, hn⟩ := hmono
  have hne : j ≠ j' := by rintro rfl; exact hn le_rfl
  have hlt : j < j' := lt_of_le_of_ne hjj hne
  let σ' : Fin m → Fin n → Fin m := fun t =>
    if t = j then σ j ⊓ σ j' else if t = j' then σ j ⊔ σ j' else σ t
  have hσj : σ' j = σ j ⊓ σ j' := by simp [σ']
  have hσj' : σ' j' = σ j ⊔ σ j' := by simp [σ', Ne.symm hne]
  have hσt : ∀ t, t ≠ j → t ≠ j' → σ' t = σ t := by
    intro t h1 h2; simp [σ', h1, h2]
  -- bijectivity
  have hbij' : ∀ i, Function.Bijective (fun t => σ' t i) := by
    intro i
    by_cases hle : σ j i ≤ σ j' i
    · have : (fun t => σ' t i) = (fun t => σ t i) := by
        funext t
        by_cases h1 : t = j
        · subst h1; rw [hσj]; simp [Pi.inf_apply, hle]
        by_cases h2 : t = j'
        · subst h2; rw [hσj']; simp [Pi.sup_apply, hle]
        rw [hσt t h1 h2]
      rw [this]; exact hbij i
    · have : (fun t => σ' t i) = (fun t => σ t i) ∘ Equiv.swap j j' := by
        funext t
        simp only [Function.comp]
        push_neg at hle
        by_cases h1 : t = j
        · subst h1; rw [hσj, Equiv.swap_apply_left]; simp [Pi.inf_apply, hle.le]
        by_cases h2 : t = j'
        · subst h2; rw [hσj', Equiv.swap_apply_right]; simp [Pi.sup_apply, hle.le]
        rw [hσt t h1 h2, Equiv.swap_apply_of_ne_of_ne h1 h2]
      rw [this]; exact (hbij i).comp (Equiv.swap j j').bijective
  -- potential increases
  have hP : mtP σ < mtP σ' := by
    unfold mtP
    obtain ⟨i0, hi0⟩ : ∃ i, ¬ σ j i ≤ σ j' i := by
      by_contra hc; push_neg at hc; exact hn (fun i => hc i)
    have hloc : ∀ i, ((j : ℕ) * (σ j i : ℕ) + (j' : ℕ) * (σ j' i : ℕ) ≤
        (j : ℕ) * (σ' j i : ℕ) + (j' : ℕ) * (σ' j' i : ℕ)) ∧
        (¬ σ j i ≤ σ j' i → (j : ℕ) * (σ j i : ℕ) + (j' : ℕ) * (σ j' i : ℕ) <
        (j : ℕ) * (σ' j i : ℕ) + (j' : ℕ) * (σ' j' i : ℕ)) := by
      intro i
      rw [hσj, hσj', Pi.inf_apply, Pi.sup_apply]
      have hjl : (j : ℕ) < (j' : ℕ) := hlt
      by_cases hle : σ j i ≤ σ j' i
      · simp [hle]
      · refine ⟨?_, fun _ => ?_⟩ <;>
        · have hle2 : σ j' i < σ j i := lt_of_not_ge hle
          rw [inf_eq_right.2 hle2.le, sup_eq_left.2 hle2.le]
          have h3 : (σ j' i : ℕ) < (σ j i : ℕ) := hle2
          nlinarith
    apply Finset.sum_lt_sum
    · intro i _
      obtain ⟨R, h1, h2⟩ := mt_sum_two (fun t => (t : ℕ) * (σ t i : ℕ))
        (fun t => (t : ℕ) * (σ' t i : ℕ)) j j' hne (fun t h1 h2 => by simp [hσt t h1 h2])
      rw [h1, h2]; exact Nat.add_le_add_right (hloc i).1 _
    · refine ⟨i0, Finset.mem_univ _, ?_⟩
      obtain ⟨R, h1, h2⟩ := mt_sum_two (fun t => (t : ℕ) * (σ t i0 : ℕ))
        (fun t => (t : ℕ) * (σ' t i0 : ℕ)) j j' hne (fun t h1 h2 => by simp [hσt t h1 h2])
      rw [h1, h2]; exact Nat.add_lt_add_right ((hloc i0).2 hi0) _
  have hsum : ∑ t, g (σ t) t ≤ ∑ t, g (σ' t) t := by
    obtain ⟨R, h1, h2⟩ := mt_sum_two (fun t => g (σ t) t) (fun t => g (σ' t) t) j j' hne
      (fun t h1 h2 => by simp [hσt t h1 h2])
    rw [h1, h2]
    have := hg (σ j) (σ j') j j'
    rw [sup_eq_right.2 hjj, inf_eq_left.2 hjj] at this
    simp only [hσj, hσj']
    linarith
  have hb := mt_P_le σ'
  have := ih (n * (m * (m * m)) - mtP σ') (by omega) σ' rfl hbij'
  exact hsum.trans this

theorem mt_part1 {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)] [∀ i, Fintype (X i)]
    [∀ i, Nonempty (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : Supermodularity.Monotonicity.SupermodularOn
      (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ) :
    ∃ x : Fin m → ∀ i, X i, IsIncreasingMatching x ∧ IsOptimalMatching f x := by
  have hs : ∀ a b : ∀ i, X i, ∀ j j' : Fin m,
      f a j + f b j' ≤ f (a ⊔ b) (j ⊔ j') + f (a ⊓ b) (j ⊓ j') := by
    intro a b j j'
    exact hf (x := (a, j)) (y := (b, j')) (Set.mem_univ _) (Set.mem_univ _)
  let S : Fin m → Finset (∀ i, X i) := fun j =>
    Finset.univ.filter (fun a => ∀ b, f b j ≤ f a j)
  have hSne : ∀ j, (S j).Nonempty := by
    intro j
    obtain ⟨a, ha⟩ := Finite.exists_max (fun a => f a j)
    exact ⟨a, by simp [S, ha]⟩
  let x : Fin m → ∀ i, X i := fun j => (S j).sup' (hSne j) id
  have hxmem : ∀ j, ∀ b, f b j ≤ f (x j) j := by
    intro j
    have : x j ∈ ({a | ∀ b, f b j ≤ f a j} : Set (∀ i, X i)) := by
      apply Finset.sup'_mem
      · intro a ha c hc b
        have h := hs a c j j
        simp only [sup_idem, inf_idem] at h
        have := ha (a ⊓ c)
        have := hc b
        have : f c j ≤ f (a ⊔ c) j := by linarith [ha c]
        linarith
      · intro a ha; simpa [S] using ha
    simpa using this
  have hxge : ∀ j a, (∀ b, f b j ≤ f a j) → a ≤ x j := by
    intro j a ha
    exact Finset.le_sup' (f := id) (by simp [S, ha])
  refine ⟨x, ?_, ?_⟩
  · intro j j' hjj
    have h := hs (x j) (x j') j j'
    rw [sup_eq_right.2 hjj, inf_eq_left.2 hjj] at h
    have h1 := hxmem j (x j ⊓ x j')
    have h2 : ∀ b, f b j' ≤ f (x j ⊔ x j') j' := by
      intro b; have := hxmem j' b; linarith
    exact le_sup_left.trans (hxge j' _ h2)
  · intro y
    exact Finset.sum_le_sum (fun j _ => hxmem j (y j))

theorem mt_part2 {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : Supermodularity.Monotonicity.SupermodularOn
      (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ)
    (x : Fin m → ∀ i, X i) (hxt : IsTightMatching x) (hxi : IsIncreasingMatching x)
    (y : Fin m → ∀ i, X i) (hyt : IsTightMatching y) : ∑ j, f (y j) j ≤ ∑ j, f (x j) j := by
  let e : ∀ i, Fin m ≃ X i := fun i => Equiv.ofBijective (fun j => x j i) (hxt i)
  let φ : (Fin n → Fin m) → ∀ i, X i := fun k i => x (k i) i
  have hsup : ∀ k k', φ (k ⊔ k') = φ k ⊔ φ k' := by
    intro k k'; funext i
    simp only [φ, Pi.sup_apply]
    rcases le_total (k i) (k' i) with h | h
    · rw [sup_eq_right.2 h, sup_eq_right.2 (hxi h i)]
    · rw [sup_eq_left.2 h, sup_eq_left.2 (hxi h i)]
  have hinf : ∀ k k', φ (k ⊓ k') = φ k ⊓ φ k' := by
    intro k k'; funext i
    simp only [φ, Pi.inf_apply]
    rcases le_total (k i) (k' i) with h | h
    · rw [inf_eq_left.2 h, inf_eq_left.2 (hxi h i)]
    · rw [inf_eq_right.2 h, inf_eq_right.2 (hxi h i)]
  let g : (Fin n → Fin m) → Fin m → ℝ := fun k j => f (φ k) j
  have hg : ∀ k k' j j', g k j + g k' j' ≤ g (k ⊔ k') (j ⊔ j') + g (k ⊓ k') (j ⊓ j') := by
    intro k k' j j'
    simp only [g, hsup, hinf]
    exact hf (x := (φ k, j)) (y := (φ k', j')) (Set.mem_univ _) (Set.mem_univ _)
  let σ : Fin m → Fin n → Fin m := fun j i => (e i).symm (y j i)
  have hyσ : ∀ j, φ (σ j) = y j := by
    intro j; funext i
    exact (e i).apply_symm_apply (y j i)
  have hbij : ∀ i, Function.Bijective (fun j => σ j i) :=
    fun i => (e i).symm.bijective.comp (hyt i)
  have := mt_core g hg _ σ rfl hbij
  simpa [g, hyσ, φ] using this

theorem mt_main {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)] [∀ i, Fintype (X i)]
    [∀ i, Nonempty (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : Supermodularity.Monotonicity.SupermodularOn
      (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ) :
    (∃ x : Fin m → ∀ i, X i, IsIncreasingMatching x ∧ IsOptimalMatching f x) ∧
      ((∀ i, Fintype.card (X i) = m) →
        ∀ x : Fin m → ∀ i, X i, IsTightMatching x → IsIncreasingMatching x →
          ∀ y : Fin m → ∀ i, X i, IsTightMatching y → ∑ j, f (y j) j ≤ ∑ j, f (x j) j) :=
  ⟨mt_part1 f hf, fun _ x hxt hxi y hyt => mt_part2 f hf x hxt hxi y hyt⟩

end Supermodularity.Matching

open Supermodularity.Matching


theorem solution
    {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)] [∀ i, Fintype (X i)]
    [∀ i, Nonempty (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : Supermodularity.Monotonicity.SupermodularOn
      (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ) :
    (∃ x : Fin m → ∀ i, X i, IsIncreasingMatching x ∧ IsOptimalMatching f x) ∧
      ((∀ i, Fintype.card (X i) = m) →
        ∀ x : Fin m → ∀ i, X i, IsTightMatching x → IsIncreasingMatching x →
          ∀ y : Fin m → ∀ i, X i, IsTightMatching y → ∑ j, f (y j) j ≤ ∑ j, f (x j) j) := by
  exact mt_main f hf
