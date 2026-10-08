-- Prove2me | solution 1 for WhitneyMatroid.Binary.c2_of_cStar
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T22:12:19.12607+00:00
-- url     : https://prove2.me/submissions/2322b271-dbe1-4595-9f9a-b444d502a9ba

import Mathlib
import Definitions.Def_WhitneyMatroid_Binary_Cycles
import Definitions.Def_WhitneyMatroid_Binary_IsMatroidOf
import Definitions.Def_WhitneyMatroid_Binary_IsStrictFundamentalSet

open WhitneyMatroid.Binary Module Set


namespace WhitneyBin

section Cyc

variable {α : Type*}

lemma zmod2_eq {a b : ZMod 2} (h : a ≠ 0 ↔ b ≠ 0) : a = b :=
  (by decide : ∀ a b : ZMod 2, (a ≠ 0 ↔ b ≠ 0) → a = b) a b h

lemma vec_add_self (v : α → ZMod 2) : v + v = 0 := by
  funext x
  exact (by decide : ∀ t : ZMod 2, t + t = 0) (v x)

open Classical in
/-- The characteristic vector (mod 2) of a set. -/
noncomputable def chi (S : Set α) : α → ZMod 2 := fun x => if x ∈ S then 1 else 0

lemma chi_ne_zero {S : Set α} {x : α} : chi S x ≠ 0 ↔ x ∈ S := by
  unfold chi
  split_ifs with h <;> simp [h]

lemma chi_injective : Function.Injective (chi (α := α)) := by
  intro S T h
  ext x
  rw [← chi_ne_zero, ← chi_ne_zero, h]

lemma chi_sumMod2 {ι : Type*} (s : Finset ι) (N : ι → Set α) :
    chi (sumMod2 s N) = ∑ i ∈ s, chi (N i) := by
  classical
  funext x
  rw [Finset.sum_apply]
  refine zmod2_eq ?_
  rw [chi_ne_zero]
  have h1 : ∑ i ∈ s, chi (N i) x = ((s.filter (fun i => x ∈ N i)).card : ZMod 2) := by
    rw [← Finset.sum_boole]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold chi
    split_ifs <;> rfl
  rw [h1, ZMod.natCast_ne_zero_iff_odd]
  unfold sumMod2
  simp only [mem_setOf_eq]

lemma chi_symmDiff (S T : Set α) : chi (symmDiff S T) = chi S + chi T := by
  funext x
  refine zmod2_eq ?_
  rw [chi_ne_zero, Pi.add_apply]
  unfold chi
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> simp [hS, hT, Set.mem_symmDiff] <;> decide

lemma chi_empty : chi (∅ : Set α) = 0 := by
  funext x
  simp [chi]

lemma sum_symmDiff {β : Type*} [DecidableEq β] (F G : Finset β) (f : β → α → ZMod 2) :
    ∑ N ∈ symmDiff F G, f N = ∑ N ∈ F, f N + ∑ N ∈ G, f N := by
  rw [← Finset.sum_union_inter, symmDiff_eq_sup_sdiff_inf]
  have h := Finset.sum_sdiff (f := f) (Finset.inter_subset_union (s := F) (t := G))
  change ∑ N ∈ (F ∪ G) \ (F ∩ G), f N = _
  rw [← h, add_assoc, vec_add_self, add_zero]

variable {𝒞 : Set (Set α)}

lemma isCycle_symmDiff {Q R : Set α} (hQ : IsCycleOf 𝒞 Q) (hR : IsCycleOf 𝒞 R) :
    IsCycleOf 𝒞 (symmDiff Q R) := by
  classical
  obtain ⟨F, hF, rfl⟩ := hQ
  obtain ⟨G, hG, rfl⟩ := hR
  refine ⟨symmDiff F G, fun N hN => ?_, chi_injective ?_⟩
  · rcases Finset.mem_symmDiff.1 hN with h | h
    · exact hF h.1
    · exact hG h.1
  · rw [chi_symmDiff, chi_sumMod2, chi_sumMod2, chi_sumMod2, sum_symmDiff]

lemma isCycle_of_mem {C : Set α} (hC : C ∈ 𝒞) : IsCycleOf 𝒞 C := by
  classical
  refine ⟨{C}, by simpa using hC, chi_injective ?_⟩
  rw [chi_sumMod2, Finset.sum_singleton]
  rfl

lemma isCycle_empty : IsCycleOf 𝒞 ∅ := by
  refine ⟨∅, by simp, chi_injective ?_⟩
  rw [chi_sumMod2, Finset.sum_empty, chi_empty]

lemma isCycle_of_isTrueSum {Q : Set α} (hQ : IsTrueSumOf 𝒞 Q) : IsCycleOf 𝒞 Q := by
  classical
  obtain ⟨F, hF, hd, rfl⟩ := hQ
  refine ⟨F, hF, ?_⟩
  ext x
  simp only [mem_iUnion, sumMod2, mem_setOf_eq, id, exists_prop]
  have hle : (F.filter (fun N => x ∈ N)).card ≤ 1 := by
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    rw [Finset.mem_filter] at ha hb
    by_contra hab
    exact Set.disjoint_left.1 (hd ha.1 hb.1 hab) ha.2 hb.2
  have hpos : (∃ N ∈ F, x ∈ N) ↔ 0 < (F.filter (fun N => x ∈ N)).card := by
    rw [Finset.card_pos, Finset.filter_nonempty_iff]
  rw [hpos, Nat.odd_iff]
  constructor
  · intro h
    have : (F.filter (fun N => x ∈ N)).card = 1 := by omega
    first
      | (simp only [Finset.filter_congr_decidable] at *; omega)
      | (rw [this])
      | (convert congrArg (· % 2) this using 2)
  · intro h
    have : (F.filter (fun N => x ∈ N)).card % 2 = 1 := by convert h
    omega

lemma exists_mem_of_isTrueSum {Q : Set α} (hQ : IsTrueSumOf 𝒞 Q) {x : α} (hx : x ∈ Q) :
    ∃ C ∈ 𝒞, x ∈ C ∧ C ⊆ Q := by
  obtain ⟨F, hF, -, rfl⟩ := hQ
  simp only [mem_iUnion, exists_prop] at hx
  obtain ⟨N, hN, hxN⟩ := hx
  exact ⟨N, hF hN, hxN, subset_biUnion_of_mem (u := id) hN⟩

lemma sumMod2_pair {P₁ P₂ : Set α} (h : P₁ ≠ P₂) :
    sumMod2 ({P₁, P₂} : Finset (Set α)) id = symmDiff P₁ P₂ := by
  classical
  refine chi_injective ?_
  rw [chi_sumMod2, Finset.sum_pair h, chi_symmDiff]
  rfl

end Cyc

section CycMatroid

variable {α : Type*} {M : Matroid α}

/-- Theorem 33. -/
theorem isCircuit_iff_minimal (hC : SatisfiesCStar {C | M.IsCircuit C}) (C : Set α) :
    M.IsCircuit C ↔
      (IsCycleOf {C | M.IsCircuit C} C ∧ C.Nonempty ∧
        ∀ D : Set α, IsCycleOf {C | M.IsCircuit C} D → D.Nonempty → D ⊆ C → D = C) := by
  constructor
  · intro hCc
    refine ⟨isCycle_of_mem hCc, hCc.nonempty, fun D hD hDn hDC => ?_⟩
    obtain ⟨x, hx⟩ := hDn
    obtain ⟨C', hC', -, hC'D⟩ := exists_mem_of_isTrueSum (hC D hD) hx
    have := hC'.eq_of_subset_isCircuit hCc (hC'D.trans hDC)
    exact subset_antisymm hDC (this ▸ hC'D)
  · rintro ⟨hcyc, ⟨x, hx⟩, hmin⟩
    obtain ⟨C', hC', -, hC'C⟩ := exists_mem_of_isTrueSum (hC C hcyc) hx
    rwa [← hmin C' (isCycle_of_mem hC') hC'.nonempty hC'C]

/-- (C₂) from (C*). -/
theorem c2 {𝒞 : Set (Set α)} (hC : SatisfiesCStar 𝒞)
    (P₁ P₂ : Set α) (hP₁ : P₁ ∈ 𝒞) (hP₂ : P₂ ∈ 𝒞) (e₁ e₂ : α)
    (h₁₁ : e₁ ∈ P₁) (h₁₂ : e₁ ∈ P₂) (h₂₁ : e₂ ∈ P₁) (h₂₂ : e₂ ∉ P₂) :
    ∃ P₃ ∈ 𝒞, P₃ ⊆ P₁ ∪ P₂ ∧ e₂ ∈ P₃ ∧ e₁ ∉ P₃ := by
  classical
  have hne : P₁ ≠ P₂ := fun h => h₂₂ (h ▸ h₂₁)
  have hcyc : IsCycleOf 𝒞 (symmDiff P₁ P₂) :=
    isCycle_symmDiff (isCycle_of_mem hP₁) (isCycle_of_mem hP₂)
  have he₂ : e₂ ∈ symmDiff P₁ P₂ := Set.mem_symmDiff.2 (Or.inl ⟨h₂₁, h₂₂⟩)
  obtain ⟨P₃, hP₃, he, hsub⟩ := exists_mem_of_isTrueSum (hC _ hcyc) he₂
  refine ⟨P₃, hP₃, hsub.trans symmDiff_subset_union, he, fun h => ?_⟩
  rcases Set.mem_symmDiff.1 (hsub h) with h' | h'
  · exact h'.2 h₁₂
  · exact h'.2 h₁₁

end CycMatroid

end WhitneyBin

theorem solution {α : Type*} [Finite α] (𝒞 : Set (Set α)) (hC : SatisfiesCStar 𝒞)
    (P₁ P₂ : Set α) (hP₁ : P₁ ∈ 𝒞) (hP₂ : P₂ ∈ 𝒞) (e₁ e₂ : α)
    (h₁₁ : e₁ ∈ P₁) (h₁₂ : e₁ ∈ P₂) (h₂₁ : e₂ ∈ P₁) (h₂₂ : e₂ ∉ P₂) :
    ∃ P₃ ∈ 𝒞, P₃ ⊆ P₁ ∪ P₂ ∧ e₂ ∈ P₃ ∧ e₁ ∉ P₃ :=
  WhitneyBin.c2 hC P₁ P₂ hP₁ hP₂ e₁ e₂ h₁₁ h₁₂ h₂₁ h₂₂
