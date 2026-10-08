-- Prove2me | solution 1 for WhitneyMatroid.Binary.cycles_eq_sums_of_strictFundamentalSet
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T22:12:22.77331+00:00
-- url     : https://prove2.me/submissions/76e8ef71-1b89-42bf-aa69-04989bcd8ccd

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


namespace WhitneyBin

section Fund

variable {r q : ℕ}

lemma natAdd_ne_castAdd (i : Fin q) (j : Fin r) : Fin.natAdd r i ≠ Fin.castAdd q j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.coe_natAdd, Fin.coe_castAdd] at this
  omega

lemma natAdd_notMem (i : Fin q) :
    Fin.natAdd r i ∉ range (Fin.castAdd q : Fin r → Fin (r + q)) := by
  rintro ⟨j, hj⟩
  exact natAdd_ne_castAdd i j hj.symm

lemma castAdd_mem (j : Fin r) :
    Fin.castAdd q j ∈ range (Fin.castAdd q : Fin r → Fin (r + q)) := ⟨j, rfl⟩

/-- A set containing `e_{n-q+i}` but no other `e_{n-q+j}` lies in `B + e_{n-q+i}`. -/
lemma subset_insert_of_mem_iff {P : Set (Fin (r + q))} {i : Fin q}
    (h : ∀ j, Fin.natAdd r j ∈ P ↔ j = i) :
    P ⊆ insert (Fin.natAdd r i) (range (Fin.castAdd q : Fin r → Fin (r + q))) := by
  intro x hx
  induction x using Fin.addCases with
  | left j => exact Or.inr (castAdd_mem j)
  | right j =>
    rw [(h j).1 hx]
    exact mem_insert _ _

lemma mem_iff_of_subset_insert {P : Set (Fin (r + q))} {i : Fin q}
    (hmem : Fin.natAdd r i ∈ P)
    (hsub : P ⊆ insert (Fin.natAdd r i) (range (Fin.castAdd q : Fin r → Fin (r + q)))) :
    ∀ j, Fin.natAdd r j ∈ P ↔ j = i := by
  intro j
  refine ⟨fun hj => ?_, fun hj => hj ▸ hmem⟩
  rcases hsub hj with h | h
  · exact (Fin.natAdd_inj r).1 h
  · exact absurd h (natAdd_notMem j)

variable {M : Matroid (Fin (r + q))}

lemma card_B : (range (Fin.castAdd q : Fin r → Fin (r + q))).encard = r := by
  rw [← (finite_range _).cast_ncard_eq, ncard_range_of_injective (Fin.castAdd_injective r q),
    Nat.card_eq_fintype_card, Fintype.card_fin]

lemma closure_B (hE : M.E = univ) {P : Fin q → Set (Fin (r + q))}
    (hc : ∀ i, M.IsCircuit (P i)) (hm : ∀ i j, Fin.natAdd r j ∈ P i ↔ j = i) :
    M.closure (range (Fin.castAdd q : Fin r → Fin (r + q))) = univ := by
  refine eq_univ_of_forall fun x => ?_
  induction x using Fin.addCases with
  | left j =>
    exact M.subset_closure _ (by rw [hE]; exact subset_univ _) (castAdd_mem j)
  | right i =>
    have hi : Fin.natAdd r i ∈ P i := (hm i i).2 rfl
    refine M.closure_mono ?_ ((hc i).mem_closure_sdiff_singleton_of_mem hi)
    intro x ⟨hx, hxi⟩
    rcases subset_insert_of_mem_iff (hm i) hx with h | h
    · exact absurd h hxi
    · exact h

lemma eRank_eq_r (hE : M.E = univ) {P : Fin q → Set (Fin (r + q))}
    (hc : ∀ i, M.IsCircuit (P i)) (hm : ∀ i j, Fin.natAdd r j ∈ P i ↔ j = i) :
    M.eRank = M.eRk (range (Fin.castAdd q : Fin r → Fin (r + q))) := by
  rw [← M.eRk_ground, hE, ← closure_B hE hc hm, M.eRk_closure_eq]

lemma isBase_of_sfs (hE : M.E = univ) {P : Fin q → Set (Fin (r + q))}
    (hP : IsStrictFundamentalSet M P) :
    M.IsBase (range (Fin.castAdd q : Fin r → Fin (r + q))) := by
  obtain ⟨hn, hc, hm⟩ := hP
  have hcl := closure_B hE hc hm
  have hrk := eRank_eq_r hE hc hm
  have hr : M.eRank = r := by
    rw [hE, encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin] at hn
    have hne : M.eRank ≠ ⊤ := by
      intro h
      rw [h, top_add] at hn
      exact ENat.natCast_ne_top _ hn.symm
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
    rw [← hk] at hn ⊢
    have : k + q = r + q := by exact_mod_cast hn
    have : k = r := by omega
    rw [this]
  have hind : M.Indep (range (Fin.castAdd q : Fin r → Fin (r + q))) := by
    rw [Matroid.indep_iff_eRk_eq_encard_of_finite (finite_range _), card_B, ← hrk, hr]
  refine hind.isBase_of_spanning ?_
  rw [Matroid.spanning_iff_closure_eq (by rw [hE]; exact subset_univ _), hcl, hE]

lemma sfs_of (hE : M.E = univ) {P : Fin q → Set (Fin (r + q))}
    (hB : M.Indep (range (Fin.castAdd q : Fin r → Fin (r + q))))
    (hc : ∀ i, M.IsCircuit (P i)) (hm : ∀ i j, Fin.natAdd r j ∈ P i ↔ j = i) :
    IsStrictFundamentalSet M P := by
  refine ⟨?_, hc, hm⟩
  rw [eRank_eq_r hE hc hm, (Matroid.indep_iff_eRk_eq_encard_of_finite (finite_range _)).1 hB,
    card_B, hE, encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  norm_cast

/-- Theorem 9. -/
theorem exists_unique_sfs (hE : M.E = univ)
    (hB : M.IsBase (range (Fin.castAdd q : Fin r → Fin (r + q)))) :
    ∃! P : Fin q → Set (Fin (r + q)), IsStrictFundamentalSet M P := by
  set B := range (Fin.castAdd q : Fin r → Fin (r + q))
  have hm : ∀ i j, Fin.natAdd r j ∈ M.fundCircuit (Fin.natAdd r i) B ↔ j = i := fun i =>
    mem_iff_of_subset_insert (M.mem_fundCircuit _ _) (M.fundCircuit_subset_insert _ _)
  have hc : ∀ i, M.IsCircuit (M.fundCircuit (Fin.natAdd r i) B) := fun i =>
    hB.fundCircuit_isCircuit (by rw [hE]; exact mem_univ _) (natAdd_notMem i)
  refine ⟨fun i => M.fundCircuit (Fin.natAdd r i) B, sfs_of hE hB.indep hc hm, fun P hP => ?_⟩
  funext i
  exact (hP.2.1 i).eq_fundCircuit_of_subset hB.indep (subset_insert_of_mem_iff (hP.2.2 i))

lemma sumMod2_mem_iff {P : Fin q → Set (Fin (r + q))}
    (hm : ∀ i j, Fin.natAdd r j ∈ P i ↔ j = i) (s : Finset (Fin q)) (j : Fin q) :
    Fin.natAdd r j ∈ sumMod2 s P ↔ j ∈ s := by
  classical
  rw [← chi_ne_zero, chi_sumMod2, Finset.sum_apply]
  have : ∀ i ∈ s, chi (P i) (Fin.natAdd r j) = if j = i then 1 else 0 := fun i _ => by
    unfold chi
    by_cases h : j = i
    · subst h
      simp [(hm j j).2 rfl]
    · simp [h, hm i j]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  split_ifs with h <;> simp [h]

/-- Theorem 34. -/
theorem cycles_eq (hE : M.E = univ) (hC : SatisfiesCStar {C | M.IsCircuit C})
    (P : Fin q → Set (Fin (r + q))) (hP : IsStrictFundamentalSet M P) :
    {Q | IsCycleOf {C | M.IsCircuit C} Q} = range (fun s : Finset (Fin q) => sumMod2 s P) ∧
      {Q | IsCycleOf {C | M.IsCircuit C} Q}.ncard = 2 ^ q := by
  classical
  have hB := isBase_of_sfs hE hP
  obtain ⟨-, hc, hm⟩ := hP
  have hPinj : Function.Injective P := fun i j h => by
    have := (hm j i).1 (h ▸ (hm i i).2 rfl)
    exact this
  have hcyc : ∀ s : Finset (Fin q), IsCycleOf {C | M.IsCircuit C} (sumMod2 s P) := fun s => by
    refine ⟨s.image P, fun N hN => ?_, chi_injective ?_⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hN)
      exact hc i
    · rw [chi_sumMod2, chi_sumMod2, Finset.sum_image fun i _ j _ h => hPinj h]
      rfl
  have heq : {Q | IsCycleOf {C | M.IsCircuit C} Q} =
      range (fun s : Finset (Fin q) => sumMod2 s P) := by
    ext Q
    refine ⟨fun hQ => ?_, ?_⟩
    · set s := Finset.univ.filter (fun i => Fin.natAdd r i ∈ Q)
      refine ⟨s, ?_⟩
      have hR := isCycle_symmDiff hQ (hcyc s)
      have hRB : symmDiff Q (sumMod2 s P) ⊆ range (Fin.castAdd q : Fin r → Fin (r + q)) := by
        intro x hx
        induction x using Fin.addCases with
        | left j => exact castAdd_mem j
        | right j =>
          exfalso
          have h1 : Fin.natAdd r j ∈ Q ↔ Fin.natAdd r j ∈ sumMod2 s P := by
            rw [sumMod2_mem_iff hm, Finset.mem_filter]
            simp
          rcases Set.mem_symmDiff.1 hx with h | h
          · exact h.2 (h1.1 h.1)
          · exact h.2 (h1.2 h.1)
      have hR0 : symmDiff Q (sumMod2 s P) = ∅ := by
        by_contra hne
        obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
        obtain ⟨C, hCc, -, hCR⟩ := exists_mem_of_isTrueSum (hC _ hR) hx
        exact hCc.not_indep (hB.indep.subset (hCR.trans hRB))
      exact (symmDiff_eq_bot.1 hR0).symm
    · rintro ⟨s, rfl⟩
      exact hcyc s
  refine ⟨heq, ?_⟩
  rw [heq, ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_finset,
    Fintype.card_fin]
  intro s t hst
  ext j
  rw [← sumMod2_mem_iff hm, ← sumMod2_mem_iff hm]
  exact Iff.of_eq (congrArg (Fin.natAdd r j ∈ ·) hst)

/-- Theorem 35. -/
theorem circuits_eq (M' : Matroid (Fin (r + q)))
    (hE : M.E = univ) (hE' : M'.E = univ)
    (hC : SatisfiesCStar {C | M.IsCircuit C}) (hC' : SatisfiesCStar {C | M'.IsCircuit C})
    (P : Fin q → Set (Fin (r + q)))
    (hP : IsStrictFundamentalSet M P) (hP' : IsStrictFundamentalSet M' P) :
    ∀ C : Set (Fin (r + q)), M.IsCircuit C ↔ M'.IsCircuit C := by
  have h1 := (cycles_eq hE hC P hP).1
  have h2 := (cycles_eq hE' hC' P hP').1
  have hcyc : ∀ Q, IsCycleOf {C | M.IsCircuit C} Q ↔ IsCycleOf {C | M'.IsCircuit C} Q :=
    fun Q => by
      change Q ∈ {Q | IsCycleOf {C | M.IsCircuit C} Q} ↔ Q ∈ {Q | IsCycleOf {C | M'.IsCircuit C} Q}
      rw [h1, h2]
  intro C
  rw [isCircuit_iff_minimal hC, isCircuit_iff_minimal hC', hcyc]
  simp only [hcyc]

lemma eq_of_sfs (M' : Matroid (Fin (r + q)))
    (hE : M.E = univ) (hE' : M'.E = univ)
    (hC : SatisfiesCStar {C | M.IsCircuit C}) (hC' : SatisfiesCStar {C | M'.IsCircuit C})
    (P : Fin q → Set (Fin (r + q)))
    (hP : IsStrictFundamentalSet M P) (hP' : IsStrictFundamentalSet M' P) : M = M' :=
  Matroid.ext_isCircuit (hE.trans hE'.symm) fun C _ => circuits_eq M' hE hE' hC hC' P hP hP' C

end Fund

end WhitneyBin

theorem solution {r q : ℕ} (M : Matroid (Fin (r + q)))
    (hE : M.E = Set.univ) (hC : SatisfiesCStar {C | M.IsCircuit C})
    (P : Fin q → Set (Fin (r + q))) (hP : IsStrictFundamentalSet M P) :
    {Q | IsCycleOf {C | M.IsCircuit C} Q} = Set.range (fun s : Finset (Fin q) => sumMod2 s P) ∧
      {Q | IsCycleOf {C | M.IsCircuit C} Q}.ncard = 2 ^ q :=
  WhitneyBin.cycles_eq hE hC P hP
