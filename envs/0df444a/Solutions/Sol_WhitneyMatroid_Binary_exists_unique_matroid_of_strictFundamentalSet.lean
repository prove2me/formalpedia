-- Prove2me | solution 1 for WhitneyMatroid.Binary.exists_unique_matroid_of_strictFundamentalSet
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T22:12:26.32402+00:00
-- url     : https://prove2.me/submissions/d77db5bb-c917-447f-9c89-bffb200cfbeb

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


namespace WhitneyBin

section Mat

variable {α : Type*} [Fintype α] {m : ℕ} (A : Matrix (Fin m) α (ZMod 2))

lemma finrank_span_of_indep {s : Set α} (h : LinearIndepOn (ZMod 2) A.col s) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (A.col '' s)) = s.ncard := by
  have : Fintype s := Fintype.ofFinite s
  rw [image_eq_range, finrank_span_eq_card h, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

lemma mem_span_of_not_indep {s : Set α} {e : α} (hs : LinearIndepOn (ZMod 2) A.col s)
    (hn : ¬ LinearIndepOn (ZMod 2) A.col (insert e s)) :
    A.col e ∈ Submodule.span (ZMod 2) (A.col '' s) := by
  by_cases he : e ∈ s
  · exact Submodule.subset_span (mem_image_of_mem _ he)
  · by_contra hc
    exact hn ((linearIndepOn_insert he).2 ⟨hs, hc⟩)

/-- The matroid of the columns of a matrix mod 2. -/
noncomputable def binMatroid : Matroid α :=
  (IndepMatroid.ofFinite (E := univ) finite_univ
    (fun I => LinearIndepOn (ZMod 2) A.col I)
    (linearIndepOn_empty (ZMod 2) A.col)
    (fun _ _ hJ hIJ => hJ.mono hIJ)
    (fun I J hI hJ hlt => by
      by_contra hno
      push Not at hno
      have hsub : A.col '' J ⊆ Submodule.span (ZMod 2) (A.col '' I) := by
        rintro _ ⟨e, heJ, rfl⟩
        by_cases heI : e ∈ I
        · exact Submodule.subset_span (mem_image_of_mem _ heI)
        · exact mem_span_of_not_indep A hI (hno e heJ heI)
      have hle := Submodule.finrank_mono (Submodule.span_le.2 hsub)
      rw [finrank_span_of_indep A hI, finrank_span_of_indep A hJ] at hle
      omega)
    (fun _ _ => subset_univ _)).matroid

lemma binMatroid_indep {I : Set α} :
    (binMatroid A).Indep I ↔ LinearIndepOn (ZMod 2) A.col I := by
  simp [binMatroid]

lemma binMatroid_isMatroidOf : IsMatroidOf (binMatroid A) A :=
  ⟨rfl, fun _ => binMatroid_indep A⟩

lemma eq_binMatroid {M : Matroid α} (h : IsMatroidOf M A) : M = binMatroid A :=
  Matroid.ext_indep h.1 fun I _ => (h.2 I).trans (binMatroid_indep A).symm

lemma mulVec_eq_sum (b : α → ZMod 2) : A.mulVec b = ∑ j, b j • A.col j := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

lemma linIndep_iff_ker {s : Set α} :
    LinearIndepOn (ZMod 2) A.col s ↔
      ∀ b : α → ZMod 2, (∀ j ∉ s, b j = 0) → A.mulVec b = 0 → b = 0 := by
  classical
  rw [linearIndepOn_iff'']
  constructor
  · intro h b hb hA
    funext j
    by_cases hj : j ∈ s
    · refine h s.toFinset b (by simp) (fun i hi => hb i (by simpa using hi)) ?_ j (by simpa using hj)
      rw [← hA, mulVec_eq_sum]
      refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
      rw [hb i (by simpa using hi), zero_smul]
    · exact hb j hj
  · intro h t g hts htg h0 i _
    have := h g (fun j hj => htg j fun hjt => hj (hts hjt)) (by
      rw [mulVec_eq_sum, ← h0]
      exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
        rw [htg i hi, zero_smul]).symm)
    rw [this]
    rfl

variable {M : Matroid α}

lemma indep_iff_ker (h : IsMatroidOf M A) {s : Set α} :
    M.Indep s ↔ ∀ b : α → ZMod 2, (∀ j ∉ s, b j = 0) → A.mulVec b = 0 → b = 0 :=
  (h.2 s).trans (linIndep_iff_ker A)

/-- Every circuit `C` satisfies `Σ_{j ∈ C} C_j = 0`. -/
lemma circuit_chi (h : IsMatroidOf M A) {C : Set α} (hC : M.IsCircuit C) :
    A.mulVec (chi C) = 0 := by
  have hdep := hC.not_indep
  rw [indep_iff_ker A h] at hdep
  push Not at hdep
  obtain ⟨b, hb, hA, hne⟩ := hdep
  have hsupp : ∀ j, b j ≠ 0 ↔ j ∈ C := fun j =>
    ⟨fun hj => by_contra fun hjC => hj (hb j hjC), fun hjC hj0 => hne (by
      refine (indep_iff_ker A h).1 (hC.sdiff_singleton_indep hjC) b (fun i hi => ?_) hA
      by_cases hiC : i ∈ C
      · have : i = j := by
          by_contra hij
          exact hi ⟨hiC, hij⟩
        rw [this, hj0]
      · exact hb i hiC)⟩
  have : b = chi C := funext fun j => zmod2_eq (by rw [chi_ne_zero]; exact hsupp j)
  rwa [← this]

lemma exists_circuit_of_mem_support (h : IsMatroidOf M A) {b : α → ZMod 2}
    (hA : A.mulVec b = 0) {j : α} (hj : b j ≠ 0) :
    ∃ C, M.IsCircuit C ∧ j ∈ C ∧ C ⊆ {k | b k ≠ 0} := by
  classical
  obtain rfl := eq_binMatroid A h
  set v := A.col
  set N := {k | b k ≠ 0}
  set S := N \ {j}
  obtain ⟨I, hI⟩ := (binMatroid A).exists_isBasis S (subset_univ _)
  have hIi : LinearIndepOn (ZMod 2) v I := (binMatroid_indep A).1 hI.indep
  have hle : Submodule.span (ZMod 2) (v '' S) ≤ Submodule.span (ZMod 2) (v '' I) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨e, heS, rfl⟩
    by_cases heI : e ∈ I
    · exact Submodule.subset_span (mem_image_of_mem _ heI)
    · refine mem_span_of_not_indep A hIi fun hins => ?_
      exact (hI.insert_dep ⟨heS, heI⟩).not_indep ((binMatroid_indep A).2 hins)
  have hmem : ∑ i ∈ Finset.univ.erase j, b i • v i ∈ Submodule.span (ZMod 2) (v '' S) := by
    refine Submodule.sum_mem _ fun i hi => ?_
    by_cases hiN : b i ≠ 0
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, ⟨hiN, Finset.ne_of_mem_erase hi⟩, rfl⟩)
    · rw [not_not.1 hiN, zero_smul]
      exact Submodule.zero_mem _
  have hsum := Finset.add_sum_erase Finset.univ (fun i => b i • v i) (Finset.mem_univ j)
  rw [← mulVec_eq_sum, hA] at hsum
  have hvj : v j ∈ Submodule.span (ZMod 2) (v '' S) := by
    have h1 : b j • v j ∈ Submodule.span (ZMod 2) (v '' S) := by
      rw [eq_neg_of_add_eq_zero_left hsum]
      exact Submodule.neg_mem _ hmem
    have h2 := Submodule.smul_mem _ (b j)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at h2
  have hjI : j ∉ I := fun hjI => (hI.subset hjI).2 rfl
  have hdep : (binMatroid A).Dep (insert j I) :=
    ⟨fun hi => ((linearIndepOn_insert hjI).1 ((binMatroid_indep A).1 hi)).2 (hle hvj),
      subset_univ _⟩
  obtain ⟨C, hCs, hC⟩ := hdep.exists_isCircuit_subset
  have hjC : j ∈ C := by
    by_contra hjC
    exact hC.not_indep (hI.indep.subset fun x hx =>
      (hCs hx).resolve_left fun hxj => hjC (hxj ▸ hx))
  refine ⟨C, hC, hjC, fun x hx => ?_⟩
  rcases hCs hx with rfl | hxI
  · exact hj
  · exact (hI.subset hxI).1

/-- The support of a kernel vector is a true sum of circuits. -/
lemma ker_trueSum (h : IsMatroidOf M A) :
    ∀ n : ℕ, ∀ x : α → ZMod 2, A.mulVec x = 0 → {j | x j ≠ 0}.ncard = n →
      IsTrueSumOf {C | M.IsCircuit C} {j | x j ≠ 0} := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx hn
  by_cases h0 : {j | x j ≠ 0} = ∅
  · rw [h0]
    exact ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨j, hj⟩ := nonempty_iff_ne_empty.2 h0
  obtain ⟨C, hC, hjC, hCs⟩ := exists_circuit_of_mem_support A h hx hj
  set x' := x + chi C with hx'def
  have hx' : A.mulVec x' = 0 := by
    rw [hx'def, Matrix.mulVec_add, hx, circuit_chi A h hC, add_zero]
  have hs' : {k | x' k ≠ 0} = {k | x k ≠ 0} \ C := by
    ext k
    simp only [mem_setOf_eq, mem_diff, hx'def, Pi.add_apply]
    by_cases hk : k ∈ C
    · have h1 : x k ≠ 0 := hCs hk
      have h2 : chi C k ≠ 0 := chi_ne_zero.2 hk
      simp only [hk, not_true_eq_false, and_false, iff_false, not_not]
      exact (by decide : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a + b = 0) _ _ h1 h2
    · have : chi C k = 0 := by
        by_contra h2
        exact hk (chi_ne_zero.1 h2)
      simp [hk, this]
  have hlt : {k | x' k ≠ 0}.ncard < n := by
    rw [← hn, hs']
    exact ncard_lt_ncard ((ssubset_iff_of_subset diff_subset).2 ⟨j, hj, fun h => h.2 hjC⟩)
      (toFinite _)
  obtain ⟨F, hF, hd, hFeq⟩ := ih _ hlt x' hx' rfl
  have hCF : C ∉ F := fun hCF' => by
    have : j ∈ ⋃ N ∈ F, N := mem_biUnion (x := C) hCF' hjC
    rw [← hFeq, hs'] at this
    exact this.2 hjC
  refine ⟨insert C F, ?_, ?_, ?_⟩
  · rw [Finset.coe_insert]
    exact insert_subset hC hF
  · rw [Finset.coe_insert]
    refine hd.insert fun N hN _ => ?_
    have hNs : N ⊆ {k | x k ≠ 0} \ C := by
      rw [← hs', hFeq]
      exact subset_biUnion_of_mem (u := id) hN
    exact Set.disjoint_left.2 fun y hyC hyN => (hNs hyN).2 hyC
  · rw [Finset.set_biUnion_insert, ← hFeq, hs']
    exact (union_diff_cancel hCs).symm

lemma chi_cycle_ker (h : IsMatroidOf M A) {Q : Set α} (hQ : IsCycleOf {C | M.IsCircuit C} Q) :
    A.mulVec (chi Q) = 0 := by
  obtain ⟨F, hF, rfl⟩ := hQ
  rw [chi_sumMod2, Matrix.mulVec_sum]
  exact Finset.sum_eq_zero fun N hN => circuit_chi A h (hF hN)

lemma supp_chi (Q : Set α) : {j | chi Q j ≠ 0} = Q := by
  ext
  exact chi_ne_zero

lemma cStar_of_matrix (h : IsMatroidOf M A) : SatisfiesCStar {C | M.IsCircuit C} := fun Q hQ => by
  have := ker_trueSum A h _ (chi Q) (chi_cycle_ker A h hQ) rfl
  rwa [supp_chi] at this

lemma cycle_iff_ker (h : IsMatroidOf M A) (Q : Set α) :
    IsCycleOf {C | M.IsCircuit C} Q ↔ ∃ x : α → ZMod 2, A.mulVec x = 0 ∧ Q = {j | x j ≠ 0} :=
  ⟨fun hQ => ⟨chi Q, chi_cycle_ker A h hQ, (supp_chi Q).symm⟩,
    fun ⟨x, hx, hQ⟩ => hQ ▸ isCycle_of_isTrueSum (ker_trueSum A h _ x hx rfl)⟩

end Mat

/-- Appendix, p. 532. -/
theorem p532 {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (∃ M : Matroid (Fin n), IsMatroidOf M A) ∧
      ∀ M : Matroid (Fin n), IsMatroidOf M A →
        SatisfiesCStar {C | M.IsCircuit C} ∧
          ∀ Q : Set (Fin n), IsCycleOf {C | M.IsCircuit C} Q ↔
            ∃ x : Fin n → ZMod 2, A.mulVec x = 0 ∧ Q = {j | x j ≠ 0} :=
  ⟨⟨binMatroid A, binMatroid_isMatroidOf A⟩, fun _ h => ⟨cStar_of_matrix A h, cycle_iff_ker A h⟩⟩

end WhitneyBin


namespace WhitneyBin

section Ext

variable {r q m : ℕ}

open Classical in
/-- Adjoin to `A₁` the columns `C_{n-q+i} = Σ_{e_j ∈ Pᵢ, j ≤ n-q} C_j`. -/
noncomputable def extM (A₁ : Matrix (Fin m) (Fin r) (ZMod 2)) (P : Fin q → Set (Fin (r + q))) :
    Matrix (Fin m) (Fin (r + q)) (ZMod 2) :=
  fun a => Fin.append (A₁ a)
    (fun i => ∑ j ∈ Finset.univ.filter (fun j => Fin.castAdd q j ∈ P i), A₁ a j)

lemma extM_castAdd (A₁ : Matrix (Fin m) (Fin r) (ZMod 2)) (P : Fin q → Set (Fin (r + q)))
    (a : Fin m) (j : Fin r) : extM A₁ P a (Fin.castAdd q j) = A₁ a j := by
  simp [extM]

open Classical in
lemma extM_natAdd (A₁ : Matrix (Fin m) (Fin r) (ZMod 2)) (P : Fin q → Set (Fin (r + q)))
    (a : Fin m) (i : Fin q) : extM A₁ P a (Fin.natAdd r i) =
      ∑ j ∈ Finset.univ.filter (fun j => Fin.castAdd q j ∈ P i), A₁ a j := by
  simp [extM]

open Classical in
lemma mulVec_chi (A : Matrix (Fin m) (Fin (r + q)) (ZMod 2)) {P : Set (Fin (r + q))} {i : Fin q}
    (hm : ∀ j, Fin.natAdd r j ∈ P ↔ j = i) (a : Fin m) :
    A.mulVec (chi P) a =
      (∑ j ∈ Finset.univ.filter (fun j => Fin.castAdd q j ∈ P), A a (Fin.castAdd q j)) +
        A a (Fin.natAdd r i) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_add, Finset.sum_filter]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    unfold chi
    split_ifs <;> simp
  · rw [Finset.sum_eq_single i]
    · unfold chi
      simp [(hm i).2 rfl]
    · intro b _ hb
      unfold chi
      simp [hm b, hb]
    · simp

lemma build (A₁ : Matrix (Fin m) (Fin r) (ZMod 2)) (hA₁ : LinearIndependent (ZMod 2) A₁.transpose)
    (P : Fin q → Set (Fin (r + q))) (hmem : ∀ i, Fin.natAdd r i ∈ P i)
    (hsub : ∀ i, P i ⊆ insert (Fin.natAdd r i) (range (Fin.castAdd q : Fin r → Fin (r + q))))
    {N : Matroid (Fin (r + q))} (hN : IsMatroidOf N (extM A₁ P)) :
    SatisfiesCStar {C | N.IsCircuit C} ∧ IsStrictFundamentalSet N P := by
  classical
  have hm : ∀ i j, Fin.natAdd r j ∈ P i ↔ j = i := fun i =>
    mem_iff_of_subset_insert (hmem i) (hsub i)
  have hC := cStar_of_matrix _ hN
  have hBi : N.Indep (range (Fin.castAdd q : Fin r → Fin (r + q))) := by
    refine (hN.2 _).2 ?_
    change LinearIndepOn (ZMod 2) (extM A₁ P).col _
    rw [linearIndepOn_range_iff (Fin.castAdd_injective r q)]
    have hcol : (extM A₁ P).col ∘ Fin.castAdd q = A₁.col := by
      funext j a
      exact extM_castAdd A₁ P a j
    rw [hcol]
    exact hA₁
  have hker : ∀ i, (extM A₁ P).mulVec (chi (P i)) = 0 := fun i => by
    funext a
    rw [mulVec_chi _ (hm i), extM_natAdd]
    simp only [extM_castAdd, Pi.zero_apply]
    convert (by decide : ∀ t : ZMod 2, t + t = 0) _
  have hcirc : ∀ i, N.IsCircuit (P i) := fun i => by
    obtain ⟨F, hF, hd, hFe⟩ := ker_trueSum _ hN _ _ (hker i) rfl
    rw [supp_chi] at hFe
    have hfi : Fin.natAdd r i ∈ P i := hmem i
    rw [hFe] at hfi
    obtain ⟨C, hCF, hiC⟩ := mem_iUnion₂.1 hfi
    have hCP : C ⊆ P i := hFe ▸ subset_biUnion_of_mem (u := id) hCF
    suffices h : P i ⊆ C by
      rw [← subset_antisymm hCP h]
      exact hF hCF
    intro x hx
    rw [hFe] at hx
    obtain ⟨D, hDF, hxD⟩ := mem_iUnion₂.1 hx
    by_cases hDC : D = C
    · exact hDC ▸ hxD
    exfalso
    have hdisj : Disjoint D C := hd hDF hCF hDC
    have hDB : D ⊆ range (Fin.castAdd q : Fin r → Fin (r + q)) := fun y hy => by
      have hyP : y ∈ P i := hFe ▸ mem_biUnion (x := D) hDF hy
      rcases hsub i hyP with h | h
      · exact absurd (by rw [h]; exact hiC) (Set.disjoint_left.1 hdisj hy)
      · exact h
    exact (hF hDF).not_indep (hBi.subset hDB)
  exact ⟨hC, sfs_of hN.1 hBi hcirc hm⟩

/-- Theorem 36. -/
theorem exists_unique_matroid (P : Fin q → Set (Fin (r + q)))
    (hmem : ∀ i, Fin.natAdd r i ∈ P i)
    (hsub : ∀ i, P i ⊆ insert (Fin.natAdd r i) (range (Fin.castAdd q : Fin r → Fin (r + q)))) :
    ∃! M : Matroid (Fin (r + q)),
      M.E = univ ∧ SatisfiesCStar {C | M.IsCircuit C} ∧ IsStrictFundamentalSet M P := by
  have hA : LinearIndependent (ZMod 2) (1 : Matrix (Fin r) (Fin r) (ZMod 2)).transpose := by
    rw [Matrix.transpose_one]
    have h1 : (1 : Matrix (Fin r) (Fin r) (ZMod 2)) = fun i => Pi.single i 1 := by
      funext i j
      exact Matrix.one_eq_pi_single
    rw [h1]
    exact Pi.linearIndependent_single_one (Fin r) (ZMod 2)
  obtain ⟨hC, hP⟩ := build 1 hA P hmem hsub (binMatroid_isMatroidOf _)
  exact ⟨binMatroid (extM 1 P), ⟨rfl, hC, hP⟩, fun M' ⟨hE', hC', hP'⟩ =>
    eq_of_sfs (M := M') _ hE' rfl hC' hC P hP' hP⟩

/-- Theorem 37. -/
theorem main {r q m : ℕ} (M : Matroid (Fin (r + q)))
    (hE : M.E = Set.univ) (hC : SatisfiesCStar {C | M.IsCircuit C})
    (hB : M.IsBase (Set.range (Fin.castAdd q : Fin r → Fin (r + q))))
    (A₁ : Matrix (Fin m) (Fin r) (ZMod 2))
    (hA₁ : LinearIndependent (ZMod 2) A₁.transpose) :
    ∃! A : Matrix (Fin m) (Fin (r + q)) (ZMod 2),
      (∀ i : Fin m, ∀ j : Fin r, A i (Fin.castAdd q j) = A₁ i j) ∧ IsMatroidOf M A := by
  obtain ⟨P, hP, -⟩ := exists_unique_sfs hE hB
  have hm := hP.2.2
  obtain ⟨hCN, hPN⟩ := build A₁ hA₁ P (fun i => (hm i i).2 rfl)
    (fun i => subset_insert_of_mem_iff (hm i)) (binMatroid_isMatroidOf _)
  have hMN : M = binMatroid (extM A₁ P) := eq_of_sfs _ hE rfl hC hCN P hP hPN
  refine ⟨extM A₁ P, ⟨fun a j => extM_castAdd A₁ P a j, hMN ▸ binMatroid_isMatroidOf _⟩, ?_⟩
  rintro A ⟨hA1, hAM⟩
  ext a k
  induction k using Fin.addCases with
  | left j => rw [hA1, extM_castAdd]
  | right i =>
    have h0 := congrFun (circuit_chi A hAM (hP.2.1 i)) a
    rw [mulVec_chi A (hm i)] at h0
    simp only [hA1, Pi.zero_apply] at h0
    rw [extM_natAdd]
    rw [add_eq_zero_iff_eq_neg, ZMod.neg_eq_self_mod_two] at h0
    rw [← h0]

end Ext

end WhitneyBin

theorem solution {r q : ℕ}
    (P : Fin q → Set (Fin (r + q)))
    (hmem : ∀ i, Fin.natAdd r i ∈ P i)
    (hsub : ∀ i, P i ⊆ insert (Fin.natAdd r i) (Set.range (Fin.castAdd q : Fin r → Fin (r + q)))) :
    ∃! M : Matroid (Fin (r + q)),
      M.E = Set.univ ∧ SatisfiesCStar {C | M.IsCircuit C} ∧ IsStrictFundamentalSet M P :=
  WhitneyBin.exists_unique_matroid P hmem hsub
