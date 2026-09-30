-- Prove2me | solution 1 for UnderstandingML.natarajan_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T20:32:21.83088+00:00
-- url     : https://prove2.me/submissions/08427827-a34d-463e-9669-dc8e239674e9

import Definitions.Def_UnderstandingML_MulticlassLearnability

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

namespace NatarajanAux

/-- `Φ_q(n, d) = ∑_{i ≤ d} (n choose i) q^i`, the Sauer–Natarajan bound. -/
def phi (q n d : ℕ) : ℕ := ∑ i ∈ Finset.range (d + 1), n.choose i * q ^ i

lemma phi_zero_left (q d : ℕ) : phi q 0 d = 1 := by
  unfold phi
  rw [Finset.sum_range_succ']
  simp

lemma phi_zero_right (q n : ℕ) : phi q n 0 = 1 := by
  simp [phi]

lemma phi_succ_succ (q n d : ℕ) : phi q (n + 1) (d + 1) = phi q n (d + 1) + q * phi q n d := by
  unfold phi
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun i ↦ n.choose i * q ^ i)]
  simp only [Nat.choose_succ_succ, add_mul, Finset.sum_add_distrib, Nat.choose_zero_right,
    pow_zero, mul_one, Finset.mul_sum]
  have : ∀ i ∈ Finset.range (d + 1), n.choose i * q ^ (i + 1) = q * (n.choose i * q ^ i) := by
    intro i _; ring
  rw [Finset.sum_congr rfl this]
  ring

variable {X Y : Type*}

lemma nshatters_mono {H H' : Set (X → Y)} (hHH : H ⊆ H') {C : Finset X} (h : NShatters H C) :
    NShatters H' C := by
  obtain ⟨f₀, f₁, hne, hB⟩ := h
  refine ⟨f₀, f₁, hne, fun B hBC ↦ ?_⟩
  obtain ⟨g, hg, h0, h1⟩ := hB B hBC
  exact ⟨g, hHH hg, h0, h1⟩

lemma nshatters_empty {H : Set (X → Y)} (h : H.Nonempty) : NShatters H ∅ := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, g, by simp, fun B hB ↦ ⟨g, hg, fun x hx ↦ rfl, fun x hx ↦ by simp at hx⟩⟩

/-- The Sauer–Natarajan counting bound, by induction on the set of coordinates. -/
theorem card_le_phi [DecidableEq X] [LinearOrder Y] [Fintype Y] (s : Finset X) :
    ∀ (H : Finset (X → Y)) (d : ℕ),
      (∀ h₁ ∈ H, ∀ h₂ ∈ H, (∀ x ∈ s, h₁ x = h₂ x) → h₁ = h₂) →
      (∀ C ⊆ s, NShatters (H : Set (X → Y)) C → C.card ≤ d) →
      H.card ≤ phi (Finset.univ.filter (fun p : Y × Y ↦ p.1 < p.2)).card s.card d := by
  classical
  set q := (Finset.univ.filter (fun p : Y × Y ↦ p.1 < p.2)).card with hq
  induction s using Finset.induction_on with
  | empty =>
    intro H d hinj _
    rw [Finset.card_empty, phi_zero_left]
    exact Finset.card_le_one.2 fun h₁ h₁H h₂ h₂H ↦ hinj h₁ h₁H h₂ h₂H (by simp)
  | @insert x t hxt ih =>
    intro H d hinj hsh
    -- representatives: minimal value at `x` within their `t`-class
    set R := H.filter (fun h ↦ ∀ h' ∈ H, (∀ y ∈ t, h' y = h y) → h x ≤ h' x) with hR
    set P : Y × Y → Finset (X → Y) := fun p ↦
      H.filter (fun h ↦ h x = p.2 ∧ ∃ h' ∈ R, (∀ y ∈ t, h' y = h y) ∧ h' x = p.1) with hP
    set pairs := Finset.univ.filter (fun p : Y × Y ↦ p.1 < p.2) with hpairs
    have hRH : R ⊆ H := Finset.filter_subset _ _
    have hPH : ∀ p, P p ⊆ H := fun p ↦ Finset.filter_subset _ _
    -- covering
    have hcover : H ⊆ R ∪ pairs.biUnion P := by
      intro h hh
      obtain ⟨h', hh'F, hmin⟩ := Finset.exists_min_image
        (H.filter (fun g ↦ ∀ y ∈ t, g y = h y)) (fun g ↦ g x) ⟨h, by simp [hh]⟩
      simp only [Finset.mem_filter] at hh'F hmin
      have hh'R : h' ∈ R := by
        simp only [hR, Finset.mem_filter]
        refine ⟨hh'F.1, fun h'' hh'' hag ↦ hmin h'' ⟨hh'', fun y hy ↦ (hag y hy).trans
          (hh'F.2 y hy)⟩⟩
      by_cases hhR : h ∈ R
      · exact Finset.mem_union_left _ hhR
      · apply Finset.mem_union_right
        have hle : h' x ≤ h x := hmin h ⟨hh, fun y _ ↦ rfl⟩
        have hne : h' x ≠ h x := by
          intro heq
          have : h' = h := hinj h' hh'F.1 h hh (by
            intro y hy
            rcases Finset.mem_insert.1 hy with rfl | hy
            · exact heq
            · exact hh'F.2 y hy)
          exact hhR (this ▸ hh'R)
        refine Finset.mem_biUnion.2 ⟨(h' x, h x), ?_, ?_⟩
        · simp [hpairs, lt_of_le_of_ne hle hne]
        · simp only [hP, Finset.mem_filter]
          exact ⟨hh, by simp, h', hh'R, hh'F.2, by simp⟩
    have hcard : H.card ≤ R.card + ∑ p ∈ pairs, (P p).card :=
      (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left Finset.card_biUnion_le _))
    -- `R` is injective on `t`
    have hRinj : ∀ h₁ ∈ R, ∀ h₂ ∈ R, (∀ y ∈ t, h₁ y = h₂ y) → h₁ = h₂ := by
      intro h₁ h₁R h₂ h₂R hag
      simp only [hR, Finset.mem_filter] at h₁R h₂R
      have h12 := h₁R.2 h₂ h₂R.1 (fun y hy ↦ (hag y hy).symm)
      have h21 := h₂R.2 h₁ h₁R.1 hag
      apply hinj h₁ h₁R.1 h₂ h₂R.1
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact le_antisymm h12 h21
      · exact hag y hy
    have hRsh : ∀ C ⊆ t, NShatters (R : Set (X → Y)) C → C.card ≤ d := by
      intro C hC hCsh
      exact hsh C (hC.trans (Finset.subset_insert _ _))
        (nshatters_mono (by exact_mod_cast hRH) hCsh)
    have hRcard := ih R d hRinj hRsh
    -- each `P p` is injective on `t`
    have hPinj : ∀ p, ∀ h₁ ∈ P p, ∀ h₂ ∈ P p, (∀ y ∈ t, h₁ y = h₂ y) → h₁ = h₂ := by
      intro p h₁ h₁P h₂ h₂P hag
      simp only [hP, Finset.mem_filter] at h₁P h₂P
      apply hinj h₁ h₁P.1 h₂ h₂P.1
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact h₁P.2.1.trans h₂P.2.1.symm
      · exact hag y hy
    -- shattering by `P p` extends to `insert x C`
    have hPsh : ∀ p ∈ pairs, ∀ C ⊆ t, NShatters (P p : Set (X → Y)) C →
        NShatters (H : Set (X → Y)) (insert x C) := by
      intro p hp C hC hCsh
      simp only [hpairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨f₀, f₁, hne, hB⟩ := hCsh
      have hxC : x ∉ C := fun h ↦ hxt (hC h)
      refine ⟨Function.update f₀ x p.1, Function.update f₁ x p.2, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · simpa using hp.ne
        · have hyx : y ≠ x := fun h ↦ hxC (h ▸ hy)
          simpa [Function.update_of_ne hyx] using hne y hy
      · intro B hB'
        have hB0 : B.erase x ⊆ C := by
          intro y hy
          have := hB' (Finset.mem_of_mem_erase hy)
          rcases Finset.mem_insert.1 this with h | h
          · exact absurd h (Finset.ne_of_mem_erase hy)
          · exact h
        obtain ⟨g, hgP, hg0, hg1⟩ := hB (B.erase x) hB0
        have hgP' : g ∈ P p := by exact_mod_cast hgP
        simp only [hP, Finset.mem_filter] at hgP'
        obtain ⟨hgH, hgx, g', hg'R, hg'ag, hg'x⟩ := hgP'
        by_cases hxB : x ∈ B
        · refine ⟨g', by exact_mod_cast hRH hg'R, ?_, ?_⟩
          · intro y hy
            by_cases hyx : y = x
            · subst hyx; simpa using hg'x
            · rw [Function.update_of_ne hyx]
              have hyC : y ∈ C := hB0 (Finset.mem_erase.2 ⟨hyx, hy⟩)
              rw [hg'ag y (hC hyC)]
              exact hg0 y (Finset.mem_erase.2 ⟨hyx, hy⟩)
          · intro y hy hyB
            have hyx : y ≠ x := fun h ↦ hyB (h ▸ hxB)
            rw [Function.update_of_ne hyx]
            have hyC : y ∈ C := (Finset.mem_insert.1 hy).resolve_left hyx
            rw [hg'ag y (hC hyC)]
            exact hg1 y hyC (fun h ↦ hyB (Finset.mem_of_mem_erase h))
        · refine ⟨g, by exact_mod_cast hgH, ?_, ?_⟩
          · intro y hy
            have hyx : y ≠ x := fun h ↦ hxB (h ▸ hy)
            rw [Function.update_of_ne hyx]
            exact hg0 y (Finset.mem_erase.2 ⟨hyx, hy⟩)
          · intro y hy hyB
            by_cases hyx : y = x
            · subst hyx; simpa using hgx
            · rw [Function.update_of_ne hyx]
              have hyC : y ∈ C := (Finset.mem_insert.1 hy).resolve_left hyx
              exact hg1 y hyC (fun h ↦ hyB (Finset.mem_of_mem_erase h))
    rw [Finset.card_insert_of_notMem hxt]
    cases d with
    | zero =>
      have hPempty : ∀ p ∈ pairs, P p = ∅ := by
        intro p hp
        by_contra hne
        have hsh0 := hPsh p hp ∅ (Finset.empty_subset _)
          (nshatters_empty (by exact_mod_cast Finset.nonempty_iff_ne_empty.2 hne))
        have := hsh (insert x ∅) (by simp) hsh0
        simp at this
      rw [Finset.sum_eq_zero (fun p hp ↦ by rw [hPempty p hp, Finset.card_empty])] at hcard
      rw [phi_zero_right]
      rw [phi_zero_right] at hRcard
      omega
    | succ e =>
      have hPcard : ∀ p ∈ pairs, (P p).card ≤ phi q t.card e := by
        intro p hp
        refine ih (P p) e (hPinj p) fun C hC hCsh ↦ ?_
        have := hsh (insert x C) (Finset.insert_subset_insert _ hC) (hPsh p hp C hC hCsh)
        rw [Finset.card_insert_of_notMem (fun h ↦ hxt (hC h))] at this
        omega
      have hsum : ∑ p ∈ pairs, (P p).card ≤ q * phi q t.card e := by
        calc ∑ p ∈ pairs, (P p).card ≤ ∑ _p ∈ pairs, phi q t.card e := Finset.sum_le_sum hPcard
          _ = q * phi q t.card e := by rw [Finset.sum_const, smul_eq_mul, hq]
      rw [phi_succ_succ]
      omega

/-- `∑_{i ≤ d} n^i q^i ≤ n^d k^{2d}` when `n, k ≥ 1` and `q + k ≤ k²`. -/
lemma geom_le (n k q : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hq : q + k ≤ k ^ 2) :
    ∀ d : ℕ, ∑ i ∈ Finset.range (d + 1), n ^ i * q ^ i ≤ n ^ d * k ^ (2 * d) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ]
    have hqk : q ≤ k ^ 2 := by omega
    have h1 : q ^ (d + 1) ≤ q * k ^ (2 * d) := by
      rw [pow_succ', pow_mul]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqk d)
    have h2 : n ^ d ≤ n ^ (d + 1) := Nat.pow_le_pow_right hn (Nat.le_succ d)
    have h3 : 1 + q ≤ k ^ 2 := by omega
    calc ∑ i ∈ Finset.range (d + 1), n ^ i * q ^ i + n ^ (d + 1) * q ^ (d + 1)
        ≤ n ^ d * k ^ (2 * d) + n ^ (d + 1) * (q * k ^ (2 * d)) :=
          Nat.add_le_add ih (Nat.mul_le_mul_left _ h1)
      _ ≤ n ^ (d + 1) * k ^ (2 * d) + n ^ (d + 1) * (q * k ^ (2 * d)) :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ h2) _
      _ = n ^ (d + 1) * k ^ (2 * d) * (1 + q) := by ring
      _ ≤ n ^ (d + 1) * k ^ (2 * d) * k ^ 2 := Nat.mul_le_mul_left _ h3
      _ = n ^ (d + 1) * k ^ (2 * (d + 1)) := by ring

lemma phi_le_geom (q n d : ℕ) :
    phi q n d ≤ ∑ i ∈ Finset.range (d + 1), n ^ i * q ^ i :=
  Finset.sum_le_sum fun i _ ↦ Nat.mul_le_mul_right _ (Nat.choose_le_pow n i)

lemma card_pairs_le [LinearOrder Y] [Fintype Y] :
    (Finset.univ.filter (fun p : Y × Y ↦ p.1 < p.2)).card + Fintype.card Y ≤
      Fintype.card Y ^ 2 := by
  classical
  have h1 : (Finset.univ.filter (fun p : Y × Y ↦ p.1 < p.2)) ⊆ (Finset.univ : Finset Y).offDiag := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp [hp.ne]
  have h2 := Finset.card_le_card h1
  rw [Finset.offDiag_card, Finset.card_univ] at h2
  have h3 : Fintype.card Y ≤ Fintype.card Y * Fintype.card Y := Nat.le_mul_self _
  rw [sq]
  omega

end NatarajanAux

end UnderstandingML

open UnderstandingML
open UnderstandingML.NatarajanAux in
theorem solution {X Y : Type*} [Fintype X] [Fintype Y] (H : Set (X → Y)) (d : ℕ)
    (hd : ndim H = d) :
    H.ncard ≤ Fintype.card X ^ d * Fintype.card Y ^ (2 * d) := by
  classical
  letI : LinearOrder Y := LinearOrder.lift' (Fintype.equivFin Y) (Fintype.equivFin Y).injective
  have hsh : ∀ C : Finset X, NShatters H C → C.card ≤ d := by
    intro C hC
    have : (C.card : ℕ∞) ≤ ndim H := le_iSup₂ (f := fun C (_ : NShatters H C) ↦ (C.card : ℕ∞)) C hC
    rw [hd] at this
    exact_mod_cast this
  have hcount := card_le_phi (Finset.univ : Finset X) H.toFinset d
    (fun h₁ _ h₂ _ hag ↦ funext fun x ↦ hag x (Finset.mem_univ x))
    (fun C _ hC ↦ hsh C (by simpa using hC))
  rw [Set.ncard_eq_toFinset_card']
  refine hcount.trans ?_
  rw [Finset.card_univ]
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · simp [phi_zero_right]
  · -- a shattered set of positive size exists
    have hex : ∃ C : Finset X, NShatters H C ∧ 0 < C.card := by
      by_contra hno
      push_neg at hno
      have : ndim H ≤ 0 := by
        unfold ndim
        refine iSup₂_le fun C hC ↦ ?_
        have := hno C hC
        exact_mod_cast this
      rw [hd] at this
      have : d = 0 := by simpa using this
      omega
    obtain ⟨C, ⟨f₀, f₁, -, -⟩, hCpos⟩ := hex
    obtain ⟨x, -⟩ := Finset.card_pos.1 hCpos
    have hn : 1 ≤ Fintype.card X := Fintype.card_pos_iff.2 ⟨x⟩
    have hk : 1 ≤ Fintype.card Y := Fintype.card_pos_iff.2 ⟨f₀ x⟩
    exact (phi_le_geom _ _ _).trans (geom_le _ _ _ hn hk card_pairs_le d)
