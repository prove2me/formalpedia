-- Prove2me | solution 1 for UnderstandingML.ova_ndim_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T20:58:07.975933+00:00
-- url     : https://prove2.me/submissions/1eea8db1-90ee-4933-b566-e9fa268897ba

import Definitions.Def_UnderstandingML_MulticlassLearnability
import Mathlib.Analysis.Complex.ExponentialBounds

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

namespace UnderstandingML

namespace OvaAux

open NatarajanAux

variable {X : Type*}

/-! ### One-versus-All -/

section Ova

variable {k : ℕ} [NeZero k]

lemma ova_spec (hbar : Fin k → X → Bool) (x : X) (hne : ∃ j, hbar j x = true) :
    hbar (ovaPredict hbar x) x = true ∧ ∀ j, hbar j x = true → ovaPredict hbar x ≤ j := by
  classical
  have hne' : (Finset.univ.filter (fun i ↦ hbar i x = true)).Nonempty := by
    obtain ⟨j, hj⟩ := hne; exact ⟨j, by simp [hj]⟩
  have heq : ovaPredict hbar x = (Finset.univ.filter (fun i ↦ hbar i x = true)).min' hne' := by
    unfold ovaPredict; rw [dif_pos hne']
  have hmem := Finset.min'_mem _ hne'
  rw [← heq] at hmem
  refine ⟨by simpa using hmem, fun j hj ↦ ?_⟩
  rw [heq]
  exact Finset.min'_le _ _ (by simp [hj])

lemma ova_none (hbar : Fin k → X → Bool) (x : X) (h : ¬ ∃ j, hbar j x = true) :
    ovaPredict hbar x = 0 := by
  classical
  have hne' : ¬ (Finset.univ.filter (fun i ↦ hbar i x = true)).Nonempty := by
    rintro ⟨j, hj⟩; exact h ⟨j, by simpa using hj⟩
  unfold ovaPredict; rw [dif_neg hne']

/-- On a point where the prediction is `0` or `b ≠ 0`, it is `b` iff `h_b(x) ∧ ¬ h_0(x)`. -/
lemma ova_zero_b (hbar : Fin k → X → Bool) (x : X) {b : Fin k} (hb : b ≠ 0)
    (hT : ovaPredict hbar x = 0 ∨ ovaPredict hbar x = b) :
    ovaPredict hbar x = b ↔ hbar b x = true ∧ hbar 0 x = false := by
  constructor
  · intro h
    have hex : ∃ j, hbar j x = true := by
      by_contra hno
      rw [ova_none hbar x hno] at h
      exact hb h.symm
    obtain ⟨h1, h2⟩ := ova_spec hbar x hex
    refine ⟨h ▸ h1, ?_⟩
    by_contra h0
    simp only [Bool.not_eq_false] at h0
    have := h2 0 h0
    rw [h] at this
    exact hb (le_antisymm this (Fin.zero_le _))
  · rintro ⟨h1, h0⟩
    obtain ⟨hT1, hT2⟩ := ova_spec hbar x ⟨b, h1⟩
    rcases hT with h | h
    · rw [h] at hT1; rw [hT1] at h0; exact absurd h0 (by simp)
    · exact h

/-- On a point where the prediction is `a` or `b` with `0 < a < b`, it is `a` iff `h_a(x)`. -/
lemma ova_ab (hbar : Fin k → X → Bool) (x : X) {a b : Fin k} (ha : a ≠ 0) (hab : a < b)
    (hT : ovaPredict hbar x = a ∨ ovaPredict hbar x = b) :
    ovaPredict hbar x = a ↔ hbar a x = true := by
  constructor
  · intro h
    have hex : ∃ j, hbar j x = true := by
      by_contra hno
      rw [ova_none hbar x hno] at h
      exact ha h.symm
    exact h ▸ (ova_spec hbar x hex).1
  · intro h1
    have hle := (ova_spec hbar x ⟨a, h1⟩).2 a h1
    rcases hT with h | h
    · exact h
    · rw [h] at hle; exact absurd hab (not_lt.2 hle)

end Ova

/-! ### Restrictions and Sauer's lemma -/

/-- The restriction `(H_bin)_C` as a finset of functions on `C`. -/
noncomputable def restr (Hbin : Set (X → Bool)) (C : Finset X) : Finset (C → Bool) := by
  classical
  exact Finset.univ.filter (fun u ↦ ∃ h ∈ Hbin, ∀ y : C, u y = h y)

lemma mem_restr {Hbin : Set (X → Bool)} {C : Finset X} {u : C → Bool} :
    u ∈ restr Hbin C ↔ ∃ h ∈ Hbin, ∀ y : C, u y = h y := by
  classical
  unfold restr
  simp

lemma card_bool_pairs : (Finset.univ.filter (fun p : Bool × Bool ↦ p.1 < p.2)).card = 1 := by
  decide

/-- Sauer's lemma for the restriction to `C`. -/
lemma card_restr_le (Hbin : Set (X → Bool)) (d : ℕ)
    (hd : ∀ D : Finset X, Shatters Hbin D → D.card ≤ d) (C : Finset X) :
    (restr Hbin C).card ≤ phi 1 C.card d := by
  classical
  have h := card_le_phi (X := C) (Y := Bool) Finset.univ (restr Hbin C) d
    (fun h₁ _ h₂ _ hag ↦ funext fun y ↦ hag y (Finset.mem_univ y)) ?_
  · rwa [card_bool_pairs, Finset.card_univ, Fintype.card_coe] at h
  intro C' _ hC'
  obtain ⟨f₀, f₁, hne, hB⟩ := hC'
  have hsh : Shatters Hbin (C'.map (Function.Embedding.subtype _)) := by
    intro g
    let g' : C → Bool := fun y ↦ if hy : y ∈ C' then g ⟨y.1, Finset.mem_map.2 ⟨y, hy, rfl⟩⟩ else false
    let B : Finset C := C'.filter (fun y ↦ g' y = f₀ y)
    obtain ⟨u, hu, hu0, hu1⟩ := hB B (Finset.filter_subset _ _)
    have hu' : u ∈ restr Hbin C := by exact_mod_cast hu
    obtain ⟨h, hh, huh⟩ := mem_restr.1 hu'
    refine ⟨h, hh, fun z ↦ ?_⟩
    obtain ⟨z, hz⟩ := z
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hz
    simp only [Function.Embedding.coe_subtype]
    rw [← huh y]
    have hg' : g' y = g ⟨y.1, hz⟩ := by simp only [g', dif_pos hy]
    rw [← hg']
    by_cases hyB : y ∈ B
    · rw [hu0 y hyB]
      exact ((Finset.mem_filter.1 hyB).2).symm
    · rw [hu1 y hy hyB]
      have hnot : g' y ≠ f₀ y := fun hg ↦ hyB (Finset.mem_filter.2 ⟨hy, hg⟩)
      have := hne y hy
      revert hnot this
      cases g' y <;> cases f₀ y <;> cases f₁ y <;> simp
  have := hd _ hsh
  rwa [Finset.card_map] at this

lemma phi_one_le (c d : ℕ) : phi 1 c d ≤ (c + 1) ^ d := by
  unfold phi
  rw [add_pow]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hid : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 : 1 ≤ d.choose i := Nat.choose_pos hid
  calc c.choose i * 1 ^ i = c.choose i := by simp
    _ ≤ c ^ i := Nat.choose_le_pow c i
    _ ≤ c ^ i * d.choose i := Nat.le_mul_of_pos_right _ h1
    _ = c ^ i * 1 ^ (d - i) * d.choose i := by simp

lemma shatter_bound (Hbin : Set (X → Bool)) (d : ℕ) (hd : vcDim Hbin = d) :
    ∀ D : Finset X, Shatters Hbin D → D.card ≤ d := by
  intro D hD
  have : (D.card : ℕ∞) ≤ vcDim Hbin :=
    le_iSup₂ (f := fun D (_ : Shatters Hbin D) ↦ (D.card : ℕ∞)) D hD
  rw [hd] at this
  exact_mod_cast this

/-! ### The counting inequality `2^c ≤ (c+1)^{dk}` -/

lemma two_pow_le (Hbin : Set (X → Bool)) (d : ℕ) (hd : ∀ D : Finset X, Shatters Hbin D → D.card ≤ d)
    (k : ℕ) [NeZero k] (C : Finset X) (hC : NShatters (ovaClass Hbin k) C) :
    2 ^ C.card ≤ (C.card + 1) ^ (d * k) := by
  classical
  obtain ⟨f₀, f₁, hne, hB⟩ := hC
  -- patterns realized on `C`
  let pat : Finset (C → Fin k) := (Fintype.piFinset (fun _ : Fin k ↦ restr Hbin C)).image
    (fun u ↦ ovaPredict u)
  have hpat : pat.card ≤ (restr Hbin C).card ^ k := by
    refine Finset.card_image_le.trans ?_
    rw [Fintype.card_piFinset]
    simp
  have hinj : C.powerset.card ≤ pat.card := by
    let φ : Finset X → (C → Fin k) := fun B y ↦ if y.1 ∈ B then f₀ y else f₁ y
    have hφ : ∀ B ∈ C.powerset, φ B ∈ pat := by
      intro B hBC
      obtain ⟨h, hh, h0, h1⟩ := hB B (Finset.mem_powerset.1 hBC)
      obtain ⟨hbar, hbarH, rfl⟩ := hh
      refine Finset.mem_image.2 ⟨fun i y ↦ hbar i y, ?_, ?_⟩
      · refine Fintype.mem_piFinset.2 fun i ↦ mem_restr.2 ⟨hbar i, hbarH i, fun y ↦ rfl⟩
      · funext y
        simp only [φ]
        split_ifs with hy
        · rw [← h0 y hy]; rfl
        · rw [← h1 y y.2 hy]; rfl
    have hφinj : Set.InjOn φ C.powerset := by
      intro B₁ hB₁ B₂ hB₂ heq
      have hB₁' := Finset.mem_powerset.1 hB₁
      have hB₂' := Finset.mem_powerset.1 hB₂
      ext x
      constructor
      · intro hx
        have hxC := hB₁' hx
        have := congr_fun heq ⟨x, hxC⟩
        simp only [φ, hx, if_true] at this
        by_contra hx2
        rw [if_neg hx2] at this
        exact hne x hxC this
      · intro hx
        have hxC := hB₂' hx
        have := congr_fun heq ⟨x, hxC⟩
        simp only [φ, hx, if_true] at this
        by_contra hx1
        rw [if_neg hx1] at this
        exact hne x hxC this.symm
    exact Finset.card_le_card_of_injOn φ hφ hφinj
  rw [Finset.card_powerset] at hinj
  calc 2 ^ C.card ≤ (restr Hbin C).card ^ k := hinj.trans hpat
    _ ≤ (phi 1 C.card d) ^ k := Nat.pow_le_pow_left (card_restr_le Hbin d hd C) k
    _ ≤ ((C.card + 1) ^ d) ^ k := Nat.pow_le_pow_left (phi_one_le _ _) k
    _ = (C.card + 1) ^ (d * k) := by rw [pow_mul]

/-! ### The real inequality -/

lemma real_bound (m c : ℕ) (hm : 4 ≤ m) (h : 2 ^ c ≤ (c + 1) ^ m) :
    (c : ℝ) ≤ 3 * m * Real.log m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hc1 : (0 : ℝ) < (c : ℝ) + 1 := by positivity
  have h1 : (c : ℝ) * Real.log 2 ≤ m * Real.log ((c : ℝ) + 1) := by
    have h' : (2 : ℝ) ^ c ≤ ((c : ℝ) + 1) ^ m := by exact_mod_cast h
    have := Real.log_le_log (by positivity) h'
    rwa [Real.log_pow, Real.log_pow] at this
  set ℓ := Real.log 2 with hℓ
  set L := Real.log m with hLdef
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * ℓ := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hL : 2 * ℓ ≤ L := by
    have : Real.log 4 ≤ L := Real.log_le_log (by norm_num) hm4
    linarith
  have h2 : Real.log ((c : ℝ) + 1) ≤ ((c : ℝ) + 1) / (4 * m) + (2 * ℓ + L) - 1 := by
    have hpos : 0 < ((c : ℝ) + 1) / (4 * m) := by positivity
    have := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div hc1.ne' (by positivity), Real.log_mul (by norm_num) hmpos.ne', h4] at this
    linarith
  have h3 : (m : ℝ) * Real.log ((c : ℝ) + 1) ≤ ((c : ℝ) + 1) / 4 + m * (2 * ℓ + L - 1) := by
    have := mul_le_mul_of_nonneg_left h2 hmpos.le
    have heq : (m : ℝ) * (((c : ℝ) + 1) / (4 * m)) = ((c : ℝ) + 1) / 4 := by
      field_simp
    nlinarith
  by_contra hc
  push_neg at hc
  have hA : 3 * m * L * (ℓ - 1 / 4) < c * (ℓ - 1 / 4) :=
    mul_lt_mul_of_pos_right hc (by linarith)
  have hB : (m : ℝ) * L * (3 * ℓ - 7 / 4) < 1 / 4 + m * (2 * ℓ - 1) := by nlinarith
  have hC : (m : ℝ) * (2 * ℓ) * (3 * ℓ - 7 / 4) ≤ m * L * (3 * ℓ - 7 / 4) := by
    have : 0 ≤ (m : ℝ) * (3 * ℓ - 7 / 4) := mul_nonneg hmpos.le (by linarith)
    nlinarith
  have hD : (1 : ℝ) / 16 ≤ 6 * ℓ ^ 2 - 11 / 2 * ℓ + 1 := by nlinarith
  nlinarith

/-! ### The small cases `d = 1`, `k ∈ {2, 3}` -/

lemma two_pow_gt (c : ℕ) (hc : 5 ≤ c) : c ^ 2 + c + 1 < 2 ^ c := by
  induction c, hc using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : (n + 1) ^ 2 + (n + 1) + 1 ≤ 2 * (n ^ 2 + n + 1) := by nlinarith
    calc (n + 1) ^ 2 + (n + 1) + 1 ≤ 2 * (n ^ 2 + n + 1) := h1
      _ < 2 * 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by ring

/-- A set on which `{B \ A : A, B ∈ H_bin}` realizes every subset has at most `4` points when
`VCdim(H_bin) ≤ 1`. -/
lemma card_le_four_of_diff (Hbin : Set (X → Bool))
    (hd : ∀ D : Finset X, Shatters Hbin D → D.card ≤ 1) (D : Finset X)
    (hD : ∀ S ⊆ D, ∃ A ∈ Hbin, ∃ B ∈ Hbin, ∀ x ∈ D, (B x = true ∧ A x = false ↔ x ∈ S)) :
    D.card ≤ 4 := by
  classical
  choose! Af hAf Bf hBf hABf using hD
  set N := restr Hbin D with hN
  let φ : Finset X → (D → Bool) × (D → Bool) := fun S ↦ (fun y ↦ Af S y, fun y ↦ Bf S y)
  have hφ : ∀ S ∈ D.powerset, φ S ∈ insert (φ ∅) N.offDiag := by
    intro S hS
    have hS' := Finset.mem_powerset.1 hS
    by_cases hS0 : S = ∅
    · rw [hS0]; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [Finset.mem_offDiag]
      refine ⟨mem_restr.2 ⟨Af S, hAf S hS', fun y ↦ rfl⟩,
        mem_restr.2 ⟨Bf S, hBf S hS', fun y ↦ rfl⟩, ?_⟩
      intro heq
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hS0
      have hxD := hS' hx
      have := (hABf S hS' x hxD).2 hx
      have h2 : Af S x = Bf S x := congr_fun heq ⟨x, hxD⟩
      rw [h2, this.1] at this
      exact absurd this.2 (by simp)
  have hφinj : Set.InjOn φ D.powerset := by
    intro S₁ hS₁ S₂ hS₂ heq
    have hS₁' := Finset.mem_powerset.1 hS₁
    have hS₂' := Finset.mem_powerset.1 hS₂
    simp only [φ, Prod.mk.injEq] at heq
    ext x
    constructor
    · intro hx
      have hxD := hS₁' hx
      have := (hABf S₁ hS₁' x hxD).2 hx
      rw [show Af S₁ x = Af S₂ x from congr_fun heq.1 ⟨x, hxD⟩,
        show Bf S₁ x = Bf S₂ x from congr_fun heq.2 ⟨x, hxD⟩] at this
      exact (hABf S₂ hS₂' x hxD).1 this
    · intro hx
      have hxD := hS₂' hx
      have := (hABf S₂ hS₂' x hxD).2 hx
      rw [← show Af S₁ x = Af S₂ x from congr_fun heq.1 ⟨x, hxD⟩,
        ← show Bf S₁ x = Bf S₂ x from congr_fun heq.2 ⟨x, hxD⟩] at this
      exact (hABf S₁ hS₁' x hxD).1 this
  have h1 := Finset.card_le_card_of_injOn φ hφ hφinj
  rw [Finset.card_powerset] at h1
  have hNle : N.card ≤ D.card + 1 := by
    have := card_restr_le Hbin 1 hd D
    rw [← hN] at this
    have hphi : phi 1 D.card 1 = 1 + D.card := by simp [phi, Finset.sum_range_succ]
    omega
  have h3 : 2 ^ D.card ≤ N.card * N.card - N.card + 1 := by
    have := h1.trans (Finset.card_insert_le _ _)
    rwa [Finset.offDiag_card] at this
  have h4 : N.card * N.card - N.card ≤ (D.card + 1) * (D.card + 1) - (D.card + 1) := by
    have : N.card * N.card - N.card = N.card * (N.card - 1) := by
      rw [Nat.mul_sub, mul_one]
    have h' : (D.card + 1) * (D.card + 1) - (D.card + 1) = (D.card + 1) * D.card := by
      have : (D.card + 1) * (D.card + 1) = (D.card + 1) * D.card + (D.card + 1) := by ring
      omega
    rw [this, h']
    exact Nat.mul_le_mul hNle (by omega)
  by_contra hcon
  push_neg at hcon
  have := two_pow_gt D.card hcon
  have h5 : (D.card + 1) * (D.card + 1) - (D.card + 1) = D.card ^ 2 + D.card := by
    have : (D.card + 1) * (D.card + 1) = D.card ^ 2 + D.card + (D.card + 1) := by ring
    omega
  omega

/-! ### Splitting a shattered set by label pairs -/

section Parts

variable {k : ℕ} [NeZero k]

/-- On the points whose label pair is `{0, b}`, the class `{B \ A : A, B ∈ H_bin}` realizes every
subset. -/
lemma zero_b_part (Hbin : Set (X → Bool)) (C : Finset X) (f₀ f₁ : X → Fin k)
    (hB : ∀ B ⊆ C, ∃ h ∈ ovaClass Hbin k, (∀ x ∈ B, h x = f₀ x) ∧ ∀ x ∈ C, x ∉ B → h x = f₁ x)
    (b : Fin k) (hb : b ≠ 0) :
    ∀ S ⊆ C.filter (fun x ↦ (f₀ x = 0 ∧ f₁ x = b) ∨ (f₀ x = b ∧ f₁ x = 0)),
      ∃ A ∈ Hbin, ∃ B ∈ Hbin, ∀ x ∈ C.filter (fun x ↦ (f₀ x = 0 ∧ f₁ x = b) ∨ (f₀ x = b ∧ f₁ x = 0)),
        (B x = true ∧ A x = false ↔ x ∈ S) := by
  classical
  intro S _
  obtain ⟨h, ⟨hbar, hbarH, rfl⟩, h0, h1⟩ := hB (C.filter (fun x ↦ (x ∈ S ↔ f₀ x = b)))
    (Finset.filter_subset _ _)
  refine ⟨hbar 0, hbarH 0, hbar b, hbarH b, fun x hx ↦ ?_⟩
  obtain ⟨hxC, hpair⟩ := Finset.mem_filter.1 hx
  have hb0 : (0 : Fin k) ≠ b := Ne.symm hb
  have hval : (ovaPredict hbar x = 0 ∨ ovaPredict hbar x = b) ∧ (ovaPredict hbar x = b ↔ x ∈ S) := by
    by_cases hxB : x ∈ C.filter (fun x ↦ (x ∈ S ↔ f₀ x = b))
    · rw [h0 x hxB]
      have hiff := (Finset.mem_filter.1 hxB).2
      rcases hpair with ⟨ha, hb'⟩ | ⟨ha, hb'⟩ <;> rw [ha] at hiff ⊢
      · exact ⟨Or.inl rfl, hiff.symm⟩
      · exact ⟨Or.inr rfl, ⟨fun _ ↦ hiff.2 rfl, fun _ ↦ rfl⟩⟩
    · rw [h1 x hxC hxB]
      have hiff : ¬ (x ∈ S ↔ f₀ x = b) := fun h ↦ hxB (Finset.mem_filter.2 ⟨hxC, h⟩)
      rcases hpair with ⟨ha, hb'⟩ | ⟨ha, hb'⟩ <;> rw [ha] at hiff <;> rw [hb']
      · refine ⟨Or.inr rfl, ⟨fun _ ↦ ?_, fun _ ↦ rfl⟩⟩
        by_contra hS
        exact hiff ⟨fun h ↦ absurd h hS, fun h ↦ absurd h hb0⟩
      · refine ⟨Or.inl rfl, ⟨fun h ↦ absurd h hb0, fun hS ↦ ?_⟩⟩
        exact absurd ⟨fun _ ↦ rfl, fun _ ↦ hS⟩ hiff
  rw [← hval.2]
  exact (ova_zero_b hbar x hb hval.1).symm

/-- On the points whose label pair is `{a, b}` with `0 < a < b`, `H_bin` shatters. -/
lemma ab_part (Hbin : Set (X → Bool)) (C : Finset X) (f₀ f₁ : X → Fin k)
    (hB : ∀ B ⊆ C, ∃ h ∈ ovaClass Hbin k, (∀ x ∈ B, h x = f₀ x) ∧ ∀ x ∈ C, x ∉ B → h x = f₁ x)
    (a b : Fin k) (ha : a ≠ 0) (hab : a < b) :
    Shatters Hbin (C.filter (fun x ↦ (f₀ x = a ∧ f₁ x = b) ∨ (f₀ x = b ∧ f₁ x = a))) := by
  classical
  intro g
  let g' : X → Bool := fun x ↦
    if hx : x ∈ C.filter (fun x ↦ (f₀ x = a ∧ f₁ x = b) ∨ (f₀ x = b ∧ f₁ x = a)) then g ⟨x, hx⟩
    else false
  obtain ⟨h, ⟨hbar, hbarH, rfl⟩, h0, h1⟩ := hB (C.filter (fun x ↦ (g' x = true ↔ f₀ x = a)))
    (Finset.filter_subset _ _)
  refine ⟨hbar a, hbarH a, fun z ↦ ?_⟩
  obtain ⟨x, hx⟩ := z
  obtain ⟨hxC, hpair⟩ := Finset.mem_filter.1 hx
  have hg' : g' x = g ⟨x, hx⟩ := by simp only [g', dif_pos hx]
  have hab' : a ≠ b := hab.ne
  have hval : (ovaPredict hbar x = a ∨ ovaPredict hbar x = b) ∧
      (ovaPredict hbar x = a ↔ g' x = true) := by
    by_cases hxB : x ∈ C.filter (fun x ↦ (g' x = true ↔ f₀ x = a))
    · rw [h0 x hxB]
      have hiff := (Finset.mem_filter.1 hxB).2
      rcases hpair with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;> rw [ha'] at hiff ⊢
      · exact ⟨Or.inl rfl, ⟨fun _ ↦ hiff.2 rfl, fun _ ↦ rfl⟩⟩
      · exact ⟨Or.inr rfl, hiff.symm⟩
    · rw [h1 x hxC hxB]
      have hiff : ¬ (g' x = true ↔ f₀ x = a) := fun h ↦ hxB (Finset.mem_filter.2 ⟨hxC, h⟩)
      rcases hpair with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;> rw [ha'] at hiff <;> rw [hb']
      · refine ⟨Or.inr rfl, ⟨fun h ↦ absurd h.symm hab', fun hg ↦ ?_⟩⟩
        exact absurd ⟨fun _ ↦ rfl, fun _ ↦ hg⟩ hiff
      · refine ⟨Or.inl rfl, ⟨fun _ ↦ ?_, fun _ ↦ rfl⟩⟩
        by_contra hg
        exact hiff ⟨fun h ↦ absurd h hg, fun h ↦ absurd h.symm hab'⟩
  have := (ova_ab hbar x ha hab hval.1).symm.trans hval.2
  show hbar a x = g ⟨x, hx⟩
  rw [← hg']
  cases hA : hbar a x <;> cases hG : g' x <;> simp_all

lemma fin2_pair : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide

lemma fin3_pair : ∀ a b : Fin 3, a ≠ b → ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) ∨
    ((a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0)) ∨ ((a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)) := by
  decide

lemma fin2_one_ne : (1 : Fin 2) ≠ 0 := by decide
lemma fin3_one_ne : (1 : Fin 3) ≠ 0 := by decide
lemma fin3_two_ne : (2 : Fin 3) ≠ 0 := by decide
lemma fin3_one_lt_two : (1 : Fin 3) < 2 := by decide

end Parts

end OvaAux

end UnderstandingML

open UnderstandingML
open UnderstandingML.OvaAux in
theorem solution {X : Type*} (Hbin : Set (X → Bool)) (d : ℕ) (hd : vcDim Hbin = d)
    (k : ℕ) [NeZero k] (C : Finset X) (hC : NShatters (ovaClass Hbin k) C) :
    (C.card : ℝ) ≤ 3 * k * d * Real.log (k * d) := by
  classical
  have hsh := shatter_bound Hbin d hd
  have h2 := two_pow_le Hbin d hsh k C hC
  obtain ⟨f₀, f₁, hne, hB⟩ := hC
  rcases (show k = 1 ∨ 2 ≤ k from by have := NeZero.pos k; omega) with rfl | hk2
  · -- one label: nothing is shattered
    have hC0 : C = ∅ := by
      by_contra hne'
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hne'
      exact hne x hx (Subsingleton.elim _ _)
    rw [hC0, Finset.card_empty, Nat.cast_zero]
    have := Real.log_natCast_nonneg d
    push_cast
    rw [one_mul]
    positivity
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · have : C.card = 0 := by
      rw [zero_mul, pow_zero] at h2
      by_contra h0
      have := Nat.one_lt_two_pow (n := C.card) h0
      omega
    rw [this]; simp
  by_cases hm : 4 ≤ k * d
  · have := real_bound (k * d) C.card hm (by rwa [mul_comm] at h2)
    push_cast at this
    linarith
  · have hd1' : d = 1 := by nlinarith
    subst hd1'
    have hk : k = 2 ∨ k = 3 := by omega
    rcases hk with rfl | rfl
    · -- two labels: every point carries the pair `{0, 1}`
      have hsub : C ⊆ C.filter (fun x ↦ (f₀ x = 0 ∧ f₁ x = 1) ∨ (f₀ x = 1 ∧ f₁ x = 0)) := by
        intro x hx
        refine Finset.mem_filter.2 ⟨hx, ?_⟩
        exact fin2_pair _ _ (hne x hx)
      have h4 := card_le_four_of_diff Hbin hsh _ (zero_b_part Hbin C f₀ f₁ hB 1 fin2_one_ne)
      have hc : C.card ≤ 4 := (Finset.card_le_card hsub).trans h4
      have hc' : (C.card : ℝ) ≤ 4 := by exact_mod_cast hc
      have := Real.log_two_gt_d9
      push_cast
      norm_num
      linarith
    · -- three labels: split by the label pair
      have hsub : C ⊆ C.filter (fun x ↦ (f₀ x = 0 ∧ f₁ x = 1) ∨ (f₀ x = 1 ∧ f₁ x = 0)) ∪
          C.filter (fun x ↦ (f₀ x = 0 ∧ f₁ x = 2) ∨ (f₀ x = 2 ∧ f₁ x = 0)) ∪
          C.filter (fun x ↦ (f₀ x = 1 ∧ f₁ x = 2) ∨ (f₀ x = 2 ∧ f₁ x = 1)) := by
        intro x hx
        rcases fin3_pair _ _ (hne x hx) with h | h | h
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hx, h⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hx, h⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hx, h⟩)
      have h01 := card_le_four_of_diff Hbin hsh _ (zero_b_part Hbin C f₀ f₁ hB 1 fin3_one_ne)
      have h02 := card_le_four_of_diff Hbin hsh _ (zero_b_part Hbin C f₀ f₁ hB 2 fin3_two_ne)
      have h12 := hsh _ (ab_part Hbin C f₀ f₁ hB 1 2 fin3_one_ne fin3_one_lt_two)
      have hc : C.card ≤ 9 := by
        have := Finset.card_le_card hsub
        have hu1 := Finset.card_union_le
          (C.filter (fun x ↦ (f₀ x = 0 ∧ f₁ x = 1) ∨ (f₀ x = 1 ∧ f₁ x = 0)) ∪
            C.filter (fun x ↦ (f₀ x = 0 ∧ f₁ x = 2) ∨ (f₀ x = 2 ∧ f₁ x = 0)))
          (C.filter (fun x ↦ (f₀ x = 1 ∧ f₁ x = 2) ∨ (f₀ x = 2 ∧ f₁ x = 1)))
        have hu2 := Finset.card_union_le
          (C.filter (fun x ↦ (f₀ x = 0 ∧ f₁ x = 1) ∨ (f₀ x = 1 ∧ f₁ x = 0)))
          (C.filter (fun x ↦ (f₀ x = 0 ∧ f₁ x = 2) ∨ (f₀ x = 2 ∧ f₁ x = 0)))
        omega
      have hc' : (C.card : ℝ) ≤ 9 := by exact_mod_cast hc
      have hlog3 : 1 < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have := Real.exp_one_lt_d9
        linarith
      push_cast
      norm_num
      linarith
