-- Prove2me | solution 1 for UnderstandingML.multiclass_uc_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T22:52:28.065803+00:00
-- url     : https://prove2.me/submissions/c37348c1-202f-440e-8148-22fc7d9cfd94

import Definitions.Def_UnderstandingML_MulticlassLearnability
import Theorems.Thm_UnderstandingML_binary_uc_optimal_rate
import Mathlib

open MeasureTheory

universe u v

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

namespace UCAux

open Classical UnderstandingML UnderstandingML.NatarajanAux

variable {X : Type*} {Y : Type*}

/-- The binary loss function of a multiclass hypothesis: `true` exactly on errors. -/
noncomputable def lossFn (h : X → Y) : X × Y → Bool := fun z ↦ decide (h z.1 ≠ z.2)

/-- The binary loss class of a multiclass class. -/
def lossClass (H : Set (X → Y)) : Set (X × Y → Bool) := lossFn '' H

lemma two_le_card_of_ndim [Fintype Y] (H : Set (X → Y)) (d : ℕ) (hd : ndim H = d)
    (hd1 : 1 ≤ d) : 2 ≤ Fintype.card Y := by
  by_contra hlt
  push Not at hlt
  have hsub : Subsingleton Y := Fintype.card_le_one_iff_subsingleton.1 (by omega)
  have h0 : ndim H = 0 := by
    unfold ndim
    refine le_antisymm (iSup₂_le fun C hC ↦ ?_) bot_le
    obtain ⟨f₀, f₁, hf, -⟩ := hC
    rcases C.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
    · simp
    · exact absurd (Subsingleton.elim _ _) (hf c hc)
  rw [hd] at h0; norm_cast at h0; omega

lemma sum_choose_le (n d : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ∑ i ∈ Finset.range (d + 1), (n.choose i : ℝ) * a ^ i ≤ (1 + a) ^ n := by
  rw [add_comm (1 : ℝ) a, add_pow]
  simp only [one_pow, mul_one]
  calc ∑ i ∈ Finset.range (d + 1), (n.choose i : ℝ) * a ^ i
      = ∑ i ∈ (Finset.range (d + 1)).filter (· ≤ n), (n.choose i : ℝ) * a ^ i := by
        rw [Finset.sum_filter_of_ne]
        intro i _ hi
        by_contra h
        push Not at h
        rw [Nat.choose_eq_zero_of_lt h] at hi
        simp at hi
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * a ^ i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
          omega
        · intro i _ _; positivity
    _ = _ := Finset.sum_congr rfl fun i _ ↦ by ring

lemma phi_le_real (q n d : ℕ) (hq : 1 ≤ q) :
    (phi q n d : ℝ) ≤ (8 * q : ℝ) ^ d * (9 / 8) ^ n := by
  unfold phi
  push_cast
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  calc ∑ i ∈ Finset.range (d + 1), (n.choose i : ℝ) * (q : ℝ) ^ i
      ≤ ∑ i ∈ Finset.range (d + 1), (8 * q : ℝ) ^ d * ((n.choose i : ℝ) * (1 / 8) ^ i) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hid : i ≤ d := by simp only [Finset.mem_range] at hi; omega
        have h8 : (q : ℝ) ^ i ≤ (8 * q) ^ d * (1 / 8) ^ i := by
          have h1 : (8 * q : ℝ) ^ i ≤ (8 * q) ^ d := pow_le_pow_right₀ (by linarith) hid
          have e : (8 * q : ℝ) ^ d * (1 / 8) ^ i = (8 * q) ^ d / 8 ^ i := by
            rw [one_div, inv_pow, div_eq_mul_inv]
          rw [e, le_div_iff₀ (by positivity)]
          rw [mul_pow] at h1
          linarith
        calc (n.choose i : ℝ) * q ^ i ≤ (n.choose i) * ((8 * q) ^ d * (1 / 8) ^ i) :=
              mul_le_mul_of_nonneg_left h8 (by positivity)
          _ = _ := by ring
    _ = (8 * q : ℝ) ^ d * ∑ i ∈ Finset.range (d + 1), (n.choose i : ℝ) * (1 / 8) ^ i := by
        rw [Finset.mul_sum]
    _ ≤ (8 * q : ℝ) ^ d * (1 + 1 / 8) ^ n := by
        gcongr; exact sum_choose_le n d (by norm_num)
    _ = _ := by norm_num

/-- The VC dimension of the loss class is `O(d log |Y|)`: a shattered set has at most
`10 d log |Y|` points. -/
lemma lossClass_shatters_card [Fintype Y] (H : Set (X → Y)) (d : ℕ) (hd : ndim H = d)
    (hd1 : 1 ≤ d) (C : Finset (X × Y)) (hC : Shatters (lossClass H) C) :
    (C.card : ℝ) ≤ 10 * d * Real.log (Fintype.card Y) := by
  let _ : LinearOrder Y := LinearOrder.lift' (Fintype.equivFin Y) (Fintype.equivFin Y).injective
  set k := Fintype.card Y with hk
  have hk2 : 2 ≤ k := two_le_card_of_ndim H d hd hd1
  set q := (Finset.univ.filter (fun p : Y × Y ↦ p.1 < p.2)).card with hq
  have hqk : q + k ≤ k ^ 2 := card_pairs_le
  have hq1 : 1 ≤ q := by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < k)
    refine Finset.card_pos.2 ⟨if a < b then (a, b) else (b, a), ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · exact h
    · exact lt_of_le_of_ne (not_lt.1 h) (Ne.symm hab)
  have hreal : ∀ g : C → Bool, ∃ h ∈ H, ∀ c : C, lossFn h c = g c := by
    intro g
    obtain ⟨g', ⟨h, hH, rfl⟩, hg'⟩ := hC g
    exact ⟨h, hH, hg'⟩
  choose hg hgH hgc using hreal
  set P : Finset X := C.image Prod.fst with hP
  have hfst : Set.InjOn Prod.fst (C : Set (X × Y)) := by
    intro c₁ hc₁ c₂ hc₂ h12
    have e1 := hgc (fun _ ↦ false) ⟨c₁, hc₁⟩
    have e2 := hgc (fun _ ↦ false) ⟨c₂, hc₂⟩
    simp only [lossFn, decide_eq_false_iff_not, not_not] at e1 e2
    refine Prod.ext h12 ?_
    rw [← e1, ← e2, h12]
  have hPcard : P.card = C.card := Finset.card_image_of_injOn hfst
  set HF : Finset (X → Y) := Finset.univ.image hg with hHF
  have hg_inj : ∀ g₁ g₂ : C → Bool, (∀ x ∈ P, hg g₁ x = hg g₂ x) → g₁ = g₂ := by
    intro g₁ g₂ hag
    funext c
    rw [← hgc g₁ c, ← hgc g₂ c]
    simp only [lossFn]
    rw [hag c.1.1 (Finset.mem_image_of_mem _ c.2)]
  have hHFcard : HF.card = 2 ^ C.card := by
    rw [hHF, Finset.card_image_of_injective _
      (fun g₁ g₂ h ↦ hg_inj g₁ g₂ (fun x _ ↦ by rw [h]))]
    simp [Finset.card_univ, Fintype.card_bool]
  have hle := card_le_phi P HF d
    (by
      intro h₁ h₁F h₂ h₂F hag
      obtain ⟨g₁, -, rfl⟩ := Finset.mem_image.1 h₁F
      obtain ⟨g₂, -, rfl⟩ := Finset.mem_image.1 h₂F
      rw [hg_inj g₁ g₂ hag])
    (by
      intro C' _ hC'
      have hsub : (HF : Set (X → Y)) ⊆ H := by
        intro h hh
        obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hh
        exact hgH g
      have := le_iSup₂ (f := fun (C : Finset X) (_ : NShatters H C) ↦ (C.card : ℕ∞)) C'
        (nshatters_mono hsub hC')
      change _ ≤ ndim H at this
      rw [hd] at this
      exact_mod_cast this)
  rw [hHFcard, hPcard] at hle
  set n := C.card with hn
  have h1 : (2 : ℝ) ^ n ≤ (8 * q) ^ d * (9 / 8) ^ n := by
    calc (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) := by push_cast; ring
      _ ≤ phi q n d := by exact_mod_cast hle
      _ ≤ _ := phi_le_real q n d hq1
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have h2 : (16 / 9 : ℝ) ^ n ≤ ((k : ℝ) ^ 5) ^ d := by
    have e : (2 : ℝ) ^ n = (16 / 9) ^ n * (9 / 8) ^ n := by rw [← mul_pow]; norm_num
    rw [e] at h1
    have h3 : (16 / 9 : ℝ) ^ n ≤ (8 * q) ^ d := le_of_mul_le_mul_right h1 (by positivity)
    refine h3.trans (pow_le_pow_left₀ (by positivity) ?_ d)
    have hqk' : (q : ℝ) ≤ k ^ 2 := by
      have : q ≤ k ^ 2 := by omega
      exact_mod_cast this
    have hk3 : (8 : ℝ) ≤ k ^ 3 := by nlinarith
    calc (8 * q : ℝ) ≤ 8 * k ^ 2 := by linarith
      _ ≤ k ^ 3 * k ^ 2 := by nlinarith
      _ = k ^ 5 := by ring
  have hlog := Real.log_le_log (by positivity) h2
  rw [Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  have hl169 : (1 / 2 : ℝ) ≤ Real.log (16 / 9) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    have e : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have hlk : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith

end UCAux

open UnderstandingML UCAux

open Classical in
theorem solution :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSingletonClass X]
        [MeasurableSpace Y] [MeasurableSingletonClass Y] [Fintype Y]
        (H : Set (X → Y)) (d : ℕ), H.Nonempty → (∀ h ∈ H, Measurable h) →
        NPointwiseSeparable H → ndim H = d → 1 ≤ d →
        UnderstandingML.HasUniformConvergenceWith UnderstandingML.lossMulti H (fun ε δ ↦
          ⌈C₂ * (d * Real.log (Fintype.card Y) + Real.log (1 / δ)) / ε ^ 2⌉₊) := by
  obtain ⟨C, hC, hbin⟩ := binary_uc_optimal_rate.{max u v}
  refine ⟨10 * C, by positivity, ?_⟩
  intro X Y _ _ _ _ _ H d hne hmeas hsep hdim hd1 ε δ hε hε1 hδ hδ1 D hD m hm
  set k := Fintype.card Y with hk
  have hk2 := two_le_card_of_ndim H d hdim hd1
  have hlogk : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) (by exact_mod_cast hk2)
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hl2 := Real.log_two_gt_d9
  set N := ⌊10 * d * Real.log k⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by push_cast; nlinarith)
  have herrm : ∀ h : X → Y, Measurable h → MeasurableSet {z : X × Y | h z.1 ≠ z.2} := by
    intro h hh
    have : {z : X × Y | h z.1 ≠ z.2} = (⋃ y : Y, (h ⁻¹' {y}) ×ˢ {y})ᶜ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_prod,
        Set.mem_preimage, Set.mem_singleton_iff, not_exists, not_and]
      constructor
      · intro hz y h1 h2; exact hz (h1.trans h2.symm)
      · intro hz heq; exact hz _ heq rfl
    rw [this]
    exact (MeasurableSet.iUnion fun y ↦
      (hh (measurableSet_singleton y)).prod (measurableSet_singleton y)).compl
  have hlossm : ∀ h : X → Y, Measurable h → Measurable (lossFn h) := by
    intro h hh
    refine measurable_to_bool ?_
    have : lossFn h ⁻¹' {true} = {z : X × Y | h z.1 ≠ z.2} := by ext z; simp [lossFn]
    rw [this]; exact herrm h hh
  have hGmeas : ∀ g ∈ lossClass H, Measurable g := by
    rintro _ ⟨h, hH, rfl⟩
    exact hlossm h (hmeas h hH)
  have hGsep : PointwiseSeparable (lossClass H) := by
    obtain ⟨H₀, hH₀H, hH₀c, happ⟩ := hsep
    refine ⟨lossFn '' H₀, Set.image_mono hH₀H, hH₀c.image _, ?_⟩
    rintro _ ⟨h, hH, rfl⟩
    obtain ⟨u, huH₀, hu⟩ := happ h hH
    refine ⟨fun n ↦ lossFn (u n), fun n ↦ ⟨u n, huH₀ n, rfl⟩, fun z ↦ ?_⟩
    obtain ⟨M, hM⟩ := hu z.1
    exact ⟨M, fun n hn ↦ by simp only [lossFn, hM n hn]⟩
  have hGdim : vcDim (lossClass H) ≤ N := by
    unfold vcDim
    refine iSup₂_le fun C hC ↦ ?_
    have h1 := lossClass_shatters_card H d hdim hd1 C hC
    have h2 : C.card ≤ N := Nat.le_floor h1
    exact_mod_cast h2
  have hm' : ⌈C * (N + Real.log (1 / δ)) / ε ^ 2⌉₊ ≤ m := by
    refine le_trans (Nat.ceil_mono ?_) hm
    have hNle : (N : ℝ) ≤ 10 * d * Real.log k := Nat.floor_le (by positivity)
    have hl : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
    rw [div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  set e : X × Y → (X × Y) × Bool := fun z ↦ (z, false) with he_def
  have he : Measurable e := measurable_id.prodMk measurable_const
  set D' := D.map e with hD'_def
  have hD' : IsProbabilityMeasure D' := Measure.isProbabilityMeasure_map he.aemeasurable
  have key := hbin (lossClass H) N hGmeas hGsep hGdim hN1 ε δ hε hε1 hδ hδ1 D' hD' m hm'
  set E : (Fin m → X × Y) → (Fin m → (X × Y) × Bool) := fun S i ↦ e (S i) with hE
  have hmp : MeasurePreserving E (iidLaw D m) (iidLaw D' m) := by
    unfold iidLaw
    exact measurePreserving_pi _ _ fun _ ↦ ⟨he, rfl⟩
  have hloss : ∀ (h : X → Y) z, loss01 (lossFn h) (e z) = lossMulti h z := by
    intro h z
    by_cases hz : h z.1 = z.2 <;> simp [loss01, lossMulti, lossFn, he_def, hz]
  have hloss01m : ∀ g : X × Y → Bool, Measurable g → Measurable (loss01 g) := by
    intro g hg
    have hs : MeasurableSet {p : (X × Y) × Bool | g p.1 = p.2} := by
      have : {p : (X × Y) × Bool | g p.1 = p.2} = ⋃ b : Bool, (g ⁻¹' {b}) ×ˢ {b} := by
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_preimage,
          Set.mem_singleton_iff]
        exact ⟨fun h' ↦ ⟨p.2, h', rfl⟩, fun ⟨b, h1, h2⟩ ↦ h1.trans h2.symm⟩
      rw [this]
      exact MeasurableSet.iUnion fun b ↦ (hg (measurableSet_singleton b)).prod
        (measurableSet_singleton b)
    unfold loss01
    exact Measurable.ite hs measurable_const measurable_const
  have hrisk : ∀ h ∈ H, risk loss01 D' (lossFn h) = risk lossMulti D h := by
    intro h hH
    unfold risk
    rw [hD'_def, integral_map he.aemeasurable
      (hloss01m _ (hlossm h (hmeas h hH))).aestronglyMeasurable]
    simp_rw [hloss]
  have hemp : ∀ h S, empRisk loss01 (E S) (lossFn h) = empRisk lossMulti S h := by
    intro h S
    unfold empRisk
    simp_rw [hE, hloss]
  have hsub : {S : Fin m → X × Y | ¬ IsRepresentative lossMulti H D ε S} ⊆
      E ⁻¹' {S' | ¬ IsRepresentative loss01 (lossClass H) D' ε S'} := by
    intro S hS hall
    apply hS
    intro h hH
    have := hall (lossFn h) ⟨h, hH, rfl⟩
    rwa [hemp, hrisk h hH] at this
  calc iidLaw D m {S | ¬ IsRepresentative lossMulti H D ε S}
      ≤ iidLaw D m (E ⁻¹' {S' | ¬ IsRepresentative loss01 (lossClass H) D' ε S'}) :=
        measure_mono hsub
    _ ≤ (iidLaw D m).map E {S' | ¬ IsRepresentative loss01 (lossClass H) D' ε S'} :=
        Measure.le_map_apply hmp.measurable.aemeasurable _
    _ = iidLaw D' m {S' | ¬ IsRepresentative loss01 (lossClass H) D' ε S'} := by
        rw [hmp.map_eq]
    _ ≤ ENNReal.ofReal δ := key
