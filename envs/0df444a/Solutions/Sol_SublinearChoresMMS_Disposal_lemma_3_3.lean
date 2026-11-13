-- Prove2me | solution 1 for SublinearChoresMMS.Disposal.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:27:25.397547+00:00
-- url     : https://prove2.me/submissions/9ace46ce-2300-419a-88a6-a45a82e382a6

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Slots

section
noncomputable section

namespace SublinearChoresMMS.Disposal.Dev.L33.PartAB

open SublinearChoresMMS.Disposal
open Finset

/-! ## Part A: abstract slot rounding (Birkhoff–von Neumann) -/

theorem round_exists {E S : Type} [Fintype E] [Fintype S] [DecidableEq S]
    (f : S → E → ℝ) (h0 : ∀ s e, 0 ≤ f s e) (h1 : ∀ e, ∑ s, f s e = 1)
    (h2 : ∀ s, ∑ e, f s e ≤ 1) :
    ∃ P : FiniteLaw (E → S),
      (∀ e s, P.mean (fun A => if A e = s then 1 else 0) = f s e) ∧
      ∀ a : Fin P.size, 0 < P.weight a →
        Function.Injective (P.atom a) ∧ (∀ e, 0 < f (P.atom a e) e) ∧
        (∀ s, ∑ e, f s e = 1 → ∃ e, P.atom a e = s) := by
  classical
  have hcard : Fintype.card E ≤ Fintype.card S := by
    have : (Fintype.card E : ℝ) ≤ Fintype.card S := by
      calc (Fintype.card E : ℝ) = ∑ e : E, ∑ s, f s e := by simp [h1]
        _ = ∑ s, ∑ e, f s e := Finset.sum_comm
        _ ≤ ∑ s : S, (1:ℝ) := Finset.sum_le_sum fun s _ => h2 s
        _ = Fintype.card S := by simp
    exact_mod_cast this
  set k := Fintype.card S - Fintype.card E with hk
  have hcardES : Fintype.card (E ⊕ Fin k) = Fintype.card S := by
    simp only [Fintype.card_sum, Fintype.card_fin]; omega
  let φ : S ≃ E ⊕ Fin k := (Fintype.equivOfCardEq hcardES).symm
  let d : S → ℝ := fun s => 1 - ∑ e, f s e
  have hd0 : ∀ s, 0 ≤ d s := fun s => by simp only [d]; linarith [h2 s]
  have hdsum : ∑ s, d s = (k : ℝ) := by
    simp only [d, Finset.sum_sub_distrib, Finset.sum_const, card_univ, nsmul_eq_mul, mul_one]
    rw [Finset.sum_comm]; simp [h1, k, Nat.cast_sub hcard]
  have hdk : ∀ s, (k:ℝ) * (d s / k) = d s := by
    intro s
    rcases Nat.eq_zero_or_pos k with h | h
    · have : d s = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => hd0 s)).1 (by rw [hdsum, h]; simp) s
          (mem_univ _)
      simp [this]
    · have : (0:ℝ) < k := by exact_mod_cast h
      field_simp
  let M : Matrix S S ℝ := fun r s => Sum.elim (fun e => f s e) (fun _ => d s / k) (φ r)
  have hM : M ∈ doublyStochastic ℝ S := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨?_, ?_, ?_⟩
    · intro r s
      rcases hφ : φ r with e | j
      · simp [M, hφ, h0]
      · simp only [M, hφ, Sum.elim_inr]; exact div_nonneg (hd0 s) (Nat.cast_nonneg _)
    · intro r
      rcases hφ : φ r with e | j
      · simp [M, hφ, h1]
      · simp only [M, hφ, Sum.elim_inr]
        rw [← Finset.sum_div, hdsum]
        have : (0:ℝ) < k := by exact_mod_cast j.pos
        field_simp
    · intro s
      rw [← φ.symm.sum_comp]
      simp only [M, Equiv.apply_symm_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hdk]
      simp [d]
  obtain ⟨w, hw0, hw1, hwM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  have hentry : ∀ r s, M r s = ∑ σ : Equiv.Perm S, w σ * (if σ r = s then 1 else 0) := by
    intro r s
    rw [← hwM]
    simp [Matrix.sum_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have hge : ∀ (σ : Equiv.Perm S) r, w σ ≤ M r (σ r) := by
    intro σ r
    rw [hentry]
    have := Finset.single_le_sum (f := fun τ : Equiv.Perm S => w τ * (if τ r = σ r then 1 else 0))
      (fun τ _ => mul_nonneg (hw0 τ) (by split_ifs <;> norm_num)) (mem_univ σ)
    simpa using this
  let A : Equiv.Perm S → E → S := fun σ e => σ (φ.symm (Sum.inl e))
  let l : OAI.CliqueFreeIndependence.Lottery.Law (E → S) :=
    (Finset.univ : Finset (Equiv.Perm S)).toList.map (fun σ => (w σ, A σ))
  have hexp : ∀ g : (E → S) → ℝ,
      OAI.CliqueFreeIndependence.Lottery.expect l g = ∑ σ, w σ * g (A σ) := by
    intro g
    simp only [OAI.CliqueFreeIndependence.Lottery.expect, l, List.map_map]
    exact Finset.sum_map_toList _ _
  have hprob : OAI.CliqueFreeIndependence.Lottery.IsProb l := by
    refine ⟨?_, ?_⟩
    · intro z hz
      simp only [l, List.mem_map] at hz
      obtain ⟨σ, -, rfl⟩ := hz
      exact hw0 σ
    · simp only [OAI.CliqueFreeIndependence.Lottery.total, hexp, mul_one, hw1]
  refine ⟨⟨l, hprob⟩, ?_, ?_⟩
  · intro e s
    simp only [FiniteLaw.mean, hexp]
    have := hentry (φ.symm (Sum.inl e)) s
    simp only [M, Equiv.apply_symm_apply, Sum.elim_inl] at this
    rw [this]
  · intro a ha
    have hlen : a.val < (Finset.univ : Finset (Equiv.Perm S)).toList.length := by
      have := a.isLt; simpa [FiniteLaw.size, l] using this
    set σ := (Finset.univ : Finset (Equiv.Perm S)).toList[a.val]'hlen with hσ
    have hat : FiniteLaw.atom ⟨l, hprob⟩ a = A σ := by
      simp [FiniteLaw.atom, l, σ]
    have hwt : FiniteLaw.weight ⟨l, hprob⟩ a = w σ := by
      simp [FiniteLaw.weight, l, σ]
    rw [hwt] at ha
    rw [hat]
    refine ⟨?_, ?_, ?_⟩
    · intro e₁ e₂ h
      simpa [A] using h
    · intro e
      have := hge σ (φ.symm (Sum.inl e))
      simp only [M, Equiv.apply_symm_apply, Sum.elim_inl] at this
      exact lt_of_lt_of_le ha this
    · intro s hs
      have hds : d s = 0 := by simp [d, hs]
      have := hge σ (σ.symm s)
      simp only [M, Equiv.apply_symm_apply] at this
      rcases hφ : φ (σ.symm s) with e | j
      · refine ⟨e, ?_⟩
        simp only [A]
        rw [← hφ, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
      · rw [hφ] at this
        simp only [Sum.elim_inr, hds, zero_div] at this
        linarith

/-! ## Part B: general unit-slots -/

theorem gs_nonneg {m : ℕ} (z : Fin m → ℝ) (e : Fin m) (s : ℕ) : 0 ≤ generalSlot z e s := by
  unfold generalSlot ChoresEFX.slotMass; exact le_max_left _ _

/-- Length of `[a,b) ∩ [x,y)`. -/
def ilen (a b x y : ℝ) : ℝ := max 0 (min b y - max a x)

lemma ilen_split2 {a b x y w : ℝ} (hab : a ≤ b) (hxy : x ≤ y) (hyw : y ≤ w) :
    ilen a b x y + ilen a b y w = ilen a b x w := by
  simp only [ilen, max_def, min_def]; split_ifs <;> linarith

lemma ilen_split1 {a b c x y : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hxy : x ≤ y) :
    ilen a b x y + ilen b c x y = ilen a c x y := by
  simp only [ilen, max_def, min_def]; split_ifs <;> linarith

lemma ilen_le_right {a b x y : ℝ} (hxy : x ≤ y) : ilen a b x y ≤ y - x := by
  simp only [ilen, max_def, min_def]; split_ifs <;> linarith

lemma ilen_le_left {a b x y : ℝ} (hab : a ≤ b) : ilen a b x y ≤ b - a := by
  simp only [ilen, max_def, min_def]; split_ifs <;> linarith

lemma ilen_sum_range {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (N : ℕ) :
    ∑ s ∈ range N, ilen a b s (s + 1) = ilen a b 0 N := by
  induction N with
  | zero =>
    simp only [range_zero, sum_empty, Nat.cast_zero, ilen, max_def, min_def]
    split_ifs <;> linarith
  | succ N ih =>
    rw [sum_range_succ, ih, ilen_split2 hab (by positivity) (by simp)]
    push_cast; rfl

lemma ilen_full {a b x y : ℝ} (hxa : x ≤ a) (hab : a ≤ b) (hby : b ≤ y) :
    ilen a b x y = b - a := by
  simp only [ilen, max_def, min_def]; split_ifs <;> linarith

/-- Zero-extension of `z` to `ℕ`. -/
def zN {m : ℕ} (z : Fin m → ℝ) (k : ℕ) : ℝ := if h : k < m then z ⟨k, h⟩ else 0

/-- Prefix sums. -/
def PS {m : ℕ} (z : Fin m → ℝ) (N : ℕ) : ℝ := ∑ k ∈ range N, zN z k

lemma zN_nonneg {m : ℕ} {z : Fin m → ℝ} (hz : ∀ e, 0 ≤ z e) (k : ℕ) : 0 ≤ zN z k := by
  unfold zN; split_ifs
  · exact hz _
  · exact le_rfl

lemma PS_nonneg {m : ℕ} {z : Fin m → ℝ} (hz : ∀ e, 0 ≤ z e) (N : ℕ) : 0 ≤ PS z N :=
  sum_nonneg fun k _ => zN_nonneg hz k

lemma PS_mono {m : ℕ} {z : Fin m → ℝ} (hz : ∀ e, 0 ≤ z e) {N N' : ℕ} (h : N ≤ N') :
    PS z N ≤ PS z N' :=
  sum_le_sum_of_subset_of_nonneg (range_mono h) fun k _ _ => zN_nonneg hz k

lemma PS_succ {m : ℕ} (z : Fin m → ℝ) (e : Fin m) : PS z (e.val + 1) = PS z e.val + z e := by
  simp [PS, sum_range_succ, zN, e.isLt]

lemma sum_fin_eq {m : ℕ} (g : ℕ → ℝ) : ∑ e : Fin m, g e.val = ∑ k ∈ range m, g k :=
  Fin.sum_univ_eq_sum_range g m

lemma W_eq {m : ℕ} (z : Fin m → ℝ) (e : Fin m) :
    ChoresEFX.shareBefore (fun _ : Unit => z) (fun _ e => e.val) () e = PS z e.val := by
  classical
  unfold ChoresEFX.shareBefore PS
  rw [sum_filter]
  trans (∑ x : Fin m, (fun k => if k < e.val then zN z k else 0) x.val)
  · apply sum_congr rfl
    intro x _
    simp [zN, x.isLt]
  refine (sum_fin_eq (fun k => if k < e.val then zN z k else 0)).trans ?_
  rw [← sum_filter]
  congr 1
  ext k; simp only [mem_filter, mem_range]; omega

lemma gs_eq {m : ℕ} (z : Fin m → ℝ) (e : Fin m) (s : ℕ) :
    generalSlot z e s = ilen (PS z e.val) (PS z e.val + z e) s (s + 1) := by
  unfold generalSlot ChoresEFX.slotMass ilen
  rw [W_eq]

lemma load_eq {m : ℕ} (z : Fin m → ℝ) (hz : ∀ e, 0 ≤ z e) (x y : ℝ) (hxy : x ≤ y) :
    ∑ e : Fin m, ilen (PS z e.val) (PS z e.val + z e) x y = ilen 0 (PS z m) x y := by
  have key : ∀ N ≤ m, ∑ k ∈ range N, ilen (PS z k) (PS z (k + 1)) x y = ilen 0 (PS z N) x y := by
    intro N
    induction N with
    | zero =>
      intro _
      simp only [range_zero, sum_empty, PS, ilen]
      rw [eq_comm, max_eq_left (by linarith [min_le_left (0:ℝ) y, le_max_left (0:ℝ) x])]
    | succ N ih =>
      intro hN
      rw [sum_range_succ, ih (by omega)]
      exact ilen_split1 (PS_nonneg hz _) (PS_mono hz (by omega)) hxy
  rw [← key m le_rfl]
  rw [← sum_fin_eq (fun k => ilen (PS z k) (PS z (k + 1)) x y)]
  apply sum_congr rfl
  intro e _
  rw [PS_succ]

lemma gs_load_eq {m : ℕ} (z : Fin m → ℝ) (hz : ∀ e, 0 ≤ z e) (s : ℕ) :
    ∑ e, generalSlot z e s = ilen 0 (PS z m) s (s + 1) := by
  simp only [gs_eq]
  exact load_eq z hz _ _ (by linarith)

lemma W_add_le {m : ℕ} (z : Fin m → ℝ) (hz : ∀ e, 0 ≤ z e) (e : Fin m) :
    PS z e.val + z e ≤ ∑ e, z e := by
  rw [← PS_succ]
  have : ∑ e, z e = PS z m := by
    rw [PS, ← sum_fin_eq]
    apply sum_congr rfl; intro x _; simp [zN, x.isLt]
  rw [this]; exact PS_mono hz e.isLt

theorem gs_sum_slots {m : ℕ} (z : Fin m → ℝ) (hz : ∀ e, 0 ≤ z e)
    (hsum : ∑ e, z e ≤ (m : ℝ) + 1) (e : Fin m) :
    ∑ s : Fin (m + 1), generalSlot z e s.val = z e := by
  rw [sum_fin_eq (fun s => generalSlot z e s)]
  simp only [gs_eq]
  rw [ilen_sum_range (PS_nonneg hz _) (by linarith [hz e])]
  rw [ilen_full (PS_nonneg hz _) (by linarith [hz e])]
  · ring
  · have := W_add_le z hz e; push_cast; linarith

theorem gs_load_le {m : ℕ} (z : Fin m → ℝ) (hz : ∀ e, 0 ≤ z e) (s : ℕ) :
    ∑ e, generalSlot z e s ≤ 1 := by
  rw [gs_load_eq z hz]
  have := ilen_le_right (a := 0) (b := PS z m) (x := (s:ℝ)) (y := (s:ℝ) + 1) (by linarith)
  linarith

lemma ilen_pos {a b x y : ℝ} (h : 0 < ilen a b x y) : x < b ∧ a < y := by
  simp only [ilen] at h
  have ht : 0 < min b y - max a x := by
    rcases le_total 0 (min b y - max a x) with h' | h'
    · rcases h'.lt_or_eq with h'' | h''
      · exact h''
      · rw [← h'', max_self] at h; exact absurd h (lt_irrefl _)
    · rw [max_eq_left h'] at h; exact absurd h (lt_irrefl _)
  have := min_le_left b y
  have := min_le_right b y
  have := le_max_left a x
  have := le_max_right a x
  constructor <;> linarith

lemma ilen_cover {a b x y : ℝ} (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    ilen a b x y = y - x := by
  simp only [ilen, max_def, min_def]; split_ifs <;> linarith

lemma gs_single {m : ℕ} (c : Fin m → ℝ) (hc : Antitone c)
    (z : Fin m → ℝ) (hz : ∀ e, 0 ≤ z e) (e : Fin m) (s : ℕ)
    (hpos : 0 < generalSlot z e (s + 1)) :
    c e ≤ ∑ e', c e' * generalSlot z e' s := by
  rw [gs_eq] at hpos
  obtain ⟨hb, -⟩ := ilen_pos hpos
  rw [← PS_succ] at hb
  push_cast at hb
  have hload : ∑ e', generalSlot z e' s = 1 := by
    rw [gs_load_eq z hz, ilen_cover (by positivity) (by linarith)]
    · ring
    · have := PS_mono hz (Nat.succ_le_of_lt e.isLt); linarith
  calc c e = ∑ e', c e * generalSlot z e' s := by rw [← mul_sum, hload, mul_one]
    _ ≤ ∑ e', c e' * generalSlot z e' s := by
      apply sum_le_sum
      intro e' _
      rcases (gs_nonneg z e' s).lt_or_eq with hp | h0
      · apply mul_le_mul_of_nonneg_right _ hp.le
        apply hc
        by_contra hlt
        push Not at hlt
        rw [gs_eq] at hp
        obtain ⟨-, ha⟩ := ilen_pos hp
        have := PS_mono hz (show e.val + 1 ≤ e'.val from hlt)
        linarith
      · rw [← h0]; simp

theorem gs_cost {m : ℕ} (c : Fin m → ℝ) (hc0 : ∀ e, 0 ≤ c e) (hc : Antitone c)
    (z : Fin m → ℝ) (hz : ∀ e, 0 ≤ z e) (T : Finset (Fin m)) (σ : Fin m → ℕ)
    (hσ : Set.InjOn σ T) (hpos : ∀ e ∈ T, 0 < generalSlot z e (σ e)) :
    ∑ e ∈ T, c e ≤ (∑ e, c e * z e) + max 0 (⨆ e, c e) ∧
    ∑ e ∈ T.filter (fun e => σ e ≠ 0), c e ≤ ∑ e, c e * z e := by
  classical
  set T' := T.filter (fun e => σ e ≠ 0) with hT'
  have second : ∑ e ∈ T', c e ≤ ∑ e, c e * z e := by
    calc ∑ e ∈ T', c e ≤ ∑ e ∈ T', ∑ e', c e' * generalSlot z e' (σ e - 1) := by
          apply sum_le_sum
          intro e he
          rw [hT', mem_filter] at he
          apply gs_single c hc z hz e
          have : σ e - 1 + 1 = σ e := by omega
          rw [this]; exact hpos e he.1
      _ = ∑ e', c e' * ∑ e ∈ T', generalSlot z e' (σ e - 1) := by
          rw [sum_comm]; simp only [mul_sum]
      _ ≤ ∑ e', c e' * z e' := by
          apply sum_le_sum
          intro e' _
          apply mul_le_mul_of_nonneg_left _ (hc0 e')
          have hinj : Set.InjOn (fun e => σ e - 1) (T' : Set (Fin m)) := by
            intro e₁ h₁ e₂ h₂ h
            simp only [hT', coe_filter, Set.mem_ofPred_eq] at h₁ h₂
            apply hσ h₁.1 h₂.1
            simp only at h; omega
          rw [← sum_image (g := fun e => σ e - 1) (f := fun s => generalSlot z e' s) hinj]
          set I := T'.image (fun e => σ e - 1)
          have hsub : I ⊆ range (I.sup id + 1) := by
            intro s hs
            rw [mem_range]
            have := le_sup (f := id) hs
            simp only [id] at this; omega
          calc ∑ s ∈ I, generalSlot z e' s
              ≤ ∑ s ∈ range (I.sup id + 1), generalSlot z e' s :=
                sum_le_sum_of_subset_of_nonneg hsub fun s _ _ => gs_nonneg z e' s
            _ = ilen (PS z e'.val) (PS z e'.val + z e') 0 ((I.sup id + 1 : ℕ) : ℝ) := by
                simp only [gs_eq]
                rw [ilen_sum_range (PS_nonneg hz _) (by linarith [hz e'])]
            _ ≤ z e' := by
                have := ilen_le_left (a := PS z e'.val) (b := PS z e'.val + z e')
                  (x := 0) (y := ((I.sup id + 1 : ℕ) : ℝ)) (by linarith [hz e'])
                linarith
  refine ⟨?_, second⟩
  rw [← sum_filter_add_sum_filter_not T (fun e => σ e ≠ 0)]
  apply add_le_add second
  set T0 := T.filter (fun e => ¬ σ e ≠ 0)
  rcases T0.eq_empty_or_nonempty with h | ⟨e, he⟩
  · rw [h, sum_empty]; exact le_max_left _ _
  · have hsub : T0 ⊆ {e} := by
      intro e₂ he₂
      simp only [T0, mem_filter, not_not] at he he₂
      rw [mem_singleton]
      exact hσ he₂.1 he.1 (by rw [he₂.2, he.2])
    calc ∑ x ∈ T0, c x ≤ ∑ x ∈ {e}, c x :=
          sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => hc0 x
      _ = c e := sum_singleton _ _
      _ ≤ ⨆ e, c e := le_ciSup (Set.finite_range c).bddAbove e
      _ ≤ max 0 (⨆ e, c e) := le_max_right _ _

theorem gs_first_in_prefix {m : ℕ} (z : Fin m → ℝ) (hz : ∀ e, 0 ≤ z e) (K : ℕ)
    (hK : 1 < ∑ e ∈ univ.filter (fun e : Fin m => e.val < K), z e) (e : Fin m)
    (he : 0 < generalSlot z e 0) : e.val < K := by
  by_contra hlt
  push Not at hlt
  have hW : ∑ e ∈ univ.filter (fun e : Fin m => e.val < K), z e ≤ PS z e.val := by
    rw [← W_eq]
    unfold ChoresEFX.shareBefore
    apply sum_le_sum_of_subset_of_nonneg
    · intro x; simp only [mem_filter, mem_univ, true_and]; omega
    · intro x _ _; exact hz x
  rw [gs_eq] at he
  simp only [ilen, Nat.cast_zero, zero_add] at he
  have : min (PS z e.val + z e) 1 - max (PS z e.val) 0 ≤ 0 := by
    have h1 : min (PS z e.val + z e) 1 ≤ 1 := min_le_right _ _
    have h2 : PS z e.val ≤ max (PS z e.val) 0 := le_max_left _ _
    linarith
  rw [max_eq_left this] at he
  exact lt_irrefl _ he

end SublinearChoresMMS.Disposal.Dev.L33.PartAB
end
end

section
noncomputable section

namespace SublinearChoresMMS.Disposal.Dev.L33.PartC

open SublinearChoresMMS.Disposal
open Finset

/-! ### Generic helpers -/

lemma sum_ite_le_of_unique {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (a : ι → ℝ) (b : ℝ) (hb : 0 ≤ b) (huniq : ∀ x y, P x → P y → x = y)
    (ha : ∀ x, P x → a x ≤ b) : ∑ x, (if P x then a x else 0) ≤ b := by
  rw [← Finset.sum_filter]
  by_cases h : ∃ x, P x
  · obtain ⟨x, hx⟩ := h
    have : univ.filter P = {x} := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun hy => huniq _ _ hy hx, fun hy => hy ▸ hx⟩
    rw [this, sum_singleton]
    exact ha x hx
  · push_neg at h
    have : univ.filter P = ∅ := by
      ext y
      simp [h y]
    rw [this, sum_empty]
    exact hb

lemma card_filter_div_le {α : Type*} (S : Finset α) (f : α → ℕ) (hf : Set.InjOn f S)
    (d s : ℕ) (hd : 0 < d) : (S.filter (fun g => f g / d = s)).card ≤ d := by
  calc (S.filter (fun g => f g / d = s)).card ≤ (Ico (s * d) (s * d + d)).card := by
        apply card_le_card_of_injOn f
        · intro g hg
          simp only [coe_filter, Set.mem_setOf_eq] at hg
          simp only [coe_Ico, Set.mem_Ico]
          have h1 := Nat.div_add_mod (f g) d
          have h2 := Nat.mod_lt (f g) hd
          rw [hg.2] at h1
          constructor
          · rw [Nat.mul_comm]; omega
          · rw [Nat.mul_comm]; omega
        · exact hf.mono (fun x hx => (mem_filter.mp hx).1)
    _ = d := by simp

lemma sum_ite_mem_le_one {m : ℕ} (F : Finset (Fin m)) (d : ℕ) (hd : 0 < d) (hF : F.card ≤ d) :
    ∑ g, (if g ∈ F then 1 / (d : ℝ) else 0) ≤ 1 := by
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, mul_one_div,
    div_le_one (by exact_mod_cast hd)]
  exact_mod_cast hF

/-! ### Positions -/

lemma position_le_val {m : ℕ} (S : Finset (Fin m)) (g : Fin m) : position S g ≤ g.val := by
  unfold position
  calc (S.filter (fun x => x.val < g.val)).card ≤ (Iio g).card := by
        apply card_le_card
        intro x hx
        simp only [mem_filter] at hx
        rw [mem_Iio]
        exact Fin.lt_iff_val_lt_val.mpr hx.2
    _ = g.val := Fin.card_Iio g

lemma position_mono {m : ℕ} (S : Finset (Fin m)) {g h : Fin m} (hgh : g ≤ h) :
    position S g ≤ position S h := by
  unfold position
  apply card_le_card
  intro x hx
  simp only [mem_filter] at hx ⊢
  have := Fin.le_iff_val_le_val.mp hgh
  exact ⟨hx.1, by omega⟩

lemma position_lt {m : ℕ} (S : Finset (Fin m)) {g h : Fin m} (hg : g ∈ S) (hgh : g < h) :
    position S g < position S h := by
  unfold position
  apply card_lt_card
  have hgh' := Fin.lt_iff_val_lt_val.mp hgh
  rw [ssubset_iff_of_subset]
  · refine ⟨g, ?_, ?_⟩
    · simp only [mem_filter]; exact ⟨hg, hgh'⟩
    · simp
  · intro x hx
    simp only [mem_filter] at hx ⊢
    exact ⟨hx.1, by omega⟩

lemma position_injOn {m : ℕ} (S : Finset (Fin m)) : Set.InjOn (position S) S := by
  intro g hg h hh he
  rcases lt_trichotomy g h with H | H | H
  · exact absurd he (ne_of_lt (position_lt S hg H))
  · exact H
  · exact absurd he.symm (ne_of_lt (position_lt S hh H))

lemma position_lt_card {m : ℕ} (S : Finset (Fin m)) {g : Fin m} (hg : g ∈ S) :
    position S g < S.card := by
  unfold position
  apply card_lt_card
  rw [ssubset_iff_of_subset (filter_subset _ _)]
  exact ⟨g, hg, by simp⟩

lemma position_surj {m : ℕ} (S : Finset (Fin m)) {k : ℕ} (hk : k < S.card) :
    ∃ g ∈ S, position S g = k := by
  have hsub : S.image (position S) ⊆ range S.card := by
    intro x hx
    simp only [mem_image] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact mem_range.mpr (position_lt_card S hg)
  have hcard : (range S.card).card ≤ (S.image (position S)).card := by
    rw [card_range, card_image_of_injOn (position_injOn S)]
  have heq := eq_of_subset_of_card_le hsub hcard
  have hk' : k ∈ S.image (position S) := by rw [heq]; exact mem_range.mpr hk
  simpa using hk'

lemma val_le_K_add_position {m : ℕ} (Z : Finset (Fin m)) (K : ℕ) (hK : Z.card ≤ K)
    (g : Fin m) : g.val ≤ K + position (univ \ Z) g := by
  have h1 : Iio g ⊆ ((univ \ Z).filter (fun x => x.val < g.val)) ∪ Z := by
    intro x hx
    rw [mem_Iio] at hx
    by_cases hxZ : x ∈ Z
    · exact mem_union_right _ hxZ
    · apply mem_union_left
      simp only [mem_filter, mem_sdiff, mem_univ, true_and]
      exact ⟨hxZ, Fin.lt_iff_val_lt_val.mp hx⟩
  have h2 := card_le_card h1
  rw [Fin.card_Iio] at h2
  have h3 := card_union_le ((univ \ Z).filter (fun x => x.val < g.val)) Z
  unfold position
  omega

/-! ### The shift -/

lemma shift_sum_le {m : ℕ} (Z : Finset (Fin m)) (K : ℕ) (hK : Z.card ≤ K) (F w : Fin m → ℝ)
    (hF : ∀ g, 0 ≤ F g) (hw0 : ∀ g, 0 ≤ w g)
    (hw : ∀ e g : Fin m, g.val ≤ e.val → w e ≤ w g) :
    ∑ e, w e * (if e.val < K then 0 else ∑ g : Fin m,
        if g ∉ Z ∧ position (univ \ Z) g = e.val - K then F g else 0)
      ≤ ∑ g, if g ∉ Z then w g * F g else 0 := by
  have step : ∀ e : Fin m, w e * (if e.val < K then 0 else ∑ g : Fin m,
        if g ∉ Z ∧ position (univ \ Z) g = e.val - K then F g else 0) =
      ∑ g : Fin m, if g ∉ Z ∧ e.val = K + position (univ \ Z) g then w e * F g else 0 := by
    intro e
    split_ifs with he
    · rw [mul_zero]
      symm
      apply sum_eq_zero
      intro g _
      rw [if_neg]
      omega
    · rw [mul_sum]
      apply sum_congr rfl
      intro g _
      by_cases hg : g ∉ Z
      · by_cases hp : position (univ \ Z) g = e.val - K
        · rw [if_pos ⟨hg, hp⟩, if_pos ⟨hg, by omega⟩]
        · rw [if_neg (fun h => hp h.2), if_neg (fun h => hp (by omega)), mul_zero]
      · rw [if_neg (fun h => hg h.1), if_neg (fun h => hg h.1), mul_zero]
  rw [sum_congr rfl (fun e _ => step e), sum_comm]
  apply sum_le_sum
  intro g _
  by_cases hg : g ∉ Z
  · rw [if_pos hg]
    apply sum_ite_le_of_unique (fun e : Fin m => g ∉ Z ∧ e.val = K + position (univ \ Z) g)
    · exact mul_nonneg (hw0 g) (hF g)
    · intro x y hx hy
      exact Fin.ext (hx.2.trans hy.2.symm)
    · intro e he
      have := val_le_K_add_position Z K hK g
      exact mul_le_mul_of_nonneg_right (hw e g (by omega)) (hF g)
  · rw [if_neg hg]
    apply le_of_eq
    apply sum_eq_zero
    intro e _
    rw [if_neg]
    exact fun h => hg h.1

/-! ### Basic facts about the definitions -/

section basic

variable {n m q : ℕ}

def slotIdx (P : Labels n m q) (t : Fin (n / q)) (g : Fin m) : ℕ :=
  if t.val + 1 = n / q then position (G P t) g / denominator n q t else g.val / q

lemma rawSlot_eq (P : Labels n m q) (t : Fin (n / q)) (g : Fin m) (s : ℕ) :
    rawSlot P t g s = if s = slotIdx P t g then rawBase P t g else 0 := rfl

lemma slotIdx_le (P : Labels n m q) (t : Fin (n / q)) (g : Fin m) : slotIdx P t g ≤ g.val := by
  unfold slotIdx
  split_ifs
  · exact (Nat.div_le_self _ _).trans (position_le_val _ _)
  · exact Nat.div_le_self _ _

lemma rawBase_nonneg (P : Labels n m q) (t : Fin (n / q)) (g : Fin m) : 0 ≤ rawBase P t g := by
  unfold rawBase
  split_ifs <;> positivity

lemma rawBase_le (P : Labels n m q) (t : Fin (n / q)) (g : Fin m) :
    rawBase P t g ≤ if g ∈ G P t then 1 / (denominator n q t : ℝ) else 0 := by
  unfold rawBase
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd h1.2 h2
  · positivity
  · exact le_rfl

lemma rawSlot_nonneg (P : Labels n m q) (t : Fin (n / q)) (g : Fin m) (s : ℕ) :
    0 ≤ rawSlot P t g s := by
  rw [rawSlot_eq]
  split_ifs
  · exact rawBase_nonneg _ _ _
  · exact le_rfl

lemma rawSlot_sum (P : Labels n m q) (t : Fin (n / q)) (g : Fin m) :
    ∑ s : Fin (m + 1), rawSlot P t g s.val = rawBase P t g := by
  have hk : slotIdx P t g < m + 1 := by
    have := slotIdx_le P t g
    have := g.isLt
    omega
  simp only [rawSlot_eq]
  rw [sum_eq_single ⟨slotIdx P t g, hk⟩]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext h)
  · intro h
    exact absurd (mem_univ _) h

lemma rawSlot_top (P : Labels n m q) (t : Fin (n / q)) (g : Fin m) : rawSlot P t g m = 0 := by
  rw [rawSlot_eq, if_neg]
  intro h
  have := slotIdx_le P t g
  have := g.isLt
  omega

lemma card_Z_le_K {R : Finset (Fin n)} (p : Packings n m q R) (i : Ordinary R) :
    (Z (p i)).card ≤ K p := by
  unfold K
  exact le_sup (f := fun i => (Z (p i)).card) (mem_univ i)

lemma G_unique (P : Labels n m q) {t t' : Fin (n / q)} {e : Fin m} (h : e ∈ G P t)
    (h' : e ∈ G P t') : t = t' := by
  unfold G at h h'
  simp only [mem_filter, mem_univ, true_and] at h h'
  rw [h] at h'
  exact Fin.ext (Option.some_injective _ h')

lemma survivor_last (P : Labels n m q) (t : Fin (n / q)) (e : Fin m) (hZ : e ∉ Z P)
    (hG : e ∈ G P t) (hlast : t.val + 1 = n / q) :
    denominator n q t ≤ position (G P t) e := by
  unfold Z at hZ
  simp only [mem_filter, mem_univ, true_and, not_not] at hZ
  obtain ⟨t', hG', h⟩ := hZ
  have := G_unique P hG hG'
  subst this
  rcases h with h | h
  · exact absurd hlast h
  · exact h

lemma shiftedSlot_source {R : Finset (Fin n)} (p : Packings n m q R) (i : Ordinary R)
    (t : Fin (n / q)) (e : Fin m) (s : ℕ) (hpos : 0 < shiftedSlot p i t e s) :
    ∃ g, g ∉ Z (p i) ∧ g ∈ G (p i) t ∧ g.val ≤ e.val ∧ s = slotIdx (p i) t g ∧
      position (univ \ Z (p i)) g = e.val - K p ∧ K p ≤ e.val := by
  unfold shiftedSlot at hpos
  split_ifs at hpos with he
  · exact absurd hpos (lt_irrefl 0)
  have : ∃ g, 0 < (if g ∉ Z (p i) ∧ position (univ \ Z (p i)) g = e.val - K p
      then rawSlot (p i) t g s else 0) := by
    by_contra hne
    push_neg at hne
    exact absurd (sum_nonpos (fun g _ => hne g)) (not_le.mpr hpos)
  obtain ⟨g, hg⟩ := this
  split_ifs at hg with hc
  · rw [rawSlot_eq] at hg
    split_ifs at hg with hs
    · unfold rawBase at hg
      split_ifs at hg with hb
      · refine ⟨g, hc.1, hb.2, ?_, hs, hc.2, by omega⟩
        have := val_le_K_add_position (Z (p i)) (K p) (card_Z_le_K p i) g
        omega
      · exact absurd hg (lt_irrefl 0)
    · exact absurd hg (lt_irrefl 0)
  · exact absurd hg (lt_irrefl 0)

/-! ### Blocks and the bound `cost (G t) ≤ denominator` -/

def blk (hdiv : q ∣ m) (e : Fin m) : Fin (m / q) :=
  ⟨e.val / q, Nat.div_lt_div_of_lt_of_dvd hdiv e.isLt⟩

lemma mem_G_iff (P : Labels n m q) (hdiv : q ∣ m) (t : Fin (n / q)) (e : Fin m) :
    e ∈ G P t ↔ (P (blk hdiv e)).map (fun v => min v.val (n / q - 1)) = some t.val := by
  unfold G mergedLabel blk
  simp only [mem_filter, mem_univ, true_and]
  rw [dif_pos (Nat.div_lt_div_of_lt_of_dvd hdiv e.isLt)]

lemma le_rep (c : Cost n m) (i : Fin n) (hanti : Antitone (c i)) (hdiv : q ∣ m) (e : Fin m) :
    c i e ≤ representativeCost c i q (blk hdiv e) := by
  unfold representativeCost blk
  have h : e.val / q * q < m := lt_of_le_of_lt (Nat.div_mul_le_self _ _) e.isLt
  split_ifs with h'
  · apply hanti
    exact Fin.le_iff_val_le_val.mpr (Nat.div_mul_le_self _ _)
  · exact absurd h h'

lemma rep_nonneg (c : Cost n m) (i : Fin n) (hpos : ∀ e, 0 < c i e) (r : Fin (m / q)) :
    0 ≤ representativeCost c i q r := by
  unfold representativeCost
  split_ifs
  · exact (hpos _).le
  · exact le_rfl

lemma bins_sum_le (hq : 0 < q) (hqn : q ≤ n) (t : Fin (n / q)) :
    ∑ v : Fin (binCount n q), (if min v.val (n / q - 1) = t.val then binCapacity n q v else 0)
      ≤ (denominator n q t : ℝ) / q := by
  have hL : 0 < n / q := Nat.div_pos hqn hq
  have hbc : binCount n q ≤ n / q + 1 := by unfold binCount; split_ifs <;> omega
  have hcap0 : ∀ v, 0 ≤ binCapacity n q v := by
    intro v; unfold binCapacity; split_ifs <;> positivity
  have ht := t.isLt
  calc ∑ v : Fin (binCount n q), (if min v.val (n / q - 1) = t.val then binCapacity n q v else 0)
      ≤ ∑ v : Fin (binCount n q), ((if v.val = t.val then binCapacity n q v else 0) +
          (if t.val + 1 = n / q ∧ v.val = n / q then binCapacity n q v else 0)) := by
        apply sum_le_sum
        intro v _
        have hv := v.isLt
        split_ifs <;> first | linarith [hcap0 v] | (exfalso; omega)
    _ = (∑ v : Fin (binCount n q), (if v.val = t.val then binCapacity n q v else 0)) +
          ∑ v : Fin (binCount n q),
            (if t.val + 1 = n / q ∧ v.val = n / q then binCapacity n q v else 0) :=
        sum_add_distrib
    _ ≤ 1 + (if t.val + 1 = n / q then ((n % q : ℕ) : ℝ) / q else 0) := by
        apply add_le_add
        · apply sum_ite_le_of_unique (fun v : Fin (binCount n q) => v.val = t.val)
          · exact zero_le_one
          · intro x y hx hy; exact Fin.ext (hx.trans hy.symm)
          · intro v hv
            unfold binCapacity
            rw [if_pos (by omega)]
        · by_cases hlast : t.val + 1 = n / q
          · rw [if_pos hlast]
            apply sum_ite_le_of_unique
              (fun v : Fin (binCount n q) => t.val + 1 = n / q ∧ v.val = n / q)
            · positivity
            · intro x y hx hy; exact Fin.ext (hx.2.trans hy.2.symm)
            · intro v hv
              unfold binCapacity
              rw [if_neg (by omega)]
          · rw [if_neg hlast]
            apply le_of_eq
            apply sum_eq_zero
            intro v _
            rw [if_neg]
            exact fun h => hlast h.1
    _ = (denominator n q t : ℝ) / q := by
        have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
        unfold denominator
        split_ifs
        · push_cast
          rw [add_div, div_self hq']
        · push_cast
          rw [add_zero, add_zero, div_self hq']

lemma cost_G_le (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m) (c : Cost n m) (i : Fin n)
    (hpos : ∀ e, 0 < c i e) (hanti : Antitone (c i)) (P : Labels n m q)
    (hP : ValidPacking c i P) (t : Fin (n / q)) :
    ∑ e ∈ G P t, c i e ≤ (denominator n q t : ℝ) := by
  classical
  have s1 : ∑ e ∈ G P t, c i e ≤ ∑ e : Fin m,
      (if (P (blk hdiv e)).map (fun v => min v.val (n / q - 1)) = some t.val then
        representativeCost c i q (blk hdiv e) else 0) := by
    rw [← sum_filter]
    have : univ.filter (fun e =>
        (P (blk hdiv e)).map (fun v => min v.val (n / q - 1)) = some t.val) = G P t := by
      ext e
      simp [mem_G_iff P hdiv]
    rw [this]
    exact sum_le_sum (fun e _ => le_rep c i hanti hdiv e)
  have s2 : ∑ e : Fin m,
      (if (P (blk hdiv e)).map (fun v => min v.val (n / q - 1)) = some t.val then
        representativeCost c i q (blk hdiv e) else 0)
      ≤ ∑ b : Fin (m / q), (q : ℝ) *
        (if (P b).map (fun v => min v.val (n / q - 1)) = some t.val then
          representativeCost c i q b else 0) := by
    rw [← sum_fiberwise univ (blk hdiv)]
    apply sum_le_sum
    intro b _
    rw [sum_congr rfl (g := fun _ => if (P b).map (fun v => min v.val (n / q - 1)) = some t.val
        then representativeCost c i q b else 0)
      (by intro e he; simp only [mem_filter] at he; rw [he.2])]
    rw [sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by split_ifs; exact rep_nonneg c i hpos b; exact le_rfl)
    have hset : univ.filter (fun e => blk hdiv e = b) =
        univ.filter (fun e : Fin m => e.val / q = b.val) := by
      ext e
      simp [blk, Fin.ext_iff]
    have : (univ.filter (fun e => blk hdiv e = b)).card ≤ q := by
      rw [hset]
      exact card_filter_div_le univ (fun e : Fin m => e.val) (fun x _ y _ h => Fin.ext h) q b.val hq
    exact_mod_cast this
  have s3 : ∑ b : Fin (m / q),
      (if (P b).map (fun v => min v.val (n / q - 1)) = some t.val then
        representativeCost c i q b else 0)
      ≤ ∑ v : Fin (binCount n q),
        (if min v.val (n / q - 1) = t.val then binCapacity n q v else 0) := by
    have e1 : ∀ b, (if (P b).map (fun v => min v.val (n / q - 1)) = some t.val then
        representativeCost c i q b else 0) =
        ∑ v : Fin (binCount n q), if P b = some v then
          (if min v.val (n / q - 1) = t.val then representativeCost c i q b else 0) else 0 := by
      intro b
      cases hPb : P b with
      | none => simp
      | some v0 => simp [eq_comm]
    rw [sum_congr rfl (fun b _ => e1 b), sum_comm]
    apply sum_le_sum
    intro v _
    split_ifs with hv
    · exact hP.2 v
    · simp [hv]
  calc ∑ e ∈ G P t, c i e ≤ _ := s1
    _ ≤ _ := s2
    _ = (q : ℝ) * ∑ b : Fin (m / q),
        (if (P b).map (fun v => min v.val (n / q - 1)) = some t.val then
          representativeCost c i q b else 0) := by rw [mul_sum]
    _ ≤ (q : ℝ) * ((denominator n q t : ℝ) / q) :=
        mul_le_mul_of_nonneg_left (s3.trans (bins_sum_le hq hqn t)) (by positivity)
    _ = denominator n q t := by
        have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
        field_simp

end basic

/-! ## Part C: prepared bundles and their shifted slots -/

theorem prop_le_one {n m : ℕ} (hn : 0 < n) (c : Cost n m) (hc : Normalized c) (i : Fin n) :
    propShare c i ≤ 1 := by
  have hmu := hc.2.2 i
  unfold mu costShare at hmu
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have key : LittleCharity.MMS.mms (fun S => -∑ e ∈ S, c i e) n univ ≤ -(cost c i univ / n) := by
    unfold LittleCharity.MMS.mms
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    apply ciSup_le
    intro f
    obtain ⟨j, -, hj⟩ := exists_le_of_sum_le (s := univ)
      (f := fun _ : Fin n => cost c i univ / n)
      (g := fun j => ∑ e ∈ univ.filter (fun g => f g = j), c i e) univ_nonempty (by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [sum_fiberwise]
        have : (n : ℝ) * (cost c i univ / n) = cost c i univ := by field_simp
        rw [this]
        rfl)
    have hj' : cost c i univ / n ≤ ∑ e ∈ univ.filter (fun g => f g = j), c i e := hj
    calc _ ≤ -∑ e ∈ univ.filter (fun g => f g = j), c i e := ciInf_le (Set.finite_range _).bddBelow j
      _ ≤ _ := by linarith
  unfold propShare
  linarith

theorem fc_shiftedBase_le_one {n m q : ℕ} (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (p : Packings n m q R)
    (hp : ∀ i, ValidPacking c i.val (p i)) (i : Ordinary R) (t : Fin (n / q)) :
    fractionalCost c i.val (shiftedBase p i t) ≤ 1 := by
  have hcpos := hc.1 i.val
  have hanti : Antitone (c i.val) := (hc.2.1 i.val).antitone
  have hd : (0 : ℝ) < denominator n q t := by
    unfold denominator; exact_mod_cast (by omega : 0 < q + if t.val + 1 = n / q then n % q else 0)
  unfold fractionalCost shiftedBase
  refine (shift_sum_le (Z (p i)) (K p) (card_Z_le_K p i) (rawBase (p i) t) (c i.val)
    (rawBase_nonneg _ _) (fun g => (hcpos g).le)
    (fun e g h => hanti (Fin.le_iff_val_le_val.mpr h))).trans ?_
  calc ∑ g, (if g ∉ Z (p i) then c i.val g * rawBase (p i) t g else 0)
      ≤ ∑ g, (if g ∈ G (p i) t then c i.val g / denominator n q t else 0) := by
        apply sum_le_sum
        intro g _
        by_cases hZ : g ∈ Z (p i)
        · rw [if_neg (not_not.mpr hZ)]
          split_ifs
          · exact div_nonneg (hcpos g).le hd.le
          · exact le_rfl
        · rw [if_pos hZ]
          unfold rawBase
          by_cases hG : g ∈ G (p i) t
          · rw [if_pos ⟨hZ, hG⟩, if_pos hG, mul_one_div]
          · rw [if_neg (fun h => hG h.2), if_neg hG, mul_zero]
    _ = (∑ g ∈ G (p i) t, c i.val g) / denominator n q t := by
        rw [sum_ite_mem, univ_inter, sum_div]
    _ ≤ 1 := by
        rw [div_le_one hd]
        exact cost_G_le hq hqn hdiv c i.val hcpos hanti (p i) (hp i) t

theorem shiftedSlot_nonneg {n m q : ℕ} {R : Finset (Fin n)} (p : Packings n m q R)
    (i : Ordinary R) (t : Fin (n / q)) (e : Fin m) (s : ℕ) : 0 ≤ shiftedSlot p i t e s := by
  unfold shiftedSlot
  split_ifs
  · exact le_rfl
  · apply sum_nonneg
    intro g _
    split_ifs
    · exact rawSlot_nonneg _ _ _ _
    · exact le_rfl

theorem shiftedSlot_sum_slots {n m q : ℕ} (hq : 0 < q) {R : Finset (Fin n)}
    (p : Packings n m q R) (i : Ordinary R) (t : Fin (n / q)) (e : Fin m) :
    ∑ s : Fin (m + 1), shiftedSlot p i t e s.val = shiftedBase p i t e := by
  unfold shiftedSlot shiftedBase
  by_cases he : e.val < K p
  · simp [he]
  · simp only [if_neg he]
    rw [sum_comm]
    apply sum_congr rfl
    intro g _
    split_ifs
    · exact rawSlot_sum _ _ _
    · simp

theorem shiftedSlot_top {n m q : ℕ} (hq : 0 < q) {R : Finset (Fin n)}
    (p : Packings n m q R) (i : Ordinary R) (t : Fin (n / q)) (e : Fin m) :
    shiftedSlot p i t e m = 0 := by
  unfold shiftedSlot
  split_ifs
  · rfl
  · apply sum_eq_zero
    intro g _
    split_ifs
    · exact rawSlot_top _ _ _
    · rfl

theorem shiftedSlot_load_le {n m q : ℕ} (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    {R : Finset (Fin n)} (p : Packings n m q R) (i : Ordinary R) (t : Fin (n / q)) (s : ℕ) :
    ∑ e, shiftedSlot p i t e s ≤ 1 := by
  have h1 : ∑ e, shiftedSlot p i t e s ≤
      ∑ g, if g ∉ Z (p i) then 1 * rawSlot (p i) t g s else 0 := by
    have := shift_sum_le (Z (p i)) (K p) (card_Z_le_K p i) (fun g => rawSlot (p i) t g s)
      (fun _ => 1) (fun g => rawSlot_nonneg _ _ _ _) (fun _ => zero_le_one) (fun _ _ _ => le_rfl)
    simp only [one_mul] at this ⊢
    exact this
  refine h1.trans ?_
  by_cases hlast : t.val + 1 = n / q
  · -- last merged bin: windows of `denominator` consecutive positions
    have hd0 : 0 < denominator n q t := by unfold denominator; omega
    let F := (G (p i) t).filter (fun g => position (G (p i) t) g / denominator n q t = s)
    calc ∑ g, (if g ∉ Z (p i) then 1 * rawSlot (p i) t g s else 0)
        ≤ ∑ g, (if g ∈ F then 1 / (denominator n q t : ℝ) else 0) := by
          apply sum_le_sum
          intro g _
          rw [rawSlot_eq]
          have hb := rawBase_le (p i) t g
          have hb0 := rawBase_nonneg (p i) t g
          by_cases hZ : g ∉ Z (p i)
          · rw [if_pos hZ, one_mul]
            by_cases hs : s = slotIdx (p i) t g
            · rw [if_pos hs]
              by_cases hG : g ∈ G (p i) t
              · have hgF : g ∈ F := by
                  simp only [F, mem_filter]
                  refine ⟨hG, ?_⟩
                  rw [hs]; unfold slotIdx; rw [if_pos hlast]
                rw [if_pos hgF]
                rw [if_pos hG] at hb
                exact hb
              · rw [if_neg hG] at hb
                exact hb.trans (by split_ifs <;> positivity)
            · rw [if_neg hs]; split_ifs <;> positivity
          · rw [if_neg hZ]; split_ifs <;> positivity
      _ ≤ 1 := sum_ite_mem_le_one F _ hd0
          (card_filter_div_le _ _ (position_injOn _) _ s hd0)
  · have hden : denominator n q t = q := by unfold denominator; rw [if_neg hlast, add_zero]
    let F := univ.filter (fun g : Fin m => g.val / q = s)
    calc ∑ g, (if g ∉ Z (p i) then 1 * rawSlot (p i) t g s else 0)
        ≤ ∑ g, (if g ∈ F then 1 / (q : ℝ) else 0) := by
          apply sum_le_sum
          intro g _
          rw [rawSlot_eq]
          have hb := rawBase_le (p i) t g
          have hb0 := rawBase_nonneg (p i) t g
          rw [hden] at hb
          by_cases hZ : g ∉ Z (p i)
          · rw [if_pos hZ, one_mul]
            by_cases hs : s = slotIdx (p i) t g
            · rw [if_pos hs]
              have hgF : g ∈ F := by
                simp only [F, mem_filter, mem_univ, true_and]
                rw [hs]; unfold slotIdx; rw [if_neg hlast]
              rw [if_pos hgF]
              exact hb.trans (by split_ifs <;> first | exact le_rfl | positivity)
            · rw [if_neg hs]; split_ifs <;> positivity
          · rw [if_neg hZ]; split_ifs <;> positivity
      _ ≤ 1 := sum_ite_mem_le_one F _ hq
          (card_filter_div_le _ _ (fun x _ y _ h => Fin.ext h) _ s hq)

theorem custom_cost {n m q : ℕ} (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (p : Packings n m q R)
    (hp : ∀ i, ValidPacking c i.val (p i)) (i : Ordinary R) (t : Fin (n / q))
    (T : Finset (Fin m)) (σ : Fin m → ℕ) (hσ : Set.InjOn σ T)
    (hpos : ∀ e ∈ T, 0 < shiftedSlot p i t e (σ e)) :
    ∑ e ∈ T, c i.val e ≤ 1 := by
  have hcpos := hc.1 i.val
  have hanti : Antitone (c i.val) := (hc.2.1 i.val).antitone
  choose! gs hgs using fun e (he : e ∈ T) => shiftedSlot_source p i t e (σ e) (hpos e he)
  by_cases hlast : t.val + 1 = n / q
  · -- last merged bin
    have hD0 : 0 < denominator n q t := by unfold denominator; omega
    have hdR : (0 : ℝ) < denominator n q t := by exact_mod_cast hD0
    have hσ1 : ∀ e ∈ T, σ e = position (G (p i) t) (gs e) / denominator n q t ∧
        1 ≤ σ e := by
      intro e he
      obtain ⟨hZ, hG, -, hs, -, -⟩ := hgs e he
      have hs' : σ e = position (G (p i) t) (gs e) / denominator n q t := by
        rw [hs]; unfold slotIdx; rw [if_pos hlast]
      refine ⟨hs', ?_⟩
      rw [hs']
      exact (Nat.one_le_div_iff hD0).mpr (survivor_last (p i) t (gs e) hZ hG hlast)
    have key : ∀ e ∈ T, c i.val e ≤ (∑ h ∈ (G (p i) t).filter (fun h =>
        position (G (p i) t) h / denominator n q t = σ e - 1), c i.val h) /
          denominator n q t := by
      intro e he
      obtain ⟨hZ, hG, hle, -, -, -⟩ := hgs e he
      obtain ⟨hs', hs1⟩ := hσ1 e he
      have hk := position_lt_card (G (p i) t) hG
      have hkd := Nat.div_mul_le_self (position (G (p i) t) (gs e)) (denominator n q t)
      obtain ⟨a, ha⟩ : ∃ a, σ e = a + 1 := ⟨σ e - 1, by omega⟩
      have hsa : σ e - 1 = a := by omega
      rw [hsa]
      rw [← hs', ha] at hkd
      have hmul : (a + 1) * denominator n q t = a * denominator n q t + denominator n q t := by
        ring
      have hcard : denominator n q t ≤ ((G (p i) t).filter (fun h =>
          position (G (p i) t) h / denominator n q t = a)).card := by
        have hsub : Ico (a * denominator n q t) (a * denominator n q t + denominator n q t) ⊆
            ((G (p i) t).filter (fun h =>
              position (G (p i) t) h / denominator n q t = a)).image (position (G (p i) t)) := by
          intro j hj
          rw [mem_Ico] at hj
          have hjlt : j < (G (p i) t).card := by omega
          obtain ⟨h, hh, hpj⟩ := position_surj (G (p i) t) hjlt
          rw [mem_image]
          refine ⟨h, ?_, hpj⟩
          rw [mem_filter]
          refine ⟨hh, ?_⟩
          rw [hpj]
          exact Nat.div_eq_of_lt_le hj.1 (by omega)
        have := card_le_card hsub
        rw [Nat.card_Ico] at this
        exact le_trans (by omega) (this.trans card_image_le)
      have hwin : ∀ h ∈ (G (p i) t).filter (fun h =>
          position (G (p i) t) h / denominator n q t = a), c i.val (gs e) ≤ c i.val h := by
        intro h hh
        rw [mem_filter] at hh
        apply hanti
        by_contra hlt
        push_neg at hlt
        have h1 := position_mono (G (p i) t) hlt.le
        have h2 := Nat.div_le_div_right (c := denominator n q t) h1
        rw [← hs', ha, hh.2] at h2
        omega
      rw [le_div_iff₀ hdR]
      calc c i.val e * denominator n q t ≤ c i.val (gs e) * denominator n q t :=
            mul_le_mul_of_nonneg_right (hanti (Fin.le_iff_val_le_val.mpr hle)) hdR.le
        _ ≤ c i.val (gs e) * ((G (p i) t).filter (fun h =>
              position (G (p i) t) h / denominator n q t = a)).card :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (hcpos _).le
        _ = ∑ h ∈ (G (p i) t).filter (fun h =>
              position (G (p i) t) h / denominator n q t = a), c i.val (gs e) := by
            rw [sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ _ := sum_le_sum hwin
    have hinj : ∀ x ∈ T, ∀ y ∈ T, σ x - 1 = σ y - 1 → x = y := by
      intro x hx y hy h
      have := (hσ1 x hx).2
      have := (hσ1 y hy).2
      exact hσ hx hy (by omega)
    calc ∑ e ∈ T, c i.val e ≤ ∑ e ∈ T, (∑ h ∈ (G (p i) t).filter (fun h =>
          position (G (p i) t) h / denominator n q t = σ e - 1), c i.val h) /
            denominator n q t := sum_le_sum key
      _ = (∑ w ∈ T.image (fun e => σ e - 1), ∑ h ∈ (G (p i) t).filter (fun h =>
          position (G (p i) t) h / denominator n q t = w), c i.val h) /
            denominator n q t := by
          rw [sum_image hinj, sum_div]
      _ ≤ (∑ h ∈ G (p i) t, c i.val h) / denominator n q t := by
          apply div_le_div_of_nonneg_right _ hdR.le
          apply sum_fiberwise_le_sum_of_sum_fiber_nonneg
          intro y _
          exact sum_nonneg (fun h _ => (hcpos h).le)
      _ ≤ 1 := by
          rw [div_le_one hdR]
          exact cost_G_le hq hqn hdiv c i.val hcpos hanti (p i) (hp i) t
  · -- a unit bin that is not last: slots are block indices
    have hbin : t.val < binCount n q := lt_of_lt_of_le t.isLt (by unfold binCount; omega)
    let v : Fin (binCount n q) := ⟨t.val, hbin⟩
    let Rf : ℕ → ℝ := fun k => if h : k < m / q then
      (if p i ⟨k, h⟩ = some v then representativeCost c i.val q ⟨k, h⟩ else 0) else 0
    have hR0 : ∀ k, 0 ≤ Rf k := by
      intro k
      simp only [Rf]
      split_ifs
      · exact rep_nonneg c i.val hcpos _
      · exact le_rfl
      · exact le_rfl
    have key : ∀ e ∈ T, c i.val e ≤ Rf (σ e) ∧ σ e < m / q := by
      intro e he
      obtain ⟨hZ, hG, hle, hs, -, -⟩ := hgs e he
      have hs' : σ e = (gs e).val / q := by rw [hs]; unfold slotIdx; rw [if_neg hlast]
      have hlt : (gs e).val / q < m / q := Nat.div_lt_div_of_lt_of_dvd hdiv (gs e).isLt
      refine ⟨?_, hs' ▸ hlt⟩
      rw [mem_G_iff (p i) hdiv] at hG
      have hb : p i (blk hdiv (gs e)) = some v := by
        cases hpb : p i (blk hdiv (gs e)) with
        | none => rw [hpb] at hG; simp at hG
        | some v' =>
          rw [hpb] at hG
          simp only [Option.map_some, Option.some.injEq] at hG
          have := t.isLt
          exact congrArg some (Fin.ext (by show v'.val = t.val; omega))
      calc c i.val e ≤ c i.val (gs e) := hanti (Fin.le_iff_val_le_val.mpr hle)
        _ ≤ representativeCost c i.val q (blk hdiv (gs e)) := le_rep c i.val hanti hdiv _
        _ = Rf (σ e) := by
          simp only [Rf, hs', dif_pos hlt]
          exact (if_pos hb).symm
    have hcap : (∑ b : Fin (m / q),
        if p i b = some v then representativeCost c i.val q b else 0) ≤ 1 := by
      have := (hp i).2 v
      unfold binCapacity at this
      rw [if_pos (show v.val < n / q from t.isLt)] at this
      exact this
    calc ∑ e ∈ T, c i.val e ≤ ∑ e ∈ T, Rf (σ e) := sum_le_sum (fun e he => (key e he).1)
      _ = ∑ k ∈ T.image σ, Rf k := (sum_image (fun x hx y hy h => hσ hx hy h)).symm
      _ ≤ ∑ k ∈ range (m / q), Rf k := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro k hk
            rw [mem_image] at hk
            obtain ⟨e, he, rfl⟩ := hk
            exact mem_range.mpr (key e he).2
          · intro k _ _
            exact hR0 k
      _ = ∑ b : Fin (m / q), Rf b.val := (Fin.sum_univ_eq_sum_range Rf (m / q)).symm
      _ = ∑ b : Fin (m / q), if p i b = some v then representativeCost c i.val q b else 0 := by
          apply sum_congr rfl
          intro b _
          simp only [Rf, dif_pos b.isLt]
      _ ≤ 1 := hcap

end SublinearChoresMMS.Disposal.Dev.L33.PartC
end
end

section
noncomputable section

namespace SublinearChoresMMS.Disposal.Dev.L33.PartD

open SublinearChoresMMS.Disposal
open Finset

section

variable {n m q : ℕ}

/-! ### Elementary facts -/

lemma K_le_m {R : Finset (Fin n)} (p : Packings n m q R) : K p ≤ m := by
  unfold K
  apply Finset.sup_le
  intro i _
  simpa using card_le_univ (Z (p i))

lemma card_H {R : Finset (Fin n)} (p : Packings n m q R) : (H p).card = K p := by
  have h : (H p).map Fin.valEmbedding = range (K p) := by
    ext k
    simp only [H, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact he
    · intro hk
      exact ⟨⟨k, lt_of_lt_of_le hk (K_le_m p)⟩, hk, rfl⟩
  rw [← card_map Fin.valEmbedding, h, card_range]

lemma mem_H {R : Finset (Fin n)} (p : Packings n m q R) (e : Fin m) :
    e ∈ H p ↔ e.val < K p := by
  simp [H]

lemma cost_nonneg (c : Cost n m) (hc : Normalized c) (i : Fin n) (S : Finset (Fin m)) :
    0 ≤ cost c i S :=
  sum_nonneg fun e _ => (hc.1 i e).le

lemma cost_mono (c : Cost n m) (hc : Normalized c) (i : Fin n) {S T : Finset (Fin m)}
    (h : S ⊆ T) : cost c i S ≤ cost c i T :=
  sum_le_sum_of_subset_of_nonneg h fun e _ _ => (hc.1 i e).le

lemma kappa_nonneg (c : Cost n m) (i : Fin n) : 0 ≤ kappa c i := le_max_left _ _

lemma le_kappa (c : Cost n m) (i : Fin n) (e : Fin m) : c i e ≤ kappa c i :=
  le_max_of_le_right (le_ciSup (Set.finite_range _).bddAbove e)

lemma shiftedBase_H {R : Finset (Fin n)} (p : Packings n m q R) (i : Ordinary R)
    (t : Fin (n / q)) {e : Fin m} (he : e ∈ H p) : shiftedBase p i t e = 0 := by
  unfold shiftedBase
  rw [if_pos ((mem_H p e).1 he)]

lemma shiftedBase_nonneg (hq : 0 < q) {R : Finset (Fin n)} (p : Packings n m q R)
    (i : Ordinary R) (t : Fin (n / q)) (e : Fin m) : 0 ≤ shiftedBase p i t e := by
  rw [← PartC.shiftedSlot_sum_slots hq p i t e]
  exact sum_nonneg fun s _ => PartC.shiftedSlot_nonneg p i t e s

lemma denom_ge (hn : 0 < n) (c : Cost n m) (hc : Normalized c) {R : Finset (Fin n)}
    (p : Packings n m q R) (i : Fin n) :
    cost c i (H p) ≤ (n : ℝ) * (1 - propShare c i) + cost c i (H p) := by
  have := PartC.prop_le_one hn c hc i
  have : (0 : ℝ) ≤ n * (1 - propShare c i) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  linarith

lemma tau_nonneg (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (p : Packings n m q R)
    (hp : ∀ i, ValidPacking c i.val (p i)) (i : Ordinary R) (t : Fin (n / q)) :
    0 ≤ tau c p i t := by
  unfold tau
  apply div_nonneg
  · linarith [PartC.fc_shiftedBase_le_one hq hqn hdiv c hc R p hp i t]
  · exact (cost_nonneg c hc i.val _).trans (denom_ge hn c hc p i.val)

lemma tau_mul_cost (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (p : Packings n m q R)
    (hp : ∀ i, ValidPacking c i.val (p i)) (i : Ordinary R) (t : Fin (n / q)) :
    tau c p i t * cost c i.val (H p) ≤ 1 - fractionalCost c i.val (shiftedBase p i t) := by
  have hN : 0 ≤ 1 - fractionalCost c i.val (shiftedBase p i t) := by
    linarith [PartC.fc_shiftedBase_le_one hq hqn hdiv c hc R p hp i t]
  have hCD := denom_ge hn c hc p i.val
  have hC := cost_nonneg c hc i.val (H p)
  unfold tau
  rcases eq_or_lt_of_le (hC.trans hCD) with h | h
  · rw [← h, div_zero, zero_mul]
    exact hN
  · rw [div_mul_eq_mul_div, div_le_iff₀ h]
    exact mul_le_mul_of_nonneg_left hCD hN

lemma fc_completed (c : Cost n m) {R : Finset (Fin n)} (p : Packings n m q R)
    (i : Ordinary R) (t : Fin (n / q)) :
    fractionalCost c i.val (completed c p i t) =
      tau c p i t * cost c i.val (H p) + fractionalCost c i.val (shiftedBase p i t) := by
  have hcost : cost c i.val (H p) = ∑ e, if e ∈ H p then c i.val e else 0 := by
    show ∑ e ∈ H p, c i.val e = _
    rw [sum_ite_mem, univ_inter]
  rw [hcost, mul_sum]
  unfold fractionalCost
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  unfold completed
  by_cases he : e ∈ H p
  · rw [if_pos he, if_pos he, shiftedBase_H p i t he]
    ring
  · rw [if_neg he, if_neg he]
    ring

lemma completed_nonneg (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (p : Packings n m q R)
    (hp : ∀ i, ValidPacking c i.val (p i)) (i : Ordinary R) (t : Fin (n / q)) (e : Fin m) :
    0 ≤ completed c p i t e := by
  unfold completed
  split_ifs
  · exact tau_nonneg hn hq hqn hdiv c hc R p hp i t
  · exact shiftedBase_nonneg hq p i t e

lemma fc_completed_le_one (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (p : Packings n m q R)
    (hp : ∀ i, ValidPacking c i.val (p i)) (i : Ordinary R) (t : Fin (n / q)) :
    fractionalCost c i.val (completed c p i t) ≤ 1 := by
  rw [fc_completed]
  linarith [tau_mul_cost hn hq hqn hdiv c hc R p hp i t]

/-! ### Realized fractions -/

lemma realized_ord (c : Cost n m) {R : Finset (Fin n)} (p : Packings n m q R)
    (v : Coefficients n q R) (i : Ordinary R) (e : Fin m) :
    realized c p v i.val e = ∑ t, v i t * completed c p i t e := by
  unfold realized
  rw [dif_neg i.2]

lemma pure_realized (c : Cost n m) {R : Finset (Fin n)} (p : Packings n m q R)
    (v : Coefficients n q R) (i : Ordinary R) (t : Fin (n / q))
    (ht : ∀ u, v i u = if u = t then 1 else 0) (e : Fin m) :
    realized c p v i.val e = completed c p i t e := by
  rw [realized_ord]
  simp [ht]

lemma choose_pure (c : Cost n m) {R : Finset (Fin n)} (p : Packings n m q R)
    (v : Coefficients n q R) (i : Ordinary R) (hcu : usesCustom c p v i) :
    ∀ u, v i u = if u = Classical.choose hcu then 1 else 0 := by
  obtain ⟨hsel, hpure, -⟩ := Classical.choose_spec hcu
  have hs : (Classical.choose hpure).val = (Classical.choose hcu).val := by
    rw [← hsel]
    unfold selected
    rw [dif_pos hpure]
  have : Classical.choose hpure = Classical.choose hcu := Fin.ext hs
  rw [← this]
  exact Classical.choose_spec hpure

lemma realized_nonneg (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (p : Packings n m q R)
    (hp : ∀ i, ValidPacking c i.val (p i)) (v : Coefficients n q R) (hv : Coordinated c p v)
    (i : Fin n) (e : Fin m) : 0 ≤ realized c p v i e := by
  unfold realized
  split_ifs with hi
  · apply div_nonneg
    · linarith [hv.2.1 e]
    · exact Nat.cast_nonneg _
  · exact sum_nonneg fun t _ =>
      mul_nonneg (hv.1.1 _ t) (completed_nonneg hn hq hqn hdiv c hc R p hp _ t e)

lemma realized_sum (c : Cost n m) (R : Finset (Fin n)) (hR : 1 ≤ R.card)
    (p : Packings n m q R) (v : Coefficients n q R) (e : Fin m) :
    ∑ i, realized c p v i e = 1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ R)]
  have h1 : ∑ i : {i // i ∈ R}, realized c p v i.val e = 1 - ordinaryFraction c p v e := by
    have : ∀ i : {i // i ∈ R}, realized c p v i.val e =
        (1 - ordinaryFraction c p v e) / R.card := fun i => by
      unfold realized
      rw [dif_pos i.2]
    simp only [this, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
    have : (R.card : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ R.card := by exact_mod_cast hR
      linarith
    field_simp
  have h2 : ∑ i : {i // i ∉ R}, realized c p v i.val e = ordinaryFraction c p v e := by
    unfold ordinaryFraction
    exact sum_congr rfl fun i _ => realized_ord c p v i e
  have h3 := congrArg₂ (· + ·) h1 h2
  simp only [sub_add_cancel] at h3
  convert h3 using 3
  ext x
  simp

/-! ### Slot fractions -/

lemma sf_general (c : Cost n m) {R : Finset (Fin n)} (p : Packings n m q R)
    (v : Coefficients n q R) (s : Slots n m) (i : Fin n) (hs : s.1 = i)
    (hg : GeneralAgent c p v i) (e : Fin m) :
    slotFraction c p v s e = generalSlot (realized c p v i) e s.2.val := by
  subst hs
  unfold slotFraction
  by_cases hi : s.1 ∈ R
  · rw [dif_neg (not_not.mpr hi)]
  · rw [dif_pos hi, dif_neg (hg hi)]

lemma sf_cust_H_top (c : Cost n m) {R : Finset (Fin n)} (p : Packings n m q R)
    (v : Coefficients n q R) (i : Ordinary R) (j : Fin (m + 1)) (hcu : usesCustom c p v i)
    {e : Fin m} (he : e ∈ H p) (hj : j.val = m) :
    slotFraction c p v (i.val, j) e = tau c p i (Classical.choose hcu) := by
  unfold slotFraction
  rw [dif_pos i.2, dif_pos hcu]
  simp only [if_pos he, if_pos hj]

lemma sf_cust_H_ne (c : Cost n m) {R : Finset (Fin n)} (p : Packings n m q R)
    (v : Coefficients n q R) (i : Ordinary R) (j : Fin (m + 1)) (hcu : usesCustom c p v i)
    {e : Fin m} (he : e ∈ H p) (hj : j.val ≠ m) :
    slotFraction c p v (i.val, j) e = 0 := by
  unfold slotFraction
  rw [dif_pos i.2, dif_pos hcu]
  simp only [if_pos he, if_neg hj]

lemma sf_cust_nH (c : Cost n m) {R : Finset (Fin n)} (p : Packings n m q R)
    (v : Coefficients n q R) (i : Ordinary R) (j : Fin (m + 1)) (hcu : usesCustom c p v i)
    {e : Fin m} (he : e ∉ H p) :
    slotFraction c p v (i.val, j) e = shiftedSlot p i (Classical.choose hcu) e j.val := by
  unfold slotFraction
  rw [dif_pos i.2, dif_pos hcu]
  simp only [if_neg he]

/-- Case split on the kind of agent behind a slot owner. -/
lemma agent_cases (c : Cost n m) {R : Finset (Fin n)} (p : Packings n m q R)
    (v : Coefficients n q R) (i : Fin n) :
    GeneralAgent c p v i ∨ ∃ i' : Ordinary R, i'.val = i ∧ usesCustom c p v i' := by
  by_cases hi : i ∈ R
  · exact Or.inl fun h => absurd hi h
  · by_cases hcu : usesCustom c p v ⟨i, hi⟩
    · exact Or.inr ⟨⟨i, hi⟩, rfl, hcu⟩
    · exact Or.inl fun h => hcu

/-! ### The three hypotheses of the rounding theorem -/

lemma realized_le_one (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (hR : 1 ≤ R.card)
    (p : Packings n m q R) (hp : ∀ i, ValidPacking c i.val (p i))
    (v : Coefficients n q R) (hv : Coordinated c p v) (i : Fin n) (e : Fin m) :
    realized c p v i e ≤ 1 := by
  rw [← realized_sum c R hR p v e]
  exact single_le_sum (fun j _ => realized_nonneg hn hq hqn hdiv c hc R p hp v hv j e)
    (mem_univ i)

lemma sum_realized_le (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (hR : 1 ≤ R.card)
    (p : Packings n m q R) (hp : ∀ i, ValidPacking c i.val (p i))
    (v : Coefficients n q R) (hv : Coordinated c p v) (i : Fin n) :
    ∑ e, realized c p v i e ≤ (m : ℝ) + 1 := by
  calc ∑ e, realized c p v i e ≤ ∑ _e : Fin m, (1 : ℝ) :=
        sum_le_sum fun e _ => realized_le_one hn hq hqn hdiv c hc R hR p hp v hv i e
    _ = m := by simp
    _ ≤ (m : ℝ) + 1 := by linarith

lemma sf_nonneg (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n))
    (p : Packings n m q R) (hp : ∀ i, ValidPacking c i.val (p i))
    (v : Coefficients n q R) (s : Slots n m) (e : Fin m) : 0 ≤ slotFraction c p v s e := by
  obtain ⟨i, j⟩ := s
  rcases agent_cases c p v i with hg | ⟨i', rfl, hcu⟩
  · rw [sf_general c p v (i, j) i rfl hg e]
    exact PartAB.gs_nonneg _ _ _
  · by_cases he : e ∈ H p
    · by_cases hj : j.val = m
      · rw [sf_cust_H_top c p v i' j hcu he hj]
        exact tau_nonneg hn hq hqn hdiv c hc R p hp i' _
      · rw [sf_cust_H_ne c p v i' j hcu he hj]
    · rw [sf_cust_nH c p v i' j hcu he]
      exact PartC.shiftedSlot_nonneg _ _ _ _ _

lemma sf_col (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (hR : 1 ≤ R.card)
    (p : Packings n m q R) (hp : ∀ i, ValidPacking c i.val (p i))
    (v : Coefficients n q R) (hv : Coordinated c p v) (i : Fin n) (e : Fin m) :
    ∑ j : Fin (m + 1), slotFraction c p v (i, j) e = realized c p v i e := by
  rcases agent_cases c p v i with hg | ⟨i', rfl, hcu⟩
  · rw [sum_congr rfl fun j _ => sf_general c p v (i, j) i rfl hg e]
    exact PartAB.gs_sum_slots _ (realized_nonneg hn hq hqn hdiv c hc R p hp v hv i)
      (sum_realized_le hn hq hqn hdiv c hc R hR p hp v hv i) e
  · rw [pure_realized c p v i' _ (choose_pure c p v i' hcu) e]
    unfold completed
    by_cases he : e ∈ H p
    · rw [if_pos he, sum_eq_single (Fin.last m)]
      · exact sf_cust_H_top c p v i' _ hcu he rfl
      · intro j _ hj
        exact sf_cust_H_ne c p v i' j hcu he (fun h => hj (Fin.ext h))
      · intro h
        exact absurd (mem_univ _) h
    · rw [if_neg he, sum_congr rfl fun j _ => sf_cust_nH c p v i' j hcu he]
      exact PartC.shiftedSlot_sum_slots hq p i' _ e

lemma sf_row (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n))
    (p : Packings n m q R) (hp : ∀ i, ValidPacking c i.val (p i))
    (v : Coefficients n q R) (hv : Coordinated c p v) (s : Slots n m) :
    ∑ e, slotFraction c p v s e ≤ 1 := by
  obtain ⟨i, j⟩ := s
  rcases agent_cases c p v i with hg | ⟨i', rfl, hcu⟩
  · rw [sum_congr rfl fun e _ => sf_general c p v (i, j) i rfl hg e]
    exact PartAB.gs_load_le _ (realized_nonneg hn hq hqn hdiv c hc R p hp v hv i) _
  · by_cases hj : j.val = m
    · have key : ∀ e, slotFraction c p v (i'.val, j) e =
          if e ∈ H p then tau c p i' (Classical.choose hcu) else 0 := by
        intro e
        by_cases he : e ∈ H p
        · rw [if_pos he, sf_cust_H_top c p v i' j hcu he hj]
        · rw [if_neg he, sf_cust_nH c p v i' j hcu he, hj, PartC.shiftedSlot_top hq]
      rw [sum_congr rfl fun e _ => key e, sum_ite_mem, univ_inter, sum_const, card_H,
        nsmul_eq_mul]
      exact (Classical.choose_spec hcu).2.2
    · calc ∑ e, slotFraction c p v (i'.val, j) e
          ≤ ∑ e, shiftedSlot p i' (Classical.choose hcu) e j.val := by
            apply sum_le_sum
            intro e _
            by_cases he : e ∈ H p
            · rw [sf_cust_H_ne c p v i' j hcu he hj]
              exact PartC.shiftedSlot_nonneg _ _ _ _ _
            · rw [sf_cust_nH c p v i' j hcu he]
        _ ≤ 1 := PartC.shiftedSlot_load_le hq hqn hdiv p i' _ _

/-! ### Bundles of an integral assignment -/

lemma mem_slotBundle (A : SlotAssignment n m) (i : Fin n) (e : Fin m) :
    e ∈ slotBundle A i ↔ (A e).1 = i := by
  simp [slotBundle, bundle, ChoresEFX.bundle]

lemma mem_withoutFirst (A : SlotAssignment n m) (i : Fin n) (e : Fin m) :
    e ∈ withoutFirst A i ↔ (A e).1 = i ∧ (A e).2.val ≠ 0 := by
  simp [withoutFirst]

lemma withoutFirst_eq (A : SlotAssignment n m) (i : Fin n) :
    withoutFirst A i = (slotBundle A i).filter (fun e => (A e).2.val ≠ 0) := by
  ext e
  rw [mem_filter, mem_withoutFirst, mem_slotBundle]

lemma injOn_bundle {A : SlotAssignment n m} (hA : Function.Injective A) (i : Fin n) :
    Set.InjOn (fun e => (A e).2.val) (slotBundle A i) := by
  intro x hx y hy hxy
  rw [mem_coe, mem_slotBundle] at hx hy
  exact hA (Prod.ext (hx.trans hy.symm) (Fin.ext hxy))

lemma finish (c : Cost n m) (hc : Normalized c) (i : Fin n) (B W : Finset (Fin m))
    (hW : cost c i W ≤ 1) (hex : B.Nonempty → ∃ e0 ∈ B, B.erase e0 ⊆ W) :
    MMS1 c i B ∧ cost c i B ≤ 1 + kappa c i := by
  rcases B.eq_empty_or_nonempty with h | h
  · refine ⟨Or.inl h, ?_⟩
    subst h
    have : cost c i ∅ = 0 := sum_empty
    rw [this]
    linarith [kappa_nonneg c i]
  · obtain ⟨e0, he0, hsub⟩ := hex h
    have h1 : cost c i (B.erase e0) ≤ 1 := (cost_mono c hc i hsub).trans hW
    refine ⟨Or.inr ⟨e0, he0, by rw [hc.2.2 i]; exact h1⟩, ?_⟩
    have : cost c i B = c i e0 + cost c i (B.erase e0) := (add_sum_erase B _ he0).symm
    rw [this]
    linarith [le_kappa c i e0]

lemma general_bounds (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n))
    (p : Packings n m q R) (hp : ∀ i, ValidPacking c i.val (p i))
    (v : Coefficients n q R) (hv : Coordinated c p v) (A : SlotAssignment n m)
    (hA : Function.Injective A) (hpos : ∀ e, 0 < slotFraction c p v (A e) e)
    (i : Fin n) (hg : GeneralAgent c p v i) :
    cost c i (slotBundle A i) ≤ fractionalCost c i (realized c p v i) + kappa c i ∧
    cost c i (withoutFirst A i) ≤ fractionalCost c i (realized c p v i) := by
  have key := PartAB.gs_cost (c i) (fun e => (hc.1 i e).le) (hc.2.1 i).antitone
    (realized c p v i) (realized_nonneg hn hq hqn hdiv c hc R p hp v hv i) (slotBundle A i)
    (fun e => (A e).2.val) (injOn_bundle hA i) (fun e he => by
      have h := hpos e
      rwa [sf_general c p v (A e) i ((mem_slotBundle A i e).1 he) hg e] at h)
  refine ⟨key.1, ?_⟩
  rw [withoutFirst_eq]
  exact key.2

lemma pure_bounds (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n))
    (p : Packings n m q R) (hp : ∀ i, ValidPacking c i.val (p i))
    (v : Coefficients n q R) (hv : Coordinated c p v) (A : SlotAssignment n m)
    (hA : Function.Injective A) (hpos : ∀ e, 0 < slotFraction c p v (A e) e)
    (i : Ordinary R) (hpure : Pure v i) :
    MMS1 c i.val (slotBundle A i.val) ∧
      cost c i.val (slotBundle A i.val) ≤ 1 + kappa c i.val ∧
      cost c i.val (slotBundle A i.val \ H p) ≤ 1 := by
  have hAe : ∀ e ∈ slotBundle A i.val, A e = (i.val, (A e).2) :=
    fun e he => Prod.ext ((mem_slotBundle A _ e).1 he) rfl
  by_cases hcu : usesCustom c p v i
  · have hHtop : ∀ e ∈ slotBundle A i.val, e ∈ H p → (A e).2.val = m := by
      intro e he heH
      by_contra hj
      have h := hpos e
      rw [hAe e he, sf_cust_H_ne c p v i _ hcu heH hj] at h
      exact lt_irrefl _ h
    have hW : cost c i.val (slotBundle A i.val \ H p) ≤ 1 := by
      apply PartC.custom_cost hq hqn hdiv c hc R p hp i (Classical.choose hcu)
        (slotBundle A i.val \ H p) (fun e => (A e).2.val)
        ((injOn_bundle hA i.val).mono (coe_subset.2 sdiff_subset))
      intro e he
      rw [mem_sdiff] at he
      have h := hpos e
      rwa [hAe e he.1, sf_cust_nH c p v i _ hcu he.2] at h
    have hex : (slotBundle A i.val).Nonempty →
        ∃ e0 ∈ slotBundle A i.val, (slotBundle A i.val).erase e0 ⊆ slotBundle A i.val \ H p := by
      intro hne
      by_cases hx : ∃ e0 ∈ slotBundle A i.val, e0 ∈ H p
      · obtain ⟨e0, he0, he0H⟩ := hx
        refine ⟨e0, he0, fun x hx => ?_⟩
        rw [mem_erase] at hx
        rw [mem_sdiff]
        refine ⟨hx.2, fun hxH => hx.1 ?_⟩
        exact injOn_bundle hA i.val (mem_coe.2 hx.2) (mem_coe.2 he0)
          ((hHtop x hx.2 hxH).trans (hHtop e0 he0 he0H).symm)
      · push Not at hx
        obtain ⟨e0, he0⟩ := hne
        refine ⟨e0, he0, fun x hx' => ?_⟩
        have hxB := (mem_erase.1 hx').2
        exact mem_sdiff.2 ⟨hxB, hx x hxB⟩
    obtain ⟨h1, h2⟩ := finish c hc i.val _ _ hW hex
    exact ⟨h1, h2, hW⟩
  · have hg : GeneralAgent c p v i.val := fun _ => hcu
    obtain ⟨-, hwf⟩ := general_bounds hn hq hqn hdiv c hc R p hp v hv A hA hpos i.val hg
    have ht0 := Classical.choose_spec hpure
    have hreal : realized c p v i.val = completed c p i (Classical.choose hpure) :=
      funext (pure_realized c p v i _ ht0)
    have hfc : fractionalCost c i.val (realized c p v i.val) ≤ 1 := by
      rw [hreal]
      exact fc_completed_le_one hn hq hqn hdiv c hc R p hp i _
    have hW : cost c i.val (withoutFirst A i.val) ≤ 1 := hwf.trans hfc
    have hK : 1 < (K p : ℝ) * tau c p i (Classical.choose hpure) := by
      by_contra hle
      push Not at hle
      refine hcu ⟨Classical.choose hpure, ?_, hpure, hle⟩
      unfold selected
      rw [dif_pos hpure]
    have hsum : 1 < ∑ e ∈ univ.filter (fun e : Fin m => e.val < K p), realized c p v i.val e := by
      have hH : univ.filter (fun e : Fin m => e.val < K p) = H p := rfl
      rw [hH, hreal]
      calc (1 : ℝ) < (K p : ℝ) * tau c p i (Classical.choose hpure) := hK
        _ = ∑ e ∈ H p, tau c p i (Classical.choose hpure) := by
          rw [sum_const, card_H, nsmul_eq_mul]
        _ = ∑ e ∈ H p, completed c p i (Classical.choose hpure) e := by
          apply sum_congr rfl
          intro e he
          unfold completed
          rw [if_pos he]
    have hfirst : ∀ e ∈ slotBundle A i.val, (A e).2.val = 0 → e ∈ H p := by
      intro e he h0
      have h := hpos e
      rw [sf_general c p v (A e) i.val ((mem_slotBundle A _ e).1 he) hg e, h0] at h
      exact (mem_H p e).2 (PartAB.gs_first_in_prefix _
        (realized_nonneg hn hq hqn hdiv c hc R p hp v hv i.val) (K p) hsum e h)
    have hsub : slotBundle A i.val \ H p ⊆ withoutFirst A i.val := by
      intro x hx
      rw [mem_sdiff] at hx
      rw [mem_withoutFirst]
      exact ⟨(mem_slotBundle A _ x).1 hx.1, fun h0 => hx.2 (hfirst x hx.1 h0)⟩
    have hex : (slotBundle A i.val).Nonempty →
        ∃ e0 ∈ slotBundle A i.val, (slotBundle A i.val).erase e0 ⊆ withoutFirst A i.val := by
      intro hne
      by_cases hx : ∃ e0 ∈ slotBundle A i.val, (A e0).2.val = 0
      · obtain ⟨e0, he0, h0⟩ := hx
        refine ⟨e0, he0, fun x hx => ?_⟩
        rw [mem_erase] at hx
        rw [mem_withoutFirst]
        refine ⟨(mem_slotBundle A _ x).1 hx.2, fun hx0 => hx.1 ?_⟩
        exact injOn_bundle hA i.val (mem_coe.2 hx.2) (mem_coe.2 he0) (hx0.trans h0.symm)
      · push Not at hx
        obtain ⟨e0, he0⟩ := hne
        refine ⟨e0, he0, fun x hx' => ?_⟩
        have hxB := (mem_erase.1 hx').2
        exact (mem_withoutFirst A _ x).2 ⟨(mem_slotBundle A _ x).1 hxB, hx x hxB⟩
    obtain ⟨h1, h2⟩ := finish c hc i.val _ _ hW hex
    exact ⟨h1, h2, (cost_mono c hc _ hsub).trans hW⟩

end

end SublinearChoresMMS.Disposal.Dev.L33.PartD

namespace SublinearChoresMMS.Disposal

open Finset

theorem chk_lemma_3_3 {n m q : ℕ} (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n)
    (hqm : q ≤ m) (hdiv : q ∣ m) (c : Cost n m) (hc : Normalized c)
    (R : Finset (Fin n)) (hR : 1 ≤ R.card) (hRn : R.card < n)
    (p : Packings n m q R) (hp : ∀ i, ValidPacking c i.val (p i))
    (v : Coefficients n q R) (hv : Coordinated c p v) :
    ∃ P : FiniteLaw (SlotAssignment n m),
      (∀ e s, P.mean (fun A => if A e = s then 1 else 0) = slotFraction c p v s e) ∧
      ∀ a : Fin P.size, 0 < P.weight a →
        Function.Injective (P.atom a) ∧
        (∀ e, 0 < slotFraction c p v (P.atom a e) e) ∧
        (∀ s, slotLoad (slotFraction c p v) s = 1 → ∃ e, P.atom a e = s) ∧
        (∀ i, GeneralAgent c p v i →
          cost c i (slotBundle (P.atom a) i) ≤ fractionalCost c i (realized c p v i) + kappa c i ∧
          cost c i (withoutFirst (P.atom a) i) ≤ fractionalCost c i (realized c p v i)) ∧
        ∀ i : Ordinary R, Pure v i →
          MMS1 c i.val (slotBundle (P.atom a) i.val) ∧
          cost c i.val (slotBundle (P.atom a) i.val) ≤ 1 + kappa c i.val ∧
          cost c i.val (slotBundle (P.atom a) i.val \ H p) ≤ 1 := by
  obtain ⟨P, hmean, hatoms⟩ := Dev.L33.PartAB.round_exists (E := Fin m) (S := Slots n m)
    (slotFraction c p v) (Dev.L33.PartD.sf_nonneg hn hq hqn hdiv c hc R p hp v)
    (fun e => by
      rw [Fintype.sum_prod_type]
      simp only [Dev.L33.PartD.sf_col hn hq hqn hdiv c hc R hR p hp v hv]
      exact Dev.L33.PartD.realized_sum c R hR p v e)
    (Dev.L33.PartD.sf_row hn hq hqn hdiv c hc R p hp v hv)
  refine ⟨P, hmean, fun a ha => ?_⟩
  obtain ⟨hinj, hpos, hfull⟩ := hatoms a ha
  exact ⟨hinj, hpos, hfull,
    fun i hg => Dev.L33.PartD.general_bounds hn hq hqn hdiv c hc R p hp v hv (P.atom a) hinj
      hpos i hg,
    fun i hpure => Dev.L33.PartD.pure_bounds hn hq hqn hdiv c hc R p hp v hv (P.atom a) hinj
      hpos i hpure⟩

end SublinearChoresMMS.Disposal
end
end

theorem solution : type_of% @SublinearChoresMMS.Disposal.chk_lemma_3_3 := @SublinearChoresMMS.Disposal.chk_lemma_3_3
