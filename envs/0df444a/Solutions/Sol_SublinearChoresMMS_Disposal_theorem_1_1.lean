-- Prove2me | solution 1 for SublinearChoresMMS.Disposal.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:53:28.373465+00:00
-- url     : https://prove2.me/submissions/23d526d9-80c4-46ea-9367-9c2e2bc8e742
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Slots
import Theorems.Thm_SublinearChoresMMS_Disposal_lemma_2_2
import Theorems.Thm_SublinearChoresMMS_Disposal_lemma_3_1
import Theorems.Thm_SublinearChoresMMS_Disposal_lemma_3_2
import Theorems.Thm_SublinearChoresMMS_Disposal_lemma_3_3
import Definitions.Def_SublinearChoresMMS_Disposal_Setting
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

lemma card_Z_le_K {R : Finset (Fin n)} (p : Packings n m q R) (i : Ordinary R) :
    (Z (p i)).card ≤ K p := by
  unfold K
  exact le_sup (f := fun i => (Z (p i)).card) (mem_univ i)

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

lemma cost_nonneg (c : Cost n m) (hc : Normalized c) (i : Fin n) (S : Finset (Fin m)) :
    0 ≤ cost c i S :=
  sum_nonneg fun e _ => (hc.1 i e).le

lemma cost_mono (c : Cost n m) (hc : Normalized c) (i : Fin n) {S T : Finset (Fin m)}
    (h : S ⊆ T) : cost c i S ≤ cost c i T :=
  sum_le_sum_of_subset_of_nonneg h fun e _ _ => (hc.1 i e).le

lemma kappa_nonneg (c : Cost n m) (i : Fin n) : 0 ≤ kappa c i := le_max_left _ _

lemma le_kappa (c : Cost n m) (i : Fin n) (e : Fin m) : c i e ≤ kappa c i :=
  le_max_of_le_right (le_ciSup (Set.finite_range _).bddAbove e)

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

lemma completed_nonneg (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (p : Packings n m q R)
    (hp : ∀ i, ValidPacking c i.val (p i)) (i : Ordinary R) (t : Fin (n / q)) (e : Fin m) :
    0 ≤ completed c p i t e := by
  unfold completed
  split_ifs
  · exact tau_nonneg hn hq hqn hdiv c hc R p hp i t
  · exact shiftedBase_nonneg hq p i t e

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

/-! ### Bundles of an integral assignment -/

lemma mem_slotBundle (A : SlotAssignment n m) (i : Fin n) (e : Fin m) :
    e ∈ slotBundle A i ↔ (A e).1 = i := by
  simp [slotBundle, bundle, ChoresEFX.bundle]

lemma mem_withoutFirst (A : SlotAssignment n m) (i : Fin n) (e : Fin m) :
    e ∈ withoutFirst A i ↔ (A e).1 = i ∧ (A e).2.val ≠ 0 := by
  simp [withoutFirst]

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

end

end SublinearChoresMMS.Disposal.Dev.L33.PartD

namespace SublinearChoresMMS.Disposal

open Finset

end SublinearChoresMMS.Disposal
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.T11
open SublinearChoresMMS.Disposal
open Finset
/-- The rate of Theorem 1.1. -/
def rate (n : ℕ) : ℝ := (n : ℝ) ^ (3 / 4 : ℝ) * (Real.log (2 * (n : ℝ))) ^ (1 / 4 : ℝ)

/-- A lottery that is ex-ante PROP, ex-post MMS1, with at most `B` non-MMS agents per atom. -/
def Good {n m : ℕ} (c : Cost n m) (P : FiniteLaw (Allocation n m)) (B : ℝ) : Prop :=
  (∀ i, P.mean (fun X => cost c i (bundle X i)) ≤ propShare c i) ∧
  ∀ a : Fin P.size, 0 < P.weight a →
    (∀ i, MMS1 c i (bundle (P.atom a) i)) ∧ ((nonMMS c (P.atom a)).card : ℝ) ≤ B

end SublinearChoresMMS.Disposal.Dev.T11
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.T11.PartST
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.T11
open Finset
open OAI.CliqueFreeIndependence.Lottery
/-! ### Finite-law helpers -/
lemma expect_sum {α ι : Type*} (L : Law α) (s : Finset ι) (g : ι → α → ℝ) :
    expect L (fun x => ∑ k ∈ s, g k x) = ∑ k ∈ s, expect L (g k) := by
  induction L with
  | nil => simp
  | cons z L ih =>
    obtain ⟨p, a⟩ := z
    simp only [expect_cons, ih, mul_sum, sum_add_distrib]

lemma expect_const_mul {α : Type*} (L : Law α) (r : ℝ) (g : α → ℝ) :
    expect L (fun x => r * g x) = r * expect L g := by
  induction L with
  | nil => simp
  | cons z L ih =>
    obtain ⟨p, a⟩ := z
    simp only [expect_cons, ih]; ring

lemma expect_mono {α : Type*} (L : Law α) (hL : Positive L) (f g : α → ℝ)
    (h : ∀ x, f x ≤ g x) : expect L f ≤ expect L g := by
  induction L with
  | nil => simp
  | cons z L ih =>
    obtain ⟨p, a⟩ := z
    simp only [expect_cons]
    have hp : 0 ≤ p := hL _ List.mem_cons_self
    have := ih (fun w hw => hL w (List.mem_cons_of_mem _ hw))
    exact add_le_add (mul_le_mul_of_nonneg_left (h a) hp) this

lemma expect_map {α β : Type*} (L : Law α) (g : α → β) (f : β → ℝ) :
    expect (L.map (fun z => (z.1, g z.2))) f = expect L (fun x => f (g x)) := by
  unfold OAI.CliqueFreeIndependence.Lottery.expect
  simp [List.map_map, Function.comp_def]

/-- Push a finite law forward along `g`, keeping the weights. -/
def lmap {α β : Type} (P : FiniteLaw α) (g : α → β) : FiniteLaw β where
  toLaw := P.toLaw.map (fun z => (z.1, g z.2))
  isProb := by
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [List.mem_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact P.isProb.1 w hw
    · unfold total
      rw [expect_map]
      exact P.isProb.2

lemma lmap_mean {α β : Type} (P : FiniteLaw α) (g : α → β) (f : β → ℝ) :
    (lmap P g).mean f = P.mean (fun x => f (g x)) :=
  expect_map _ _ _

lemma lmap_atom {α β : Type} (P : FiniteLaw α) (g : α → β) (a : Fin (lmap P g).size) :
    ∃ a' : Fin P.size, (lmap P g).weight a = P.weight a' ∧ (lmap P g).atom a = g (P.atom a') := by
  refine ⟨⟨a.val, by simpa [FiniteLaw.size, lmap] using a.isLt⟩, ?_, ?_⟩
  · simp [FiniteLaw.weight, lmap]
  · simp [FiniteLaw.atom, lmap]

/-! ### Shares -/
theorem prop_le_mu {n m : ℕ} (hn : 0 < n) (c : Cost n m) (i : Fin n) :
    propShare c i ≤ mu c i := by
  unfold mu costShare
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
    calc _ ≤ -∑ e ∈ univ.filter (fun g => f g = j), c i e :=
          ciInf_le (Set.finite_range _).bddBelow j
      _ ≤ _ := by linarith
  unfold propShare
  linarith

lemma good_mono {n m : ℕ} {c : Cost n m} {P : FiniteLaw (Allocation n m)} {B B' : ℝ}
    (h : Good c P B) (hB : B ≤ B') : Good c P B' :=
  ⟨h.1, fun a ha => ⟨(h.2 a ha).1, (h.2 a ha).2.trans hB⟩⟩

lemma cost_bundle_fst {n m : ℕ} (c : Cost n m) (i : Fin n) (A : Fin m → Fin n × Fin (m + 1)) :
    cost c i (bundle (fun e => (A e).1) i) =
      ∑ e, ∑ j : Fin (m + 1), c i e * (if A e = (i, j) then 1 else 0) := by
  show ∑ e ∈ univ.filter (fun e => (A e).1 = i), c i e = _
  rw [sum_filter]
  apply sum_congr rfl
  intro e _
  rw [← mul_sum]
  obtain ⟨a1, a2⟩ := A e
  by_cases h : a1 = i
  · subst h; simp
  · simp [h]

/-! ### Part S -/
theorem small_case {n m : ℕ} (hn : 0 < n) (c : Cost n m) (h0 : Nonnegative c) (hI : IDO c) :
    ∃ P : FiniteLaw (Allocation n m), Good c P n := by
  obtain ⟨z, hzdef⟩ : ∃ z : Fin m → ℝ, z = fun _ => 1 / (n : ℝ) := ⟨_, rfl⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hz : ∀ e, 0 ≤ z e := fun e => by simp only [hzdef]; positivity
  have hzsum : ∑ e, z e ≤ (m : ℝ) + 1 := by
    simp only [hzdef, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (1 : ℝ) / n ≤ 1 := by
      rw [div_le_one hnR]; exact_mod_cast hn
    nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  let f : (Fin n × Fin (m + 1)) → Fin m → ℝ := fun s e => generalSlot z e s.2.val
  have hcol : ∀ e, ∑ s, f s e = 1 := by
    intro e
    rw [Fintype.sum_prod_type]
    simp only [f, Dev.L33.PartAB.gs_sum_slots z hz hzsum e]
    simp only [hzdef, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  obtain ⟨P, hmean, hatoms⟩ := Dev.L33.PartAB.round_exists (E := Fin m)
    (S := Fin n × Fin (m + 1)) f (fun s e => Dev.L33.PartAB.gs_nonneg z e _) hcol
    (fun s => Dev.L33.PartAB.gs_load_le z hz _)
  refine ⟨lmap P (fun A e => (A e).1), ?_, ?_⟩
  · intro i
    rw [lmap_mean]
    simp only [cost_bundle_fst]
    unfold FiniteLaw.mean
    rw [expect_sum]
    simp only [expect_sum, expect_const_mul]
    have : ∀ e j, expect P.toLaw (fun A => if A e = (i, j) then (1:ℝ) else 0) = f (i, j) e :=
      fun e j => hmean e (i, j)
    simp only [this, f, ← mul_sum, Dev.L33.PartAB.gs_sum_slots z hz hzsum]
    subst hzdef
    unfold propShare cost ChoresEFX.cost
    rw [sum_div]
    apply le_of_eq
    apply sum_congr rfl; intro e _; ring
  · intro a ha
    obtain ⟨a', hw, hat⟩ := lmap_atom P (fun A e => (A e).1) a
    rw [hw] at ha
    obtain ⟨hinj, hpos, -⟩ := hatoms a' ha
    rw [hat]
    refine ⟨fun i => ?_, ?_⟩
    · set A := P.atom a'
      set T := bundle (fun e => (A e).1) i with hT
      have hmemT : ∀ e, e ∈ T ↔ (A e).1 = i := fun e => by
        simp [hT, bundle, ChoresEFX.bundle]
      rcases T.eq_empty_or_nonempty with hE | ⟨e1, he1⟩
      · exact Or.inl hE
      right
      let σ : Fin m → ℕ := fun e => (A e).2.val
      have hσ : Set.InjOn σ T := by
        intro x hx y hy hxy
        rw [mem_coe, hmemT] at hx hy
        exact hinj (Prod.ext (hx.trans hy.symm) (Fin.ext hxy))
      have hgs := (Dev.L33.PartAB.gs_cost (c i) (h0 i) (hI i) z hz T σ hσ
        (fun e _ => hpos e)).2
      have hbound : ∑ e, c i e * z e ≤ mu c i := by
        refine le_trans (le_of_eq ?_) (prop_le_mu hn c i)
        unfold propShare cost ChoresEFX.cost
        rw [sum_div]; apply sum_congr rfl; intro e _; simp only [hzdef]; ring
      classical
      by_cases hex : ∃ e0 ∈ T, σ e0 = 0
      · obtain ⟨e0, he0, hσ0⟩ := hex
        refine ⟨e0, he0, ?_⟩
        refine le_trans ?_ (hgs.trans hbound)
        apply sum_le_sum_of_subset_of_nonneg
        · intro e he
          rw [mem_erase] at he
          rw [mem_filter]
          refine ⟨he.2, fun h => he.1 (hσ he.2 he0 (h.trans hσ0.symm))⟩
        · intro e _ _; exact h0 i e
      · push Not at hex
        refine ⟨e1, he1, ?_⟩
        refine le_trans ?_ (hgs.trans hbound)
        apply sum_le_sum_of_subset_of_nonneg
        · intro e he
          rw [mem_erase] at he
          rw [mem_filter]
          exact ⟨he.2, hex e he.2⟩
        · intro e _ _; exact h0 i e
    · have := card_le_univ (nonMMS c (fun e => (P.atom a' e).1))
      simp only [Fintype.card_fin] at this
      exact_mod_cast this

end SublinearChoresMMS.Disposal.Dev.T11.PartST
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.T11
open SublinearChoresMMS.Disposal
open Finset
/-! ### Part S: every IDO instance (uniform fractions + general unit-slot rounding) -/

end SublinearChoresMMS.Disposal.Dev.T11
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.T11.PartM
open SublinearChoresMMS.Disposal
open Finset
/-! ### Part K: the common excluded prefix -/
lemma card_Z_le {n m q : ℕ} (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m) (P : Labels n m q)
    (_hP0 : ∀ r : Fin (m / q), r.val = 0 → P r = none) :
    (Z P).card ≤ q * (1 + excludedCount P) + 2 * q := by
  classical
  have hL : 1 ≤ n / q := (Nat.one_le_div_iff hq).2 hqn
  set last : Fin (n / q) := ⟨n / q - 1, by omega⟩ with hlast
  set S1 : Finset (Fin m) := univ.filter (fun e => P (L33.PartC.blk hdiv e) = none)
  set S2 : Finset (Fin m) := (G P last).filter
    (fun e => position (G P last) e < denominator n q last)
  have hsub : Z P ⊆ S1 ∪ S2 := by
    intro e he
    unfold Z at he
    simp only [mem_filter, mem_univ, true_and, not_exists, not_and] at he
    rw [mem_union]
    rcases hpe : P (L33.PartC.blk hdiv e) with _ | v
    · left; simp [S1, hpe]
    · right
      have hk : min v.val (n / q - 1) < n / q := by omega
      have hG : e ∈ G P ⟨min v.val (n / q - 1), hk⟩ := by
        rw [L33.PartC.mem_G_iff P hdiv, hpe]; rfl
      have h := he _ hG
      push Not at h
      have ht : (⟨min v.val (n / q - 1), hk⟩ : Fin (n / q)) = last := by
        have h1 : min v.val (n / q - 1) + 1 = n / q := h.1
        exact Fin.ext (show min v.val (n / q - 1) = n / q - 1 by omega)
      rw [ht] at hG h
      simp only [S2, mem_filter]
      exact ⟨hG, h.2⟩
  have hS1 : S1.card ≤ q * (1 + excludedCount P) := by
    set B : Finset (Fin (m / q)) := univ.filter (fun r => P r = none)
    have hB : B.card ≤ 1 + excludedCount P := by
      have : B ⊆ univ.filter (fun r : Fin (m / q) => r.val = 0) ∪
          univ.filter (fun r => 0 < r.val ∧ P r = none) := by
        intro r hr
        simp only [B, mem_filter, mem_univ, true_and] at hr
        simp only [mem_union, mem_filter, mem_univ, true_and]
        rcases Nat.eq_zero_or_pos r.val with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, hr⟩
      refine (card_le_card this).trans ((card_union_le _ _).trans ?_)
      unfold excludedCount
      have : (univ.filter (fun r : Fin (m / q) => r.val = 0)).card ≤ 1 := by
        rw [card_le_one]
        intro a ha b hb
        simp only [mem_filter, mem_univ, true_and] at ha hb
        exact Fin.ext (ha.trans hb.symm)
      omega
    calc S1.card ≤ q * (S1.image (L33.PartC.blk hdiv)).card := by
          apply card_le_mul_card_image
          intro r _
          have := L33.PartC.card_filter_div_le S1 (fun e => e.val)
            (fun x _ y _ h => Fin.ext h) q r.val hq
          refine le_trans (card_le_card ?_) this
          intro e he
          simp only [mem_filter] at he ⊢
          refine ⟨he.1, ?_⟩
          rw [← he.2]; rfl
      _ ≤ q * B.card := by
          apply Nat.mul_le_mul_left
          apply card_le_card
          intro r hr
          simp only [mem_image, S1, mem_filter, mem_univ, true_and] at hr
          obtain ⟨e, he, rfl⟩ := hr
          simp [B, he]
      _ ≤ q * (1 + excludedCount P) := Nat.mul_le_mul_left _ hB
  have hS2 : S2.card ≤ 2 * q := by
    calc S2.card ≤ (range (denominator n q last)).card := by
          apply card_le_card_of_injOn (position (G P last))
          · intro e he
            simp only [S2, coe_filter, Set.mem_setOf_eq] at he
            simpa using he.2
          · exact (L33.PartC.position_injOn _).mono (fun x hx => (mem_filter.mp hx).1)
      _ ≤ 2 * q := by
          rw [card_range]
          unfold denominator
          have := Nat.mod_lt n hq
          split_ifs <;> omega
  calc (Z P).card ≤ (S1 ∪ S2).card := card_le_card hsub
    _ ≤ S1.card + S2.card := card_union_le _ _
    _ ≤ _ := by omega

/-- `K_le` holds once `X ≥ 0` or some agent is ordinary. -/
theorem K_le_of {n m q : ℕ} (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    {R : Finset (Fin n)} (p : Packings n m q R)
    (hp0 : ∀ i (r : Fin (m / q)), r.val = 0 → p i r = none) (X : ℝ)
    (hX : ∀ i, (excludedCount (p i) : ℝ) ≤ X) (hX0 : 0 ≤ X ∨ Nonempty (Ordinary R)) :
    (K p : ℝ) ≤ q * (X + 3) := by
  by_cases hne : Nonempty (Ordinary R)
  · obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup (univ : Finset (Ordinary R))
      (univ_nonempty_iff.2 hne) (fun i => (Z (p i)).card)
    unfold K
    rw [hi0]
    have h1 := card_Z_le hq hqn hdiv (p i0) (hp0 i0)
    have h2 : ((Z (p i0)).card : ℝ) ≤ (q : ℝ) * (1 + excludedCount (p i0)) + 2 * q := by
      exact_mod_cast h1
    have h3 := hX i0
    have hq' : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    nlinarith
  · have hX0' : 0 ≤ X := hX0.resolve_right hne
    have : K p = 0 := by
      unfold K
      rw [not_nonempty_iff] at hne
      simp [univ_eq_empty]
    rw [this]
    push_cast
    positivity

/-- With an ordinary agent (`R.card < n`), `K_le` holds for every `X`. -/
theorem K_le {n m q : ℕ} (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    {R : Finset (Fin n)} (hRn : R.card < n) (p : Packings n m q R)
    (hp0 : ∀ i (r : Fin (m / q)), r.val = 0 → p i r = none) (X : ℝ)
    (hX : ∀ i, (excludedCount (p i) : ℝ) ≤ X) :
    (K p : ℝ) ≤ q * (X + 3) := by
  apply K_le_of hq hqn hdiv p hp0 X hX (Or.inr ?_)
  obtain ⟨i, -, hi⟩ := exists_mem_notMem_of_card_lt_card (s := R) (t := univ)
    (by simpa using hRn)
  exact ⟨⟨i, hi⟩⟩

end SublinearChoresMMS.Disposal.Dev.T11.PartM
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.T11.PartM
open SublinearChoresMMS.Disposal
open Finset
open OAI.CliqueFreeIndependence
/-! ### Part M: composing the two lotteries -/
lemma expect_eq_sum {α : Type} (L : Lottery.Law α) (f : α → ℝ) :
    Lottery.expect L f = ∑ k : Fin L.length, L[k].1 * f L[k].2 := by
  induction L with
  | nil => simp
  | cons z L ih =>
    obtain ⟨w, x⟩ := z
    rw [Lottery.expect_cons, ih]
    erw [Fin.sum_univ_succ]
    rfl

lemma mean_eq_sum {α : Type} (P : FiniteLaw α) (f : α → ℝ) :
    P.mean f = ∑ a : Fin P.size, P.weight a * f (P.atom a) :=
  expect_eq_sum _ _

lemma weight_nonneg {α : Type} (P : FiniteLaw α) (a : Fin P.size) : 0 ≤ P.weight a :=
  P.isProb.1 _ (List.getElem_mem _)

lemma sum_weight {α : Type} (P : FiniteLaw α) : ∑ a : Fin P.size, P.weight a = 1 := by
  have h := P.isProb.2
  unfold Lottery.total at h
  rw [expect_eq_sum] at h
  simp only [mul_one] at h
  exact h

lemma mean_sum {α ι : Type} (P : FiniteLaw α) (s : Finset ι) (g : ι → α → ℝ) :
    P.mean (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, P.mean (g i) := by
  simp only [mean_eq_sum, mul_sum]
  exact sum_comm

lemma mean_mul {α : Type} (P : FiniteLaw α) (r : ℝ) (g : α → ℝ) :
    P.mean (fun x => r * g x) = r * P.mean g := by
  simp only [mean_eq_sum, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

lemma expect_append {α : Type} (L M : Lottery.Law α) (f : α → ℝ) :
    Lottery.expect (L ++ M) f = Lottery.expect L f + Lottery.expect M f := by
  simp [Lottery.expect, List.map_append, List.sum_append]

lemma expect_flatten {α : Type} (Ls : List (Lottery.Law α)) (f : α → ℝ) :
    Lottery.expect Ls.flatten f = (Ls.map fun L => Lottery.expect L f).sum := by
  induction Ls with
  | nil => simp
  | cons L Ls ih => rw [List.flatten_cons, expect_append, ih]; simp

lemma expect_map {α β : Type} (L : Lottery.Law α) (w : ℝ) (h : α → β) (f : β → ℝ) :
    Lottery.expect (L.map fun z => (w * z.1, h z.2)) f = w * Lottery.expect L (fun x => f (h x)) := by
  induction L with
  | nil => simp
  | cons z L ih =>
    obtain ⟨u, x⟩ := z
    rw [List.map_cons, Lottery.expect_cons, ih, Lottery.expect_cons]
    ring

/-- The flattened composite list. -/
def bindList {α β γ : Type} (P : FiniteLaw β) (Q : β → FiniteLaw γ) (h : γ → α) : Lottery.Law α :=
  (List.ofFn fun a : Fin P.size =>
    (Q (P.atom a)).toLaw.map fun z => (P.weight a * z.1, h z.2)).flatten

lemma expect_bindList {α β γ : Type} (P : FiniteLaw β) (Q : β → FiniteLaw γ) (h : γ → α)
    (f : α → ℝ) :
    Lottery.expect (bindList P Q h) f = ∑ a, P.weight a * (Q (P.atom a)).mean (fun x => f (h x)) := by
  unfold bindList
  rw [expect_flatten, List.map_ofFn, List.sum_ofFn]
  exact sum_congr rfl fun a _ => expect_map _ _ _ _

lemma mem_bindList {α β γ : Type} (P : FiniteLaw β) (Q : β → FiniteLaw γ) (h : γ → α)
    (z : ℝ × α) (hz : z ∈ bindList P Q h) :
    ∃ a b, z = (P.weight a * (Q (P.atom a)).weight b, h ((Q (P.atom a)).atom b)) := by
  unfold bindList at hz
  rw [List.mem_flatten] at hz
  obtain ⟨l, hl, hzl⟩ := hz
  rw [List.mem_ofFn] at hl
  obtain ⟨a, rfl⟩ := hl
  rw [List.mem_map] at hzl
  obtain ⟨z', hz', rfl⟩ := hzl
  obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.1 hz'
  exact ⟨a, ⟨b, hb⟩, rfl⟩

/-- The composite law. -/
def bindLaw {α β γ : Type} (P : FiniteLaw β) (Q : β → FiniteLaw γ) (h : γ → α) :
    FiniteLaw α where
  toLaw := bindList P Q h
  isProb := by
    refine ⟨fun z hz => ?_, ?_⟩
    · obtain ⟨a, b, rfl⟩ := mem_bindList P Q h z hz
      exact mul_nonneg (weight_nonneg P a) (weight_nonneg _ b)
    · unfold Lottery.total
      rw [expect_bindList]
      have : ∀ a : Fin P.size, (Q (P.atom a)).mean (fun _ => (1 : ℝ)) = 1 := fun a => by
        rw [mean_eq_sum]; simpa using sum_weight (Q (P.atom a))
      simp only [this, mul_one]
      exact sum_weight P

lemma bindLaw_mean {α β γ : Type} (P : FiniteLaw β) (Q : β → FiniteLaw γ) (h : γ → α)
    (f : α → ℝ) :
    (bindLaw P Q h).mean f = ∑ a, P.weight a * (Q (P.atom a)).mean (fun x => f (h x)) :=
  expect_bindList P Q h f

lemma bindLaw_atom {α β γ : Type} (P : FiniteLaw β) (Q : β → FiniteLaw γ) (h : γ → α)
    (k : Fin (bindLaw P Q h).size) (hk : 0 < (bindLaw P Q h).weight k) :
    ∃ a b, 0 < P.weight a ∧ 0 < (Q (P.atom a)).weight b ∧
      (bindLaw P Q h).atom k = h ((Q (P.atom a)).atom b) := by
  obtain ⟨a, b, hab⟩ := mem_bindList P Q h _ (List.getElem_mem (l := bindList P Q h) k.2)
  have hw : (bindLaw P Q h).weight k = P.weight a * (Q (P.atom a)).weight b :=
    congrArg Prod.fst hab
  have hat : (bindLaw P Q h).atom k = h ((Q (P.atom a)).atom b) := congrArg Prod.snd hab
  rw [hw] at hk
  have ha := weight_nonneg P a
  have hb := weight_nonneg (Q (P.atom a)) b
  refine ⟨a, b, ?_, ?_, hat⟩
  · rcases ha.lt_or_eq with h1 | h1
    · exact h1
    · rw [← h1, zero_mul] at hk; exact absurd hk (lt_irrefl 0)
  · rcases hb.lt_or_eq with h1 | h1
    · exact h1
    · rw [← h1, mul_zero] at hk; exact absurd hk (lt_irrefl 0)

end SublinearChoresMMS.Disposal.Dev.T11.PartM
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.T11.PartM
open SublinearChoresMMS.Disposal
open Finset
variable {n m q : ℕ}
def toAlloc (A : SlotAssignment n m) : Allocation n m := fun e => (A e).1

def trivLaw (hn : 0 < n) : FiniteLaw (SlotAssignment n m) where
  toLaw := [(1, fun _ => (⟨0, hn⟩, 0))]
  isProb := by
    refine ⟨fun z hz => ?_, ?_⟩
    · rw [List.mem_singleton] at hz; rw [hz]; norm_num
    · simp [OAI.CliqueFreeIndependence.Lottery.total]

lemma card_ordinary (R : Finset (Fin n)) : Fintype.card (Ordinary R) = n - R.card := by
  rw [Fintype.card_subtype, filter_not, filter_mem_eq_inter, univ_inter, ← compl_eq_univ_sdiff,
    card_compl, Fintype.card_fin]

lemma cost_eq_sum (c : Cost n m) (i : Fin n) : cost c i univ = ∑ e, c i e := rfl

/-- Average over the coefficient lottery of an ordinary column. -/
lemma avg_ord (c : Cost n m) {R : Finset (Fin n)} (p : Packings n m q R)
    (heta : ∀ i e, (∑ t, eta n q t * completed c p i t e) = 1 / (n : ℝ))
    (P : FiniteLaw (Coefficients n q R))
    (hmean : ∀ i t, P.mean (fun v => v i t) = eta n q t) (j : Ordinary R) (e : Fin m) :
    ∑ a, P.weight a * ∑ t, P.atom a j t * completed c p j t e = 1 / (n : ℝ) := by
  rw [← heta j e]
  have h1 : ∀ t, eta n q t = ∑ a, P.weight a * P.atom a j t := fun t => by
    rw [← hmean j t, mean_eq_sum]
  simp only [h1, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

lemma avg_realized (hn : 0 < n) (c : Cost n m) {R : Finset (Fin n)} (hR : 1 ≤ R.card)
    (hRn : R.card < n) (p : Packings n m q R)
    (heta : ∀ i e, (∑ t, eta n q t * completed c p i t e) = 1 / (n : ℝ))
    (P : FiniteLaw (Coefficients n q R))
    (hmean : ∀ i t, P.mean (fun v => v i t) = eta n q t) (i : Fin n) (e : Fin m) :
    ∑ a, P.weight a * realized c p (P.atom a) i e = 1 / (n : ℝ) := by
  by_cases hi : i ∈ R
  · have hrw : ∀ a, realized c p (P.atom a) i e =
        (1 - ordinaryFraction c p (P.atom a) e) / (R.card : ℝ) := fun a => by
      unfold realized; rw [dif_pos hi]
    simp only [hrw]
    have hO : ∑ a, P.weight a * ordinaryFraction c p (P.atom a) e =
        ((n - R.card : ℕ) : ℝ) / n := by
      unfold ordinaryFraction
      simp only [mul_sum]
      rw [sum_comm]
      simp only [← mul_sum]
      rw [sum_congr rfl fun j _ => avg_ord c p heta P hmean j e, sum_const, card_univ,
        card_ordinary, nsmul_eq_mul]
      ring
    have h1 : ∑ a, P.weight a * ((1 - ordinaryFraction c p (P.atom a) e) / (R.card : ℝ)) =
        (∑ a, P.weight a - ∑ a, P.weight a * ordinaryFraction c p (P.atom a) e) /
          (R.card : ℝ) := by
      rw [sub_div, sum_div, sum_div, ← sum_sub_distrib]
      exact sum_congr rfl fun _ _ => by ring
    rw [h1, hO, sum_weight, Nat.cast_sub hRn.le]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hr' : (R.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : R.card ≠ 0)
    field_simp
    ring
  · simp only [fun a => L33.PartD.realized_ord c p (P.atom a) ⟨i, hi⟩ e]
    exact avg_ord c p heta P hmean ⟨i, hi⟩ e

lemma avg_fc (hn : 0 < n) (c : Cost n m) {R : Finset (Fin n)} (hR : 1 ≤ R.card)
    (hRn : R.card < n) (p : Packings n m q R)
    (heta : ∀ i e, (∑ t, eta n q t * completed c p i t e) = 1 / (n : ℝ))
    (P : FiniteLaw (Coefficients n q R))
    (hmean : ∀ i t, P.mean (fun v => v i t) = eta n q t) (i : Fin n) :
    ∑ a, P.weight a * fractionalCost c i (realized c p (P.atom a) i) = propShare c i := by
  unfold fractionalCost propShare
  simp only [mul_sum]
  rw [sum_comm, cost_eq_sum, sum_div]
  refine sum_congr rfl fun e _ => ?_
  have := avg_realized hn c hR hRn p heta P hmean i e
  calc ∑ a, P.weight a * (c i e * realized c p (P.atom a) i e)
      = c i e * ∑ a, P.weight a * realized c p (P.atom a) i e := by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    _ = c i e / n := by rw [this]; ring

lemma ind_sum (A : SlotAssignment n m) (i : Fin n) (e : Fin m) :
    (∑ j : Fin (m + 1), if A e = (i, j) then (1 : ℝ) else 0) =
      if (A e).1 = i then 1 else 0 := by
  by_cases h : (A e).1 = i
  · rw [if_pos h, sum_eq_single (A e).2]
    · rw [if_pos (Prod.ext h rfl : A e = (i, (A e).2))]
    · intro j _ hj
      rw [if_neg]
      intro h'
      exact hj (by rw [h'])
    · intro hh; exact absurd (mem_univ _) hh
  · rw [if_neg h]
    exact sum_eq_zero fun j _ => if_neg fun h' => h (by rw [h'])

lemma marg_cost (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (hR : 1 ≤ R.card)
    (p : Packings n m q R) (hp : ∀ i, ValidPacking c i.val (p i))
    (v : Coefficients n q R) (hv : Coordinated c p v) (Q : FiniteLaw (SlotAssignment n m))
    (hQ : ∀ e s, Q.mean (fun A => if A e = s then 1 else 0) = slotFraction c p v s e)
    (i : Fin n) :
    Q.mean (fun A => cost c i (bundle (toAlloc A) i)) =
      fractionalCost c i (realized c p v i) := by
  have hcost : ∀ A : SlotAssignment n m, cost c i (bundle (toAlloc A) i) =
      ∑ e, c i e * ∑ j : Fin (m + 1), if A e = (i, j) then (1 : ℝ) else 0 := by
    intro A
    simp only [ind_sum, mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    rfl
  simp only [hcost]
  rw [mean_sum]
  unfold fractionalCost
  refine sum_congr rfl fun e _ => ?_
  rw [mean_mul, mean_sum]
  simp only [hQ]
  rw [L33.PartD.sf_col hn hq hqn hdiv c hc R hR p hp v hv i e]

lemma fc_realized_le_one (hn : 0 < n) (c : Cost n m) (hc : Normalized c)
    {R : Finset (Fin n)} (hR : 1 ≤ R.card) (hRn : R.card < n) (p : Packings n m q R)
    (hfc : ∀ i t, fractionalCost c i.val (completed c p i t) ≤ 1)
    (v : Coefficients n q R) (hv : Coordinated c p v) (i : Fin n) :
    fractionalCost c i (realized c p v i) ≤ 1 := by
  by_cases hi : i ∈ R
  · have hrw : fractionalCost c i (realized c p v i) =
        (∑ e, c i e - ∑ e, c i e * ordinaryFraction c p v e) / (R.card : ℝ) := by
      have hr : ∀ e, realized c p v i e = (1 - ordinaryFraction c p v e) / (R.card : ℝ) :=
        fun e => by unfold realized; rw [dif_pos hi]
      unfold fractionalCost
      simp only [hr]
      rw [← sum_sub_distrib, sum_div]
      exact sum_congr rfl fun _ _ => by ring
    have hO : ∑ e, c i e * ordinaryFraction c p v e =
        ∑ j, ∑ t, v j t * fractionalCost c i (completed c p j t) := by
      unfold ordinaryFraction fractionalCost
      simp only [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun j _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    rw [hrw, hO, hv.2.2 i hi, ← cost_eq_sum, Nat.cast_sub hRn.le]
    have hP : cost c i univ = n * propShare c i := by
      unfold propShare
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    rw [hP]
    have hr' : (R.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : R.card ≠ 0)
    have : ((n : ℝ) * propShare c i - ((n : ℝ) - R.card) * propShare c i) / R.card =
        propShare c i := by
      field_simp; ring
    rw [this]
    exact L33.PartC.prop_le_one hn c hc i
  · have hrw : fractionalCost c i (realized c p v i) =
        ∑ t, v ⟨i, hi⟩ t * fractionalCost c i (completed c p ⟨i, hi⟩ t) := by
      unfold fractionalCost
      simp only [L33.PartD.realized_ord c p v ⟨i, hi⟩, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    rw [hrw]
    calc ∑ t, v ⟨i, hi⟩ t * fractionalCost c i (completed c p ⟨i, hi⟩ t)
        ≤ ∑ t, v ⟨i, hi⟩ t * 1 :=
          sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hfc ⟨i, hi⟩ t) (hv.1.1 _ t)
      _ = 1 := by simp only [mul_one]; exact hv.1.2 _

lemma mms1_atom (hn : 0 < n) (c : Cost n m) (hc : Normalized c)
    {R : Finset (Fin n)} (hR : 1 ≤ R.card) (hRn : R.card < n) (p : Packings n m q R)
    (hfc : ∀ i t, fractionalCost c i.val (completed c p i t) ≤ 1)
    (v : Coefficients n q R) (hv : Coordinated c p v) (A : SlotAssignment n m)
    (hA : Function.Injective A)
    (hgen : ∀ i, GeneralAgent c p v i →
      cost c i (withoutFirst A i) ≤ fractionalCost c i (realized c p v i))
    (hpure : ∀ i : Ordinary R, Pure v i → MMS1 c i.val (slotBundle A i.val)) (i : Fin n) :
    MMS1 c i (bundle (toAlloc A) i) := by
  classical
  show MMS1 c i (slotBundle A i)
  rcases L33.PartD.agent_cases c p v i with hg | ⟨i', rfl, hcu⟩
  · have hW := (hgen i hg).trans (fc_realized_le_one hn c hc hR hRn p hfc v hv i)
    refine (L33.PartD.finish c hc i (slotBundle A i) (withoutFirst A i) hW ?_).1
    intro hne
    by_cases h0 : ∃ e0 ∈ slotBundle A i, (A e0).2.val = 0
    · obtain ⟨e0, he0, h0⟩ := h0
      refine ⟨e0, he0, fun e he => ?_⟩
      rw [mem_erase] at he
      rw [L33.PartD.mem_withoutFirst]
      have h1 := (L33.PartD.mem_slotBundle A i e).1 he.2
      refine ⟨h1, fun h2 => he.1 (hA ?_)⟩
      exact Prod.ext (h1.trans ((L33.PartD.mem_slotBundle A i e0).1 he0).symm)
        (Fin.ext (h2.trans h0.symm))
    · push Not at h0
      obtain ⟨e0, he0⟩ := hne
      refine ⟨e0, he0, fun e he => ?_⟩
      have he' := mem_of_mem_erase he
      rw [L33.PartD.mem_withoutFirst]
      exact ⟨(L33.PartD.mem_slotBundle A i e).1 he', h0 e he'⟩
  · obtain ⟨t, -, hpv, -⟩ := hcu
    exact hpure i' hpv

lemma nonMMS_card (c : Cost n m) (hc : Normalized c)
    {R : Finset (Fin n)} (p : Packings n m q R)
    (v : Coefficients n q R) (A : SlotAssignment n m)
    (hpure : ∀ i : Ordinary R, Pure v i → cost c i.val (slotBundle A i.val \ H p) ≤ 1) :
    (nonMMS c (toAlloc A)).card ≤ R.card + mixedCount v + K p := by
  classical
  have hsub : nonMMS c (toAlloc A) ⊆ R ∪ (univ.filter (fun i => ¬Pure v i)).image Subtype.val ∪
      (H p).image (fun e => (A e).1) := by
    intro i hi
    unfold nonMMS at hi
    rw [mem_filter] at hi
    by_contra hcon
    simp only [mem_union, mem_image, mem_filter, mem_univ, true_and, not_or, not_exists,
      not_and] at hcon
    obtain ⟨⟨hiR, hpv⟩, hH⟩ := hcon
    have hP : Pure v ⟨i, hiR⟩ := by
      by_contra hnp
      exact hpv ⟨i, hiR⟩ hnp rfl
    have hb := hpure ⟨i, hiR⟩ hP
    have : slotBundle A i \ H p = slotBundle A i := by
      ext e
      simp only [mem_sdiff, and_iff_left_iff_imp]
      intro he heH
      exact hH e heH ((L33.PartD.mem_slotBundle A i e).1 he)
    rw [this, ← hc.2.2 i] at hb
    exact absurd hi.2 (not_lt.2 hb)
  have hM : ((univ.filter (fun i => ¬Pure v i)).image Subtype.val).card ≤ mixedCount v := by
    refine card_image_le.trans (le_of_eq ?_)
    unfold mixedCount
    congr 1
  calc (nonMMS c (toAlloc A)).card
      ≤ (R ∪ (univ.filter (fun i => ¬Pure v i)).image Subtype.val ∪
          (H p).image (fun e => (A e).1)).card := card_le_card hsub
    _ ≤ R.card + ((univ.filter (fun i => ¬Pure v i)).image Subtype.val).card +
          ((H p).image (fun e => (A e).1)).card :=
        (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    _ ≤ R.card + mixedCount v + K p := by
        have := card_image_le (s := H p) (f := fun e => (A e).1)
        rw [L33.PartD.card_H] at this
        omega

end SublinearChoresMMS.Disposal.Dev.T11.PartM
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.T11.PartM
open SublinearChoresMMS.Disposal
open Finset
/-- The composition of the coefficient lottery of Lemma 3.2 with the slot rounding of Lemma 3.3. -/
theorem compose {n m q : ℕ} (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hqm : q ≤ m)
    (hdiv : q ∣ m) (c : Cost n m) (hc : Normalized c)
    (R : Finset (Fin n)) (hR : 1 ≤ R.card) (hRn : R.card < n)
    (p : Packings n m q R) (hp : ∀ i, ValidPacking c i.val (p i))
    (heta : ∀ i e, (∑ t, eta n q t * completed c p i t e) = 1 / (n : ℝ))
    (hfc : ∀ i t, fractionalCost c i.val (completed c p i t) ≤ 1)
    (P : FiniteLaw (Coefficients n q R))
    (hmean : ∀ i t, P.mean (fun v => v i t) = eta n q t)
    (hatoms : ∀ a : Fin P.size, 0 < P.weight a →
      Coordinated c p (P.atom a) ∧ mixedCount (P.atom a) ≤ 2 * (R.card + 1)) :
    ∃ Q : FiniteLaw (Allocation n m),
      Good c Q ((R.card : ℝ) + 2 * (R.card + 1) + K p) := by
  classical
  let Qf : Coefficients n q R → FiniteLaw (SlotAssignment n m) := fun v =>
    if h : Coordinated c p v then
      Classical.choose (lemma_3_3 hn hq hqn hqm hdiv c hc R hR hRn p hp v h)
    else trivLaw hn
  have hQf : ∀ v (h : Coordinated c p v),
      Qf v = Classical.choose (lemma_3_3 hn hq hqn hqm hdiv c hc R hR hRn p hp v h) :=
    fun v h => dif_pos h
  refine ⟨bindLaw P Qf toAlloc, fun i => ?_, fun k hk => ?_⟩
  · rw [bindLaw_mean, ← avg_fc hn c hR hRn p heta P hmean i]
    refine le_of_eq (sum_congr rfl fun a _ => ?_)
    rcases (weight_nonneg P a).lt_or_eq with ha | ha
    · have hv := (hatoms a ha).1
      rw [hQf _ hv]
      rw [marg_cost hn hq hqn hdiv c hc R hR p hp _ hv _
        (Classical.choose_spec (lemma_3_3 hn hq hqn hqm hdiv c hc R hR hRn p hp _ hv)).1 i]
    · rw [← ha, zero_mul, zero_mul]
  · obtain ⟨a, b, ha, hb, hat⟩ := bindLaw_atom P Qf toAlloc k hk
    obtain ⟨hv, hmix⟩ := hatoms a ha
    have hspec : ∀ b : Fin (Qf (P.atom a)).size, 0 < (Qf (P.atom a)).weight b →
        Function.Injective ((Qf (P.atom a)).atom b) ∧
        (∀ e, 0 < slotFraction c p (P.atom a) ((Qf (P.atom a)).atom b e) e) ∧
        (∀ s, slotLoad (slotFraction c p (P.atom a)) s = 1 →
          ∃ e, (Qf (P.atom a)).atom b e = s) ∧
        (∀ i, GeneralAgent c p (P.atom a) i →
          cost c i (slotBundle ((Qf (P.atom a)).atom b) i) ≤
            fractionalCost c i (realized c p (P.atom a) i) + kappa c i ∧
          cost c i (withoutFirst ((Qf (P.atom a)).atom b) i) ≤
            fractionalCost c i (realized c p (P.atom a) i)) ∧
        ∀ i : Ordinary R, Pure (P.atom a) i →
          MMS1 c i.val (slotBundle ((Qf (P.atom a)).atom b) i.val) ∧
          cost c i.val (slotBundle ((Qf (P.atom a)).atom b) i.val) ≤ 1 + kappa c i.val ∧
          cost c i.val (slotBundle ((Qf (P.atom a)).atom b) i.val \ H p) ≤ 1 := by
      rw [hQf _ hv]
      exact (Classical.choose_spec
        (lemma_3_3 hn hq hqn hqm hdiv c hc R hR hRn p hp _ hv)).2
    obtain ⟨hinj, -, -, hgen, hpure⟩ := hspec b hb
    rw [hat]
    refine ⟨fun i => mms1_atom hn c hc hR hRn p hfc _ hv _ hinj (fun i hg => (hgen i hg).2)
      (fun i hpi => (hpure i hpi).1) i, ?_⟩
    have h1 := nonMMS_card c hc p _ _ (fun i hpi => (hpure i hpi).2.2)
    have h2 : ((nonMMS c (toAlloc ((Qf (P.atom a)).atom b))).card : ℝ) ≤
        (R.card + mixedCount (P.atom a) + K p : ℕ) := by exact_mod_cast h1
    have h3 : ((mixedCount (P.atom a) : ℕ) : ℝ) ≤ 2 * ((R.card : ℝ) + 1) := by
      exact_mod_cast hmix
    push_cast at h2
    linarith

end SublinearChoresMMS.Disposal.Dev.T11.PartM
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.T11
open SublinearChoresMMS.Disposal
open Finset
/-! ### Part M: normalized instances with `blockSize n ∣ m`, from Lemmas 3.1–3.3 -/
alias compose := SublinearChoresMMS.Disposal.Dev.T11.PartM.compose

alias K_le := SublinearChoresMMS.Disposal.Dev.T11.PartM.K_le

end SublinearChoresMMS.Disposal.Dev.T11
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.T11.PartP
open SublinearChoresMMS.Disposal
open Finset
/-- `s := √(n log n)`. -/
def sq (n : ℕ) : ℝ := Real.sqrt ((n : ℝ) * Real.log n)

lemma log_pos3 {n : ℕ} (hn : 3 ≤ n) : 1 < Real.log n := by
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  linarith

lemma log_le_self' {n : ℕ} (hn : 3 ≤ n) : Real.log n ≤ n := by
  have h0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have := Real.log_le_sub_one_of_pos h0
  linarith

lemma sq_sq {n : ℕ} (hn : 3 ≤ n) : sq n ^ 2 = n * Real.log n := by
  have h1 := log_pos3 hn
  have h0 : (0 : ℝ) ≤ n := by positivity
  unfold sq
  rw [Real.sq_sqrt (by positivity)]

lemma one_lt_sq {n : ℕ} (hn : 3 ≤ n) : 1 < sq n := by
  have h1 := log_pos3 hn
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  unfold sq
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by nlinarith)

lemma sq_le_n {n : ℕ} (hn : 3 ≤ n) : sq n ≤ n := by
  have h1 := log_le_self' hn
  have h2 := log_pos3 hn
  have h0 : (0 : ℝ) ≤ n := by positivity
  unfold sq
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith

lemma block_bounds {n : ℕ} (hn : 3 ≤ n) :
    (blockSize n : ℝ) ≤ sq n ∧ sq n < 2 * blockSize n := by
  have hs := one_lt_sq hn
  have hs0 : 0 < sq n := by linarith
  set j := ⌊Real.logb 2 (sq n)⌋₊ with hj
  have hb : (blockSize n : ℝ) = (2 : ℝ) ^ (j : ℝ) := by
    unfold blockSize
    rw [Real.rpow_natCast]
    push_cast
    rfl
  have hlog0 : 0 ≤ Real.logb 2 (sq n) := Real.logb_nonneg (by norm_num) hs.le
  have hrp : (2 : ℝ) ^ Real.logb 2 (sq n) = sq n := Real.rpow_logb (by norm_num) (by norm_num) hs0
  constructor
  · rw [hb, ← hrp]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hlog0)
  · have hlt : Real.logb 2 (sq n) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    have : sq n < (2 : ℝ) ^ ((j : ℝ) + 1) := by
      rw [← hrp]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
    rw [Real.rpow_add (by norm_num), Real.rpow_one] at this
    rw [hb]; linarith

lemma block_pos (n : ℕ) : 0 < blockSize n := by
  unfold blockSize; positivity

lemma block_le_n {n : ℕ} (hn : 3 ≤ n) : blockSize n ≤ n := by
  have := (block_bounds hn).1
  have := sq_le_n hn
  exact_mod_cast (by linarith : (blockSize n : ℝ) ≤ n)

/-- If `64 E² log n ≤ n` then `4 E log n ≤ q`. -/
lemma four_log_le {n : ℕ} (hn : 3 ≤ n) (E : ℝ) (hE : 0 ≤ E)
    (h : 64 * E ^ 2 * Real.log n ≤ n) : 4 * E * Real.log n ≤ blockSize n := by
  have h1 := log_pos3 hn
  obtain ⟨_, h2⟩ := block_bounds hn
  have hs := sq_sq hn
  have hs0 : 0 < sq n := by linarith [one_lt_sq hn]
  have : 8 * E * Real.log n ≤ sq n := by
    have hsq : (8 * E * Real.log n) ^ 2 ≤ sq n ^ 2 := by
      rw [hs]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hs0.le (by norm_num)).1 hsq
  linarith

lemma eventually_log (D : ℝ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → D * Real.log n ≤ n := by
  have hD : (0 : ℝ) < max D 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h := (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop).bound
    (inv_pos.2 hD)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_ge_atTop 1))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  simp only [Function.comp, id, Real.norm_eq_abs] at h1
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hl0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [abs_of_nonneg hl0, abs_of_nonneg hn0] at h1
  have := mul_le_mul_of_nonneg_left h1 hD.le
  rw [← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul] at this
  nlinarith [le_max_left D 1]

lemma rate_nonneg (n : ℕ) : 0 ≤ rate n := by
  unfold rate
  have : 0 ≤ Real.log (2 * (n : ℝ)) := by
    have := Real.log_natCast_nonneg (2 * n); push_cast at this; exact this
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg this _)

lemma rate_sq {n : ℕ} (hn : 3 ≤ n) : (n : ℝ) * sq n ≤ rate n ^ 2 := by
  have h1 := log_pos3 hn
  have h0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl2 : Real.log n ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log h0 (by linarith)
  have hl20 : 0 ≤ Real.log (2 * (n : ℝ)) := by linarith
  have h4 : rate n ^ 4 = (n : ℝ) ^ 3 * Real.log (2 * (n : ℝ)) := by
    unfold rate
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (_ ^ (1 / 4 : ℝ)),
      ← Real.rpow_mul h0.le, ← Real.rpow_mul hl20]
    norm_num
  have hsq : ((n : ℝ) * sq n) ^ 2 ≤ (rate n ^ 2) ^ 2 := by
    rw [mul_pow, sq_sq hn, ← pow_mul, h4]
    have : (0 : ℝ) ≤ n ^ 3 := by positivity
    nlinarith
  have hs0 : 0 ≤ (n : ℝ) * sq n := by unfold sq; positivity
  exact (pow_le_pow_iff_left₀ hs0 (by positivity) (by norm_num)).1 hsq

lemma Good_mono {n m : ℕ} {c : Cost n m} {P : FiniteLaw (Allocation n m)} {B B' : ℝ}
    (h : Good c P B) (hB : B ≤ B') : Good c P B' :=
  ⟨h.1, fun a ha => ⟨(h.2 a ha).1, (h.2 a ha).2.trans hB⟩⟩

theorem norm_case : ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ m : ℕ,
    blockSize n ≤ m → blockSize n ∣ m → ∀ c : Cost n m, Normalized c →
    ∃ P : FiniteLaw (Allocation n m), Good c P (C₀ * rate n) := by
  obtain ⟨A, B, hA, hB, n₁, -, h31⟩ := lemma_3_1
  obtain ⟨C₂, hC₂, n₂, -, h32⟩ := lemma_3_2 B hB
  obtain ⟨N₁, hN₁⟩ := eventually_log 64
  obtain ⟨N₂, hN₂⟩ := eventually_log (64 * (C₂ ^ 2) ^ 2)
  refine ⟨6 * C₂ + A + 8, by positivity, max (max n₁ n₂) (max (max N₁ N₂) 3), ?_⟩
  intro n hn m hqm hdiv c hc
  have hn1 : n₁ ≤ n := by omega
  have hn2 : n₂ ≤ n := by omega
  have hnN1 : N₁ ≤ n := by omega
  have hnN2 : N₂ ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hq0 := block_pos n
  have hqn := block_le_n hn3
  obtain ⟨hqs, hsq⟩ := block_bounds hn3
  have hlog := log_pos3 hn3
  have hss := sq_sq hn3
  have hs1 := one_lt_sq hn3
  have hsn := sq_le_n hn3
  have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  set q := blockSize n with hqdef
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  have h4 : 4 * Real.log n ≤ q := by
    have := four_log_le hn3 1 zero_le_one (by simp only [one_pow, mul_one]; exact hN₁ n hnN1)
    linarith
  have h4C : 4 * C₂ ^ 2 * Real.log n ≤ q := four_log_le hn3 (C₂ ^ 2) (by positivity) (hN₂ n hnN2)
  set y := Real.log n / (q : ℝ) with hy
  have hy0 : 0 < y := div_pos (by linarith) hqr
  set x := C₂ * n * Real.sqrt y with hx
  have hx0 : 0 < x := by
    have := Real.sqrt_pos.2 hy0
    have : (0 : ℝ) < n := by linarith
    positivity
  have hhalf : C₂ * Real.sqrt y ≤ 1 / 2 := by
    have hy4 : C₂ ^ 2 * y ≤ 1 / 4 := by
      rw [hy, ← mul_div_assoc, div_le_iff₀ hqr]; linarith
    have : (C₂ * Real.sqrt y) ^ 2 ≤ (1 / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hy0.le]; linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num)).1 this
  have hxn : x ≤ n / 2 := by
    calc x = n * (C₂ * Real.sqrt y) := by rw [hx]; ring
      _ ≤ n * (1 / 2) := mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ = n / 2 := by ring
  set k := ⌈x⌉₊ with hk
  have hk1 : 1 ≤ k := Nat.ceil_pos.2 hx0
  have hklt : (k : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
  have hkn : k < n := by
    have : (k : ℝ) < n := by linarith
    exact_mod_cast this
  set R : Finset (Fin n) := (univ : Finset (Fin k)).map (Fin.castLEEmb hkn.le) with hRdef
  have hRcard : R.card = k := by simp [R]
  have hRx : x ≤ (R.card : ℝ) := by rw [hRcard]; exact Nat.le_ceil x
  have hex : ∀ i : Ordinary R, ∃ p : Labels n m q, ValidPacking c i.val p ∧
      (excludedCount p : ℝ) ≤ A * Real.sqrt (n / q : ℕ) ∧
      (segments p : ℝ) ≤ B * (n / q : ℕ) ^ 3 := fun i => h31 n hn1 m hqm hdiv c hc i.val
  choose p hp using hex
  obtain ⟨-, -, -, heta, hfc, -, P, hmean, hatoms⟩ :=
    h32 n hn2 m c hc hqm hdiv R (hRcard ▸ hk1) (hRcard ▸ hkn) h4 hRx p
      (fun i => (hp i).1) (fun i => (hp i).2.2)
  obtain ⟨Q, hQ⟩ := compose (n := n) (m := m) (q := q) (by omega) hq0 hqn hqm hdiv c hc R
    (hRcard ▸ hk1) (hRcard ▸ hkn) p (fun i => (hp i).1) heta hfc P hmean hatoms
  have hK := K_le hq0 hqn hdiv (hRcard ▸ hkn) p (fun i r hr => (hp i).1.1 r hr)
    (A * Real.sqrt (n / q : ℕ)) (fun i => (hp i).2.1)
  refine ⟨Q, Good_mono hQ ?_⟩
  rw [hRcard]
  -- numeric bounds
  have hr0 := rate_nonneg n
  have hr2 := rate_sq hn3
  set r := rate n with hrdef
  set s := sq n with hsdef
  have hs0 : 0 ≤ s := by linarith
  have hsr : s ≤ r := by
    have : s ^ 2 ≤ r ^ 2 := by
      have := mul_le_mul_of_nonneg_right hsn hs0
      have e : s ^ 2 = s * s := by ring
      linarith
    exact (pow_le_pow_iff_left₀ hs0 hr0 (by norm_num)).1 this
  have hr1 : 1 ≤ r := by
    have : (1 : ℝ) ≤ n * s := by nlinarith
    nlinarith
  set L : ℕ := n / q with hL
  have hqL : (q : ℝ) * L ≤ n := by
    have : q * L ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n q
    exact_mod_cast this
  have hqsL : (q : ℝ) * Real.sqrt L ≤ r := by
    have h0 : 0 ≤ (q : ℝ) * Real.sqrt L := by positivity
    have : ((q : ℝ) * Real.sqrt L) ^ 2 ≤ r ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have a1 := mul_le_mul_of_nonneg_left hqL hqr.le
      have a2 := mul_le_mul_of_nonneg_right hqs (by positivity : (0 : ℝ) ≤ n)
      have e : (q : ℝ) ^ 2 * L = q * (q * L) := by ring
      have e' : s * n = n * s := by ring
      linarith
    exact (pow_le_pow_iff_left₀ h0 hr0 (by norm_num)).1 this
  have hny : (n : ℝ) * Real.sqrt y ≤ 2 * r := by
    have h0 : 0 ≤ (n : ℝ) * Real.sqrt y := by positivity
    have hb : (n : ℝ) ^ 2 * y ≤ 2 * n * s := by
      rw [hy, ← mul_div_assoc, div_le_iff₀ hqr]
      have e1 : (n : ℝ) ^ 2 * Real.log n = n * s ^ 2 := by rw [hss]; ring
      have e2 : (n : ℝ) * s ^ 2 ≤ n * s * (2 * q) := by
        have : s * s ≤ s * (2 * q) := mul_le_mul_of_nonneg_left hsq.le hs0
        have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ n)
        have e3 : (n : ℝ) * s ^ 2 = n * (s * s) := by ring
        have e4 : (n : ℝ) * s * (2 * q) = n * (s * (2 * q)) := by ring
        rw [e3, e4]; exact this
      have e5 : (n : ℝ) * s * (2 * q) = 2 * n * s * q := by ring
      linarith
    have : ((n : ℝ) * Real.sqrt y) ^ 2 ≤ (2 * r) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hy0.le]
      have e6 : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
      have e7 : 2 * (n : ℝ) * s = 2 * (n * s) := by ring
      have := sq_nonneg r
      linarith
    exact (pow_le_pow_iff_left₀ h0 (by positivity) (by norm_num)).1 this
  have hxr : x ≤ C₂ * (2 * r) := by
    calc x = C₂ * ((n : ℝ) * Real.sqrt y) := by rw [hx]; ring
      _ ≤ C₂ * (2 * r) := mul_le_mul_of_nonneg_left hny hC₂.le
  have hKr : (K p : ℝ) ≤ A * r + 3 * r := by
    have : (q : ℝ) * (A * Real.sqrt L + 3) = A * ((q : ℝ) * Real.sqrt L) + 3 * q := by ring
    have h2 := mul_le_mul_of_nonneg_left hqsL hA.le
    linarith
  have e8 : C₂ * (2 * r) = 2 * (C₂ * r) := by ring
  have e9 : (6 * C₂ + A + 8) * r = 6 * (C₂ * r) + A * r + 8 * r := by ring
  rw [e9]
  linarith

end SublinearChoresMMS.Disposal.Dev.T11.PartP
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.T11
open SublinearChoresMMS.Disposal
open Finset
alias norm_case := SublinearChoresMMS.Disposal.Dev.T11.PartP.norm_case

end SublinearChoresMMS.Disposal.Dev.T11
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.T11.PartN
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.T11
open Finset
open OAI.CliqueFreeIndependence.Lottery
open Filter Topology
/-! ### Finite-law helpers (copied from Part ST) -/
lemma expect_sum {α ι : Type*} (L : Law α) (s : Finset ι) (g : ι → α → ℝ) :
    expect L (fun x => ∑ k ∈ s, g k x) = ∑ k ∈ s, expect L (g k) := by
  induction L with
  | nil => simp
  | cons z L ih =>
    obtain ⟨p, a⟩ := z
    simp only [expect_cons, ih, mul_sum, sum_add_distrib]

lemma expect_const_mul {α : Type*} (L : Law α) (r : ℝ) (g : α → ℝ) :
    expect L (fun x => r * g x) = r * expect L g := by
  induction L with
  | nil => simp
  | cons z L ih =>
    obtain ⟨p, a⟩ := z
    simp only [expect_cons, ih]; ring

lemma expect_map {α β : Type*} (L : Law α) (g : α → β) (f : β → ℝ) :
    expect (L.map (fun z => (z.1, g z.2))) f = expect L (fun x => f (g x)) := by
  unfold OAI.CliqueFreeIndependence.Lottery.expect
  simp [List.map_map, Function.comp_def]

/-- Push a finite law forward along `g`, keeping the weights. -/
def lmap {α β : Type} (P : FiniteLaw α) (g : α → β) : FiniteLaw β where
  toLaw := P.toLaw.map (fun z => (z.1, g z.2))
  isProb := by
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [List.mem_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact P.isProb.1 w hw
    · unfold total
      rw [expect_map]
      exact P.isProb.2

lemma lmap_mean {α β : Type} (P : FiniteLaw α) (g : α → β) (f : β → ℝ) :
    (lmap P g).mean f = P.mean (fun x => f (g x)) :=
  expect_map _ _ _

lemma lmap_atom {α β : Type} (P : FiniteLaw α) (g : α → β) (a : Fin (lmap P g).size) :
    ∃ a' : Fin P.size, (lmap P g).weight a = P.weight a' ∧ (lmap P g).atom a = g (P.atom a') := by
  refine ⟨⟨a.val, by simpa [FiniteLaw.size, lmap] using a.isLt⟩, ?_, ?_⟩
  · simp [FiniteLaw.weight, lmap]
  · simp [FiniteLaw.atom, lmap]

theorem prop_le_mu {n m : ℕ} (hn : 0 < n) (c : Cost n m) (i : Fin n) :
    propShare c i ≤ mu c i := by
  unfold mu costShare
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
    calc _ ≤ -∑ e ∈ univ.filter (fun g => f g = j), c i e :=
          ciInf_le (Set.finite_range _).bddBelow j
      _ ≤ _ := by linarith
  unfold propShare
  linarith

/-! ### More finite-law helpers: weights of outcomes -/
lemma expect_nonneg {α : Type*} (L : Law α) (hL : Positive L) (g : α → ℝ)
    (hg : ∀ x, 0 ≤ g x) : 0 ≤ expect L g := by
  induction L with
  | nil => simp
  | cons z L ih =>
    obtain ⟨p, a⟩ := z
    simp only [expect_cons]
    have hp : 0 ≤ p := hL _ List.mem_cons_self
    have := ih (fun w hw => hL w (List.mem_cons_of_mem _ hw))
    have := mul_nonneg hp (hg a)
    linarith

lemma expect_eq_zero {α : Type*} (L : Law α) (hL : Positive L) (g : α → ℝ)
    (hg : ∀ z ∈ L, 0 < z.1 → g z.2 = 0) : expect L g = 0 := by
  induction L with
  | nil => simp
  | cons z L ih =>
    obtain ⟨p, a⟩ := z
    simp only [expect_cons]
    have hp : 0 ≤ p := hL _ List.mem_cons_self
    rw [ih (fun w hw => hL w (List.mem_cons_of_mem _ hw))
      (fun w hw => hg w (List.mem_cons_of_mem _ hw))]
    rcases hp.lt_or_eq with h | h
    · rw [hg _ List.mem_cons_self h]; ring
    · rw [← h]; ring

/-- The total weight of the outcome `x`. -/
def wt {α : Type} [DecidableEq α] (P : FiniteLaw α) (x : α) : ℝ :=
  P.mean (fun y => if y = x then 1 else 0)

lemma wt_nonneg {α : Type} [DecidableEq α] (P : FiniteLaw α) (x : α) : 0 ≤ wt P x := by
  unfold wt FiniteLaw.mean
  exact expect_nonneg _ P.isProb.1 _ (fun y => by split_ifs <;> norm_num)

lemma wt_sum {α : Type} [DecidableEq α] [Fintype α] (P : FiniteLaw α) : ∑ x, wt P x = 1 := by
  unfold wt FiniteLaw.mean
  rw [← expect_sum]
  simp only [sum_ite_eq, mem_univ, if_true]
  exact P.isProb.2

lemma mean_eq_sum {α : Type} [DecidableEq α] [Fintype α] (P : FiniteLaw α) (f : α → ℝ) :
    P.mean f = ∑ x, wt P x * f x := by
  have hf : f = fun y => ∑ x, f x * (if y = x then (1 : ℝ) else 0) := by
    funext y; simp
  unfold wt FiniteLaw.mean
  conv_lhs => rw [hf]
  rw [expect_sum]
  apply sum_congr rfl
  intro x _
  rw [expect_const_mul, mul_comm]

lemma wt_pos {α : Type} [DecidableEq α] (P : FiniteLaw α) (x : α) (hx : 0 < wt P x) :
    ∃ a : Fin P.size, 0 < P.weight a ∧ P.atom a = x := by
  by_contra hcon
  push Not at hcon
  have : wt P x = 0 := by
    unfold wt FiniteLaw.mean
    apply expect_eq_zero _ P.isProb.1
    intro z hz hz1
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hz
    have := hcon ⟨i, hi⟩ hz1
    simp only [FiniteLaw.atom] at this
    simp [this]
  linarith

/-- The finite law with weights `w` on all outcomes. -/
def ofWeights {α : Type} [Fintype α] (w : α → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∑ x, w x = 1) : FiniteLaw α where
  toLaw := (Finset.univ.toList).map (fun x => (w x, x))
  isProb := by
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [List.mem_map] at hz
      obtain ⟨x, -, rfl⟩ := hz
      exact hw0 x
    · unfold total OAI.CliqueFreeIndependence.Lottery.expect
      rw [List.map_map]
      simp only [Function.comp_def, mul_one]
      rw [Finset.sum_map_toList]
      exact hw1

lemma ofWeights_mean {α : Type} [Fintype α] (w : α → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∑ x, w x = 1) (f : α → ℝ) : (ofWeights w hw0 hw1).mean f = ∑ x, w x * f x := by
  unfold ofWeights FiniteLaw.mean OAI.CliqueFreeIndependence.Lottery.expect
  simp only [List.map_map, Function.comp_def]
  rw [Finset.sum_map_toList]

lemma ofWeights_weight {α : Type} [Fintype α] (w : α → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∑ x, w x = 1) (a : Fin (ofWeights w hw0 hw1).size) :
    (ofWeights w hw0 hw1).weight a = w ((ofWeights w hw0 hw1).atom a) := by
  simp [FiniteLaw.weight, FiniteLaw.atom, ofWeights]

/-! ### Comparison of cost shares -/
lemma costShare_le {m m' n : ℕ} (hn : 0 < n) (u : Fin m → ℝ) (v : Fin m' → ℝ) (a D : ℝ)
    (ha : 0 ≤ a)
    (h : ∀ g : Fin m' → Fin n, ∃ f : Fin m → Fin n, ∀ j,
      ∑ e ∈ univ.filter (fun e => f e = j), u e ≤
        a * ∑ e ∈ univ.filter (fun e => g e = j), v e + D) :
    costShare u n ≤ a * costShare v n + D := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have key : a * (⨆ g : Fin m' → Fin n, ⨅ j : Fin n,
        -∑ e ∈ univ.filter (fun e => g e = j), v e) ≤
      (⨆ f : Fin m → Fin n, ⨅ j : Fin n, -∑ e ∈ univ.filter (fun e => f e = j), u e) + D := by
    rw [Real.mul_iSup_of_nonneg ha]
    apply ciSup_le
    intro g
    obtain ⟨f, hf⟩ := h g
    obtain ⟨j0, hj0⟩ := exists_eq_ciInf_of_finite
      (f := fun j : Fin n => -∑ e ∈ univ.filter (fun e => f e = j), u e)
    calc a * (⨅ j : Fin n, -∑ e ∈ univ.filter (fun e => g e = j), v e)
        ≤ a * (-∑ e ∈ univ.filter (fun e => g e = j0), v e) :=
          mul_le_mul_of_nonneg_left (ciInf_le (Set.finite_range _).bddBelow j0) ha
      _ ≤ -∑ e ∈ univ.filter (fun e => f e = j0), u e + D := by linarith [hf j0]
      _ = (⨅ j : Fin n, -∑ e ∈ univ.filter (fun e => f e = j), u e) + D := by rw [hj0]
      _ ≤ (⨆ f' : Fin m → Fin n, ⨅ j : Fin n,
            -∑ e ∈ univ.filter (fun e => f' e = j), u e) + D := by
          gcongr
          exact le_ciSup (f := fun f' : Fin m → Fin n => ⨅ j : Fin n,
            -∑ e ∈ univ.filter (fun e => f' e = j), u e) (Set.finite_range _).bddAbove f
  unfold costShare LittleCharity.MMS.mms
  linarith

lemma sum_le_add_card {m : ℕ} (u v : Fin m → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ e, u e ≤ v e + δ)
    (F : Finset (Fin m)) : ∑ e ∈ F, u e ≤ ∑ e ∈ F, v e + δ * m := by
  have hc : (F.card : ℝ) ≤ m := by
    have := card_le_univ F
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  calc ∑ e ∈ F, u e ≤ ∑ e ∈ F, (v e + δ) := sum_le_sum fun e _ => h e
    _ = ∑ e ∈ F, v e + F.card * δ := by rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    _ ≤ _ := by nlinarith

lemma costShare_add_le {m n : ℕ} (hn : 0 < n) (u v : Fin m → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ e, u e ≤ v e + δ) : costShare u n ≤ costShare v n + δ * m := by
  have := costShare_le hn u v 1 (δ * m) zero_le_one (fun g => ⟨g, fun j => by
    rw [one_mul]; exact sum_le_add_card u v δ hδ h _⟩)
  linarith

lemma costShare_smul {m n : ℕ} (hn : 0 < n) (u : Fin m → ℝ) (a : ℝ) (ha : 0 < a) :
    costShare (fun e => a * u e) n = a * costShare u n := by
  apply le_antisymm
  · have := costShare_le hn (fun e => a * u e) u a 0 ha.le (fun g => ⟨g, fun j => by
      rw [mul_sum, add_zero]⟩)
    linarith
  · have h1 := costShare_le hn u (fun e => a * u e) a⁻¹ 0 (inv_nonneg.2 ha.le) (fun g => ⟨g,
      fun j => by rw [mul_sum, add_zero]; apply le_of_eq; apply sum_congr rfl; intro e _
                  field_simp⟩)
    have h2 := mul_le_mul_of_nonneg_left h1 ha.le
    rw [add_zero, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at h2
    exact h2

/-! ### Scaling -/
lemma good_scale {n m : ℕ} (hn : 0 < n) {c c' : Cost n m} (s : Fin n → ℝ) (hs : ∀ i, 0 < s i)
    (hc : ∀ i e, c i e = s i * c' i e) {P : FiniteLaw (Allocation n m)} {B : ℝ}
    (h : Good c' P B) : Good c P B := by
  have hcost : ∀ i S, cost c i S = s i * cost c' i S := by
    intro i S
    show ∑ e ∈ S, c i e = s i * ∑ e ∈ S, c' i e
    rw [mul_sum]; exact sum_congr rfl (fun e _ => hc i e)
  have hmu : ∀ i, mu c i = s i * mu c' i := by
    intro i
    have : c i = fun e => s i * c' i e := funext (hc i)
    unfold mu; rw [this]; exact costShare_smul hn _ _ (hs i)
  have hprop : ∀ i, propShare c i = s i * propShare c' i := by
    intro i; unfold propShare; rw [hcost]; ring
  have hnon : ∀ X, nonMMS c X = nonMMS c' X := by
    intro X; unfold nonMMS; apply filter_congr; intro i _
    rw [hmu, hcost]; exact mul_lt_mul_iff_of_pos_left (hs i)
  refine ⟨fun i => ?_, fun a ha => ?_⟩
  · have := h.1 i
    unfold FiniteLaw.mean at this ⊢
    simp only [hcost, expect_const_mul, hprop]
    exact mul_le_mul_of_nonneg_left this (hs i).le
  · obtain ⟨h1, h2⟩ := h.2 a ha
    refine ⟨fun i => ?_, by rw [hnon]; exact h2⟩
    rcases h1 i with hE | ⟨e, he, hle⟩
    · exact Or.inl hE
    · exact Or.inr ⟨e, he, by rw [hcost, hmu]; exact mul_le_mul_of_nonneg_left hle (hs i).le⟩

/-! ### The limit argument -/
theorem limit_good {n m : ℕ} (hn : 0 < n) (d : Cost n m) (dk : ℕ → Cost n m) (δ : ℕ → ℝ)
    (hlo : ∀ k i e, d i e ≤ dk k i e) (hhi : ∀ k i e, dk k i e ≤ d i e + δ k)
    (hδ0 : ∀ k, 0 ≤ δ k) (hδ : Tendsto δ atTop (𝓝 0)) (B : ℝ)
    (hP : ∀ k, ∃ P : FiniteLaw (Allocation n m), Good (dk k) P B) :
    ∃ P : FiniteLaw (Allocation n m), Good d P B := by
  classical
  choose P hP using hP
  let W : ℕ → Allocation n m → ℝ := fun k => wt (P k)
  have hW : ∀ k, W k ∈ stdSimplex ℝ (Allocation n m) :=
    fun k => ⟨fun x => wt_nonneg _ _, wt_sum _⟩
  obtain ⟨w, hw, φ, hφ, hlim⟩ := (isCompact_stdSimplex ℝ (Allocation n m)).tendsto_subseq hW
  have hcoord : ∀ X, Tendsto (fun k => W (φ k) X) atTop (𝓝 (w X)) :=
    fun X => tendsto_pi_nhds.1 hlim X
  have hδφ : Tendsto (fun k => δ (φ k)) atTop (𝓝 0) := hδ.comp hφ.tendsto_atTop
  have hcost_lo : ∀ k i S, cost d i S ≤ cost (dk k) i S :=
    fun k i S => sum_le_sum fun e _ => hlo k i e
  have hcost_hi : ∀ k i S, cost (dk k) i S ≤ cost d i S + δ k * m :=
    fun k i S => sum_le_add_card _ _ _ (hδ0 k) (hhi k i) S
  have hmu_hi : ∀ k i, mu (dk k) i ≤ mu d i + δ k * m :=
    fun k i => costShare_add_le hn _ _ _ (hδ0 k) (hhi k i)
  have hmuT : ∀ i, Tendsto (fun k => mu d i + δ (φ k) * m) atTop (𝓝 (mu d i)) := by
    intro i
    have := (hδφ.mul_const (m : ℝ)).const_add (mu d i)
    simpa using this
  refine ⟨ofWeights w hw.1 hw.2, fun i => ?_, fun a ha => ?_⟩
  · rw [ofWeights_mean]
    have hle : ∀ k, ∑ X, W (φ k) X * cost d i (bundle X i) ≤
        (cost d i univ + δ (φ k) * m) / n := by
      intro k
      calc _ ≤ ∑ X, W (φ k) X * cost (dk (φ k)) i (bundle X i) :=
            sum_le_sum fun X _ => mul_le_mul_of_nonneg_left (hcost_lo _ _ _) (wt_nonneg _ _)
        _ = (P (φ k)).mean (fun X => cost (dk (φ k)) i (bundle X i)) := (mean_eq_sum _ _).symm
        _ ≤ propShare (dk (φ k)) i := (hP (φ k)).1 i
        _ ≤ _ := by
            unfold propShare
            exact div_le_div_of_nonneg_right (hcost_hi _ _ _) (Nat.cast_nonneg _)
    have hL : Tendsto (fun k => ∑ X, W (φ k) X * cost d i (bundle X i)) atTop
        (𝓝 (∑ X, w X * cost d i (bundle X i))) :=
      tendsto_finsetSum _ fun X _ => (hcoord X).mul_const _
    have hR : Tendsto (fun k => (cost d i univ + δ (φ k) * m) / n) atTop
        (𝓝 ((cost d i univ + 0 * m) / n)) :=
      ((hδφ.mul_const _).const_add _).div_const _
    have := le_of_tendsto_of_tendsto' hL hR hle
    simpa [propShare] using this
  · rw [ofWeights_weight] at ha
    set X := (ofWeights w hw.1 hw.2).atom a
    have hev : ∀ᶠ k in atTop, 0 < W (φ k) X := (hcoord X).eventually (lt_mem_nhds ha)
    have hgood : ∀ᶠ k in atTop, (∀ i, MMS1 (dk (φ k)) i (bundle X i)) ∧
        ((nonMMS (dk (φ k)) X).card : ℝ) ≤ B := by
      filter_upwards [hev] with k hk
      obtain ⟨a', ha', hX⟩ := wt_pos _ _ hk
      rw [← hX]; exact (hP (φ k)).2 a' ha'
    refine ⟨fun i => ?_, ?_⟩
    · by_contra hcon
      unfold MMS1 at hcon
      push Not at hcon
      obtain ⟨hne, hall⟩ := hcon
      have hev2 : ∀ᶠ k in atTop, ∀ e ∈ bundle X i,
          mu d i + δ (φ k) * m < cost d i ((bundle X i).erase e) := by
        rw [Filter.eventually_all_finset]
        intro e he
        exact (hmuT i).eventually (gt_mem_nhds (hall e he))
      obtain ⟨k, hk1, hk2⟩ := (hgood.and hev2).exists
      rcases hk1.1 i with hE | ⟨e, he, hle⟩
      · exact hne.ne_empty hE
      · have := hk2 e he
        have h1 := hcost_lo (φ k) i ((bundle X i).erase e)
        have h2 := hmu_hi (φ k) i
        linarith
    · have hev3 : ∀ᶠ k in atTop, nonMMS d X ⊆ nonMMS (dk (φ k)) X := by
        have : ∀ i, ∀ᶠ k in atTop, i ∈ nonMMS d X → i ∈ nonMMS (dk (φ k)) X := by
          intro i
          by_cases hi : i ∈ nonMMS d X
          · have hi' : mu d i < cost d i (bundle X i) := by simpa [nonMMS] using hi
            filter_upwards [(hmuT i).eventually (gt_mem_nhds hi')] with k hk _
            simp only [nonMMS, mem_filter, mem_univ, true_and]
            linarith [hmu_hi (φ k) i, hcost_lo (φ k) i (bundle X i)]
          · exact Eventually.of_forall (fun k h => absurd h hi)
        filter_upwards [Filter.eventually_all.2 this] with k hk i hi using hk i hi
      obtain ⟨k, hk1, hk2⟩ := (hgood.and hev3).exists
      exact le_trans (by exact_mod_cast card_le_card hk2) hk1.2

/-! ### Perturbation: nonnegative IDO instances from normalized ones -/
/-- The perturbed costs `d i e + (m - e) / (k + 1)`. -/
def pert {n m : ℕ} (d : Cost n m) (k : ℕ) : Cost n m :=
  fun i e => d i e + 1 / ((k : ℝ) + 1) * ((m : ℝ) - e.val)

theorem perturb {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (B : ℝ)
    (hN : ∀ c : Cost n m, Normalized c → ∃ P : FiniteLaw (Allocation n m), Good c P B)
    (d : Cost n m) (h0 : Nonnegative d) (hI : IDO d) :
    ∃ P : FiniteLaw (Allocation n m), Good d P B := by
  have hε : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hgap : ∀ e : Fin m, (0 : ℝ) < (m : ℝ) - e.val := fun e => by
    have := e.isLt; rw [sub_pos]; exact_mod_cast this
  apply limit_good hn d (pert d) (fun k => 1 / ((k : ℝ) + 1) * m) ?_ ?_ ?_ ?_ B ?_
  · intro k i e
    have := mul_pos (hε k) (hgap e)
    simp only [pert]; linarith
  · intro k i e
    simp only [pert]
    have : 1 / ((k : ℝ) + 1) * ((m : ℝ) - e.val) ≤ 1 / ((k : ℝ) + 1) * m :=
      mul_le_mul_of_nonneg_left (by have := e.val.cast_nonneg (α := ℝ); linarith) (hε k).le
    linarith
  · intro k; exact mul_nonneg (hε k).le (Nat.cast_nonneg _)
  · have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (m : ℝ)
    simpa using this
  · intro k
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hpos : ∀ i e, 0 < pert d k i e := fun i e =>
      add_pos_of_nonneg_of_pos (h0 i e) (mul_pos (hε k) (hgap e))
    have hmu : ∀ i, 0 < mu (pert d k) i := fun i => by
      refine lt_of_lt_of_le ?_ (prop_le_mu hn _ i)
      unfold propShare
      exact div_pos (sum_pos (fun e _ => hpos i e) univ_nonempty) (Nat.cast_pos.2 hn)
    let c : Cost n m := fun i e => (mu (pert d k) i)⁻¹ * pert d k i e
    have hc : Normalized c := by
      refine ⟨fun i e => mul_pos (inv_pos.2 (hmu i)) (hpos i e), fun i => ?_, fun i => ?_⟩
      · intro a b hab
        apply mul_lt_mul_of_pos_left _ (inv_pos.2 (hmu i))
        simp only [pert]
        have h1 := hI i hab.le
        have h2 : (a.val : ℝ) < b.val := by exact_mod_cast hab
        have h3 := mul_lt_mul_of_pos_left (show (m : ℝ) - b.val < (m : ℝ) - a.val by linarith)
          (hε k)
        linarith
      · show costShare (fun e => (mu (pert d k) i)⁻¹ * pert d k i e) n = 1
        rw [costShare_smul hn _ _ (inv_pos.2 (hmu i))]
        exact inv_mul_cancel₀ (hmu i).ne'
    obtain ⟨P, hP⟩ := hN c hc
    refine ⟨P, good_scale hn (fun i => mu (pert d k) i) hmu (fun i e => ?_) hP⟩
    show _ = _ * (_⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ (hmu i).ne', one_mul]

/-! ### Padding with zero-cost chores -/
/-- Pad an instance with zero-cost chores at the end. -/
def pad {n m m' : ℕ} (c : Cost n m) : Cost n m' :=
  fun i e => if h : e.val < m then c i ⟨e.val, h⟩ else 0

lemma pad_nonneg {n m m' : ℕ} {c : Cost n m} (h0 : Nonnegative c) :
    Nonnegative (pad c : Cost n m') := by
  intro i e
  unfold pad
  split_ifs
  · exact h0 _ _
  · exact le_rfl

lemma pad_ido {n m m' : ℕ} {c : Cost n m} (h0 : Nonnegative c) (hI : IDO c) :
    IDO (pad c : Cost n m') := by
  intro i a b hab
  have hab' : a.val ≤ b.val := hab
  unfold pad
  by_cases hb : b.val < m
  · have ha : a.val < m := lt_of_le_of_lt hab' hb
    rw [dif_pos hb, dif_pos ha]
    exact hI i (show (⟨a.val, ha⟩ : Fin m) ≤ ⟨b.val, hb⟩ from hab')
  · rw [dif_neg hb]
    split_ifs
    · exact h0 _ _
    · exact le_rfl

lemma sum_pad {n m m' : ℕ} (hm : m ≤ m') (c : Cost n m) (i : Fin n) (S : Finset (Fin m')) :
    ∑ e ∈ S, (pad c : Cost n m') i e =
      ∑ e ∈ S.preimage (Fin.castLE hm) (Fin.castLE_injective hm).injOn, c i e := by
  rw [← Finset.sum_preimage (Fin.castLE hm) S (Fin.castLE_injective hm).injOn
    ((pad c : Cost n m') i)]
  · apply sum_congr rfl
    intro e _
    simp [pad]
  · intro x _ hx
    unfold pad
    rw [dif_neg]
    intro h
    exact hx ⟨⟨x.val, h⟩, Fin.ext rfl⟩

/-- Restrict an allocation to the first `m` chores. -/
def restr {n m m' : ℕ} (hm : m ≤ m') (X : Allocation n m') : Allocation n m :=
  fun e => X (Fin.castLE hm e)

lemma bundle_restr {n m m' : ℕ} (hm : m ≤ m') (X : Allocation n m') (i : Fin n) :
    bundle (restr hm X) i =
      (bundle X i).preimage (Fin.castLE hm) (Fin.castLE_injective hm).injOn := by
  ext e
  simp only [bundle, ChoresEFX.bundle, mem_preimage, mem_filter, mem_univ, true_and]
  rfl

lemma mu_pad {n m m' : ℕ} (hn : 0 < n) (hm : m ≤ m') (c : Cost n m) (i : Fin n) :
    mu (pad c : Cost n m') i = mu c i := by
  unfold mu
  apply le_antisymm
  · have := costShare_le hn ((pad c : Cost n m') i) (c i) 1 0 zero_le_one (fun g => by
      refine ⟨fun e => if h : e.val < m then g ⟨e.val, h⟩ else ⟨0, hn⟩, fun j => ?_⟩
      rw [sum_pad hm, one_mul, add_zero]
      apply le_of_eq
      apply sum_congr _ (fun _ _ => rfl)
      ext e
      simp)
    linarith
  · have := costShare_le hn (c i) ((pad c : Cost n m') i) 1 0 zero_le_one (fun g => by
      refine ⟨fun e => g (Fin.castLE hm e), fun j => ?_⟩
      rw [sum_pad hm, one_mul, add_zero]
      apply le_of_eq
      apply sum_congr _ (fun _ _ => rfl)
      ext e
      simp)
    linarith

lemma good_pad {n m m' : ℕ} (hn : 0 < n) (hm : m ≤ m') (c : Cost n m) (h0 : Nonnegative c)
    {P : FiniteLaw (Allocation n m')} {B : ℝ} (h : Good (pad c : Cost n m') P B) :
    Good c (lmap P (restr hm)) B := by
  have hcost : ∀ i (S : Finset (Fin m')), cost (pad c : Cost n m') i S =
      cost c i (S.preimage (Fin.castLE hm) (Fin.castLE_injective hm).injOn) :=
    fun i S => sum_pad hm c i S
  have hcb : ∀ i X, cost c i (bundle (restr hm X) i) = cost (pad c : Cost n m') i (bundle X i) :=
    fun i X => by rw [hcost, bundle_restr]
  have hprop : ∀ i, propShare (pad c : Cost n m') i = propShare c i := by
    intro i; unfold propShare; rw [hcost, preimage_univ]
  have hnon : ∀ X, nonMMS c (restr hm X) = nonMMS (pad c : Cost n m') X := by
    intro X; unfold nonMMS; apply filter_congr; intro i _
    rw [hcb, mu_pad hn hm]
  refine ⟨fun i => ?_, fun a ha => ?_⟩
  · rw [lmap_mean]
    simp only [hcb, ← hprop]
    exact h.1 i
  · obtain ⟨a', hw, hat⟩ := lmap_atom P (restr hm) a
    rw [hw] at ha
    obtain ⟨h1, h2⟩ := h.2 a' ha
    rw [hat]
    refine ⟨fun i => ?_, by rw [hnon]; exact h2⟩
    set X := P.atom a'
    set T := bundle (restr hm X) i with hT
    rcases T.eq_empty_or_nonempty with hE | ⟨e1, he1⟩
    · exact Or.inl hE
    right
    rcases h1 i with hE | ⟨e, he, hle⟩
    · exfalso
      rw [hT, bundle_restr, hE] at he1
      simp at he1
    rw [← mu_pad hn hm c i]
    have hle' : cost c i ((bundle X i).erase e |>.preimage (Fin.castLE hm)
        (Fin.castLE_injective hm).injOn) ≤ mu (pad c : Cost n m') i := by
      rw [← hcost]; exact hle
    by_cases hr : e.val < m
    · refine ⟨⟨e.val, hr⟩, ?_, le_trans (le_of_eq ?_) hle'⟩
      · rw [hT, bundle_restr, mem_preimage]; exact he
      · congr 1
        rw [hT, bundle_restr]
        ext x
        simp only [mem_erase, mem_preimage, ne_eq]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨fun h => h1 (Fin.ext (by have := congrArg Fin.val h; exact this)), h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨fun h => h1 (Fin.ext (by simp [h])), h2⟩
    · refine ⟨e1, he1, le_trans ?_ hle'⟩
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        have hx' := mem_of_mem_erase hx
        rw [hT, bundle_restr, mem_preimage] at hx'
        rw [mem_preimage, mem_erase]
        refine ⟨fun h => hr ?_, hx'⟩
        rw [← h]; exact x.isLt
      · intro x _ _; exact h0 i x

/-! ### Part N -/
theorem large_case : ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n → ∀ m : ℕ,
    ∀ c : Cost n m, Nonnegative c → IDO c →
    ∃ P : FiniteLaw (Allocation n m), Good c P (C₀ * rate n) := by
  obtain ⟨C₀, hC₀, n₀, hN⟩ := norm_case
  refine ⟨C₀, hC₀, n₀, fun n hn0 hn m c h0 hI => ?_⟩
  have hq : 0 < blockSize n := by unfold blockSize; positivity
  have hmm : m ≤ blockSize n * (m / blockSize n + 1) := (Nat.lt_mul_div_succ m hq).le
  have hqm : blockSize n ≤ blockSize n * (m / blockSize n + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  obtain ⟨P, hP⟩ := perturb hn (lt_of_lt_of_le hq hqm) _
    (hN n hn0 _ hqm (dvd_mul_right _ _)) (pad c) (pad_nonneg h0) (pad_ido h0 hI)
  exact ⟨_, good_pad hn hmm c h0 hP⟩

end SublinearChoresMMS.Disposal.Dev.T11.PartN
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.T11
open SublinearChoresMMS.Disposal
open Finset
/-! ### Part N: from normalized to arbitrary nonnegative IDO instances (pad, perturb, scale, limit) -/
alias large_case := SublinearChoresMMS.Disposal.Dev.T11.PartN.large_case

end SublinearChoresMMS.Disposal.Dev.T11
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.T11.PartST
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.T11
open Finset
open OAI.CliqueFreeIndependence.Lottery
/-! ### Part T -/
lemma rate_ge {n : ℕ} (hn : 0 < n) : (Real.log 2) ^ (1 / 4 : ℝ) ≤ rate n := by
  unfold rate
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log (2 * n) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h2 : (Real.log 2) ^ (1 / 4 : ℝ) ≤ (Real.log (2 * n)) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hl2.le hl (by norm_num)
  have h3 : 0 ≤ (Real.log 2) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hl2.le _
  nlinarith

lemma rate_nonneg (n : ℕ) (hn : 0 < n) : 0 ≤ rate n :=
  le_trans (Real.rpow_nonneg (Real.log_pos (by norm_num : (1:ℝ) < 2)).le _) (rate_ge hn)

theorem ido_case : ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ), 0 < n → ∀ c : Cost n m,
    Nonnegative c → IDO c → ∃ P : FiniteLaw (Allocation n m), Good c P (C * rate n) := by
  obtain ⟨C₀, hC₀, n₀, hL⟩ := large_case
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set ℓ := (Real.log 2) ^ (1 / 4 : ℝ) with hℓ
  have hℓpos : 0 < ℓ := Real.rpow_pos_of_pos hl2 _
  have hq : 0 ≤ (n₀ : ℝ) / ℓ := by positivity
  refine ⟨C₀ + n₀ / ℓ + 1, by linarith, fun n m hn c h0 hI => ?_⟩
  have hr := rate_nonneg n hn
  by_cases hle : n₀ ≤ n
  · obtain ⟨P, hP⟩ := hL n hle hn m c h0 hI
    exact ⟨P, good_mono hP (mul_le_mul_of_nonneg_right (by linarith) hr)⟩
  · obtain ⟨P, hP⟩ := small_case hn c h0 hI
    refine ⟨P, good_mono hP ?_⟩
    have hnn : (n : ℝ) ≤ n₀ := by exact_mod_cast (not_le.mp hle).le
    have hrg := rate_ge hn
    have : (n₀ : ℝ) / ℓ * ℓ = n₀ := by field_simp
    have h4 : (n₀ : ℝ) / ℓ * ℓ ≤ (n₀ : ℝ) / ℓ * rate n := mul_le_mul_of_nonneg_left hrg hq
    nlinarith

end SublinearChoresMMS.Disposal.Dev.T11.PartST
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.T11
open SublinearChoresMMS.Disposal
open Finset
/-! ### Part T: all IDO instances, then the IDO reduction (Lemma 2.2) -/

end SublinearChoresMMS.Disposal.Dev.T11
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.T11.PartST
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.T11
open Finset
open OAI.CliqueFreeIndependence.Lottery
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ), 0 < n → ∀ c : Cost n m,
      Nonnegative c → ∃ P : FiniteLaw (Allocation n m),
        (∀ i, P.mean (fun X => cost c i (bundle X i)) ≤ propShare c i) ∧
        ∀ a : Fin P.size, 0 < P.weight a →
          (∀ i, MMS1 c i (bundle (P.atom a) i)) ∧
          ((nonMMS c (P.atom a)).card : ℝ) ≤
            C * (n : ℝ) ^ (3 / 4 : ℝ) * (Real.log (2 * (n : ℝ))) ^ (1 / 4 : ℝ) := by
  obtain ⟨C, hC, hido⟩ := ido_case
  refine ⟨C, hC, fun n m hn c hc => ?_⟩
  obtain ⟨d, rowPerm, hdI, hd, hmu, htr⟩ := SublinearChoresMMS.Disposal.lemma_2_2 hn c hc
  have hd0 : Nonnegative d := fun i r => by rw [hd]; exact hc _ _
  obtain ⟨P, hPa, hPb⟩ := hido n m hn d hd0 hdI
  have hprop : ∀ i, propShare d i = propShare c i := fun i => by
    unfold propShare; rw [(hmu i).2]
  let τ : Allocation n m → Equiv.Perm (Fin m) := fun X => Classical.choose (htr X)
  have hτ : ∀ X, (∀ r, c (X r) (τ X r) ≤ d (X r) r) ∧
      ∀ i, cost c i (bundle (fun e => X ((τ X).symm e)) i) ≤ cost d i (bundle X i) :=
    fun X => Classical.choose_spec (htr X)
  let g : Allocation n m → Allocation n m := fun X e => X ((τ X).symm e)
  refine ⟨lmap P g, fun i => ?_, fun a ha => ?_⟩
  · rw [lmap_mean]
    calc P.mean (fun X => cost c i (bundle (g X) i))
        ≤ P.mean (fun X => cost d i (bundle X i)) :=
          expect_mono _ P.isProb.1 _ _ (fun X => (hτ X).2 i)
      _ ≤ propShare d i := hPa i
      _ = propShare c i := hprop i
  · obtain ⟨a', hw, hat⟩ := lmap_atom P g a
    rw [hw] at ha
    obtain ⟨hMMS, hcard⟩ := hPb a' ha
    rw [hat]
    set X := P.atom a'
    have hmemX' : ∀ i e, e ∈ bundle (g X) i ↔ X ((τ X).symm e) = i := fun i e => by
      simp [bundle, ChoresEFX.bundle, g]
    have hmemX : ∀ i e, e ∈ bundle X i ↔ X e = i := fun i e => by
      simp [bundle, ChoresEFX.bundle]
    refine ⟨fun i => ?_, ?_⟩
    · rcases hMMS i with hE | ⟨e, he, hle⟩
      · left
        apply eq_empty_of_forall_notMem
        intro e he
        rw [hmemX'] at he
        have : (τ X).symm e ∈ bundle X i := (hmemX i _).2 he
        rw [hE] at this
        exact notMem_empty _ this
      · right
        refine ⟨τ X e, (hmemX' i _).2 (by simpa using (hmemX i e).1 he), ?_⟩
        have hset : (bundle (g X) i).erase (τ X e) = ((bundle X i).erase e).map (τ X).toEmbedding := by
          ext x
          rw [mem_erase, Finset.mem_map_equiv, mem_erase, hmemX', hmemX]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨fun h => h1 ?_, h2⟩
            rw [← h]; simp
          · rintro ⟨h1, h2⟩
            refine ⟨fun h => h1 ?_, h2⟩
            rw [h]; simp
        have : cost c i ((bundle (g X) i).erase (τ X e)) ≤ cost d i ((bundle X i).erase e) := by
          rw [hset]
          show ∑ x ∈ ((bundle X i).erase e).map (τ X).toEmbedding, c i x ≤
            ∑ r ∈ (bundle X i).erase e, d i r
          rw [sum_map]
          apply sum_le_sum
          intro r hr
          have hXr : X r = i := (hmemX i r).1 (mem_of_mem_erase hr)
          have := (hτ X).1 r
          rw [hXr] at this
          exact this
        rw [← (hmu i).1]
        exact this.trans hle
    · have hsub : nonMMS c (g X) ⊆ nonMMS d X := by
        intro i hi
        simp only [nonMMS, mem_filter, mem_univ, true_and] at hi ⊢
        rw [(hmu i).1]
        exact lt_of_lt_of_le hi ((hτ X).2 i)
      have h1 : ((nonMMS c (g X)).card : ℝ) ≤ (nonMMS d X).card := by
        exact_mod_cast card_le_card hsub
      refine h1.trans (hcard.trans (le_of_eq ?_))
      unfold rate; ring

end SublinearChoresMMS.Disposal.Dev.T11.PartST
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.T11
open SublinearChoresMMS.Disposal
open Finset
alias theorem_1_1 := SublinearChoresMMS.Disposal.Dev.T11.PartST.theorem_1_1

end SublinearChoresMMS.Disposal.Dev.T11
end
end

section
noncomputable section
open SublinearChoresMMS
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev
open SublinearChoresMMS.Disposal.Dev.T11
open SublinearChoresMMS.Disposal
open Finset
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ), 0 < n → ∀ c : Cost n m,
      Nonnegative c → ∃ P : FiniteLaw (Allocation n m),
        (∀ i, P.mean (fun X => cost c i (bundle X i)) ≤ propShare c i) ∧
        ∀ a : Fin P.size, 0 < P.weight a →
          (∀ i, MMS1 c i (bundle (P.atom a) i)) ∧
          ((nonMMS c (P.atom a)).card : ℝ) ≤
            C * (n : ℝ) ^ (3 / 4 : ℝ) * (Real.log (2 * (n : ℝ))) ^ (1 / 4 : ℝ) := by
  exact SublinearChoresMMS.Disposal.Dev.T11.theorem_1_1
end
end
