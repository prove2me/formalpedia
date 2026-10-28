-- Prove2me | solution 1 for StickyKakeya4.compact_full_direction_borel_selector
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T18:31:40.816337+00:00
-- url     : https://prove2.me/submissions/b01620f7-3c15-4939-bd43-42b59e7af787

import Mathlib
import Definitions.Def_sticky_kakeya4_core

namespace S100Kak
open StickyKakeya4 MeasureTheory Set

noncomputable def d (k : ℕ) (ℓ : MarkedLine) : ℝ :=
  if h : k < 4 then ℓ.1.2 ⟨k, h⟩ else if k = 4 then ℓ.2 else 0

lemma d_cont (k : ℕ) : Continuous (d k) := by
  unfold d
  split_ifs with h
  · exact (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) ⟨k, h⟩).comp
      (continuous_snd.comp continuous_fst)
  · exact continuous_snd
  · exact continuous_const

lemma d_ge (k : ℕ) (hk : 5 ≤ k) (ℓ : MarkedLine) : d k ℓ = 0 := by
  unfold d; rw [dif_neg (by omega), if_neg (by omega)]

lemma dir_cont : Continuous (direction : MarkedLine → E4) :=
  continuous_fst.comp continuous_fst

lemma d_inj (ℓ ℓ' : MarkedLine) (hdir : direction ℓ = direction ℓ')
    (h : ∀ k < 5, d k ℓ = d k ℓ') : ℓ = ℓ' := by
  obtain ⟨⟨a, b⟩, m⟩ := ℓ
  obtain ⟨⟨a', b'⟩, m'⟩ := ℓ'
  simp only [direction] at hdir
  have hb : b = b' := by
    ext i
    have := h i.val (by omega)
    simpa [d, i.isLt] using this
  have hm : m = m' := by simpa [d] using h 4 (by norm_num)
  subst hdir hb hm; rfl

def LexLt (ℓ' ℓ : MarkedLine) : Prop :=
  ∃ k, (∀ j < k, d j ℓ' = d j ℓ) ∧ d k ℓ' < d k ℓ

def Sel (lines : Set MarkedLine) : Set MarkedLine :=
  {ℓ | ℓ ∈ lines ∧ ∀ ℓ' ∈ lines, direction ℓ' = direction ℓ → ¬ LexLt ℓ' ℓ}

lemma lex_total (ℓ ℓ' : MarkedLine) (hdir : direction ℓ = direction ℓ') (hne : ℓ ≠ ℓ') :
    LexLt ℓ ℓ' ∨ LexLt ℓ' ℓ := by
  classical
  have hex : ∃ k, d k ℓ ≠ d k ℓ' := by
    by_contra hc
    push Not at hc
    exact hne (d_inj ℓ ℓ' hdir (fun k _ => hc k))
  have hk : d (Nat.find hex) ℓ ≠ d (Nat.find hex) ℓ' := Nat.find_spec hex
  have hlt : ∀ j < Nat.find hex, d j ℓ = d j ℓ' := fun j hj => by
    by_contra hc; exact Nat.find_min hex hj hc
  rcases lt_or_gt_of_ne hk with h | h
  · exact Or.inl ⟨_, hlt, h⟩
  · exact Or.inr ⟨_, fun j hj => (hlt j hj).symm, h⟩

noncomputable def F (K : Set MarkedLine) : ℕ → Set MarkedLine
  | 0 => K
  | k + 1 => {ℓ | ℓ ∈ F K k ∧ ∀ ℓ' ∈ F K k, d k ℓ ≤ d k ℓ'}

lemma F_cpt (K : Set MarkedLine) (hK : IsCompact K) (hne : K.Nonempty) :
    ∀ k, IsCompact (F K k) ∧ (F K k).Nonempty
  | 0 => ⟨hK, hne⟩
  | k + 1 => by
    obtain ⟨hc, hn⟩ := F_cpt K hK hne k
    refine ⟨?_, ?_⟩
    · have : F K (k+1) = F K k ∩ ⋂ ℓ' ∈ F K k, {ℓ | d k ℓ ≤ d k ℓ'} := by
        ext ℓ; simp [F]
      rw [this]
      exact hc.inter_right (isClosed_biInter fun ℓ' _ => isClosed_le (d_cont k) continuous_const)
    · obtain ⟨x, hx, hmin⟩ := hc.exists_isMinOn hn (d_cont k).continuousOn
      exact ⟨x, hx, fun ℓ' h' => hmin h'⟩

lemma F_anti (K : Set MarkedLine) (n m : ℕ) (h : n ≤ m) : F K m ⊆ F K n := by
  induction m, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact fun ℓ hℓ => ih hℓ.1

lemma F_char (K : Set MarkedLine) : ∀ k, ∀ ℓ ∈ F K k, ∀ ℓ',
    ℓ' ∈ F K k ↔ (ℓ' ∈ K ∧ ∀ j < k, d j ℓ' = d j ℓ)
  | 0 => by intro ℓ _ ℓ'; simp [F]
  | k + 1 => by
    intro ℓ hℓ ℓ'
    have IH := F_char K k ℓ hℓ.1 ℓ'
    constructor
    · intro h'
      obtain ⟨hK, hj⟩ := IH.1 h'.1
      refine ⟨hK, fun j hj' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with h | h
      · exact hj j h
      · subst h; exact le_antisymm (h'.2 ℓ hℓ.1) (hℓ.2 ℓ' h'.1)
    · rintro ⟨hK, hj⟩
      have h1 : ℓ' ∈ F K k := IH.2 ⟨hK, fun j hj' => hj j (by omega)⟩
      refine ⟨h1, fun ℓ'' h'' => ?_⟩
      rw [hj k (by omega)]
      exact hℓ.2 ℓ'' h''

lemma exists_min (K : Set MarkedLine) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ ℓ ∈ K, ∀ ℓ' ∈ K, ¬ LexLt ℓ' ℓ := by
  obtain ⟨-, ℓ, hℓ⟩ := F_cpt K hK hne 5
  refine ⟨ℓ, F_anti K 0 5 (by norm_num) hℓ, ?_⟩
  rintro ℓ' hK' ⟨i, hi, hlt⟩
  by_cases h5 : i < 5
  · have hℓi : ℓ ∈ F K (i+1) := F_anti K (i+1) 5 (by omega) hℓ
    have : ℓ' ∈ F K i := (F_char K i ℓ hℓi.1 ℓ').2 ⟨hK', hi⟩
    exact absurd (hℓi.2 ℓ' this) (not_le.2 hlt)
  · rw [d_ge i (by omega), d_ge i (by omega)] at hlt; exact lt_irrefl _ hlt

lemma sel_spec (lines : Set MarkedLine) (hcompact : IsCompact lines)
    (hfull : FullDirection lines) : IsDirectionSelector (Sel lines) := by
  intro θ hθ
  obtain ⟨ℓ0, h0, hd0⟩ := hfull θ hθ
  have hK : IsCompact (lines ∩ {ℓ | direction ℓ = θ}) :=
    hcompact.inter_right (isClosed_eq dir_cont continuous_const)
  obtain ⟨ℓ, ⟨hl, hd⟩, hmin⟩ := exists_min _ hK ⟨ℓ0, h0, hd0⟩
  refine ⟨ℓ, ⟨⟨hl, fun ℓ' h' hd' => hmin ℓ' ⟨h', hd'.trans hd⟩⟩, hd⟩, ?_⟩
  rintro y ⟨⟨hy, hymin⟩, hyd⟩
  by_contra hne
  rcases lex_total y ℓ (hyd.trans hd.symm) hne with h | h
  · exact hmin y ⟨hy, hyd⟩ h
  · exact hymin ℓ hl (hd.trans hyd.symm) h

noncomputable def p (k : ℕ) (ℓ : MarkedLine) : E4 × (Fin k → ℝ) := (direction ℓ, fun j => d j ℓ)

lemma p_cont (k : ℕ) : Continuous (p k) :=
  dir_cont.prodMk (continuous_pi fun j => d_cont j)

lemma p_eq (k : ℕ) (ℓ ℓ' : MarkedLine) :
    p k ℓ' = p k ℓ ↔ direction ℓ' = direction ℓ ∧ ∀ j < k, d j ℓ' = d j ℓ := by
  simp only [p, Prod.mk.injEq, funext_iff, Fin.forall_iff]

def Bad (lines : Set MarkedLine) (k : ℕ) (r : ℚ) : Set MarkedLine :=
  p k ⁻¹' (p k '' (lines ∩ {ℓ | d k ℓ ≤ r})) ∩ {ℓ | (r : ℝ) < d k ℓ}

lemma sel_eq (lines : Set MarkedLine) :
    Sel lines = lines ∩ ⋂ k : ℕ, ⋂ r : ℚ, (Bad lines k r)ᶜ := by
  ext ℓ
  simp only [Sel, Bad, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_compl_iff,
    mem_preimage, mem_image]
  constructor
  · rintro ⟨hl, hmin⟩
    refine ⟨hl, fun k r ⟨⟨ℓ', ⟨h', hr⟩, hp⟩, hr2⟩ => ?_⟩
    obtain ⟨hd, hj⟩ := (p_eq k ℓ ℓ').1 hp
    exact hmin ℓ' h' hd ⟨k, hj, lt_of_le_of_lt hr hr2⟩
  · rintro ⟨hl, hbad⟩
    refine ⟨hl, fun ℓ' h' hd ⟨k, hj, hlt⟩ => ?_⟩
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
    exact hbad k r ⟨⟨ℓ', ⟨h', hr1.le⟩, (p_eq k ℓ ℓ').2 ⟨hd, hj⟩⟩, hr2⟩

lemma sel_meas (lines : Set MarkedLine) (hcompact : IsCompact lines) :
    MeasurableSet (Sel lines) := by
  rw [sel_eq]
  refine hcompact.isClosed.measurableSet.inter
    (MeasurableSet.iInter fun k => MeasurableSet.iInter fun r => MeasurableSet.compl ?_)
  refine MeasurableSet.inter ?_ (isOpen_lt continuous_const (d_cont k)).measurableSet
  exact (((hcompact.inter_right (isClosed_le (d_cont k) continuous_const)).image
    (p_cont k)).isClosed.preimage (p_cont k)).measurableSet

end S100Kak

open StickyKakeya4 MeasureTheory Set in
theorem solution (lines : Set MarkedLine)
    (hcompact : IsCompact lines) (hfull : FullDirection lines) :
    ∃ selector : Set MarkedLine,
      MeasurableSet selector ∧ selector ⊆ lines ∧
      IsDirectionSelector selector :=
  ⟨S100Kak.Sel lines, S100Kak.sel_meas lines hcompact, fun _ h => h.1,
    S100Kak.sel_spec lines hcompact hfull⟩
