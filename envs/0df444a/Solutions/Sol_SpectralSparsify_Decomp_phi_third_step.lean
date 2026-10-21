-- Prove2me | solution 1 for SpectralSparsify.Decomp.phi_third_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:50:12.868722+00:00
-- url     : https://prove2.me/submissions/80c9c16d-2498-4ed3-b55f-a0c0ca9a45ee

import Mathlib
import Definitions.Def_SpectralSparsify_Decomp_vol
import Definitions.Def_SpectralSparsify_Decomp_cutEdges
import Definitions.Def_SpectralSparsify_Decomp_cond

set_option autoImplicit false
open SpectralSparsify.Decomp

section aux
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma aux_vol_nonneg (T : Finset V) : 0 ≤ vol G T :=
  Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)

lemma aux_vol_pos (hdeg : ∀ v, 0 < G.degree v) (T : Finset V) (hT : T.Nonempty) :
    0 < vol G T :=
  Finset.sum_pos (fun i _ => by exact_mod_cast hdeg i) hT

lemma aux_vol_sdiff {B S : Finset V} (h : S ⊆ B) : vol G (B \ S) = vol G B - vol G S := by
  unfold vol
  have := Finset.sum_sdiff (f := fun i => (G.degree i : ℝ)) h
  linarith

lemma aux_vol_union {R S : Finset V} (h : Disjoint R S) :
    vol G (R ∪ S) = vol G R + vol G S := by
  unfold vol
  rw [Finset.sum_union h]

lemma aux_cut_symm (X Y : Finset V) : cutEdges G X Y = cutEdges G Y X := by
  unfold cutEdges
  apply Finset.card_bij (fun p _ => (p.2, p.1))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩
  · intro p _ q _ h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext h2 h1
  · intro q hq
    refine ⟨(q.2, q.1), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product] at hq ⊢
    exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2.symm⟩

lemma aux_cut_union (B S R : Finset V) :
    cutEdges G (R ∪ S) ((B \ S) \ R) ≤ cutEdges G S (B \ S) + cutEdges G R ((B \ S) \ R) := by
  unfold cutEdges
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union, Finset.mem_sdiff] at hp ⊢
  obtain ⟨⟨hu, hv⟩, hadj⟩ := hp
  by_cases hs : p.1 ∈ S
  · left
    refine ⟨⟨hs, ?_⟩, hadj⟩
    tauto
  · right
    have hr : p.1 ∈ R := by
      rcases hu with h | h
      · exact h
      · exact absurd h hs
    exact ⟨⟨hr, hv⟩, hadj⟩

lemma aux_condRel_nonneg (B S : Finset V) : 0 ≤ condRel G B S := by
  unfold condRel
  split_ifs
  · norm_num
  · exact div_nonneg (Nat.cast_nonneg _) (le_min (aux_vol_nonneg G _) (aux_vol_nonneg G _))

lemma aux_le_cond {B : Finset V} (c : ℝ) (h1 : c ≤ 1) (h2 : ∀ R, R ⊂ B → c ≤ condRel G B R) :
    c ≤ cond G B := by
  unfold SpectralSparsify.Decomp.cond
  split_ifs with h
  · exact h1
  · apply Finset.le_inf'
    intro R hR
    exact h2 R (Finset.mem_filter.mp hR).2

lemma aux_cond_nonneg (B : Finset V) : 0 ≤ cond G B :=
  aux_le_cond G 0 (by norm_num) (fun R _ => aux_condRel_nonneg G B R)

lemma aux_condRel_swap {B R : Finset V} (hR : R ⊆ B) (hR1 : R.Nonempty) (hR2 : (B \ R).Nonempty) :
    condRel G B (B \ R) = condRel G B R := by
  unfold condRel
  rw [if_neg (Finset.nonempty_iff_ne_empty.mp hR2), if_neg (Finset.nonempty_iff_ne_empty.mp hR1),
    Finset.sdiff_sdiff_eq_self hR, aux_cut_symm, min_comm]

end aux

theorem lemma72_aux {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v) (φ : ℝ) (hφ : φ ≤ 1)
    (B S : Finset V) (hB : B.Nonempty) (hSB : S ⊂ B)
    (hC1 : vol G S ≤ vol G B / 2) (hC2 : condRel G B S ≤ φ)
    (hmax : ∀ S' : Finset V, S' ⊂ B → vol G S' ≤ vol G B / 2 → condRel G B S' ≤ φ →
      vol G S' ≤ vol G S)
    (α : ℝ) (hα : vol G S = α * vol G B) (hα3 : α ≤ 1 / 3) :
    φ * ((1 - 3 * α) / (1 - α)) ≤ cond G (B \ S) := by
  have hSB' : S ⊆ B := hSB.subset
  have hvB : 0 < vol G B := aux_vol_pos G hdeg B hB
  have hα0 : 0 ≤ α := by
    by_contra h
    push_neg at h
    have h1 := mul_neg_of_neg_of_pos h hvB
    have h2 := aux_vol_nonneg G S
    linarith
  have hq0 : 0 ≤ (1 - 3 * α) / (1 - α) := div_nonneg (by linarith) (by linarith)
  have hq1 : (1 - 3 * α) / (1 - α) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  by_cases hφ0 : φ ≤ 0
  · have : φ * ((1 - 3 * α) / (1 - α)) ≤ 0 := by nlinarith
    exact this.trans (aux_cond_nonneg G _)
  push_neg at hφ0
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (1 - 3 * α) / (1 - α) := ⟨_, rfl⟩
  rw [← hq] at hq0 hq1 ⊢
  have hq2 : q * (1 - α) = 1 - 3 * α := by
    have h1α : (1 - α) ≠ 0 := (by linarith : (0:ℝ) < 1 - α).ne'
    rw [hq]
    field_simp
  have hqS : q * (vol G B - vol G S) = vol G B - 3 * vol G S := by
    rw [hα]
    calc q * (vol G B - α * vol G B) = q * (1 - α) * vol G B := by ring
      _ = (1 - 3 * α) * vol G B := by rw [hq2]
      _ = vol G B - 3 * (α * vol G B) := by ring
  have hvBS : vol G (B \ S) = vol G B - vol G S := aux_vol_sdiff G hSB'
  have hSc : (cutEdges G S (B \ S) : ℝ) ≤ φ * vol G S := by
    by_cases hS0 : S = ∅
    · simp [hS0, cutEdges, vol]
    · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0
      have hpos := aux_vol_pos G hdeg S hne
      have hmin : min (vol G S) (vol G (B \ S)) = vol G S := by
        apply min_eq_left
        rw [hvBS]
        linarith
      have := hC2
      unfold condRel at this
      rw [if_neg hS0, hmin, div_le_iff₀ hpos] at this
      exact this
  have hφq : 0 ≤ φ * q := by positivity
  have main : ∀ R : Finset V, R ⊆ B \ S → R.Nonempty → ((B \ S) \ R).Nonempty →
      vol G R ≤ vol G (B \ S) / 2 → φ * q ≤ condRel G (B \ S) R := by
    intro R hRB hRne hR'ne hRvol
    have hdisj : Disjoint R S := by
      rw [Finset.disjoint_left]
      intro a ha haS
      exact (Finset.mem_sdiff.mp (hRB ha)).2 haS
    have hvR := aux_vol_pos G hdeg R hRne
    have hvR' := aux_vol_pos G hdeg _ hR'ne
    have hvS0 := aux_vol_nonneg G S
    have hvR'eq : vol G ((B \ S) \ R) = vol G (B \ S) - vol G R := aux_vol_sdiff G hRB
    have hT : vol G (R ∪ S) = vol G R + vol G S := aux_vol_union G hdisj
    have hcutR : (cutEdges G (R ∪ S) ((B \ S) \ R) : ℝ) ≤
        cutEdges G S (B \ S) + cutEdges G R ((B \ S) \ R) := by
      exact_mod_cast aux_cut_union G B S R
    have hcondR : condRel G (B \ S) R =
        (cutEdges G R ((B \ S) \ R) : ℝ) / min (vol G R) (vol G ((B \ S) \ R)) := by
      unfold condRel
      rw [if_neg (Finset.nonempty_iff_ne_empty.mp hRne)]
    have hvm : min (vol G R) (vol G ((B \ S) \ R)) = vol G R :=
      min_eq_left (by linarith)
    have hφT : φ * vol G (R ∪ S) = φ * vol G R + φ * vol G S := by rw [hT]; ring
    obtain ⟨a0, ha0⟩ := hR'ne
    have ha0B : a0 ∈ B := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ha0).1).1
    have hBT : B \ (R ∪ S) = (B \ S) \ R := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    have hT_sub : R ∪ S ⊂ B := by
      refine ⟨Finset.union_subset (hRB.trans Finset.sdiff_subset) hSB', fun h => ?_⟩
      have := h ha0B
      rw [Finset.mem_union] at this
      have h2 := Finset.mem_sdiff.mp ha0
      have h3 := Finset.mem_sdiff.mp h2.1
      tauto
    have hR'ne : ((B \ S) \ R).Nonempty := ⟨a0, ha0⟩
    by_cases hA : vol G (R ∪ S) ≤ vol G B / 2
    · -- Case A: T = R ∪ S satisfies (C.1)
      have hnot : ¬ condRel G B (R ∪ S) ≤ φ := by
        intro hle
        have := hmax _ hT_sub hA hle
        linarith
      push_neg at hnot
      have hTne : R ∪ S ≠ ∅ := (hRne.mono Finset.subset_union_left).ne_empty
      have hvTpos : 0 < vol G (R ∪ S) := by linarith
      have hminT : min (vol G (R ∪ S)) (vol G (B \ (R ∪ S))) = vol G (R ∪ S) := by
        apply min_eq_left
        rw [hBT]
        linarith
      unfold condRel at hnot
      rw [if_neg hTne, hminT, lt_div_iff₀ hvTpos, hBT] at hnot
      rw [hcondR, hvm, le_div_iff₀ hvR]
      have : φ * q * vol G R ≤ φ * vol G R := by
        have := mul_nonneg (mul_pos hφ0 hvR).le (by linarith : 0 ≤ 1 - q)
        nlinarith
      linarith
    · -- Case B
      push_neg at hA
      by_cases hα3' : α < 1 / 3
      · have hT'sub : (B \ S) \ R ⊂ B := by
          refine ⟨Finset.sdiff_subset.trans Finset.sdiff_subset, fun h => ?_⟩
          obtain ⟨r0, hr0⟩ := hRne
          have := h (Finset.mem_sdiff.mp (hRB hr0) |>.1)
          exact (Finset.mem_sdiff.mp this).2 hr0
        have hvT' : vol G ((B \ S) \ R) = vol G B - vol G (R ∪ S) := by
          rw [hvR'eq, hvBS, hT]
          ring
        have hvB3 : 0 < vol G B * (1 - 3 * α) := mul_pos hvB (by linarith)
        have hgt : vol G S < vol G ((B \ S) \ R) := by
          rw [hvR'eq, hvBS]
          rw [hvBS] at hRvol
          nlinarith
        have hnot : ¬ condRel G B ((B \ S) \ R) ≤ φ := by
          intro hle
          have := hmax _ hT'sub (by linarith) hle
          linarith
        push_neg at hnot
        have hT'ne : (B \ S) \ R ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hR'ne
        have hBT' : B \ ((B \ S) \ R) = R ∪ S := by
          ext a
          simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · rintro ⟨hB', h⟩
            by_cases hS : a ∈ S
            · right
              exact hS
            · left
              by_contra hR
              exact h ⟨⟨hB', hS⟩, hR⟩
          · rintro (h | h)
            · have := Finset.mem_sdiff.mp (hRB h)
              exact ⟨this.1, fun hh => hh.2 h⟩
            · exact ⟨hSB' h, fun hh => hh.1.2 h⟩
        have hminT' : min (vol G ((B \ S) \ R)) (vol G (R ∪ S)) = vol G ((B \ S) \ R) := by
          apply min_eq_left
          linarith
        unfold condRel at hnot
        rw [if_neg hT'ne, hBT', hminT', lt_div_iff₀ hvR', aux_cut_symm] at hnot
        have hm_pos : 0 < min (vol G R) (vol G ((B \ S) \ R)) := lt_min hvR hvR'
        have hm_le : min (vol G R) (vol G ((B \ S) \ R)) ≤ vol G R := min_le_left _ _
        rw [hcondR, le_div_iff₀ hm_pos]
        have F1 : φ * q * min (vol G R) (vol G ((B \ S) \ R)) ≤ φ * q * ((vol G B - vol G S) / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hφq
        have F2 : φ * q * (vol G B - vol G S) = φ * (vol G B - 3 * vol G S) := by
          rw [mul_assoc, hqS]
        have F3 : φ * ((vol G B - vol G S) / 2) ≤ φ * vol G ((B \ S) \ R) :=
          mul_le_mul_of_nonneg_left (by rw [hvR'eq, hvBS]; rw [hvBS] at hRvol; linarith) hφ0.le
        have F5 : φ * vol G S ≥ (cutEdges G S (B \ S) : ℝ) := hSc
        nlinarith
      · have hq00 : q = 0 := by
          rw [hq, show 1 - 3 * α = 0 by linarith, zero_div]
        rw [hq00, mul_zero]
        exact aux_condRel_nonneg G _ _
  apply aux_le_cond
  · nlinarith
  · intro R hR
    by_cases hRe : R = ∅
    · subst hRe
      unfold condRel
      rw [if_pos rfl]
      nlinarith
    · have hRne : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr hRe
      have hR'ne : ((B \ S) \ R).Nonempty := Finset.sdiff_nonempty.mpr hR.2
      by_cases hv : vol G R ≤ vol G (B \ S) / 2
      · exact main R hR.1 hRne hR'ne hv
      · push_neg at hv
        have h1 := aux_vol_sdiff G hR.1
        have := main ((B \ S) \ R) Finset.sdiff_subset hR'ne
          (by rw [Finset.sdiff_sdiff_eq_self hR.1]; exact hRne) (by linarith)
        calc φ * q ≤ condRel G (B \ S) ((B \ S) \ R) := this
          _ = condRel G (B \ S) R := aux_condRel_swap G hR.1 hRne hR'ne

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v) (φ : ℝ) (hφ : φ ≤ 1)
    (B S : Finset V) (hB : B.Nonempty) (hSB : S ⊂ B)
    (hC1 : vol G S ≤ vol G B / 2) (hC2 : condRel G B S ≤ φ)
    (hmax : ∀ S' : Finset V, S' ⊂ B → vol G S' ≤ vol G B / 2 → condRel G B S' ≤ φ →
      vol G S' ≤ vol G S)
    (h4 : vol G S ≤ vol G B / 4) :
    φ / 3 ≤ cond G (B \ S) := by
  have hvB : 0 < vol G B := aux_vol_pos G hdeg B hB
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = vol G S / vol G B := ⟨_, rfl⟩
  have hα : vol G S = α * vol G B := by rw [hαdef]; field_simp
  have hα4 : α ≤ 1 / 4 := by
    rw [hαdef, div_le_iff₀ hvB]
    linarith
  have h72 := lemma72_aux G hdeg φ hφ B S hB hSB hC1 hC2 hmax α hα (by linarith)
  by_cases hφ0 : 0 ≤ φ
  · have h13 : 1 / 3 ≤ (1 - 3 * α) / (1 - α) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    calc φ / 3 = φ * (1 / 3) := by ring
      _ ≤ φ * ((1 - 3 * α) / (1 - α)) := mul_le_mul_of_nonneg_left h13 hφ0
      _ ≤ cond G (B \ S) := h72
  · push_neg at hφ0
    have := aux_cond_nonneg G (B \ S)
    linarith
