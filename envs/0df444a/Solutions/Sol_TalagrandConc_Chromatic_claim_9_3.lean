-- Prove2me | solution 1 for TalagrandConc.Chromatic.claim_9_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:29:04.227168+00:00
-- url     : https://prove2.me/submissions/f2cf3bad-3d13-4e02-a638-c7b70ed6a2c7

import Mathlib
import Definitions.Def_TalagrandConc_Chromatic_Basic

open MeasureTheory
open scoped Classical


namespace TalagrandConc.Chromatic

lemma vxGraph_adj_congr {n : ℕ} {ω ω' : VxSpace n} {i j : Fin n}
    (hi : ω i = ω' i) (hj : ω j = ω' j) :
    (vxGraph ω).Adj i j ↔ (vxGraph ω').Adj i j := by
  simp only [vxGraph, SimpleGraph.fromRel_adj, hi, hj]

lemma coe_le_chiMZ_iff {n : ℕ} (G : SimpleGraph (Fin n)) (m q : ℕ) :
    (((q : ℤ)) : WithTop ℤ) ≤ chiMZ G m ↔ (q : ℕ∞) ≤ chiM G m := by
  unfold chiMZ
  induction chiM G m using WithTop.recTopCoe with
  | top => exact ⟨fun _ => le_top, fun _ => le_top⟩
  | coe c =>
    rw [WithTop.map_coe]
    constructor
    · intro h
      have h' : (q : ℤ) ≤ (c : ℤ) := WithTop.coe_le_coe.mp h
      exact Nat.cast_le.mpr (by exact_mod_cast h')
    · intro h
      have h' : q ≤ c := Nat.cast_le.mp h
      exact WithTop.coe_le_coe.mpr (by exact_mod_cast h')

lemma zero_le_chiMZ {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) :
    (((0 : ℤ)) : WithTop ℤ) ≤ chiMZ G m := by
  have := (coe_le_chiMZ_iff G m 0).mpr (by simp)
  simpa using this

/-- Combining a coloring of `G.induce A₀` with `n₁` colors (used off `F`) and a coloring of
`G'.induce F` with `k` colors, when `G` and `G'` agree outside `F`. -/
lemma colorable_combine {n : ℕ} (G G' : SimpleGraph (Fin n)) (A₀ F : Finset (Fin n))
    (hagree : ∀ i ∈ A₀, ∀ j ∈ A₀, i ∉ F → j ∉ F → (G.Adj i j ↔ G'.Adj i j))
    (n₁ k : ℕ) (h₀ : (G.induce (A₀ : Set (Fin n))).Colorable n₁)
    (h₁ : (G'.induce (F : Set (Fin n))).Colorable k) :
    (G'.induce (A₀ : Set (Fin n))).Colorable (n₁ + k) := by
  obtain ⟨c₀⟩ := h₀
  obtain ⟨c₁⟩ := h₁
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => if h : v.1 ∈ F then Fin.natAdd n₁ (c₁ ⟨v.1, by simpa using h⟩)
      else Fin.castAdd k (c₀ v)) ?_⟩
  intro u v huv
  rw [SimpleGraph.induce_adj] at huv
  have hu : u.1 ∈ A₀ := by simpa using u.2
  have hv : v.1 ∈ A₀ := by simpa using v.2
  by_cases hF : u.1 ∈ F <;> by_cases hF' : v.1 ∈ F
  · simp only [hF, hF', dite_true]
    intro heq
    have hadj : (G'.induce (F : Set (Fin n))).Adj ⟨u.1, by simpa using hF⟩ ⟨v.1, by simpa using hF'⟩ := by
      rw [SimpleGraph.induce_adj]; exact huv
    apply c₁.valid hadj
    have := congrArg Fin.val heq
    simp only [Fin.val_natAdd] at this
    exact Fin.ext (by omega)
  · simp only [hF, hF', dite_true, dite_false]
    intro heq
    have := congrArg Fin.val heq
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    have := (c₀ v).isLt
    omega
  · simp only [hF, hF', dite_true, dite_false]
    intro heq
    have := congrArg Fin.val heq
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    have := (c₀ u).isLt
    omega
  · simp only [hF, hF', dite_false]
    intro heq
    have hadj : (G.induce (A₀ : Set (Fin n))).Adj u v := by
      rw [SimpleGraph.induce_adj]; exact (hagree u.1 hu v.1 hv hF hF').mpr huv
    apply c₀.valid hadj
    have := congrArg Fin.val heq
    simp only [Fin.val_castAdd] at this
    exact Fin.ext this

theorem claim_9_3_core (n m k : ℕ) (t : ℝ) (ht : 0 < t) (a : ℤ) (ω : VxSpace n)
    (hω : ω ∈ setB (setA n m k t a) t) :
    (((a - k : ℤ)) : WithTop ℤ) ≤ chiMZ (vxGraph ω) m := by
  by_cases hak : a - k ≤ 0
  · exact le_trans (WithTop.coe_le_coe.mpr hak) (zero_le_chiMZ _ _)
  push Not at hak
  obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = a - k := ⟨(a - k).toNat, Int.toNat_of_nonneg hak.le⟩
  have ha : a = ((q + k : ℕ) : ℤ) := by push_cast; omega
  rw [← hq, coe_le_chiMZ_iff]
  unfold chiM
  simp only [le_iInf_iff]
  intro A₀ hA₀
  -- the weights
  set α : Fin n → ℝ := fun j => if j ∈ A₀ then 1 else 0 with hαdef
  have hα : ∀ j, 0 ≤ α j := fun j => by simp only [hαdef]; split_ifs <;> norm_num
  obtain ⟨ω', hω'A, hsum⟩ := hω α hα
  set F : Finset (Fin n) := A₀.filter (fun j => ω j ≠ ω' j) with hFdef
  have hsq : ∑ j, α j ^ 2 = m := by
    simp only [hαdef]
    have : ∀ j : Fin n, (if j ∈ A₀ then (1 : ℝ) else 0) ^ 2 = if j ∈ A₀ then 1 else 0 := by
      intro j; split_ifs <;> norm_num
    simp_rw [this]
    rw [Finset.sum_boole]
    simp [hA₀]
  have hcardF : (F.card : ℝ) ≤ t * Real.sqrt m := by
    have : (∑ j, if ω j ≠ ω' j then α j else 0) = (F.card : ℝ) := by
      have h1 : ∀ j : Fin n, (if ω j ≠ ω' j then α j else 0)
          = if (j ∈ A₀ ∧ ω j ≠ ω' j) then (1 : ℝ) else 0 := by
        intro j; by_cases h1 : ω j = ω' j <;> by_cases h2 : j ∈ A₀ <;> simp [hαdef, h1, h2]
      simp_rw [h1]
      rw [Finset.sum_boole]
      congr 2
      ext j; simp [hFdef]
    rw [← this, ← hsq]; exact hsum
  -- consequences of ω' ∈ A
  have hA1 : (a : WithTop ℤ) ≤ chiMZ (vxGraph ω') m := hω'A.1
  have hA2 : localSup (vxGraph ω') (t * Real.sqrt m) ≤ k := hω'A.2
  have hFcol : ((vxGraph ω').induce (F : Set (Fin n))).Colorable k := by
    rw [← SimpleGraph.chromaticNumber_le_iff_colorable]
    refine le_trans ?_ hA2
    unfold localSup
    exact le_iSup_of_le F (le_iSup_of_le hcardF le_rfl)
  have hA0' : ((q + k : ℕ) : ℕ∞) ≤ chiSet (vxGraph ω') A₀ := by
    rw [ha, coe_le_chiMZ_iff] at hA1
    refine le_trans hA1 ?_
    unfold chiM
    exact iInf_le_of_le A₀ (iInf_le_of_le hA₀ le_rfl)
  -- the coloring of G[A₀]
  set n₁ : ℕ := ENat.toNat (chiSet (vxGraph ω) A₀) with hn₁
  have hn₁top : chiSet (vxGraph ω) A₀ ≠ ⊤ := by
    unfold chiSet
    exact ne_top_of_le_ne_top (WithTop.coe_ne_top) SimpleGraph.chromaticNumber_le_card
  have hn₁eq : (n₁ : ℕ∞) = chiSet (vxGraph ω) A₀ := ENat.natCast_toNat hn₁top
  have h₀ : ((vxGraph ω).induce (A₀ : Set (Fin n))).Colorable n₁ :=
    SimpleGraph.colorable_chromaticNumber_of_fintype _
  have hagree : ∀ i ∈ A₀, ∀ j ∈ A₀, i ∉ F → j ∉ F →
      ((vxGraph ω).Adj i j ↔ (vxGraph ω').Adj i j) := by
    intro i hi j hj hiF hjF
    have hi' : ω i = ω' i := by
      by_contra h; exact hiF (by simp [hFdef, hi, h])
    have hj' : ω j = ω' j := by
      by_contra h; exact hjF (by simp [hFdef, hj, h])
    exact vxGraph_adj_congr hi' hj'
  have hcomb := colorable_combine (vxGraph ω) (vxGraph ω') A₀ F hagree n₁ k h₀ hFcol
  have hle : chiSet (vxGraph ω') A₀ ≤ ((n₁ + k : ℕ) : ℕ∞) := by
    unfold chiSet
    exact hcomb.chromaticNumber_le
  have h3 : ((q + k : ℕ) : ℕ∞) ≤ ((n₁ + k : ℕ) : ℕ∞) := le_trans hA0' hle
  have h4 : q + k ≤ n₁ + k := by exact_mod_cast h3
  rw [← hn₁eq]
  exact_mod_cast (by omega : q ≤ n₁)

end TalagrandConc.Chromatic

open TalagrandConc.Chromatic


theorem solution (n m k : ℕ) (t : ℝ) (ht : 0 < t) (a : ℤ) (ω : VxSpace n)
    (hω : ω ∈ setB (setA n m k t a) t) :
    (((a - k : ℤ)) : WithTop ℤ) ≤ chiMZ (vxGraph ω) m := by
  exact claim_9_3_core n m k t ht a ω hω
