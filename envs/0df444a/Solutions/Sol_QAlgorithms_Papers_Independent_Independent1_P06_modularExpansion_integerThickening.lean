-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P06.modularExpansion_integerThickening
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:19:19.916637+00:00
-- url     : https://prove2.me/submissions/c2c37b41-ea55-443c-bbe1-b26f5d622c5a

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SurgeryFaultComplexes
import Definitions.Def_QAlgorithms_Defs_MitigationOperationBasis
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P06_Model
set_option autoImplicit false

/-!
# Fast and fault-tolerant logical measurements (arXiv:2510.14895v1)

Paper-local definitions and statement-only targets. Deferred nodes are recorded in the
assigned unit's HARD.md and GAPS.json. No operational fault-distance lower bound is
inferred from the open-boundary homology calculation.
-/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P06
/-- Corollary 7.10, PDF pp.37–38: positive integer t-fold thickening at any one level. -/
theorem gq_syn_inl {V E : Type*} [Fintype V] [Fintype E] (G : Matrix V E F2) (t : ℕ)
    (v : V × Fin t → F2) (e : E) (l : Fin t) :
    ((thickIncidence G t).transpose.mulVec v) (Sum.inl (e, l)) =
      (G.transpose.mulVec (fun u => v (u, l))) e := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, thickIncidence,
    Matrix.fromCols_apply_inl, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Matrix.one_apply]
  apply Finset.sum_congr rfl
  intro u _
  simp

theorem gq_syn_inr {V E : Type*} [Fintype V] [Fintype E] (G : Matrix V E F2) (t : ℕ)
    (v : V × Fin t → F2) (u : V) (e : Fin (t-1)) :
    ((thickIncidence G t).transpose.mulVec v) (Sum.inr (u, e)) =
      v (u, ⟨e.val, by omega⟩) + v (u, ⟨e.val+1, by omega⟩) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, thickIncidence,
    Matrix.fromCols_apply_inr, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Matrix.one_apply, pathIncidence, Matrix.of_apply]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  have hx : ∀ x : V, (∑ x1 : Fin t, if x1.val = e.val ∨ x1.val = e.val + 1 then (if x = u then v (x, x1) else 0) else 0) =
      if x = u then ∑ x1 : Fin t, (if x1.val = e.val ∨ x1.val = e.val + 1 then v (u, x1) else 0) else 0 := by
    intro x
    by_cases hxu : x = u
    · subst hxu; simp
    · simp [hxu]
  rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have h : ∀ l : Fin t, (if l.val = e.val ∨ l.val = e.val + 1 then v (u, l) else 0) =
      (if l = ⟨e.val, by omega⟩ then v (u, l) else 0) + (if l = ⟨e.val+1, by omega⟩ then v (u, l) else 0) := by
    intro l
    by_cases h1 : l.val = e.val
    · rw [if_pos (Or.inl h1), if_pos (Fin.ext h1), if_neg (fun h => by have := congrArg Fin.val h; simp at this; omega), add_zero]
    · by_cases h2 : l.val = e.val + 1
      · rw [if_pos (Or.inr h2), if_neg (fun h => h1 (congrArg Fin.val h)), if_pos (Fin.ext h2), zero_add]
      · rw [if_neg (by tauto), if_neg (fun h => h1 (congrArg Fin.val h)), if_neg (fun h => h2 (congrArg Fin.val h)), add_zero]
  rw [Finset.sum_congr rfl (fun l _ => h l), Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem gq_ivt (t : ℕ) (f : Fin t → F2) (a b : Fin t) (h : f a ≠ f b) :
    ∃ e : Fin (t-1), f ⟨e.val, by omega⟩ ≠ f ⟨e.val+1, by omega⟩ := by
  by_contra hc
  push Not at hc
  have key : ∀ n (hn : n < t), f ⟨n, hn⟩ = f ⟨0, by omega⟩ := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ k ih =>
      intro hn
      rw [← ih (by omega)]
      exact (hc ⟨k, by omega⟩).symm
  apply h
  rw [show a = ⟨a.val, a.isLt⟩ from rfl, show b = ⟨b.val, b.isLt⟩ from rfl, key _ a.isLt, key _ b.isLt]

theorem gq_mcw_le {V : Type*} [Fintype V] (W : Submodule F2 (V → F2)) (x w : V → F2) (hw : w ∈ W) :
    modularCosetWeight W x ≤ hammingNorm (x + w) :=
  Finset.inf'_le _ (Finset.mem_univ (⟨w, hw⟩ : W))

theorem gq_f2_ne (a b : F2) (h : a + b ≠ 0) : a ≠ b := by
  intro hab; subst hab; revert h; revert a; decide

theorem solution {V E : Type*} [Fintype V] [Fintype E]
    (G : Matrix V E F2) (W : Submodule F2 (V → F2))
    (kernel : LinearMap.ker G.transpose.mulVecLin ≤ W) (t : ℕ) (positive : 1 ≤ t) :
    ∀ ell : Fin t, HasModularExpansion (thickIncidence G t) (levelSpace W t ell) (t : ℝ) 1 := by
  intro ell
  refine ⟨by exact_mod_cast (by omega : 0 < t), fun v => ?_⟩
  rw [one_mul]
  set s := (thickIncidence G t).transpose.mulVec v with hs
  have hcard : ∀ (A : Finset ((E × Fin t) ⊕ (V × Fin (t-1)))), (∀ p ∈ A, s p ≠ 0) →
      A.card ≤ hammingNorm s := by
    intro A hA
    unfold hammingNorm
    apply Finset.card_le_card
    intro p hp
    simp [hA p hp]
  by_cases hall : ∀ l : Fin t, G.transpose.mulVec (fun u => v (u, l)) ≠ 0
  · have hle : (t : ℝ) ≤ hammingNorm s := by
      have hsub : (Finset.univ : Finset (Fin t)) ⊆
          ((Finset.univ.filter (fun p : E × Fin t => s (Sum.inl p) ≠ 0)).image Prod.snd) := by
        intro l _
        obtain ⟨e, he⟩ := Function.ne_iff.mp (hall l)
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(e, l), by rw [hs, gq_syn_inl]; exact he, rfl⟩
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at h1
      have h2 := Finset.card_image_le (s := Finset.univ.filter (fun p : E × Fin t => s (Sum.inl p) ≠ 0)) (f := Prod.snd)
      have h3 : (Finset.univ.filter (fun p : E × Fin t => s (Sum.inl p) ≠ 0)).card ≤ hammingNorm s := by
        rw [← Finset.card_map ⟨Sum.inl, Sum.inl_injective⟩]
        apply hcard
        intro p hp
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        exact hq
      exact_mod_cast h1.trans (h2.trans h3)
    exact (min_le_left _ _).trans hle
  · push Not at hall
    obtain ⟨l0, hl0⟩ := hall
    have hv0 : (fun u => v (u, l0)) ∈ W := kernel (by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hl0)
    set D := Finset.univ.filter (fun u : V => v (u, ell) ≠ v (u, l0)) with hD
    have hw : modularCosetWeight (levelSpace W t ell) (restrictVertices (addressed (levelSpace W t ell)) v) ≤ D.card := by
      have hw1 := gq_mcw_le (levelSpace W t ell) (restrictVertices (addressed (levelSpace W t ell)) v)
        (levelEmbedding t ell (fun u => v (u, l0))) (Submodule.mem_map_of_mem hv0)
      refine le_trans hw1 ?_
      unfold hammingNorm
      refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := D) (f := fun u => (u, ell)))
      intro p hp
      obtain ⟨u, l⟩ := p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hemb : ∀ (x : V → F2) (q : V × Fin t), levelEmbedding t ell x q = if q.2 = ell then x q.1 else 0 :=
        fun x q => rfl
      have hnot : ∀ q : V × Fin t, q.2 ≠ ell → q ∉ addressed (levelSpace W t ell) := by
        intro q hq hqa
        simp only [addressed, Finset.mem_filter, Finset.mem_univ, true_and] at hqa
        obtain ⟨w, hw, hwq⟩ := hqa
        obtain ⟨w', _, rfl⟩ := Submodule.mem_map.mp hw
        rw [hemb] at hwq
        simp [hq] at hwq
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, hD]
      by_cases hl : l = ell
      · subst hl
        refine ⟨u, ?_, rfl⟩
        by_cases ha : (u, l) ∈ addressed (levelSpace W t l)
        · simp only [restrictVertices, ha, if_true, Pi.add_apply, hemb, if_true] at hp
          exact gq_f2_ne _ _ hp
        · exfalso
          simp only [restrictVertices, ha, if_false, Pi.add_apply, hemb, if_true, zero_add] at hp
          apply ha
          simp only [addressed, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨levelEmbedding t l (fun u => v (u, l0)), Submodule.mem_map_of_mem hv0, by rw [hemb]; simpa using hp⟩
      · exfalso
        have := hnot (u, l) hl
        simp only [restrictVertices, this, if_false, Pi.add_apply, hemb, hl, zero_add] at hp
        exact hp rfl
    have hDs : (D.card : ℝ) ≤ hammingNorm s := by
      have hsub : D ⊆ ((Finset.univ.filter (fun p : V × Fin (t-1) => s (Sum.inr p) ≠ 0)).image Prod.fst) := by
        intro u hu
        simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        obtain ⟨e, he⟩ := gq_ivt t (fun l => v (u, l)) ell l0 hu
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨(u, e), ?_, rfl⟩
        rw [hs, gq_syn_inr]
        intro h0
        apply he
        have : ∀ a b : F2, a + b = 0 → a = b := by decide
        exact this _ _ h0
      have h2 := Finset.card_image_le (s := Finset.univ.filter (fun p : V × Fin (t-1) => s (Sum.inr p) ≠ 0)) (f := Prod.fst)
      have h3 : (Finset.univ.filter (fun p : V × Fin (t-1) => s (Sum.inr p) ≠ 0)).card ≤ hammingNorm s := by
        rw [← Finset.card_map ⟨Sum.inr, Sum.inr_injective⟩]
        apply hcard
        intro p hp
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        exact hq
      exact_mod_cast (Finset.card_le_card hsub).trans (h2.trans h3)
    have hw' : ((modularCosetWeight (levelSpace W t ell) (restrictVertices (addressed (levelSpace W t ell)) v) : ℕ) : ℝ) ≤ D.card := by
      exact_mod_cast hw
    exact (min_le_right _ _).trans (hw'.trans hDs)

