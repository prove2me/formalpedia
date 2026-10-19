-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P06.modularExpansion_thickening
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:28:05.405429+00:00
-- url     : https://prove2.me/submissions/ea443453-c024-4650-8d9f-4c8e175e49c1

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
/-- Theorem 7.8, PDF p.37 and pp.87–88: positive certified expansion M and an integer
L at least 1/M give certified expansion one at every selected level. -/
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

theorem gq_hn_add {ι : Type*} [Fintype ι] (a b : ι → F2) :
    hammingNorm (a + b) ≤ hammingNorm a + hammingNorm b := by
  unfold hammingNorm
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Pi.add_apply] at hi ⊢
  by_contra h
  push Not at h
  apply hi
  rw [h.1, h.2, add_zero]

theorem gq_hn_sum {V E : Type*} [Fintype V] [Fintype E] (G : Matrix V E F2) (L : ℕ)
    (v : V × Fin L → F2) :
    (∑ l : Fin L, hammingNorm (G.transpose.mulVec (fun u => v (u, l)))) +
      (Finset.univ.filter (fun p : V × Fin (L-1) => (thickIncidence G L).transpose.mulVec v (Sum.inr p) ≠ 0)).card =
      hammingNorm ((thickIncidence G L).transpose.mulVec v) := by
  unfold hammingNorm
  simp only [Finset.card_filter]
  rw [Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro e _
  rw [gq_syn_inl]

theorem gq_mcw_attain {V : Type*} [Fintype V] (W : Submodule F2 (V → F2)) (x : V → F2) :
    ∃ w ∈ W, modularCosetWeight W x = hammingNorm (x + w) := by
  unfold modularCosetWeight
  obtain ⟨w, _, h⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty_iff.mpr ⟨(0 : W)⟩)
    (fun w : W => hammingNorm (x + w.val))
  exact ⟨w.1, w.2, h⟩

theorem solution {V E : Type*} [Fintype V] [Fintype E]
    (G : Matrix V E F2) (W : Submodule F2 (V → F2)) (t M : ℝ)
    (expansion : HasModularExpansion G W t M) (positive : 0 < M)
    (L : ℕ) (levels : 1 ≤ L) (enough : M⁻¹ ≤ (L : ℝ)) :
    ∀ ell : Fin L, HasModularExpansion (thickIncidence G L) (levelSpace W L ell) t 1 := by
  intro ell
  refine ⟨expansion.1, fun v => ?_⟩
  rw [one_mul]
  set s := (thickIncidence G L).transpose.mulVec v with hs
  set U := addressed W with hU
  set A := addressed (levelSpace W L ell) with hAdef
  set vl : Fin L → V → F2 := fun l u => v (u, l) with hvl
  have hemb : ∀ (x : V → F2) (q : V × Fin L), levelEmbedding L ell x q = if q.2 = ell then x q.1 else 0 :=
    fun x q => rfl
  have hA : ∀ u l, (u, l) ∈ A ↔ l = ell ∧ u ∈ U := by
    intro u l
    simp only [hAdef, hU, addressed, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, hwq⟩
      obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.mp hw
      rw [hemb] at hwq
      by_cases hl : l = ell
      · simp only [hl, if_true] at hwq
        exact ⟨hl, w', hw', hwq⟩
      · simp [hl] at hwq
    · rintro ⟨rfl, w, hw, hwu⟩
      exact ⟨levelEmbedding L l w, Submodule.mem_map_of_mem hw, by rw [hemb]; simpa using hwu⟩
  have K1 : modularCosetWeight (levelSpace W L ell) (restrictVertices A v) ≤
      modularCosetWeight W (restrictVertices U (vl ell)) := by
    obtain ⟨w, hw, hweq⟩ := gq_mcw_attain W (restrictVertices U (vl ell))
    rw [hweq]
    refine (gq_mcw_le _ _ (levelEmbedding L ell w) (Submodule.mem_map_of_mem hw)).trans ?_
    unfold hammingNorm
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le
      (s := Finset.univ.filter (fun u => (restrictVertices U (vl ell) + w) u ≠ 0)) (f := fun u => (u, ell)))
    rintro ⟨u, l⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, restrictVertices, hemb] at hp
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, restrictVertices]
    by_cases hl : l = ell
    · subst hl
      refine ⟨u, ?_, rfl⟩
      by_cases hu : u ∈ U
      · have : (u, l) ∈ A := (hA u l).2 ⟨rfl, hu⟩
        simpa [this, hu, hvl] using hp
      · have : (u, l) ∉ A := fun h => hu ((hA u l).1 h).2
        simpa [this, hu, hvl] using hp
    · exfalso
      have : (u, l) ∉ A := fun h => hl ((hA u l).1 h).1
      simp [this, hl] at hp
  have K2 : ∀ l, modularCosetWeight W (restrictVertices U (vl ell)) ≤
      modularCosetWeight W (restrictVertices U (vl l)) +
        (Finset.univ.filter (fun u : V => v (u, ell) ≠ v (u, l))).card := by
    intro l
    obtain ⟨w, hw, hweq⟩ := gq_mcw_attain W (restrictVertices U (vl l))
    have h0 := gq_mcw_le W (restrictVertices U (vl ell)) w hw
    have h2 : ∀ x y z : F2, x + z = (y + z) + (x + y) := by decide
    have heq : restrictVertices U (vl ell) + w = (restrictVertices U (vl l) + w) +
        (restrictVertices U (vl ell) + restrictVertices U (vl l)) := by
      funext u; simp only [Pi.add_apply]; exact h2 _ _ _
    rw [heq] at h0
    refine h0.trans ((gq_hn_add _ _).trans ?_)
    rw [← hweq]
    apply Nat.add_le_add_left
    unfold hammingNorm
    apply Finset.card_le_card
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, restrictVertices, hvl] at hu ⊢
    split_ifs at hu
    · exact gq_f2_ne _ _ hu
    · simp at hu
  have K3 : ∀ l, (Finset.univ.filter (fun u : V => v (u, ell) ≠ v (u, l))).card ≤
      (Finset.univ.filter (fun p : V × Fin (L-1) => s (Sum.inr p) ≠ 0)).card := by
    intro l
    have hsub : (Finset.univ.filter (fun u : V => v (u, ell) ≠ v (u, l))) ⊆
        ((Finset.univ.filter (fun p : V × Fin (L-1) => s (Sum.inr p) ≠ 0)).image Prod.fst) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      obtain ⟨e, he⟩ := gq_ivt L (fun l => v (u, l)) ell l hu
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(u, e), ?_, rfl⟩
      rw [hs, gq_syn_inr]
      intro h0
      apply he
      have : ∀ a b : F2, a + b = 0 → a = b := by decide
      exact this _ _ h0
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have K5 : ∀ l, M * min t (modularCosetWeight W (restrictVertices U (vl l)) : ℝ) ≤
      hammingNorm (G.transpose.mulVec (vl l)) := fun l => expansion.2 (vl l)
  have K4 := gq_hn_sum G L v
  set N2 := (Finset.univ.filter (fun p : V × Fin (L-1) => s (Sum.inr p) ≠ 0)).card with hN2
  set m := min t (modularCosetWeight W (restrictVertices U (vl ell)) : ℝ) with hm
  have K4' : (∑ l : Fin L, (hammingNorm (G.transpose.mulVec (vl l)) : ℝ)) + (N2 : ℝ) = hammingNorm s := by
    exact_mod_cast K4
  have hS0 : (0 : ℝ) ≤ ∑ l : Fin L, (hammingNorm (G.transpose.mulVec (vl l)) : ℝ) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hmain : m ≤ hammingNorm s := by
    by_cases hmN : m ≤ N2
    · linarith
    · push Not at hmN
      have hl : ∀ l, M * (m - N2) ≤ hammingNorm (G.transpose.mulVec (vl l)) := by
        intro l
        have h1 : m - N2 ≤ min t (modularCosetWeight W (restrictVertices U (vl l)) : ℝ) := by
          apply le_min
          · have := min_le_left t (modularCosetWeight W (restrictVertices U (vl ell)) : ℝ)
            have : (0 : ℝ) ≤ N2 := by positivity
            linarith
          · have a := K2 l
            have b := K3 l
            have c := min_le_right t (modularCosetWeight W (restrictVertices U (vl ell)) : ℝ)
            have : (modularCosetWeight W (restrictVertices U (vl ell)) : ℝ) ≤
                modularCosetWeight W (restrictVertices U (vl l)) + N2 := by
              exact_mod_cast (a.trans (by omega))
            linarith
        exact (mul_le_mul_of_nonneg_left h1 positive.le).trans (K5 l)
      have hsum : (L : ℝ) * (M * (m - N2)) ≤ ∑ l : Fin L, (hammingNorm (G.transpose.mulVec (vl l)) : ℝ) := by
        have := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => hl l)
        simpa using this
      have hLM : 1 ≤ (L : ℝ) * M := by
        have := mul_le_mul_of_nonneg_right enough positive.le
        rwa [inv_mul_cancel₀ positive.ne'] at this
      have : m - N2 ≤ (L : ℝ) * M * (m - N2) := by nlinarith
      nlinarith
  exact (min_le_min_left _ (by exact_mod_cast K1)).trans hmain

