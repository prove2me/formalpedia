-- Prove2me | solution 1 for ROLDescent.eq_70
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:08:45.677407+00:00
-- url     : https://prove2.me/submissions/524d242e-4e09-4d8a-b900-f2c20387a23f

import Mathlib
import Definitions.Def_ROLDescent_WeightedComplex
import Definitions.Def_ROLDescent_facetMass
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_ROLDescent_remRank
import Definitions.Def_ROLDescent_outProb
import Definitions.Def_ROLDescent_linkWalk

open ROLDescent
open scoped BigOperators


private theorem mass_nonneg {V : Type*} [DecidableEq V]
    {X : Finset (Finset V)} {d : ℕ} {w : Finset V → ℝ}
    (hX : WeightedComplex X d w) (τ : Finset V) : 0 ≤ facetMass X d w τ := by
  exact Finset.sum_nonneg (fun F hF => (hX.2.2.2 F (Finset.mem_filter.mp hF).1).le)

private theorem mass_pos {V : Type*} [DecidableEq V]
    {X : Finset (Finset V)} {d : ℕ} {w : Finset V → ℝ}
    (hX : WeightedComplex X d w) {τ : Finset V} (hτ : τ ∈ X) : 0 < facetMass X d w τ := by
  let candidates := X.filter (fun F => τ ⊆ F)
  obtain ⟨F, hF, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card ⟨τ, Finset.mem_filter.mpr ⟨hτ, le_rfl⟩⟩
  have hF' := Finset.mem_filter.mp hF
  have hcard : F.card = d := hX.2.1.2 F hF'.1 (by
    intro G hG hFG
    have hG' : G ∈ candidates := Finset.mem_filter.mpr ⟨hG, hF'.2.trans hFG⟩
    exact (Finset.eq_of_subset_of_card_le hFG (hmax G hG')).symm)
  have hf : F ∈ SteurerHDX.faces X d := Finset.mem_filter.mpr ⟨hF'.1, hcard⟩
  unfold facetMass
  refine lt_of_lt_of_le (hX.2.2.2 F hf) (Finset.single_le_sum ?_ (Finset.mem_filter.mpr ⟨hf,hF'.2⟩))
  exact fun G hG => (hX.2.2.2 G (Finset.mem_filter.mp hG).1).le

private theorem degree_identity {V : Type*} [DecidableEq V]
    {X : Finset (Finset V)} {d : ℕ} {w : Finset V → ℝ}
    (τ S : Finset V) (hS : ∀ v ∈ S, v ∉ τ)
    (hCover : ∀ F ∈ SteurerHDX.faces X d, τ ⊆ F → F \ τ ⊆ S) :
    ∑ i ∈ S, facetMass X d w (insert i τ) = (remRank d τ : ℝ) * facetMass X d w τ := by
  classical
  simp only [facetMass, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro F hF
  by_cases hτF : τ ⊆ F
  · have hFS : S.filter (fun i => insert i τ ⊆ F) = F \ τ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.insert_subset_iff, hτF, and_true]
      exact ⟨fun h => ⟨h.2, hS v h.1⟩, fun h => ⟨hCover F hF hτF (Finset.mem_sdiff.mpr h), h.1⟩⟩
    rw [← Finset.sum_filter, hFS, Finset.sum_const, nsmul_eq_mul,
      Finset.card_sdiff_of_subset hτF, (Finset.mem_filter.mp hF).2]
    simp [remRank, hτF]
  · have hnone : ∀ i ∈ S, ¬ insert i τ ⊆ F := by
      intro i _ hi
      exact hτF (Finset.subset_insert i τ |>.trans hi)
    simp [hτF, Finset.sum_eq_zero (fun i hi => if_neg (hnone i hi))]

private theorem link_mem {V : Type*} [Fintype V] [DecidableEq V]
    {X : Finset (Finset V)} {τ : Finset V} {i : V} :
    i ∈ HDXConc.linkVerts X τ ↔ i ∉ τ ∧ insert i τ ∈ X := by
  simp [HDXConc.linkVerts]


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (X : Finset (Finset V)) (d : ℕ) (w : Finset V → ℝ) (hX : WeightedComplex X d w)
    (τ : Finset V) (hτ : τ ∈ X) (hτd : τ.card + 2 ≤ d) :
    (∑ i ∈ HDXConc.linkVerts X τ, facetMass X d w (insert i τ) =
        (remRank d τ : ℝ) * facetMass X d w τ) ∧
    (∀ i ∈ HDXConc.linkVerts X τ, ∑ j ∈ (HDXConc.linkVerts X τ).erase i, facetMass X d w (insert j (insert i τ)) =
        ((remRank d τ : ℝ) - 1) * facetMass X d w (insert i τ)) ∧
    ((∀ i ∈ HDXConc.linkVerts X τ, 0 ≤ outProb X d w τ i) ∧
        ∑ i ∈ HDXConc.linkVerts X τ, outProb X d w τ i = 1) ∧
    (∀ i ∈ HDXConc.linkVerts X τ, (∀ j ∈ HDXConc.linkVerts X τ, 0 ≤ linkWalk X d w τ i j) ∧
        ∑ j ∈ HDXConc.linkVerts X τ, linkWalk X d w τ i j = 1) ∧
    (∀ i ∈ HDXConc.linkVerts X τ, ∀ j ∈ HDXConc.linkVerts X τ, i ≠ j →
        outProb X d w τ i * linkWalk X d w τ i j =
          facetMass X d w (insert j (insert i τ)) /
            ((remRank d τ : ℝ) * ((remRank d τ : ℝ) - 1) * facetMass X d w τ)) ∧
    (∀ i ∈ HDXConc.linkVerts X τ, ∀ j ∈ HDXConc.linkVerts X τ,
        outProb X d w τ i * linkWalk X d w τ i j = outProb X d w τ j * linkWalk X d w τ j i) := by
  classical
  have hdn : (1 : ℝ) < (remRank d τ : ℝ) := by
    exact_mod_cast (show 1 < remRank d τ from by unfold remRank; omega)
  have hden : 0 < (remRank d τ : ℝ) * facetMass X d w τ :=
    mul_pos (by linarith) (mass_pos hX hτ)
  have hd1 : ∑ i ∈ HDXConc.linkVerts X τ, facetMass X d w (insert i τ) =
      (remRank d τ : ℝ) * facetMass X d w τ := by
    refine degree_identity τ _ (fun i hi => (link_mem.mp hi).1) ?_
    intro F hF hτF i hi
    obtain ⟨hiF, hiτ⟩ := Finset.mem_sdiff.mp hi
    exact link_mem.mpr ⟨hiτ, hX.2.1.1 F (Finset.mem_filter.mp hF).1 _
      (Finset.insert_subset_iff.mpr ⟨hiF, hτF⟩)⟩
  have hd2 : ∀ i ∈ HDXConc.linkVerts X τ,
      ∑ j ∈ (HDXConc.linkVerts X τ).erase i, facetMass X d w (insert j (insert i τ)) =
        ((remRank d τ : ℝ) - 1) * facetMass X d w (insert i τ) := by
    intro i hi
    have hiτ := (link_mem.mp hi).1
    have hrank : (remRank d (insert i τ) : ℝ) = (remRank d τ : ℝ) - 1 := by
      have hn : remRank d (insert i τ) + 1 = remRank d τ := by
        unfold remRank
        rw [Finset.card_insert_of_notMem hiτ]
        omega
      have hreal : (remRank d (insert i τ) : ℝ) + 1 = (remRank d τ : ℝ) := by exact_mod_cast hn
      linarith
    rw [← hrank]
    refine degree_identity (insert i τ) _ ?_ ?_
    · intro j hj
      obtain ⟨hji, hjτ⟩ := Finset.mem_erase.mp hj
      simpa [hji] using (link_mem.mp hjτ).1
    · intro F hF hτF j hj
      obtain ⟨hjF, hjτi⟩ := Finset.mem_sdiff.mp hj
      have hτF' : τ ⊆ F := (Finset.subset_insert i τ).trans hτF
      have hji : j ≠ i := fun hej => hjτi (hej ▸ Finset.mem_insert_self _ _)
      have hjτ : j ∉ τ := fun h => hjτi (Finset.mem_insert_of_mem h)
      exact Finset.mem_erase.mpr ⟨hji, link_mem.mpr ⟨hjτ,
        hX.2.1.1 F (Finset.mem_filter.mp hF).1 _
          (Finset.insert_subset_iff.mpr ⟨hjF, hτF'⟩)⟩⟩
  have hrowden : ∀ i ∈ HDXConc.linkVerts X τ,
      0 < ((remRank d τ : ℝ) - 1) * facetMass X d w (insert i τ) := by
    intro i hi
    exact mul_pos (sub_pos.mpr hdn) (mass_pos hX (link_mem.mp hi).2)
  have hbalance : ∀ i ∈ HDXConc.linkVerts X τ, ∀ j ∈ HDXConc.linkVerts X τ, i ≠ j →
      outProb X d w τ i * linkWalk X d w τ i j =
        facetMass X d w (insert j (insert i τ)) /
          ((remRank d τ : ℝ) * ((remRank d τ : ℝ) - 1) * facetMass X d w τ) := by
    intro i hi j _ hij
    rw [outProb, linkWalk, if_neg hij]
    have hpm := (mass_pos hX hτ).ne'
    have him := (mass_pos hX (link_mem.mp hi).2).ne'
    have hr : (remRank d τ : ℝ) ≠ 0 := by linarith
    have hr1 : (remRank d τ : ℝ) - 1 ≠ 0 := (sub_pos.mpr hdn).ne'
    field_simp
    <;> ring
  refine ⟨hd1, hd2, ⟨?_, ?_⟩, ?_, hbalance, ?_⟩
  · intro i _
    exact div_nonneg (mass_nonneg hX _) hden.le
  · unfold outProb
    rw [← Finset.sum_div, hd1, div_self hden.ne']
  · intro i hi
    constructor
    · intro j _
      unfold linkWalk
      split
      · exact le_rfl
      · exact div_nonneg (mass_nonneg hX _) (hrowden i hi).le
    · rw [← Finset.sum_erase_add _ _ hi]
      have hdiag : linkWalk X d w τ i i = 0 := by simp [linkWalk]
      rw [hdiag, add_zero]
      calc
        (∑ j ∈ (HDXConc.linkVerts X τ).erase i, linkWalk X d w τ i j) =
            ∑ j ∈ (HDXConc.linkVerts X τ).erase i, facetMass X d w (insert j (insert i τ)) /
              (((remRank d τ : ℝ) - 1) * facetMass X d w (insert i τ)) := by
                apply Finset.sum_congr rfl
                intro j hj
                simp [linkWalk, (Finset.mem_erase.mp hj).1.symm]
        _ = 1 := by rw [← Finset.sum_div, hd2 i hi, div_self (hrowden i hi).ne']
  · intro i hi j hj
    by_cases hij : i = j
    · subst j
      rfl
    · rw [hbalance i hi j hj hij, hbalance j hj i hi (Ne.symm hij), Finset.insert_comm]

#print axioms solution
