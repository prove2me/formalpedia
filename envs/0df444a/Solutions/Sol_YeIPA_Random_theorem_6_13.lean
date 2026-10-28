-- Prove2me | solution 1 for YeIPA.Random.theorem_6_13
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T05:48:46.599638+00:00
-- url     : https://prove2.me/submissions/ec962256-5510-4b3b-b288-5012f92c07d1

import Mathlib
import Definitions.Def_YeIPA_Random_Setting

open Matrix MeasureTheory ProbabilityTheory YeIPA.Random

namespace T613

lemma pi_ac : ∀ n : ℕ, Measure.pi (fun _ : Fin n => gaussianReal 0 1) ≪
    Measure.pi (fun _ : Fin n => (volume : Measure ℝ))
  | 0 => by
    intro s hs
    have h0 : Measure.pi (fun _ : Fin 0 => gaussianReal 0 1) =
        Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) := by
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
    rw [h0]; exact hs
  | n + 1 => by
    have h1 := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) 0).symm
    have h2 := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure ℝ)) 0).symm
    rw [← h1.map_eq, ← h2.map_eq]
    exact ((gaussianReal_absolutelyContinuous 0 one_ne_zero).prod (pi_ac n)).map
      (MeasurableEquiv.measurable _)

lemma gauss_submodule_null {n : ℕ} (S : Submodule ℝ (Fin n → ℝ)) (hS : S ≠ ⊤) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) (S : Set (Fin n → ℝ)) = 0 :=
  pi_ac n (Measure.addHaar_submodule volume S hS)

lemma ae_linIndep {n : ℕ} {ι : Type} [Fintype ι] (P : (Fin n → ℝ) →ₗ[ℝ] (ι → ℝ)) :
    ∀ k : ℕ, k ≤ Module.finrank ℝ (LinearMap.range P) →
      ∀ᵐ r ∂(Measure.pi fun _ : Fin k => Measure.pi (fun _ : Fin n => gaussianReal 0 1)),
        LinearIndependent ℝ (fun i => P (r i))
  | 0, _ => ae_of_all _ (fun r => linearIndependent_empty_type)
  | k + 1, hk => by
    set ν := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
    have ih := ae_linIndep P k (by omega)
    have hP : Continuous P := LinearMap.continuous_of_finiteDimensional P
    have hmeas : ∀ (j : ℕ), MeasurableSet {r : Fin j → Fin n → ℝ |
        LinearIndependent ℝ (fun i => P (r i))} := by
      intro j
      have : IsOpen {r : Fin j → Fin n → ℝ | LinearIndependent ℝ (fun i => P (r i))} :=
        (isOpen_setOfPred_linearIndependent (𝕜 := ℝ) (E := ι → ℝ) (ι := Fin j)).preimage
          (continuous_pi fun i => hP.comp (continuous_apply i))
      exact this.measurableSet
    have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => ν) 0).symm
    rw [← hmp.map_eq]
    rw [ae_map_iff (MeasurableEquiv.measurable _).aemeasurable (hmeas (k+1))]
    have key : ∀ z : (Fin n → ℝ) × (Fin k → Fin n → ℝ),
        (fun i => P ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => Fin n → ℝ) 0).symm z i))
          = Fin.cons (P z.1) (fun i => P (z.2 i)) := by
      intro z; funext i
      refine Fin.cases ?_ ?_ i
      · simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
      · intro j; simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
    have hm2 : MeasurableSet {z : (Fin n → ℝ) × (Fin k → Fin n → ℝ) |
        LinearIndependent ℝ (Fin.cons (P z.1) (fun i => P (z.2 i)) : Fin (k+1) → ι → ℝ)} := by
      have := (hmeas (k+1)).preimage
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => Fin n → ℝ) 0).symm.measurable
      convert this using 1
      ext z
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      rw [key]
    simp_rw [key]
    rw [Measure.ae_prod_iff_ae_ae hm2, Measure.ae_ae_comm hm2]
    filter_upwards [ih] with rest hrest
    simp only [linearIndependent_finCons]
    set W := Submodule.span ℝ (Set.range fun i => P (rest i))
    have hW : W.comap P ≠ ⊤ := by
      intro h
      have hle : LinearMap.range P ≤ W := by
        rintro _ ⟨x, rfl⟩
        have : x ∈ W.comap P := h ▸ Submodule.mem_top
        exact this
      have h1 := Submodule.finrank_mono hle
      have h2 : Module.finrank ℝ W ≤ k := by
        have := finrank_range_le_card (R := ℝ) (b := fun i => P (rest i))
        simpa [Set.finrank] using this
      omega
    have h0 := gauss_submodule_null (W.comap P) hW
    rw [ae_iff]
    refine measure_mono_null ?_ h0
    intro x hx
    simp only [Set.mem_ofPred_eq, not_and, not_not] at hx
    exact hx hrest


lemma ae_G {m n : ℕ} (hmn : m ≤ n) :
    ∀ᵐ A ∂YeIPA.Random.gaussianMatrix m n, ∀ T : Finset (Fin n), T.card ≤ m →
      LinearIndependent ℝ (fun j : T => fun i => A i j) := by
  have hT : ∀ T : Finset (Fin n), T.card = m → ∀ᵐ A ∂YeIPA.Random.gaussianMatrix m n,
      LinearIndependent ℝ (fun j : T => fun i => A i j) := by
    intro T hTm
    let P : (Fin n → ℝ) →ₗ[ℝ] (T → ℝ) := LinearMap.funLeft ℝ ℝ (Subtype.val : T → Fin n)
    have hsurj : Function.Surjective P :=
      LinearMap.funLeft_surjective_of_injective _ _ _ Subtype.val_injective
    have hrk : m ≤ Module.finrank ℝ (LinearMap.range P) := by
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
        Fintype.card_coe, hTm]
    have h := ae_linIndep P m hrk
    unfold YeIPA.Random.gaussianMatrix
    filter_upwards [h] with A hA
    let M : Matrix (Fin m) T ℝ := fun i t => A i t
    have hrow : M.rank = m := by
      rw [Matrix.rank_eq_finrank_span_row]
      have := finrank_span_eq_card hA
      simp only [Fintype.card_fin] at this
      exact this
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_coe, hTm]
    rw [Matrix.rank_eq_finrank_span_cols] at hrow
    exact hrow.symm
  have hall : ∀ᵐ A ∂YeIPA.Random.gaussianMatrix m n, ∀ T : {T : Finset (Fin n) // T.card = m},
      LinearIndependent ℝ (fun j : T.1 => fun i => A i j) := by
    rw [ae_all_iff]; intro T; exact hT T.1 T.2
  filter_upwards [hall] with A hA
  intro T hTm
  obtain ⟨U, hTU, -, hU⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ T) hTm
    (by simpa using hmn)
  have := hA ⟨U, hU⟩
  exact this.comp (fun j : T => (⟨j.1, hTU j.2⟩ : U)) (fun a b h => by
    simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)


lemma dual_coord {k : ℕ} (f : StrongDual ℝ (Fin k → ℝ)) (v : Fin k → ℝ) :
    f v = ∑ i, v i * f (Pi.single i 1) := by
  have := f.toLinearMap.pi_apply_eq_sum_univ v
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
  rw [this]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

lemma gordan {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hn : 1 ≤ n)
    (h : ¬ ∃ x, IsFeasible65 A x) : ∃ y, IsInterior611 A y := by
  set s := (Matrix.mulVecLin A) '' stdSimplex ℝ (Fin n) with hs
  have hsc : IsCompact s := (isCompact_stdSimplex ℝ (Fin n)).image
    (LinearMap.continuous_of_finiteDimensional _)
  have hsv : Convex ℝ s := (convex_stdSimplex ℝ (Fin n)).linear_image _
  have hdisj : Disjoint s {0} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨x, hx, hAx⟩
    apply h
    refine ⟨x, hAx, hx.1, ?_⟩
    rintro rfl
    have := hx.2
    simp at this
  obtain ⟨f, u, v, hfu, huv, hfv⟩ := geometric_hahn_banach_compact_closed hsv hsc
    (convex_singleton 0) isClosed_singleton hdisj
  have hv : v < 0 := by simpa using hfv 0 rfl
  refine ⟨fun i => -f (Pi.single i 1), ?_⟩
  have key : ∀ j, (Aᵀ *ᵥ fun i => -f (Pi.single i 1)) j = - f (A.col j) := by
    intro j
    rw [dual_coord f (A.col j)]
    simp [mulVec, dotProduct, Finset.sum_neg_distrib, Matrix.col]
  have hpos : ∀ j, 0 < (Aᵀ *ᵥ fun i => -f (Pi.single i 1)) j := by
    intro j
    rw [key]
    have : A.col j ∈ s := ⟨Pi.single j 1, single_mem_stdSimplex ℝ j, by
      simp⟩
    have := hfu _ this
    linarith
  refine ⟨⟨fun j => (hpos j).le, ?_⟩, hpos⟩
  intro h0
  have := hpos ⟨0, hn⟩
  rw [h0] at this
  simp at this

lemma stiemke {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hn : 1 ≤ n)
    (h : ¬ ∃ y, IsFeasible611 A y) : ∃ x, IsInterior65 A x := by
  set t : Set (Fin n → ℝ) := (LinearMap.range (Matrix.mulVecLin Aᵀ) : Set (Fin n → ℝ)) with ht
  have htc : IsClosed t := Submodule.closed_of_finiteDimensional _
  have htv : Convex ℝ t := (LinearMap.range (Matrix.mulVecLin Aᵀ)).convex
  have hdisj : Disjoint (stdSimplex ℝ (Fin n)) t := by
    rw [Set.disjoint_left]
    rintro a ha ⟨y, rfl⟩
    apply h
    refine ⟨y, ha.1, ?_⟩
    intro h0
    have := ha.2
    simp only [Matrix.mulVecLin_apply] at this
    rw [h0] at this
    simp at this
  obtain ⟨f, u, v, hfu, huv, hfv⟩ := geometric_hahn_banach_compact_closed
    (convex_stdSimplex ℝ (Fin n)) (isCompact_stdSimplex ℝ (Fin n)) htv htc hdisj
  have hv : v < 0 := by simpa using hfv 0 (LinearMap.range (Matrix.mulVecLin Aᵀ)).zero_mem
  have hzero : ∀ y, f (Aᵀ *ᵥ y) = 0 := by
    intro y
    by_contra hc
    have hmem : Aᵀ *ᵥ (((v - 1) / f (Aᵀ *ᵥ y)) • y) ∈ t := ⟨_, rfl⟩
    have := hfv _ hmem
    rw [Matrix.mulVec_smul, map_smul, smul_eq_mul, div_mul_cancel₀ _ hc] at this
    linarith
  have hpos : ∀ j, 0 < -f (Pi.single j 1) := by
    intro j
    have := hfu _ (single_mem_stdSimplex ℝ j)
    linarith
  refine ⟨fun j => -f (Pi.single j 1), ⟨?_, fun j => (hpos j).le, ?_⟩, hpos⟩
  · funext i
    have h1 := hzero (Pi.single i 1)
    rw [mulVec_single_one, dual_coord] at h1
    simp only [mulVec, dotProduct, Pi.zero_apply]
    have : ∑ x, A i x * -f (Pi.single x 1) = -∑ x, (Aᵀ.col i) x * f (Pi.single x 1) := by
      simp [Finset.sum_neg_distrib, Matrix.col]
    rw [this, h1, neg_zero]
  · intro h0
    have := hpos ⟨0, hn⟩
    have h2 := congrFun h0 ⟨0, hn⟩
    simp only [Pi.zero_apply] at h2
    linarith


lemma no611 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hG : ∀ T : Finset (Fin n), T.card ≤ m → LinearIndependent ℝ (fun j : T => fun i => A i j))
    (hx : ∃ x, IsFeasible65 A x) : ¬ ∃ y, IsFeasible611 A y := by
  obtain ⟨x, hAx, hx0, hxne⟩ := hx
  rintro ⟨y, hs0, hsne⟩
  set s := Aᵀ *ᵥ y with hs
  have hsum : ∑ j, x j * s j = 0 := by
    have : ∑ j, x j * s j = y ⬝ᵥ (A *ᵥ x) := by
      rw [dotProduct_mulVec, hs, mulVec_transpose, dotProduct_comm]; rfl
    rw [this, hAx, dotProduct_zero]
  have hprod : ∀ j, x j * s j = 0 := by
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hx0 j) (hs0 j))).mp hsum j
      (Finset.mem_univ j)
  set J := Finset.univ.filter (fun j => s j = 0) with hJ
  set S := Finset.univ.filter (fun j => x j ≠ 0) with hS
  have hSJ : S ⊆ J := by
    intro j hj
    simp only [hS, hJ, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rcases mul_eq_zero.mp (hprod j) with h | h
    · exact absurd h hj
    · exact h
  by_cases hm : m ≤ J.card
  · obtain ⟨T, -, hTJ, hT⟩ := Finset.exists_subsuperset_card_eq (Finset.empty_subset J)
      (by simp) hm
    have hli := hG T hT.le
    have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [hT])
    have hy : ∀ v ∈ Submodule.span ℝ (Set.range (fun j : T => fun i => A i j)), y ⬝ᵥ v = 0 := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨j, rfl⟩ := hw
        have hj : s j = 0 := by
          have := hTJ j.2
          simpa [hJ] using this
        rw [← hj, hs]
        simp [mulVec, dotProduct, mul_comm]
      | zero => simp
      | add a b _ _ ha hb => rw [dotProduct_add, ha, hb, add_zero]
      | smul c a _ ha => rw [dotProduct_smul, ha, smul_zero]
    have hyy : y ⬝ᵥ y = 0 := hy y (hspan ▸ Submodule.mem_top)
    rw [dotProduct_self_eq_zero] at hyy
    apply hsne
    rw [hs, hyy, mulVec_zero]
  · have hSm : S.card ≤ m := by
      have := Finset.card_le_card hSJ
      omega
    have hli := hG S hSm
    have hcomb : ∑ j : S, x j • (fun i => A i j) = 0 := by
      rw [Finset.sum_coe_sort S (fun j => x j • fun i => A i j), hS, Finset.sum_filter]
      funext i
      have hi := congrFun hAx i
      simp only [mulVec, dotProduct, Pi.zero_apply] at hi
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      refine Eq.trans ?_ hi
      refine Finset.sum_congr rfl (fun j _ => ?_)
      split_ifs with h
      · simp [mul_comm]
      · push Not at h; simp [h]
    have := Fintype.linearIndependent_iff.mp hli (fun j : S => x j) hcomb
    apply hxne
    funext j
    by_contra hj
    have hj' : x j ≠ 0 := hj
    have hjS : j ∈ S := by simp [hS, hj']
    exact hj (this ⟨j, hjS⟩)

end T613

open YeIPA.Random Matrix MeasureTheory ProbabilityTheory

theorem solution {m n : ℕ} (hn : 1 ≤ n) (hmn : m ≤ n) :
    ∀ᵐ A ∂gaussianMatrix m n,
      ((¬ ∃ x, IsFeasible65 (Matrix.of A) x) ∧ ∃ y, IsInterior611 (Matrix.of A) y) ∨
      ((¬ ∃ y, IsFeasible611 (Matrix.of A) y) ∧ ∃ x, IsInterior65 (Matrix.of A) x) := by
  filter_upwards [T613.ae_G hmn] with A hA
  by_cases h : ∃ x, IsFeasible65 (Matrix.of A) x
  · have h2 := T613.no611 (Matrix.of A) hA h
    exact Or.inr ⟨h2, T613.stiemke _ hn h2⟩
  · exact Or.inl ⟨h, T613.gordan _ hn h⟩
