-- Prove2me | solution 1 for RSSubspaceDesign.proposition_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:58:22.753148+00:00
-- url     : https://prove2.me/submissions/542d416f-145a-43c1-a220-7c089ad23d1d

import Mathlib
import Definitions.Def_RSSubspaceDesign_IsEffective
import Definitions.Def_RSSubspaceDesign_ratRank
import Definitions.Def_RSSubspaceDesign_ratFuncAlgebra
import Theorems.Thm_RSSubspaceDesign_theorem_2_14
import Theorems.Thm_RSSubspaceDesign_corollary_2_16
import Theorems.Thm_RSSubspaceDesign_lemma_2_20


-- ===== P43_indep.lean
open Polynomial

namespace RSSDP43

theorem ratAlg_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F] (c : K[X]) :
    letI := RSSubspaceDesign.ratFuncAlgebra K F
    algebraMap (RatFunc K) (RatFunc F) (algebraMap K[X] (RatFunc K) c) =
      algebraMap F[X] (RatFunc F) (c.map (algebraMap K F)) := by
  letI := RSSubspaceDesign.ratFuncAlgebra K F
  show RatFunc.mapRingHom _ _ _ = _
  rw [RatFunc.coe_mapRingHom_eq_coe_map]
  have h := RatFunc.map_apply_div (Polynomial.mapRingHom (algebraMap K F))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap K F).injective)) c 1
  simp only [map_one, div_one] at h
  simpa using h

theorem ratAlg_smul {K F : Type*} [Field K] [Field F] [Algebra K F] (c : K[X]) (u : F[X]) :
    letI := RSSubspaceDesign.ratFuncAlgebra K F
    algebraMap F[X] (RatFunc F) (c.map (algebraMap K F) * u) =
      (algebraMap K[X] (RatFunc K) c) • algebraMap F[X] (RatFunc F) u := by
  letI := RSSubspaceDesign.ratFuncAlgebra K F
  rw [Algebra.smul_def, ratAlg_algebraMap, map_mul]

/-- `K[X]`-independence of polynomials gives `K(X)`-independence of their images in `F(X)`. -/
theorem linIndep_of_polyIndep {K F : Type*} [Field K] [Field F] [Algebra K F] {t : ℕ}
    (u : Fin t → F[X])
    (hu : ∀ c : Fin t → K[X], ∑ a, (c a).map (algebraMap K F) * u a = 0 → c = 0) :
    letI := RSSubspaceDesign.ratFuncAlgebra K F
    LinearIndependent (RatFunc K) fun a => algebraMap F[X] (RatFunc F) (u a) := by
  letI := RSSubspaceDesign.ratFuncAlgebra K F
  rw [Fintype.linearIndependent_iff]
  intro ℓ hℓ a
  obtain ⟨⟨D, hD⟩, hDint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors K[X])
    (Finset.univ : Finset (Fin t)) ℓ
  have hint : ∀ a, ∃ c : K[X], algebraMap K[X] (RatFunc K) c = D • ℓ a :=
    fun a => hDint a (Finset.mem_univ a)
  choose c hc using hint
  have hsum : ∑ a, (c a).map (algebraMap K F) * u a = 0 := by
    apply (IsFractionRing.injective F[X] (RatFunc F))
    rw [map_zero, map_sum, Finset.sum_congr rfl (fun a _ => ratAlg_smul (K := K) (c a) (u a))]
    simp_rw [hc, Algebra.smul_def (A := RatFunc K) D, mul_smul]
    rw [← Finset.smul_sum, hℓ, smul_zero]
  have hc0 := congrFun (hu c hsum) a
  have h1 := hc a
  rw [hc0, Pi.zero_apply, map_zero, Algebra.smul_def] at h1
  have hD0 : algebraMap K[X] (RatFunc K) D ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))]
    exact nonZeroDivisors.ne_zero hD
  rcases mul_eq_zero.mp h1.symm with h | h
  · exact absurd h hD0
  · exact h

end RSSDP43


-- ===== P43_det.lean
open Polynomial

namespace RSSDP43

theorem pow_dvd_prod_of_card {F : Type*} [Field F] {t : ℕ} (f : Fin t → F[X]) (x : F)
    (S : Finset (Fin t)) (hS : ∀ j ∈ S, (f j).eval x = 0) :
    (X - C x) ^ S.card ∣ ∏ j, f j := by
  classical
  have h1 : (X - C x) ^ S.card = ∏ j ∈ S, (X - C x) := by simp
  rw [h1, ← Finset.prod_mul_prod_compl S]
  apply dvd_mul_of_dvd_left
  apply Finset.prod_dvd_prod_of_dvd
  intro j hj
  exact dvd_iff_isRoot.mpr (hS j hj)

theorem rootMultiplicity_det_ge {F : Type*} [Field F] {t : ℕ}
    (M : Matrix (Fin t) (Fin t) F[X]) (x : F) (J R : Finset (Fin t))
    (hM : ∀ s ∉ R, ∀ j ∈ J, (M s j).eval x = 0) (hdet : M.det ≠ 0) :
    J.card - R.card ≤ M.det.rootMultiplicity x := by
  classical
  rw [le_rootMultiplicity_iff hdet, Matrix.det_apply]
  apply Finset.dvd_sum
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul]
  apply Dvd.dvd.mul_left
  let S := J.filter (fun j => σ j ∉ R)
  have hS : ∀ j ∈ S, (M (σ j) j).eval x = 0 := by
    intro j hj
    simp only [S, Finset.mem_filter] at hj
    exact hM _ hj.2 _ hj.1
  have hcard : J.card - R.card ≤ S.card := by
    have h2 : (J.filter (fun j => σ j ∈ R)).card ≤ R.card := by
      have : (J.filter (fun j => σ j ∈ R)).map σ.toEmbedding ⊆ R := by
        intro y hy
        simp only [Finset.mem_map, Finset.mem_filter, Equiv.toEmbedding_apply] at hy
        obtain ⟨j, ⟨_, hj⟩, rfl⟩ := hy
        exact hj
      simpa using Finset.card_le_card this
    have h3 := Finset.card_filter_add_card_filter_not (s := J) (fun j => σ j ∈ R)
    simp only [S]
    omega
  exact (pow_dvd_pow _ hcard).trans (pow_dvd_prod_of_card (fun j => M (σ j) j) x S hS)

end RSSDP43

namespace RSSDP43

theorem natDegree_det_le_rows {R : Type*} [CommRing R] {t : ℕ}
    (M : Matrix (Fin t) (Fin t) R[X]) (dr : Fin t → ℕ)
    (h : ∀ s j, (M s j).natDegree ≤ dr s) : M.det.natDegree ≤ ∑ s, dr s := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ j, (M (σ j) j).natDegree ≤ ∑ j, dr (σ j) := Finset.sum_le_sum fun j _ => h _ _
    _ = ∑ s, dr s := Equiv.sum_comp σ dr

theorem natDegree_det_le_cols {R : Type*} [CommRing R] {t : ℕ}
    (M : Matrix (Fin t) (Fin t) R[X]) (dc : Fin t → ℕ)
    (h : ∀ s j, (M s j).natDegree ≤ dc j) : M.det.natDegree ≤ ∑ j, dc j := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  exact Finset.sum_le_sum fun j _ => h _ _

theorem sum_rootMultiplicity_le {F : Type*} [Field F] {n : ℕ} (α : Fin n → F)
    (hα : Function.Injective α) (P : F[X]) (hP : P ≠ 0) :
    ∑ i, P.rootMultiplicity (α i) ≤ P.natDegree := by
  classical
  calc ∑ i, P.rootMultiplicity (α i) = ∑ i, P.roots.count (α i) := by
        simp [Polynomial.count_roots]
    _ = ∑ y ∈ Finset.univ.image α, P.roots.count y := by
        rw [Finset.sum_image (fun x _ y _ h => hα h)]
    _ ≤ Multiset.card P.roots := by
        calc ∑ y ∈ Finset.univ.image α, P.roots.count y
            ≤ ∑ y ∈ Finset.univ.image α ∪ P.roots.toFinset, P.roots.count y :=
              Finset.sum_le_sum_of_subset Finset.subset_union_left
          _ = Multiset.card P.roots := Multiset.sum_count_eq_card (fun a ha =>
              Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ha))
    _ ≤ P.natDegree := Polynomial.card_roots' P

end RSSDP43


-- ===== P43_point.lean

open Polynomial

namespace RSSDP43

/-- The `K`-span of the maximal minors of `C`. -/
noncomputable def QW {K : Type*} [Field K] {t e : ℕ} (C : Matrix (Fin t) (Fin e) K[X]) :
    Submodule K K[X] :=
  Submodule.span K (Set.range fun S : {S : Finset (Fin e) // S.card = t} =>
    (C.submatrix id (S.1.orderEmbOfFin S.2)).det)

theorem det_mem_QW {K : Type*} [Field K] {t e : ℕ} (ht : 1 ≤ t) (hte : t ≤ e)
    (C : Matrix (Fin t) (Fin e) K[X]) (T : Matrix (Fin e) (Fin t) K) :
    (C * T.map Polynomial.C).det ∈ QW C := by
  have hinj : Function.Injective (algebraMap K[X] (RatFunc K)) := IsFractionRing.injective _ _
  have hCB := RSSubspaceDesign.theorem_2_14 ht hte (C.map (algebraMap K[X] (RatFunc K)))
    ((T.map Polynomial.C).map (algebraMap K[X] (RatFunc K)))
  have hdet : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin m) K[X]),
      (M.map (algebraMap K[X] (RatFunc K))).det = algebraMap K[X] (RatFunc K) M.det :=
    fun M => (RingHom.map_det _ M).symm
  rw [← Matrix.map_mul, hdet] at hCB
  have hsub : ∀ {m : ℕ} {a b : Type} (M : Matrix a b K[X]) (r : Fin m → a) (c : Fin m → b),
      (M.map (algebraMap K[X] (RatFunc K))).submatrix r c =
        (M.submatrix r c).map (algebraMap K[X] (RatFunc K)) := fun _ _ _ => rfl
  simp only [hsub, hdet] at hCB
  have key : (C * T.map Polynomial.C).det = ∑ S : {S : Finset (Fin e) // S.card = t},
      (T.submatrix (S.1.orderEmbOfFin S.2) id).det • (C.submatrix id (S.1.orderEmbOfFin S.2)).det := by
    apply hinj
    rw [hCB, map_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Algebra.smul_def, map_mul, mul_comm]
    congr 2
    rw [Polynomial.algebraMap_eq, RingHom.map_det]
    rfl
  rw [key]
  exact Submodule.sum_mem _ fun S _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, rfl⟩)

end RSSDP43

namespace RSSDP43

open Classical in
theorem perPoint {K F : Type*} [Field K] [Field F] [Algebra K F]
    (W : Submodule K F[X]) {t e : ℕ} (ht : 1 ≤ t) (hte : t ≤ e)
    (u : Fin t → F[X]) (C : Matrix (Fin t) (Fin e) K[X]) (wb : Module.Basis (Fin e) K W)
    (hw : ∀ l, (wb l : F[X]) = ∑ a, (C a l).map (algebraMap K F) * u a)
    (σs : Fin t → (F ≃ₐ[K] F))
    (hP : (Matrix.of fun s a => (u a).map (σs s).toRingEquiv.toRingHom).det ≠ 0)
    (hrank : letI := RSSubspaceDesign.ratFuncAlgebra K F
       Module.finrank (RatFunc K)
        (Submodule.span (RatFunc K) (algebraMap F[X] (RatFunc F) '' (W : Set F[X]))) = t)
    (x : F) :
    ∃ q ∈ QW C, q ≠ 0 ∧
      RSSubspaceDesign.ratRank K {f : F[X] | f ∈ W ∧ f.eval x = 0} ≤
        (Finset.univ.filter fun s => σs s x ≠ x).card +
        (Matrix.of fun s a => (u a).map (σs s).toRingEquiv.toRingHom).det.rootMultiplicity x +
        (q.map (algebraMap K F)).rootMultiplicity x := by
  classical
  letI := RSSubspaceDesign.ratFuncAlgebra K F
  set L := RatFunc K
  set ι := algebraMap F[X] (RatFunc F) with hιdef
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  set S : Set (RatFunc F) := ι '' (W : Set F[X]) with hSdef
  set S0 : Set (RatFunc F) := ι '' {f : F[X] | f ∈ W ∧ f.eval x = 0} with hS0def
  -- the span of S is finite dimensional of dimension t
  haveI hfin : Module.Finite L (Submodule.span L S) :=
    Module.finite_of_finrank_pos (by rw [hrank]; omega)
  obtain ⟨s0, hs0S0, hs0span, hs0li⟩ := exists_linearIndependent L S0
  have hS0S : S0 ⊆ S := Set.image_mono (fun f hf => hf.1)
  obtain ⟨bb, hbbS, hs0bb, hSbb, hbbli⟩ :=
    exists_linearIndepOn_id_extension (K := L) hs0li (hs0S0.trans hS0S)
  have hspan_bb : Submodule.span L bb = Submodule.span L S :=
    le_antisymm (Submodule.span_mono hbbS) (Submodule.span_le.mpr hSbb)
  -- finiteness of bb
  have hbbfin : Finite bb := by
    let fam : bb → Submodule.span L S := fun y => ⟨y.1, Submodule.subset_span (hbbS y.2)⟩
    have hli : LinearIndependent L fam := by
      apply LinearIndependent.of_comp (Submodule.span L S).subtype
      exact hbbli
    exact hli.finite
  haveI : Fintype bb := Fintype.ofFinite bb
  haveI : Fintype s0 := Set.Finite.fintype ((Set.toFinite bb).subset hs0bb)
  have hcard_bb : Fintype.card bb = t := by
    have h1 := finrank_span_set_eq_card hbbli
    rw [hspan_bb, hrank] at h1
    rw [h1, Set.toFinset_card]
  have hcard_s0 : RSSubspaceDesign.ratRank K {f : F[X] | f ∈ W ∧ f.eval x = 0} =
      Fintype.card s0 := by
    have h1 := finrank_span_set_eq_card hs0li
    rw [hs0span] at h1
    rw [Set.toFinset_card] at h1
    exact h1
  -- enumerate bb
  let φ : Fin t ≃ bb := (Fintype.equivFinOfCardEq hcard_bb).symm
  have hφS : ∀ j, ∃ h : F[X], h ∈ W ∧ ι h = (φ j).1 := by
    intro j
    obtain ⟨h, hh, he⟩ := hbbS (φ j).2
    exact ⟨h, hh, he⟩
  choose hh hhW hhι using hφS
  -- the columns indexed by s0 vanish at x
  set J : Finset (Fin t) := Finset.univ.filter fun j => (φ j).1 ∈ s0 with hJdef
  have hJcard : J.card = Fintype.card s0 := by
    rw [← Set.toFinset_card]
    refine Finset.card_bij (fun j _ => (φ j).1) ?_ ?_ ?_
    · intro j hj
      simp only [hJdef, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simpa using hj
    · intro j₁ _ j₂ _ h
      exact φ.injective (Subtype.ext h)
    · intro y hy
      have hy' : y ∈ s0 := by simpa using hy
      refine ⟨φ.symm ⟨y, hs0bb hy'⟩, ?_, ?_⟩
      · simp [hJdef, hy']
      · simp
  have hJzero : ∀ j ∈ J, (hh j).eval x = 0 := by
    intro j hj
    simp only [hJdef, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨f, ⟨_, hfx⟩, hfe⟩ := hs0S0 hj
    have : f = hh j := hι (hfe.trans (hhι j).symm)
    rw [← this]; exact hfx
  -- coordinates of hh in the basis
  let T : Matrix (Fin e) (Fin t) K := fun l j => wb.repr ⟨hh j, hhW j⟩ l
  have hhT : ∀ j, hh j = ∑ l, T l j • (wb l : F[X]) := by
    intro j
    have := congrArg Subtype.val (wb.sum_repr ⟨hh j, hhW j⟩)
    rw [Submodule.coe_sum] at this
    exact this.symm
  set CT : Matrix (Fin t) (Fin t) K[X] := C * T.map Polynomial.C with hCTdef
  have hhCT : ∀ j, hh j = ∑ a, (CT a j).map (algebraMap K F) * u a := by
    intro j
    rw [hhT j]
    simp_rw [hw, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hCTdef, Matrix.mul_apply, Matrix.map_apply, Polynomial.map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Algebra.smul_def, Polynomial.algebraMap_apply]
    ring
  -- the matrix of conjugates of the hh's factors through that of the u's
  set U : Matrix (Fin t) (Fin t) F[X] :=
    Matrix.of fun s a => (u a).map (σs s).toRingEquiv.toRingHom with hUdef
  set H : Matrix (Fin t) (Fin t) F[X] :=
    Matrix.of fun s j => (hh j).map (σs s).toRingEquiv.toRingHom with hHdef
  have hσK : ∀ s, ((σs s).toRingEquiv.toRingHom).comp (algebraMap K F) = algebraMap K F := by
    intro s; ext c; exact (σs s).commutes c
  have hHU : H = U * CT.map (Polynomial.map (algebraMap K F)) := by
    refine Matrix.ext fun s j => ?_
    simp only [hHdef, hUdef, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
    rw [hhCT j, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_map, hσK, mul_comm]
  set q : K[X] := CT.det with hqdef
  have hdetH : H.det = U.det * q.map (algebraMap K F) := by
    rw [hHU, Matrix.det_mul]
    congr 1
    rw [hqdef, ← Polynomial.coe_mapRingHom, RingHom.map_det]
    rfl
  -- q ≠ 0
  have hq0 : q ≠ 0 := by
    intro hq
    have hdetL : (CT.map (algebraMap K[X] L)).det = 0 := by
      rw [show (CT.map (algebraMap K[X] L)).det = algebraMap K[X] L CT.det from
        (RingHom.map_det _ _).symm, ← hqdef, hq, map_zero]
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetL
    have hli : LinearIndependent L fun j => ι (hh j) := by
      have : (fun j => ι (hh j)) = (Subtype.val : bb → RatFunc F) ∘ φ := by
        funext j; exact hhι j
      rw [this]
      exact (hbbli.linearIndependent).comp φ φ.injective
    apply hv0
    rw [Fintype.linearIndependent_iff] at hli
    funext j
    apply hli v ?_ j
    calc ∑ j, v j • ι (hh j)
        = ∑ j, v j • ∑ a, (algebraMap K[X] L (CT a j)) • ι (u a) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hhCT j, map_sum]
          congr 1
          exact Finset.sum_congr rfl fun a _ => ratAlg_smul (CT a j) (u a)
      _ = ∑ a, (∑ j, algebraMap K[X] L (CT a j) * v j) • ι (u a) := by
          simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
          rw [mul_comm]
      _ = 0 := by
          refine Finset.sum_eq_zero fun a _ => ?_
          have := congrFun hv a
          simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at this
          rw [this, zero_smul]
  -- multiplicities
  have hqmap0 : q.map (algebraMap K F) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K F).injective).mpr hq0
  have hHne : H.det ≠ 0 := by
    rw [hdetH]; exact mul_ne_zero hP hqmap0
  set R : Finset (Fin t) := Finset.univ.filter fun s => σs s x ≠ x with hRdef
  have hzero : ∀ s ∉ R, ∀ j ∈ J, (H s j).eval x = 0 := by
    intro s hs j hj
    have hsx : σs s x = x := by
      by_contra hne
      exact hs (by simp [hRdef, hne])
    simp only [hHdef, Matrix.of_apply]
    have h1 : ((hh j).map (σs s).toRingEquiv.toRingHom).eval x =
        (σs s).toRingEquiv.toRingHom ((hh j).eval x) := by
      conv_lhs => rw [← hsx]
      rw [Polynomial.eval_map]
      exact Polynomial.eval₂_hom _ _
    rw [h1, hJzero j hj, map_zero]
  have hm := rootMultiplicity_det_ge H x J R hzero hHne
  rw [hdetH, Polynomial.rootMultiplicity_mul (hdetH ▸ hHne)] at hm
  refine ⟨q, det_mem_QW ht hte C T, hq0, ?_⟩
  rw [hcard_s0, ← hJcard]
  omega

end RSSDP43


-- ===== P43_main.lean

open Polynomial RSSubspaceDesign RSSDP43

theorem solution {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F]
    {n g b r k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (α : Fin n → F) (hα : IsEffective K n g b r α)
    (W : Submodule K F[X]) (hW0 : W ≠ ⊥) (hWk : W ≤ (degreeLT F k).restrictScalars K)
    (hWr : Module.finrank K W ≤ r) :
    (∑ i : Fin n, (ratRank K {f : F[X] | f ∈ W ∧ f.eval (α i) = 0} : ℝ)) ≤
      (ratRank K (W : Set F[X]) : ℝ) * ((k : ℝ) - 1) +
        (b : ℝ) * ratRank K (W : Set F[X]) * Real.logb 2 (ratRank K (W : Set F[X])) := by
  classical
  obtain ⟨hn1, hg1, hbn, hr2, hinj, ⟨σ, hσ, hσb⟩, hMB⟩ := hα
  letI := ratFuncAlgebra K F
  haveI : Fintype F := Fintype.ofFinite F
  set L := RatFunc K
  set ι := algebraMap F[X] (RatFunc F) with hιdef
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  -- finite dimensionality of W
  haveI : Finite K := Finite.of_injective _ (algebraMap K F).injective
  haveI : Module.Finite K F := Module.Finite.of_finite
  have hdegfin : ((degreeLT F k : Submodule F F[X]) : Set F[X]).Finite := by
    haveI : Finite (degreeLT F k) := Finite.of_injective _ (degreeLTEquiv F k).injective
    exact Set.toFinite _
  haveI : Finite W := (hdegfin.subset (fun x hx => hWk hx)).to_subtype
  haveI hWfin : FiniteDimensional K W := Module.Finite.of_finite
  set A : Submodule L (RatFunc F) := Submodule.span L (ι '' (W : Set F[X])) with hAdef
  set t := Module.finrank L A with htdef
  have htrr : ratRank K (W : Set F[X]) = t := rfl
  rw [htrr]
  set e := Module.finrank K W with hedef
  let wb := Module.finBasis K W
  -- A is spanned by the images of the basis
  have hAspan : A = Submodule.span L (Set.range fun l => ι (wb l : F[X])) := by
    apply le_antisymm
    · rw [hAdef, Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      have hfs : ∑ l, ((wb.repr ⟨f, hf⟩ l • wb l : W) : F[X]) = f := by
        have := congrArg Subtype.val (wb.sum_repr ⟨f, hf⟩)
        rw [Submodule.coe_sum] at this
        exact this
      rw [← hfs, map_sum]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [Submodule.coe_smul, Algebra.smul_def, map_mul]
      have h1 : ι (algebraMap K F[X] (wb.repr ⟨f, hf⟩ l)) =
          algebraMap L (RatFunc F) (algebraMap K L (wb.repr ⟨f, hf⟩ l)) := by
        rw [Polynomial.algebraMap_apply, ← Polynomial.map_C, ← ratAlg_algebraMap]
        rfl
      rw [h1, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    · rw [hAdef, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact Submodule.subset_span ⟨_, (wb l).2, rfl⟩
  have hte : t ≤ e := by
    rw [htdef, hAspan]
    exact (finrank_range_le_card _).trans (by simp [hedef])
  have ht1 : 1 ≤ t := by
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    haveI : Module.Finite L A := by rw [hAspan]; exact FiniteDimensional.span_of_finite _ (Set.finite_range _)
    have hA0 : A ≠ ⊥ := by
      intro h
      have : ι w ∈ A := Submodule.subset_span ⟨w, hwW, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hw0 (hι (this.trans (map_zero ι).symm))
    exact Nat.one_le_iff_ne_zero.mpr (fun h0 => hA0 (Submodule.finrank_eq_zero.mp h0))
  -- reduced basis of A ∩ F[X]
  obtain ⟨u, hu_mem, hu_ind, hu_gen, hu_deg, -⟩ := corollary_2_16 (K := K) (F := F) t A rfl
  have hLI := linIndep_of_polyIndep u hu_ind
  obtain ⟨B, hBcard, hBdown, hBdet, hBmove⟩ := lemma_2_20 hg1 ht1 σ hσ u hLI
  let eB : Fin t ≃ B := (B.equivFinOfCardEq hBcard).symm
  let σs : Fin t → (F ≃ₐ[K] F) := fun s => (List.ofFn fun j => σ j ^ (eB s : Fin g → ℕ) j).prod
  have hP : (Matrix.of fun s a => (u a).map (σs s).toRingEquiv.toRingHom).det ≠ 0 := hBdet eB
  -- coordinates of the basis of W
  have hgen : ∀ l, ∃ c : Fin t → K[X], (wb l : F[X]) = ∑ a, (c a).map (algebraMap K F) * u a :=
    fun l => hu_gen _ (Submodule.subset_span ⟨_, (wb l).2, rfl⟩)
  choose Cf hCf using hgen
  let C : Matrix (Fin t) (Fin e) K[X] := fun a l => Cf l a
  have hw : ∀ l, (wb l : F[X]) = ∑ a, (C a l).map (algebraMap K F) * u a := hCf
  -- per point bounds
  have hpt := fun i => perPoint W ht1 hte u C wb hw σs hP rfl (α i)
  choose qs hqsQ hqs0 hqsle using hpt
  -- degree bookkeeping
  have hu0 : ∀ a, u a ≠ 0 := by
    intro a ha
    have := congrFun (hu_ind (Pi.single a 1) (by
      refine Finset.sum_eq_zero fun a' _ => ?_
      by_cases h : a' = a
      · subst h; rw [ha, mul_zero]
      · rw [Pi.single_eq_of_ne h, Polynomial.map_zero, zero_mul])) a
    simp at this
  have hdeg_al : ∀ a l, (u a).degree + (C a l).degree < k := by
    intro a l
    have h1 := hu_deg (fun a => C a l)
    rw [← hw l] at h1
    have h2 : (wb l : F[X]).degree < k := by
      have := hWk (wb l).2
      simpa [Polynomial.mem_degreeLT] using this
    rw [h1] at h2
    exact (Finset.sup_lt_iff (WithBot.bot_lt_coe k)).mp h2 a (Finset.mem_univ a)
  have hrow : ∀ a, ∃ l, C a l ≠ 0 := by
    intro a
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hQ : QW C = ⊥ := by
      rw [QW, Submodule.span_eq_bot]
      rintro _ ⟨S, rfl⟩
      exact Matrix.det_eq_zero_of_row_eq_zero a (fun l => hcon _)
    have := hqsQ ⟨0, hn1⟩
    rw [hQ, Submodule.mem_bot] at this
    exact hqs0 _ this
  have hnu : ∀ a, (u a).natDegree ≤ k - 1 := by
    intro a
    obtain ⟨l, hl⟩ := hrow a
    have h := hdeg_al a l
    rw [Polynomial.degree_eq_natDegree (hu0 a), Polynomial.degree_eq_natDegree hl] at h
    have : (u a).natDegree + (C a l).natDegree < k := by exact_mod_cast h
    omega
  have hCdeg : ∀ a l, (C a l).natDegree ≤ k - 1 - (u a).natDegree := by
    intro a l
    by_cases hl : C a l = 0
    · rw [hl, Polynomial.natDegree_zero]; exact Nat.zero_le _
    · have h := hdeg_al a l
      rw [Polynomial.degree_eq_natDegree (hu0 a), Polynomial.degree_eq_natDegree hl] at h
      have : (u a).natDegree + (C a l).natDegree < k := by exact_mod_cast h
      omega
  set AW : ℕ := ∑ a, (k - 1 - (u a).natDegree) with hAWdef
  have hminor : ∀ S : {S : Finset (Fin e) // S.card = t},
      (C.submatrix id (S.1.orderEmbOfFin S.2)).det.natDegree ≤ AW :=
    fun S => natDegree_det_le_rows _ _ (fun a l => hCdeg a _)
  have hQAW : QW C ≤ degreeLT K (AW + 1) := by
    rw [QW, Submodule.span_le]
    rintro _ ⟨S, rfl⟩
    rw [SetLike.mem_coe, Polynomial.mem_degreeLT]
    calc _ ≤ ((C.submatrix id (S.1.orderEmbOfFin S.2)).det.natDegree : WithBot ℕ) :=
          Polynomial.degree_le_natDegree
      _ < (AW + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_of_le (hminor S)
  have hAWt : AW ≤ t * (k - 1) := by
    calc AW ≤ ∑ _a : Fin t, (k - 1) := Finset.sum_le_sum fun a _ => Nat.sub_le _ _
      _ = t * (k - 1) := by simp
  have hter : t ≤ r := hte.trans hWr
  have hQle : QW C ≤ degreeLT K (n * r) := by
    refine hQAW.trans (Polynomial.degreeLT_mono ?_)
    have h1 : t * (k - 1) ≤ r * (n - 1) := Nat.mul_le_mul hter (by omega)
    have h2 : r * (n - 1) + 1 ≤ n * r := by
      have : r * (n - 1) + r = n * r := by
        rw [mul_comm n r, ← Nat.mul_succ]; congr 1; omega
      omega
    omega
  have hQne : QW C ≠ ⊥ := by
    intro h
    have := hqsQ ⟨0, hn1⟩
    rw [h, Submodule.mem_bot] at this
    exact hqs0 _ this
  have hQrank : Module.finrank K (QW C) ≤ 2 ^ r := by
    calc Module.finrank K (QW C) ≤ Fintype.card {S : Finset (Fin e) // S.card = t} :=
          finrank_range_le_card _
      _ ≤ Fintype.card (Finset (Fin e)) := Fintype.card_subtype_le _
      _ = 2 ^ e := by simp
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hWr
  obtain ⟨q₀, hq₀Q, hq₀0, hq₀le⟩ := hMB (QW C) hQle hQne hQrank qs (fun i => ⟨hqsQ i, hqs0 i⟩)
  have hq₀deg : q₀.natDegree ≤ AW := by
    have := hQAW hq₀Q
    rw [Polynomial.mem_degreeLT, Polynomial.degree_eq_natDegree hq₀0] at this
    exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
  -- the determinant P
  set P : F[X] := (Matrix.of fun s a => (u a).map (σs s).toRingEquiv.toRingHom).det with hPdef
  have hPdeg : P.natDegree ≤ ∑ a, (u a).natDegree :=
    natDegree_det_le_cols _ _ (fun s a => by
      simp only [Matrix.of_apply]
      rw [Polynomial.natDegree_map_eq_of_injective (σs s).toRingEquiv.toRingHom.injective])
  have hPmult := sum_rootMultiplicity_le α hinj P hP
  have hnuAW : ∑ a, (u a).natDegree + AW = t * (k - 1) := by
    rw [hAWdef, ← Finset.sum_add_distrib]
    calc ∑ a, ((u a).natDegree + (k - 1 - (u a).natDegree)) = ∑ _a : Fin t, (k - 1) :=
          Finset.sum_congr rfl fun a _ => by have := hnu a; omega
      _ = t * (k - 1) := by simp
  -- movement
  let τω : (Fin g → ℕ) → (F ≃ₐ[K] F) := fun ω => (List.ofFn fun j => σ j ^ ω j).prod
  have hRcard : ∀ i, (Finset.univ.filter fun s => σs s (α i) ≠ α i).card =
      (B.filter fun ω => τω ω (α i) ≠ α i).card := by
    intro i
    refine Finset.card_bij (fun s _ => (eB s : Fin g → ℕ)) ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      exact Finset.mem_filter.mpr ⟨(eB s).2, hs⟩
    · intro s₁ _ s₂ _ h
      exact eB.injective (Subtype.ext h)
    · intro ω hω
      have hωB := (Finset.mem_filter.mp hω).1
      refine ⟨eB.symm ⟨ω, hωB⟩, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have : (eB (eB.symm ⟨ω, hωB⟩) : Fin g → ℕ) = ω := by simp
      show τω (eB (eB.symm ⟨ω, hωB⟩) : Fin g → ℕ) (α i) ≠ α i
      rw [this]; exact (Finset.mem_filter.mp hω).2
  have hmove := hBmove n α hinj
  have hsup : (Finset.univ.sup fun j => (Finset.univ.filter fun i => σ j (α i) ≠ α i).card) ≤ b :=
    Finset.sup_le fun j _ => hσb j
  -- final count
  have hnat : ∀ i, ratRank K {f : F[X] | f ∈ W ∧ f.eval (α i) = 0} ≤
      (B.filter fun ω => τω ω (α i) ≠ α i).card + P.rootMultiplicity (α i) +
        ((qs i).map (algebraMap K F)).rootMultiplicity (α i) := by
    intro i; rw [← hRcard i]; exact hqsle i
  have hsumnat : (∑ i, ratRank K {f : F[X] | f ∈ W ∧ f.eval (α i) = 0} : ℝ) ≤
      (∑ i, ((B.filter fun ω => τω ω (α i) ≠ α i).card : ℝ)) + (t * (k - 1) : ℕ) := by
    have h1 : ∑ i, ratRank K {f : F[X] | f ∈ W ∧ f.eval (α i) = 0} ≤
        ∑ i, (B.filter fun ω => τω ω (α i) ≠ α i).card + (t * (k - 1)) := by
      calc _ ≤ ∑ i, ((B.filter fun ω => τω ω (α i) ≠ α i).card + P.rootMultiplicity (α i) +
            ((qs i).map (algebraMap K F)).rootMultiplicity (α i)) := Finset.sum_le_sum fun i _ => hnat i
        _ = ∑ i, (B.filter fun ω => τω ω (α i) ≠ α i).card + ∑ i, P.rootMultiplicity (α i) +
            ∑ i, ((qs i).map (algebraMap K F)).rootMultiplicity (α i) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        _ ≤ _ := by
              have := hq₀le.trans hq₀deg
              omega
    exact_mod_cast h1
  have hlog : 0 ≤ Real.logb 2 t := Real.logb_nonneg (by norm_num) (by exact_mod_cast ht1)
  have hmove' : (∑ i, ((B.filter fun ω => τω ω (α i) ≠ α i).card : ℝ)) ≤ t * Real.logb 2 t * b := by
    refine hmove.trans ?_
    apply mul_le_mul_of_nonneg_left (by exact_mod_cast hsup)
    positivity
  have hk : ((t * (k - 1) : ℕ) : ℝ) = (t : ℝ) * ((k : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hk1, Nat.cast_one]
  rw [hk] at hsumnat
  nlinarith [hsumnat, hmove']

