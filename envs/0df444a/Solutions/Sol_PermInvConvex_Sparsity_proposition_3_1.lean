-- Prove2me | solution 1 for PermInvConvex.Sparsity.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:09:38.880993+00:00
-- url     : https://prove2.me/submissions/5fab80a8-890f-4802-89ab-6d27a20cb8c0

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Definitions.Def_PermInvConvex_Sparsity_Majorization
import Definitions.Def_PermInvConvex_Sparsity_Setting

open Set
open scoped Topology

namespace PermInvConvex.Sparsity

noncomputable def bodySeminorm {n : ℕ} (ns : (Fin n → ℝ) → ℝ)
    (hns : IsSymmetricGauge ns) : Seminorm ℝ (Fin n → ℝ) :=
  Seminorm.of ns hns.add_le (by simpa only [Real.norm_eq_abs] using hns.smul)

theorem body_continuous {n : ℕ} (ns : (Fin n → ℝ) → ℝ)
    (hns : IsSymmetricGauge ns) : Continuous ns := by
  have hc : ConvexOn ℝ Set.univ ns := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    calc
      ns (a • x + b • y) ≤ ns (a • x) + ns (b • y) := hns.add_le _ _
      _ = a • ns x + b • ns y := by
        rw [hns.smul, hns.smul, abs_of_nonneg ha, abs_of_nonneg hb]
        rfl
  exact continuousOn_univ.mp (hc.continuousOn isOpen_univ)

theorem body_coordinate_le {n : ℕ} (ns : (Fin n → ℝ) → ℝ)
    (hns : IsSymmetricGauge ns) (x : Fin n → ℝ) (i : Fin n) :
    |x i| * ns (Pi.single i 1) ≤ ns x := by
  classical
  let y : Fin n → ℝ := fun j => if j = i then x j else -x j
  have hy : ns y = ns x := hns.sign y x (by intro j; simp [y]; split_ifs <;> simp)
  have heq : (2 : ℝ) • (x i • Pi.single i (1 : ℝ)) = x + y := by
    ext j
    by_cases hj : j = i <;> simp [y, hj]
    ring
  have hh := hns.add_le x y
  rw [← heq, hns.smul, hns.smul, hy] at hh
  norm_num at hh
  linarith

theorem body_basis_pos {n : ℕ} (ns : (Fin n → ℝ) → ℝ)
    (hns : IsSymmetricGauge ns) (i : Fin n) : 0 < ns (Pi.single i 1) := by
  have hn := apply_nonneg (bodySeminorm ns hns) (Pi.single i (1 : ℝ))
  change 0 ≤ ns (Pi.single i 1) at hn
  apply lt_of_le_of_ne hn
  intro h
  have he := (hns.eq_zero_iff _).mp h.symm
  have := congrFun he i
  simp at this

theorem body_unit_compact {n : ℕ} (ns : (Fin n → ℝ) → ℝ)
    (hns : IsSymmetricGauge ns) : IsCompact {x | ns x ≤ 1} := by
  classical
  let B : Set (Fin n → ℝ) := Set.pi Set.univ
    (fun i => Set.Icc (-(ns (Pi.single i 1))⁻¹) (ns (Pi.single i 1))⁻¹)
  have hB : IsCompact B := isCompact_univ_pi (fun _ => isCompact_Icc)
  apply hB.of_isClosed_subset (isClosed_le (body_continuous ns hns) continuous_const)
  intro x hx i hi
  have hp := body_basis_pos ns hns i
  have habs : |x i| ≤ (ns (Pi.single i 1))⁻¹ := by
    rw [← one_div, le_div_iff₀ hp]
    exact (body_coordinate_le ns hns x i).trans hx
  exact abs_le.mp habs

theorem body_unit_convex {n : ℕ} (ns : (Fin n → ℝ) → ℝ)
    (hns : IsSymmetricGauge ns) : Convex ℝ {x | ns x ≤ 1} := by
  intro x hx y hy a b ha hb hab
  change ns (a • x + b • y) ≤ 1
  calc
    _ ≤ ns (a • x) + ns (b • y) := hns.add_le _ _
    _ = a * ns x + b * ns y := by rw [hns.smul, hns.smul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = 1 := by simpa using hab

theorem body_compact_join {n : ℕ} {s t : Set (Fin n → ℝ)}
    (hs : IsCompact s) (ht : IsCompact t) : IsCompact (convexJoin ℝ s t) := by
  have heq : convexJoin ℝ s t =
      (fun p : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        (1 - p.1) • p.2.1 + p.1 • p.2.2) '' (Icc (0 : ℝ) 1 ×ˢ (s ×ˢ t)) := by
    ext z
    simp only [mem_convexJoin, segment_eq_image, mem_image, mem_prod, mem_Icc]
    constructor
    · rintro ⟨x, hx, y, hy, a, ha, rfl⟩
      exact ⟨(a, x, y), ⟨ha, hx, hy⟩, rfl⟩
    · rintro ⟨⟨a, x, y⟩, ⟨ha, hx, hy⟩, rfl⟩
      exact ⟨x, hx, y, hy, a, ha, rfl⟩
  rw [heq]
  exact (isCompact_Icc.prod (hs.prod ht)).image (by fun_prop)

theorem body_compact_finite_hull {n : ℕ} {ι : Type*} (u : Finset ι)
    (S : ι → Set (Fin n → ℝ))
    (hS : ∀ i ∈ u, IsCompact (S i) ∧ Convex ℝ (S i)) :
    IsCompact (convexHull ℝ (⋃ i ∈ u, S i)) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | @insert a u ha ih =>
    have hSa := hS a (Finset.mem_insert_self _ _)
    have hSu := ih (fun i hi => hS i (Finset.mem_insert_of_mem hi))
    rw [Finset.set_biUnion_insert]
    by_cases hA : (S a).Nonempty
    · by_cases hU : (⋃ i ∈ u, S i).Nonempty
      · rw [convexHull_union hA hU, hSa.2.convexHull_eq]
        exact body_compact_join hSa.1 hSu
      · rw [Set.not_nonempty_iff_eq_empty.mp hU, union_empty, hSa.2.convexHull_eq]
        exact hSa.1
    · rw [Set.not_nonempty_iff_eq_empty.mp hA, empty_union]
      exact hSu

theorem body_hull_compact {n : ℕ} (ns : (Fin n → ℝ) → ℝ)
    (hns : IsSymmetricGauge ns) (K : ℕ) : IsCompact (convexHull ℝ (NK ns K)) := by
  classical
  let C : Finset (Fin n) → Set (Fin n → ℝ) := fun s =>
    {x | ns x ≤ 1} ∩ {x | ∀ i, i ∉ s → x i = 0}
  let u : Finset (Finset (Fin n)) := Finset.univ.filter (fun s => s.card ≤ K)
  have heq : NK ns K = ⋃ s ∈ u, C s := by
    ext x
    simp only [NK, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hnorm, hcard⟩
      refine ⟨Finset.univ.filter (fun i => x i ≠ 0), ?_, hnorm, ?_⟩
      · simpa [u, card] using hcard
      · intro i hi
        simpa using hi
    · rintro ⟨s, hs, hnorm, hsupport⟩
      refine ⟨hnorm, ?_⟩
      have hsub : Finset.univ.filter (fun i => x i ≠ 0) ⊆ s := by
        intro i hi
        by_contra his
        exact (Finset.mem_filter.mp hi).2 (hsupport i his)
      exact (Finset.card_le_card hsub).trans (by simpa [u] using hs)
  rw [heq]
  apply body_compact_finite_hull
  intro s hs
  have hclosed : IsClosed {x : Fin n → ℝ | ∀ i, i ∉ s → x i = 0} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply i) continuous_const
  constructor
  · exact (body_unit_compact ns hns).inter_right hclosed
  · apply (body_unit_convex ns hns).inter
    intro x hx y hy a b ha hb hab i hi
    simp [Pi.add_apply, Pi.smul_apply, hx i hi, hy i hi]

theorem body_hull_interior {n : ℕ} (ns : (Fin n → ℝ) → ℝ)
    (hns : IsSymmetricGauge ns) (K : ℕ) (hK : 1 ≤ K) :
    (interior (convexHull ℝ (NK ns K))).Nonempty := by
  classical
  have hzero : (0 : Fin n → ℝ) ∈ NK ns K := by
    simp [NK, card, (hns.eq_zero_iff 0).mpr rfl]
  have hbasis (i : Fin n) : Pi.single i (1 : ℝ) ∈ Submodule.span ℝ (NK ns K) := by
    have hp := body_basis_pos ns hns i
    have hnormalized : (ns (Pi.single i 1))⁻¹ • Pi.single i (1 : ℝ) ∈ NK ns K := by
      constructor
      · rw [hns.smul, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
      · apply le_trans _ hK
        unfold card
        calc
          _ ≤ ({i} : Finset (Fin n)).card := by
            apply Finset.card_le_card
            intro j hj
            by_contra hj'
            have hji : j ≠ i := by simpa using hj'
            simp [Pi.single_apply, hji] at hj
          _ = 1 := Finset.card_singleton _
    have hm := (Submodule.span ℝ (NK ns K)).smul_mem (ns (Pi.single i 1))
      (Submodule.subset_span hnormalized)
    simpa [smul_smul, hp.ne'] using hm
  have hspan : Submodule.span ℝ (NK ns K) = ⊤ := by
    apply top_unique
    intro x hx
    have heq : x = ∑ i, x i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply, Finset.sum_apply]
    rw [heq]
    exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (hbasis i))
  apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
  apply SetLike.coe_injective
  calc
    (affineSpan ℝ (NK ns K) : Set (Fin n → ℝ)) =
        (affineSpan ℝ (insert 0 (NK ns K)) : Set (Fin n → ℝ)) := by
          rw [insert_eq_of_mem hzero]
    _ = (Submodule.span ℝ (NK ns K) : Set (Fin n → ℝ)) := affineSpan_insert_zero _
    _ = (⊤ : AffineSubspace ℝ (Fin n → ℝ)) := by rw [hspan]; rfl

end PermInvConvex.Sparsity

open PermInvConvex.Sparsity

theorem solution {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (hK : 1 < K) (hKn : K < n) :
    IsConvexBody (convexHull ℝ (NK ns K)) := by
  exact ⟨body_hull_compact ns hns K, convex_convexHull ℝ _,
    body_hull_interior ns hns K hK.le⟩

