-- Prove2me | solution 1 for PermInvConvex.Sparsity.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:16:08.387983+00:00
-- url     : https://prove2.me/submissions/ae4cbd20-1ae1-4a6c-8e4d-619aad9b3900

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Definitions.Def_PermInvConvex_Sparsity_Majorization
import Definitions.Def_PermInvConvex_Sparsity_Setting
import Theorems.Thm_PermInvConvex_Sparsity_proposition_3_1

open PermInvConvex.Sparsity

namespace GaugeNormAux

def signMap {n : ℕ} (s : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := s i * x i
  map_add' x y := by ext i; exact mul_add _ _ _
  map_smul' a x := by
    ext i
    change s i * (a * x i) = a * (s i * x i)
    ring

def permMap {n : ℕ} (σ : Equiv.Perm (Fin n)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x := x ∘ σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma card_signMap_le {n : ℕ} (s x : Fin n → ℝ) : card (signMap s x) ≤ card x := by
  classical
  unfold card
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  intro h
  exact hi (by change s i * x i = 0; rw [h, mul_zero])

lemma card_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    card (x ∘ σ) = card x := by
  classical
  simp only [card, Finset.card_filter, Function.comp_apply]
  exact Equiv.sum_comp σ (fun i => if x i ≠ 0 then (1 : ℕ) else 0)

lemma hull_map {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (K : ℕ)
    (T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hT : ∀ x ∈ NK ns K, T x ∈ NK ns K) {x : Fin n → ℝ}
    (hx : x ∈ convexHull ℝ (NK ns K)) : T x ∈ convexHull ℝ (NK ns K) := by
  have hsubset : convexHull ℝ (NK ns K) ⊆ T ⁻¹' convexHull ℝ (NK ns K) := by
    apply convexHull_min
    · intro z hz
      exact subset_convexHull ℝ (NK ns K) (hT z hz)
    · exact (convex_convexHull ℝ (NK ns K)).linear_preimage T
  exact hsubset hx

lemma hull_signMap {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (s : Fin n → ℝ) (hs : ∀ i, |s i| = 1) {x : Fin n → ℝ}
    (hx : x ∈ convexHull ℝ (NK ns K)) : signMap s x ∈ convexHull ℝ (NK ns K) := by
  apply hull_map ns K (signMap s) ?_ hx
  intro z hz
  refine ⟨?_, (card_signMap_le s z).trans hz.2⟩
  have heq : ns (signMap s z) = ns z := hns.sign _ _ (by
    intro i
    change |s i * z i| = |z i|
    rw [abs_mul, hs, one_mul])
  exact heq.le.trans hz.1

lemma hull_sign {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (x y : Fin n → ℝ) (hxy : ∀ i, |x i| = |y i|)
    (hx : x ∈ convexHull ℝ (NK ns K)) : y ∈ convexHull ℝ (NK ns K) := by
  classical
  let s : Fin n → ℝ := fun i => if x i = y i then 1 else -1
  have hs : ∀ i, |s i| = 1 := by
    intro i
    dsimp [s]
    split <;> norm_num
  have heq : signMap s x = y := by
    ext i
    change (if x i = y i then (1 : ℝ) else -1) * x i = y i
    split_ifs with h
    · simpa only [one_mul] using h
    · have hneg : x i = -y i := (abs_eq_abs.mp (hxy i)).resolve_left h
      simp only [neg_one_mul, hneg, neg_neg]
  rw [← heq]
  exact hull_signMap ns hns K s hs hx

lemma hull_perm {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (σ : Equiv.Perm (Fin n)) {x : Fin n → ℝ}
    (hx : x ∈ convexHull ℝ (NK ns K)) : x ∘ σ ∈ convexHull ℝ (NK ns K) := by
  apply hull_map ns K (permMap σ) ?_ hx
  intro z hz
  change ns (z ∘ σ) ≤ 1 ∧ card (z ∘ σ) ≤ K
  rw [hns.perm, card_perm]
  exact hz

lemma gauge_perm {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    normC ns K (x ∘ σ) = normC ns K x := by
  simp only [normC, gauge_def']
  congr 1
  ext r
  constructor
  · rintro ⟨hr, hm⟩
    refine ⟨hr, ?_⟩
    have hp := hull_perm ns hns K σ.symm hm
    have heq : (r⁻¹ • (x ∘ σ)) ∘ σ.symm = r⁻¹ • x := by
      ext i
      simp
    exact heq ▸ hp
  · rintro ⟨hr, hm⟩
    exact ⟨hr, hull_perm ns hns K σ hm⟩

lemma gauge_sign {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (x y : Fin n → ℝ) (hxy : ∀ i, |x i| = |y i|) :
    normC ns K x = normC ns K y := by
  simp only [normC, gauge_def']
  congr 1
  ext r
  have hscaled : ∀ i, |(r⁻¹ • x) i| = |(r⁻¹ • y) i| := by
    intro i
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, hxy]
  constructor
  · rintro ⟨hr, hm⟩
    exact ⟨hr, hull_sign ns hns K _ _ hscaled hm⟩
  · rintro ⟨hr, hm⟩
    exact ⟨hr, hull_sign ns hns K _ _ (fun i => (hscaled i).symm) hm⟩

theorem gaugeNorm_of_body {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (hbody : IsConvexBody (convexHull ℝ (NK ns K))) :
    IsSymmetricGauge (normC ns K) ∧
      convexHull ℝ (NK ns K) = {x | normC ns K x ≤ 1} := by
  let C := convexHull ℝ (NK ns K)
  have hc : Convex ℝ C := hbody.2.1
  have hneg : ∀ x ∈ C, -x ∈ C := by
    intro x hx
    exact hull_sign ns hns K x (-x) (by intro i; simp) hx
  have hbalanced : Balanced ℝ C := (balanced_iff_neg_mem hc).mpr (by
    intro x hx
    exact hneg x hx)
  have hinterior : (0 : Fin n → ℝ) ∈ interior C := by
    obtain ⟨z, hz⟩ := hbody.2.2
    have hmid := hc.combo_interior_self_mem_interior hz (hneg z (interior_subset hz))
      (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    simpa only [smul_neg, add_neg_cancel] using hmid
  have hnhds : C ∈ nhds (0 : Fin n → ℝ) := mem_interior_iff_mem_nhds.mp hinterior
  have habsorb : Absorbent ℝ C := absorbent_nhds_zero hnhds
  have hbounded : Bornology.IsVonNBounded ℝ C := hbody.1.isVonNBounded ℝ
  constructor
  · refine { eq_zero_iff := ?_, add_le := ?_, smul := ?_, perm := ?_, sign := ?_ }
    · intro x
      exact gauge_eq_zero habsorb hbounded
    · intro x y
      exact gauge_add_le hc habsorb x y
    · intro a x
      change gauge C (a • x) = |a| * gauge C x
      simpa only [Real.norm_eq_abs] using gauge_smul hbalanced a x
    · exact gauge_perm ns hns K
    · exact gauge_sign ns hns K
  · ext x
    change x ∈ C ↔ gauge C x ≤ 1
    rw [gauge_le_one_iff_mem_closure hc hnhds, hbody.1.isClosed.closure_eq]

end GaugeNormAux

theorem solution {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (hK : 1 < K) (hKn : K < n) :
    IsSymmetricGauge (normC ns K) ∧
      convexHull ℝ (NK ns K) = {x | normC ns K x ≤ 1} := by
  exact GaugeNormAux.gaugeNorm_of_body ns hns K
    (PermInvConvex.Sparsity.proposition_3_1 ns hns K hK hKn)
